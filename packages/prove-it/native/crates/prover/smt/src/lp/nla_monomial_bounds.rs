// Ported from Z3 (src/math/lp/monomial_bounds.{h,cpp}, src/util/mpq.h root), MIT license, see
// z3-license.txt. Bounds of monomials from the intervals of their factors and back, the
// linearization of monomials with at most one non-fixed factor, and the optimization of the bounds
// of nonlinear variables over the tableau. The shared-factor and binomial-sign lemmas, off by
// default (arith.nl.monomial_sandwich, arith.nl.monomial_binomial_sign), are not ported.
//
// optimize_nl_bounds calls find_feasible_solution twice and drains the changed bounds right after
// each, see the top of nla_core.rs.
use std::cmp::Ordering;

use prove_num::{Rational, get_lcm};

use crate::lp::constraints::{ConstraintKind, KIND_EQ, KIND_GE, KIND_GT, KIND_LE, KIND_LT};
use crate::lp::core_solver::LP_INFEASIBLE;
use crate::lp::dep_intervals::{
    DepInterval, DepsMode, div, mk_dep_interval, mul_in_place, power_in_place, separated_from_zero,
    set, set_value,
};
use crate::lp::dependency::{Dependency, linearize, mk_join};
use crate::lp::explanation::Explanation;
use crate::lp::lar_solver::NULL_LPVAR;
use crate::lp::nla_core::{NLA_PARAMS, Nla, NlaEquality, NlaFixedEquality};
use crate::lp::nla_types::LemmaBuilder;
use crate::lp::numeric_pair::Impq;

#[derive(Clone)]
struct Gain {
    is_unbounded: bool,
    min_gain: Rational,
    max_gain: Impq,
}

struct ImprovedBound {
    column: usize,
    kind: ConstraintKind,
    bound: Rational,
    dep: Dependency,
}

// The non-fixed factor and the factor fixed to zero of a linear monomial, NULL_LPVAR for none.
struct Linear {
    non_fixed: usize,
    fixed_to_zero: usize,
}

// pick_var_to_leave's result.
struct Picked {
    is_safe: bool,
    gain: Gain,
    leaving: usize,
    leaving_coeff: Rational,
}

// The choice of a round of max_min, which TS keeps in the round's local variables.
struct Round {
    entering: usize,
    leaving: usize,
    leaving_coeff: Rational,
    best: Gain,
    is_increasing: bool,
    has_bound: bool,
}

fn get_abs(value: Impq) -> Impq {
    if value.x.is_negative() || (value.x.is_zero() && value.y.is_negative()) {
        value.neg()
    } else {
        value
    }
}

// normalize_gain: rounds a value down to a multiple of an integral divisor, -1 meaning none.
fn round_down(value: &Impq, divisor: &Rational) -> Impq {
    if *divisor == Rational::one() {
        return Impq::from_x(value.floor());
    }
    if *divisor == Rational::minus_one() {
        return value.clone();
    }
    Impq::from_x(value.div(divisor).floor().mul(divisor))
}

fn get_bit_size(value: &Rational) -> u64 {
    if value.num().is_zero() {
        1
    } else {
        value.num().bit_length()
    }
}

fn get_explanation(dep: &Dependency) -> Explanation {
    let mut explanation = Explanation::new();
    for constraint in linearize(std::slice::from_ref(dep)) {
        explanation.add_pair(constraint as usize, Rational::one());
    }
    explanation
}

fn is_safe_gain(gain: &Gain) -> bool {
    gain.is_unbounded
        || Impq::from_x(gain.min_gain.clone()).compare(&gain.max_gain) != Ordering::Greater
}

#[derive(Default)]
pub struct MonomialBounds {}

impl MonomialBounds {
    // generate_lemmas: with the sandwich and binomial-sign lemmas off, the conflict of an
    // infeasible lp solver, once some monic needs refinement.
    pub fn generate_lemmas(nla: &mut Nla<'_, '_>) {
        if nla.to_refine.size() > 0 {
            MonomialBounds::add_lemma(nla);
        }
    }

    fn compute_product(nla: &Nla<'_, '_>, start: usize, monic: usize, product: &mut DepInterval) {
        let mut interval = mk_dep_interval();
        let vars = &nla.emons.monics[monic].vars;
        let mut index = start;
        while index < vars.len() {
            let lp_var = vars[index];
            MonomialBounds::var_to_interval(nla, lp_var, &mut interval);
            index += 1;
            let mut exponent = 1;
            while index < vars.len() && vars[index] == lp_var {
                index += 1;
                exponent += 1;
            }
            power_in_place(&mut interval, exponent, DepsMode::WithDeps);
            mul_in_place(product, &interval, DepsMode::WithDeps);
        }
    }

    fn var_to_interval(nla: &Nla<'_, '_>, lp_var: usize, interval: &mut DepInterval) {
        match nla.lra.get_bound(lp_var, false) {
            Some(lower) => {
                interval.is_lower_open = lower.is_strict;
                interval.lower = lower.value;
                interval.lower_dep = lower.dep;
                interval.is_lower_inf = false;
            }
            None => interval.is_lower_inf = true,
        }
        match nla.lra.get_bound(lp_var, true) {
            Some(upper) => {
                interval.is_upper_open = upper.is_strict;
                interval.upper = upper.value;
                interval.upper_dep = upper.dep;
                interval.is_upper_inf = false;
            }
            None => interval.is_upper_inf = true,
        }
    }

    // tighten_lp: the bounds of the factors from the monic's interval, and of the monic from
    // theirs.
    fn tighten_lp(nla: &mut Nla<'_, '_>, monic: usize) -> bool {
        let (num_free, free_var) = MonomialBounds::analyze_monomial(nla, monic);
        let variable = nla.emons.monics[monic].variable;
        let is_propagating_up = num_free == 0;
        let is_propagating_down = !MonomialBounds::is_free(nla, variable) && num_free <= 1;
        if !is_propagating_up && !is_propagating_down {
            return false;
        }
        let mut product = mk_dep_interval();
        let mut interval = mk_dep_interval();
        let mut monic_interval = mk_dep_interval();
        let mut other_product = mk_dep_interval();
        MonomialBounds::var_to_interval(nla, variable, &mut monic_interval);
        set_value(&mut product, &Rational::one());
        let mut is_tightened = false;
        let vars = nla.emons.monics[monic].vars.clone();
        let mut index = 0;
        while index < vars.len() {
            let lp_var = vars[index];
            index += 1;
            let mut exponent = 1;
            while index < vars.len() && lp_var == vars[index] {
                index += 1;
                exponent += 1;
            }
            MonomialBounds::var_to_interval(nla, lp_var, &mut interval);
            power_in_place(&mut interval, exponent, DepsMode::WithDeps);
            if is_propagating_down && (num_free == 0 || free_var == lp_var) {
                set(&mut other_product, &product, DepsMode::WithDeps);
                MonomialBounds::compute_product(nla, index, monic, &mut other_product);
                if MonomialBounds::tighten_lp_bound_by_division(
                    nla,
                    &monic_interval,
                    lp_var,
                    exponent,
                    &other_product,
                ) {
                    is_tightened = true;
                }
            }
            mul_in_place(&mut product, &interval, DepsMode::WithDeps);
        }
        if !is_propagating_up {
            return is_tightened;
        }
        MonomialBounds::tighten_lp_bound(nla, &product, variable, 1) || is_tightened
    }

    fn tighten_lp_bound_by_division(
        nla: &mut Nla<'_, '_>,
        monic_interval: &DepInterval,
        lp_var: usize,
        exponent: u32,
        product: &DepInterval,
    ) -> bool {
        if !separated_from_zero(product) {
            return false;
        }
        let mut range = mk_dep_interval();
        div(monic_interval, product, &mut range, DepsMode::WithDeps);
        MonomialBounds::tighten_lp_bound(nla, &range, lp_var, exponent)
    }

    fn is_free(nla: &Nla<'_, '_>, lp_var: usize) -> bool {
        !nla.has_lower_bound(lp_var) && !nla.has_upper_bound(lp_var)
    }

    fn is_zero(nla: &Nla<'_, '_>, lp_var: usize) -> bool {
        nla.has_lower_bound(lp_var)
            && nla.has_upper_bound(lp_var)
            && nla.get_lower_bound(lp_var).is_zero()
            && nla.get_upper_bound(lp_var).is_zero()
    }

    // analyze_monomial: the number of free variables of odd degree, and the last of them.
    fn analyze_monomial(nla: &Nla<'_, '_>, monic: usize) -> (usize, usize) {
        let vars = &nla.emons.monics[monic].vars;
        let mut num_free = 0;
        let mut free_var = NULL_LPVAR;
        let mut index = 0;
        while index < vars.len() {
            let lp_var = vars[index];
            index += 1;
            let mut exponent = 1;
            while index < vars.len() && vars[index] == lp_var {
                index += 1;
                exponent += 1;
            }
            if MonomialBounds::is_zero(nla, lp_var) {
                return (0, free_var);
            }
            if exponent % 2 == 1 && MonomialBounds::is_free(nla, lp_var) {
                num_free += 1;
                free_var = lp_var;
            }
        }
        (num_free, free_var)
    }

    pub fn propagate_changed_bounds(nla: &mut Nla<'_, '_>) -> bool {
        let mut is_propagated = false;
        let mut index = 0;
        while index < nla.monics_with_changed_bounds.elems.len() {
            let lp_var = nla.monics_with_changed_bounds.elems[index];
            index += 1;
            if !nla.is_monic_var(lp_var) {
                continue;
            }
            let monic = nla.emons.get_index(lp_var);
            if MonomialBounds::propagate_linear_bound(nla, monic) {
                is_propagated = true;
            }
            if MonomialBounds::tighten_lp(nla, monic) {
                is_propagated = true;
            }
            if nla.lra.status == LP_INFEASIBLE {
                break;
            }
        }
        is_propagated
    }

    // add_lemma: a conflict lemma when the lp solver is infeasible.
    fn add_lemma(nla: &mut Nla<'_, '_>) -> bool {
        if nla.lra.status != LP_INFEASIBLE {
            return false;
        }
        let mut explanation = Explanation::new();
        nla.lra.get_infeasibility_explanation(&mut explanation);
        LemmaBuilder::new(nla).add_explanation(nla, &explanation);
        true
    }

    fn propagate_linear_bound(nla: &mut Nla<'_, '_>, monic: usize) -> bool {
        if nla.emons.monics[monic].is_propagated {
            return false;
        }
        let Some(linear) = MonomialBounds::get_linear(nla, monic) else {
            return false;
        };
        nla.emons.set_propagated(monic);
        MonomialBounds::linearize(nla, monic, linear.non_fixed, linear.fixed_to_zero)
    }

    fn linearize(
        nla: &mut Nla<'_, '_>,
        monic: usize,
        non_fixed: usize,
        fixed_to_zero: usize,
    ) -> bool {
        let is_propagated = if fixed_to_zero != NULL_LPVAR {
            MonomialBounds::propagate_fixed_to_zero(nla, monic, fixed_to_zero)
        } else {
            let product = MonomialBounds::get_fixed_var_product(nla, monic, non_fixed);
            if non_fixed == NULL_LPVAR {
                MonomialBounds::propagate_fixed(nla, monic, product)
            } else {
                MonomialBounds::propagate_nonfixed(nla, monic, &product, non_fixed)
            }
        };
        if is_propagated {
            nla.stats().nla_propagate_eq += 1;
        }
        is_propagated
    }

    // propagate_violated_linear_monomials: the defining rows of violated monomials with at most
    // one non-fixed factor, except for small fixed products, which branching enumerates.
    pub fn propagate_violated_linear_monomials(nla: &mut Nla<'_, '_>) -> bool {
        if !NLA_PARAMS.linearize_violated_monomials || !nla.lra.is_feasible() {
            return false;
        }
        let mut is_propagated = false;
        for monic in 0..nla.emons.monics.len() {
            if nla.check_monic(monic) {
                continue;
            }
            let Some(linear) = MonomialBounds::get_linear(nla, monic) else {
                continue;
            };
            if linear.fixed_to_zero == NULL_LPVAR && linear.non_fixed != NULL_LPVAR {
                let product = MonomialBounds::get_fixed_var_product(nla, monic, linear.non_fixed);
                if product.is_int() && get_bit_size(&product) <= 16 {
                    continue;
                }
            }
            if MonomialBounds::linearize(nla, monic, linear.non_fixed, linear.fixed_to_zero) {
                is_propagated = true;
            }
            if nla.lra.status == LP_INFEASIBLE {
                break;
            }
        }
        is_propagated
    }

    fn propagate_fixed_to_zero(nla: &mut Nla<'_, '_>, monic: usize, fixed_to_zero: usize) -> bool {
        let variable = nla.emons.monics[monic].variable;
        if nla.var_is_fixed_to_zero(variable) {
            return false;
        }
        let dep = nla.lra.get_bound_witnesses(fixed_to_zero);
        nla.lra
            .update_column_type_and_bound(variable, KIND_EQ, &Impq::zero(), dep.clone());
        nla.fixed_equalities.push(NlaFixedEquality {
            lp_var: variable,
            value: Rational::zero(),
            explanation: get_explanation(&dep),
        });
        true
    }

    fn propagate_fixed(nla: &mut Nla<'_, '_>, monic: usize, value: Rational) -> bool {
        let variable = nla.emons.monics[monic].variable;
        if nla.var_is_fixed(variable) && nla.get_lower_bound(variable) == value {
            return false;
        }
        let dep = MonomialBounds::explain_fixed(nla, monic, &value);
        nla.lra.update_column_type_and_bound(
            variable,
            KIND_EQ,
            &Impq::from_x(value.clone()),
            dep.clone(),
        );
        nla.fixed_equalities.push(NlaFixedEquality {
            lp_var: variable,
            value,
            explanation: get_explanation(&dep),
        });
        true
    }

    // propagate_nonfixed: the row m - k * w = 0.
    fn propagate_nonfixed(
        nla: &mut Nla<'_, '_>,
        monic: usize,
        coeff: &Rational,
        non_fixed: usize,
    ) -> bool {
        let variable = nla.emons.monics[monic].variable;
        if nla.val(variable) == coeff.mul(&nla.val(non_fixed)) {
            return false;
        }
        let column = nla.lra.add_term(
            &[(non_fixed, coeff.neg()), (variable, Rational::one())],
            NULL_LPVAR,
        );
        let dep = MonomialBounds::explain_fixed(nla, monic, coeff);
        nla.lra
            .update_column_type_and_bound(column, KIND_EQ, &Impq::zero(), dep.clone());
        if *coeff == Rational::one() {
            nla.equalities.push(NlaEquality {
                first: variable,
                second: non_fixed,
                explanation: get_explanation(&dep),
            });
        }
        true
    }

    fn explain_fixed(nla: &Nla<'_, '_>, monic: usize, value: &Rational) -> Dependency {
        let lra = &nla.lra;
        let mut dep: Dependency = None;
        let mut update_dep = |lp_var: usize| {
            dep = mk_join(&dep, lra.get_lower_witness(lp_var));
            dep = mk_join(&dep, lra.get_upper_witness(lp_var));
            dep.clone()
        };
        let vars = &nla.emons.monics[monic].vars;
        if value.is_zero() {
            for lp_var in vars {
                if nla.var_is_fixed_to_zero(*lp_var) {
                    return update_dep(*lp_var);
                }
            }
        } else {
            for lp_var in vars {
                if nla.var_is_fixed(*lp_var) {
                    update_dep(*lp_var);
                }
            }
        }
        dep
    }

    // is_linear: the one non-fixed factor, or a factor fixed to zero, unless two are non-fixed.
    fn get_linear(nla: &Nla<'_, '_>, monic: usize) -> Option<Linear> {
        let mut non_fixed = NULL_LPVAR;
        for lp_var in &nla.emons.monics[monic].vars {
            if !nla.var_is_fixed(*lp_var) {
                if non_fixed != NULL_LPVAR {
                    return None;
                }
                non_fixed = *lp_var;
            } else if nla.get_lower_bound(*lp_var).is_zero() {
                return Some(Linear {
                    non_fixed,
                    fixed_to_zero: *lp_var,
                });
            }
        }
        Some(Linear {
            non_fixed,
            fixed_to_zero: NULL_LPVAR,
        })
    }

    // fixed_var_product: from the lower bounds, since a value may lie outside its bounds.
    fn get_fixed_var_product(nla: &Nla<'_, '_>, monic: usize, non_fixed: usize) -> Rational {
        let mut product = Rational::one();
        for lp_var in &nla.emons.monics[monic].vars {
            if *lp_var != non_fixed {
                product = product.mul(&nla.lra.get_lower_bound(*lp_var).x);
            }
        }
        product
    }

    // range is an interval that v^p lies in: v's upper bound from it.
    fn tighten_lp_upper_bound(
        nla: &mut Nla<'_, '_>,
        range: &DepInterval,
        lp_var: usize,
        exponent: u32,
    ) -> bool {
        let is_improving_upper = |nla: &Nla<'_, '_>, candidate: &Rational| {
            !nla.has_upper_bound(lp_var)
                || candidate.compare(&nla.get_upper_bound(lp_var)) == Ordering::Less
        };
        let mut is_tightened = false;
        if !range.is_upper_inf
            && let Some(root) = range.upper.root(exponent)
            && is_improving_upper(nla, &root)
        {
            let kind = if range.is_upper_open {
                KIND_LT
            } else {
                KIND_LE
            };
            MonomialBounds::propagate_lp_bound(nla, lp_var, kind, &root, range.upper_dep.clone());
            is_tightened = true;
        }
        if exponent.is_multiple_of(2)
            && !range.is_lower_inf
            && nla.has_upper_bound(lp_var)
            && !nla.get_upper_bound(lp_var).is_positive()
            && !range.lower.is_negative()
            && let Some(root) = range.lower.root(exponent)
            && is_improving_upper(nla, &root.neg())
        {
            let dep = mk_join(&range.lower_dep, nla.lra.get_upper_witness(lp_var));
            let kind = if range.is_lower_open {
                KIND_LT
            } else {
                KIND_LE
            };
            MonomialBounds::propagate_lp_bound(nla, lp_var, kind, &root.neg(), dep);
            is_tightened = true;
        }
        is_tightened
    }

    fn tighten_lp_lower_bound(
        nla: &mut Nla<'_, '_>,
        range: &DepInterval,
        lp_var: usize,
        exponent: u32,
    ) -> bool {
        let is_improving_lower = |nla: &Nla<'_, '_>, candidate: &Rational| {
            !nla.has_lower_bound(lp_var)
                || candidate.compare(&nla.get_lower_bound(lp_var)) == Ordering::Greater
        };
        let mut is_tightened = false;
        if exponent % 2 == 1 {
            if !range.is_lower_inf
                && let Some(root) = range.lower.root(exponent)
                && is_improving_lower(nla, &root)
            {
                let kind = if range.is_lower_open {
                    KIND_GT
                } else {
                    KIND_GE
                };
                MonomialBounds::propagate_lp_bound(
                    nla,
                    lp_var,
                    kind,
                    &root,
                    range.lower_dep.clone(),
                );
                is_tightened = true;
            }
            return is_tightened;
        }
        if !range.is_upper_inf
            && !range.upper.is_negative()
            && let Some(root) = range.upper.root(exponent)
            && is_improving_lower(nla, &root.neg())
        {
            let kind = if range.is_upper_open {
                KIND_GT
            } else {
                KIND_GE
            };
            MonomialBounds::propagate_lp_bound(
                nla,
                lp_var,
                kind,
                &root.neg(),
                range.upper_dep.clone(),
            );
            is_tightened = true;
        }
        if !range.is_lower_inf
            && nla.has_lower_bound(lp_var)
            && !nla.get_lower_bound(lp_var).is_negative()
            && !range.lower.is_negative()
            && let Some(root) = range.lower.root(exponent)
            && is_improving_lower(nla, &root)
        {
            let dep = mk_join(&range.lower_dep, nla.lra.get_lower_witness(lp_var));
            let kind = if range.is_lower_open {
                KIND_GT
            } else {
                KIND_GE
            };
            MonomialBounds::propagate_lp_bound(nla, lp_var, kind, &root, dep);
            is_tightened = true;
        }
        is_tightened
    }

    // propagate_lp_bound: a bound on v, integral when v is.
    fn propagate_lp_bound(
        nla: &mut Nla<'_, '_>,
        lp_var: usize,
        kind: ConstraintKind,
        value: &Rational,
        dep: Dependency,
    ) {
        let (update_kind, bound) = if !nla.var_is_int(lp_var) {
            (kind, value.clone())
        } else if value.is_int() {
            if kind == KIND_GT {
                (KIND_GE, value.add(&Rational::one()))
            } else if kind == KIND_LT {
                (KIND_LE, value.sub(&Rational::one()))
            } else {
                (kind, value.clone())
            }
        } else if kind == KIND_GE || kind == KIND_GT {
            (KIND_GE, value.ceil())
        } else {
            (KIND_LE, value.floor())
        };
        nla.lra
            .update_column_type_and_bound(lp_var, update_kind, &Impq::from_x(bound), dep);
    }

    fn tighten_lp_bound(
        nla: &mut Nla<'_, '_>,
        range: &DepInterval,
        lp_var: usize,
        exponent: u32,
    ) -> bool {
        let mut is_propagated = false;
        if MonomialBounds::tighten_lp_upper_bound(nla, range, lp_var, exponent) {
            is_propagated = true;
        }
        if MonomialBounds::tighten_lp_lower_bound(nla, range, lp_var, exponent) {
            is_propagated = true;
        }
        is_propagated
    }

    pub fn tighten_lp_bounds(nla: &mut Nla<'_, '_>) -> bool {
        let mut is_new_bound = false;
        for monic in 0..nla.emons.monics.len() {
            if MonomialBounds::tighten_lp(nla, monic) {
                is_new_bound = true;
            }
        }
        is_new_bound
    }

    // max_min: a bounded-effort primal simplex walk that maximizes or minimizes a column, keeping
    // integer columns integral, as theory_arith::max_min does.

    fn init_gains(nla: &Nla<'_, '_>, column: usize, is_increasing: bool) -> Gain {
        let core = &nla.lra.core;
        let mut gain = Gain {
            is_unbounded: true,
            min_gain: Rational::minus_one(),
            max_gain: Impq::zero(),
        };
        if is_increasing && core.has_upper_bound(column) {
            gain.is_unbounded = false;
            gain.max_gain = core.upper_bounds[column].sub(&core.x[column]);
        } else if !is_increasing && core.has_lower_bound(column) {
            gain.is_unbounded = false;
            gain.max_gain = core.x[column].sub(&core.lower_bounds[column]);
        }
        if nla.lra.is_int(column) {
            gain.min_gain = Rational::one();
        }
        gain
    }

    fn update_gains(
        nla: &Nla<'_, '_>,
        is_increasing: bool,
        basic: usize,
        coeff: &Rational,
        gain: &mut Gain,
    ) -> bool {
        let core = &nla.lra.core;
        if !is_safe_gain(gain) {
            return false;
        }
        let is_decrementing =
            (is_increasing && coeff.is_positive()) || (!is_increasing && coeff.is_negative());
        let mut is_bounded = false;
        let mut max_increase = Impq::zero();
        if is_decrementing && core.has_lower_bound(basic) {
            max_increase = get_abs(core.x[basic].sub(&core.lower_bounds[basic]).div(coeff));
            is_bounded = true;
        } else if !is_decrementing && core.has_upper_bound(basic) {
            max_increase = get_abs(core.upper_bounds[basic].sub(&core.x[basic]).div(coeff));
            is_bounded = true;
        }
        let is_basic_int = nla.lra.is_int(basic);
        let coeff_den = if is_basic_int {
            Rational::from(coeff.den().clone())
        } else {
            Rational::one()
        };
        if is_basic_int && coeff_den != Rational::one() {
            gain.min_gain = if gain.min_gain.is_negative() {
                coeff_den
            } else {
                Rational::from(get_lcm(gain.min_gain.num(), coeff_den.num()))
            };
            if !gain.is_unbounded {
                gain.max_gain = round_down(&gain.max_gain, &gain.min_gain);
            }
        }
        if is_basic_int && !gain.is_unbounded && !gain.max_gain.is_int() {
            gain.max_gain = round_down(&Impq::from_x(gain.max_gain.floor()), &gain.min_gain);
        }
        if !is_bounded {
            return false;
        }
        if is_basic_int {
            max_increase = round_down(&Impq::from_x(max_increase.floor()), &gain.min_gain);
        }
        if gain.is_unbounded {
            gain.is_unbounded = false;
            gain.max_gain = max_increase;
            return true;
        }
        if gain.max_gain.compare(&max_increase) == Ordering::Greater {
            gain.max_gain = max_increase;
            return true;
        }
        false
    }

    fn pick_var_to_leave(nla: &Nla<'_, '_>, column: usize, is_increasing: bool) -> Picked {
        let core = &nla.lra.core;
        let mut leaving = NULL_LPVAR;
        let mut leaving_coeff = Rational::zero();
        let mut gain = MonomialBounds::init_gains(nla, column, is_increasing);
        if nla.lra.is_int(column) && !core.x[column].is_int() {
            return Picked {
                is_safe: false,
                gain,
                leaving,
                leaving_coeff,
            };
        }
        for cell in &core.matrix.columns[column] {
            let basic = core.basis[cell.row];
            let coeff = core.matrix.get_val(cell);
            if MonomialBounds::update_gains(nla, is_increasing, basic, coeff, &mut gain)
                || (leaving == NULL_LPVAR && !gain.is_unbounded)
            {
                leaving = basic;
                leaving_coeff = coeff.clone();
            }
        }
        Picked {
            is_safe: is_safe_gain(&gain),
            gain,
            leaving,
            leaving_coeff,
        }
    }

    fn update_value(nla: &mut Nla<'_, '_>, column: usize, delta: &Impq) {
        if delta.is_zero() {
            return;
        }
        let value = nla.lra.core.x[column].add(delta);
        nla.lra.set_value_for_nbasic_column(column, value);
    }

    fn move_to_bound(nla: &mut Nla<'_, '_>, column: usize, is_increasing: bool) -> bool {
        if nla.lra.is_int(column) && !nla.lra.core.x[column].is_int() {
            return false;
        }
        let mut gain = MonomialBounds::init_gains(nla, column, is_increasing);
        let core = &nla.lra.core;
        for cell in &core.matrix.columns[column] {
            MonomialBounds::update_gains(
                nla,
                is_increasing,
                core.basis[cell.row],
                core.matrix.get_val(cell),
                &mut gain,
            );
        }
        if !is_safe_gain(&gain) || gain.is_unbounded {
            return false;
        }
        let delta = if is_increasing {
            gain.max_gain.clone()
        } else {
            gain.max_gain.neg()
        };
        MonomialBounds::update_value(nla, column, &delta);
        !gain.max_gain.is_zero()
    }

    // The closure `consider` of optimize: whether the candidate column ends the search of the
    // round, choosing it as the entering column when it gains more.
    fn consider(
        nla: &Nla<'_, '_>,
        round: &mut Round,
        best_efforts: &mut u32,
        candidate: usize,
        objective_coeff: &Rational,
        is_maximizing: bool,
    ) -> bool {
        let core = &nla.lra.core;
        let is_current_increasing = if objective_coeff.is_positive() {
            is_maximizing
        } else {
            !is_maximizing
        };
        if (is_current_increasing && core.has_upper_bound(candidate))
            || (!is_current_increasing && core.has_lower_bound(candidate))
        {
            round.has_bound = true;
        }
        if is_current_increasing
            && core.has_upper_bound(candidate)
            && core.x[candidate] == core.upper_bounds[candidate]
        {
            return false;
        }
        if !is_current_increasing
            && core.has_lower_bound(candidate)
            && core.x[candidate] == core.lower_bounds[candidate]
        {
            return false;
        }
        let picked = MonomialBounds::pick_var_to_leave(nla, candidate, is_current_increasing);
        if !picked.is_safe {
            round.has_bound = true;
            *best_efforts += 1;
            return false;
        }
        let is_ending = picked.leaving == NULL_LPVAR;
        let is_selected = is_ending
            || picked.gain.max_gain.compare(&round.best.max_gain) == Ordering::Greater
            || (picked.gain.max_gain.is_zero()
                && (round.leaving == NULL_LPVAR || picked.leaving < round.leaving));
        if is_selected {
            round.leaving = picked.leaving;
            round.entering = candidate;
            round.leaving_coeff = picked.leaving_coeff;
            round.best = picked.gain;
            round.is_increasing = is_current_increasing;
        }
        is_ending
    }

    fn optimize(nla: &mut Nla<'_, '_>, target: usize, is_maximizing: bool) -> Option<Rational> {
        let mut best_efforts = 0;
        let mut rounds = 0;
        while best_efforts < 20 && rounds < 200 && !nla.is_canceled() {
            rounds += 1;
            let mut round = Round {
                entering: NULL_LPVAR,
                leaving: NULL_LPVAR,
                leaving_coeff: Rational::zero(),
                best: Gain {
                    is_unbounded: true,
                    min_gain: Rational::minus_one(),
                    max_gain: Impq::zero(),
                },
                is_increasing: false,
                has_bound: false,
            };
            let view: &Nla<'_, '_> = nla;
            let core = &view.lra.core;
            if !core.is_base(target) {
                MonomialBounds::consider(
                    view,
                    &mut round,
                    &mut best_efforts,
                    target,
                    &Rational::one(),
                    is_maximizing,
                );
            } else {
                let row = &core.matrix.rows[core.heading[target] as usize];
                let target_coeff = row
                    .iter()
                    .find(|cell| cell.column == target)
                    .map_or_else(Rational::zero, |cell| cell.coeff.clone());
                for cell in row {
                    if cell.column == target {
                        continue;
                    }
                    let objective_coeff = if target_coeff.is_negative() {
                        cell.coeff.clone()
                    } else {
                        cell.coeff.neg()
                    };
                    if MonomialBounds::consider(
                        view,
                        &mut round,
                        &mut best_efforts,
                        cell.column,
                        &objective_coeff,
                        is_maximizing,
                    ) {
                        break;
                    }
                }
            }
            if !round.has_bound && round.leaving == NULL_LPVAR && round.entering == NULL_LPVAR {
                return None;
            }
            let core = &nla.lra.core;
            if round.entering == NULL_LPVAR {
                if best_efforts != 0 || !core.x[target].y.is_zero() {
                    return None;
                }
                return Some(core.x[target].x.clone());
            }
            let gain = round.best;
            let entering = round.entering;
            let leaving = round.leaving;
            let is_increasing = round.is_increasing;
            if gain.min_gain.is_positive() && gain.min_gain != Rational::one() {
                best_efforts += 1;
            }
            let delta = if is_increasing {
                gain.max_gain.clone()
            } else {
                gain.max_gain.neg()
            };
            if leaving == NULL_LPVAR {
                let has_blocking_bound = if is_increasing {
                    core.has_upper_bound(entering)
                } else {
                    core.has_lower_bound(entering)
                };
                if !has_blocking_bound || gain.max_gain.is_zero() {
                    return None;
                }
                MonomialBounds::update_value(nla, entering, &delta);
                continue;
            }
            if core.has_lower_bound(entering)
                && core.has_upper_bound(entering)
                && core.lower_bounds[entering] != core.upper_bounds[entering]
                && core.upper_bounds[entering].sub(&core.lower_bounds[entering]) == gain.max_gain
            {
                MonomialBounds::update_value(nla, entering, &delta);
                continue;
            }
            nla.lra.core.pivot(entering, leaving);
            let is_leaving_increasing = if is_increasing {
                round.leaving_coeff.is_negative()
            } else {
                round.leaving_coeff.is_positive()
            };
            if !MonomialBounds::move_to_bound(nla, leaving, is_leaving_increasing) {
                best_efforts += 1;
            }
        }
        None
    }

    // mm_dep_from_row: the witnesses of the bounds that bound the column through its row.
    fn get_dep_from_row(
        nla: &Nla<'_, '_>,
        target: usize,
        is_maximizing: bool,
    ) -> Option<Dependency> {
        let lra = &nla.lra;
        let core = &lra.core;
        if !core.is_base(target) {
            return None;
        }
        let row = &core.matrix.rows[core.heading[target] as usize];
        let target_coeff = row
            .iter()
            .find(|cell| cell.column == target)
            .map_or_else(Rational::zero, |cell| cell.coeff.clone());
        if target_coeff.is_zero() {
            return None;
        }
        let mut dep: Dependency = None;
        for cell in row {
            if cell.column == target {
                continue;
            }
            let coeff = cell.coeff.neg().div(&target_coeff);
            if coeff.is_zero() {
                continue;
            }
            let is_using_upper = if is_maximizing {
                coeff.is_positive()
            } else {
                coeff.is_negative()
            };
            if is_using_upper {
                if !core.has_upper_bound(cell.column) {
                    return None;
                }
                dep = mk_join(&dep, lra.get_upper_witness(cell.column));
            } else {
                if !core.has_lower_bound(cell.column) {
                    return None;
                }
                dep = mk_join(&dep, lra.get_lower_witness(cell.column));
            }
        }
        Some(dep)
    }

    fn improve_bound(
        nla: &mut Nla<'_, '_>,
        column: usize,
        is_lower: bool,
    ) -> Option<(Rational, Dependency)> {
        if !nla.lra.is_feasible() {
            return None;
        }
        let bound = MonomialBounds::optimize(nla, column, !is_lower)?;
        let dep = MonomialBounds::get_dep_from_row(nla, column, !is_lower)?;
        let core = &nla.lra.core;
        if is_lower
            && core.has_lower_bound(column)
            && bound.compare(&core.lower_bounds[column].x) != Ordering::Greater
        {
            return None;
        }
        if !is_lower
            && core.has_upper_bound(column)
            && bound.compare(&core.upper_bounds[column].x) != Ordering::Less
        {
            return None;
        }
        Some((bound, dep))
    }

    fn add_candidate(nla: &mut Nla<'_, '_>, candidates: &mut Vec<usize>, lp_var: usize) {
        if nla.active_var_set.has(lp_var) {
            return;
        }
        nla.active_var_set.add(lp_var);
        if !nla.lra.is_fixed(lp_var) {
            candidates.push(lp_var);
        }
    }

    // optimize_nl_bounds: tightens the bounds of the variables of monomials by optimizing each
    // over the tableau, then applies them together and makes the tableau feasible again.
    pub fn optimize_nl_bounds(nla: &mut Nla<'_, '_>) -> bool {
        if !NLA_PARAMS.optimize_bounds || !nla.lra.is_feasible() {
            return false;
        }
        let status = nla.lra.find_feasible_solution();
        nla.drain_changed_bounds();
        if status == LP_INFEASIBLE {
            nla.init_to_refine();
            return false;
        }
        let mut candidates = Vec::new();
        nla.active_var_set.clear();
        for monic in 0..nla.emons.monics.len() {
            let variable = nla.emons.monics[monic].variable;
            MonomialBounds::add_candidate(nla, &mut candidates, variable);
            for index in 0..nla.emons.monics[monic].vars.len() {
                let lp_var = nla.emons.monics[monic].vars[index];
                MonomialBounds::add_candidate(nla, &mut candidates, lp_var);
            }
        }
        let max_vars = NLA_PARAMS.optimize_bounds_lp_max_vars;
        if max_vars != 0 && candidates.len() > max_vars {
            nla.init_to_refine();
            return false;
        }
        let mut improvements = Vec::new();
        for column in candidates {
            if !nla.lra.is_feasible() {
                break;
            }
            for is_lower in [true, false] {
                let Some((bound, dep)) = MonomialBounds::improve_bound(nla, column, is_lower)
                else {
                    continue;
                };
                improvements.push(ImprovedBound {
                    column,
                    kind: if is_lower { KIND_GE } else { KIND_LE },
                    bound,
                    dep,
                });
            }
        }
        let is_improved = !improvements.is_empty();
        for improved in improvements {
            nla.lra.update_column_type_and_bound(
                improved.column,
                improved.kind,
                &Impq::from_x(improved.bound),
                improved.dep,
            );
        }
        nla.lra.find_feasible_solution();
        nla.drain_changed_bounds();
        nla.init_to_refine();
        is_improved
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lp::nla_core::tests::{NlaFixture, show_lemmas};

    // What the TS oracle printed after a pass: the lp status, the values and the variables to
    // refine, the bounds of the columns with their witnesses' constraints, and the equalities nla
    // found.
    fn show(fixture: &NlaFixture<'_>) -> [String; 4] {
        let lra = &fixture.lra;
        let show_witness = |dep: &Dependency| {
            let constraints: Vec<String> = linearize(std::slice::from_ref(dep))
                .iter()
                .map(u32::to_string)
                .collect();
            constraints.join(",")
        };
        let bounds: Vec<String> = (0..lra.get_column_count())
            .map(|column| {
                let lower = if lra.core.has_lower_bound(column) {
                    format!(
                        "{}{{{}}}",
                        lra.core.lower_bounds[column],
                        show_witness(lra.get_lower_witness(column))
                    )
                } else {
                    "-".to_string()
                };
                let upper = if lra.core.has_upper_bound(column) {
                    format!(
                        "{}{{{}}}",
                        lra.core.upper_bounds[column],
                        show_witness(lra.get_upper_witness(column))
                    )
                } else {
                    "-".to_string()
                };
                format!("v{column}[{lower},{upper}]")
            })
            .collect();
        let show_explanation = |explanation: &Explanation| {
            let constraints: Vec<String> =
                explanation.iter().map(|index| index.to_string()).collect();
            constraints.join(",")
        };
        let mut eqs: Vec<String> = fixture
            .core
            .fixed_equalities
            .iter()
            .map(|eq| {
                format!(
                    "v{}={}{{{}}}",
                    eq.lp_var,
                    eq.value,
                    show_explanation(&eq.explanation)
                )
            })
            .collect();
        eqs.extend(fixture.core.equalities.iter().map(|eq| {
            format!(
                "v{}=v{}{{{}}}",
                eq.first,
                eq.second,
                show_explanation(&eq.explanation)
            )
        }));
        [
            format!("status {}", lra.status),
            fixture.show_state(),
            format!("bounds {}", bounds.join(" ")),
            format!(
                "eqs {} propagateEq {}",
                eqs.join(" "),
                lra.settings().stats.nla_propagate_eq
            ),
        ]
    }

    // The TS oracle's scenario with terms over the variables, added before the monics.
    fn mk_term_scenario<'l>(
        num_vars: usize,
        terms: &[(&[(usize, i64)], usize)],
        monics: &[(usize, &[usize])],
        bounds: &[(usize, ConstraintKind, i64)],
    ) -> NlaFixture<'l> {
        let mut fixture = NlaFixture::new();
        for external in 0..num_vars {
            fixture.lra.add_var(external, true);
        }
        for term in terms {
            let coeffs: Vec<(usize, Rational)> = term
                .0
                .iter()
                .map(|entry| (entry.0, Rational::from(entry.1)))
                .collect();
            fixture.lra.add_term(&coeffs, term.1);
        }
        fixture.with_nla(|nla| {
            for monic in monics {
                nla.add_monic(monic.0, monic.1);
            }
        });
        for bound in bounds {
            fixture.add_bound(bound.0, bound.1, bound.2);
        }
        fixture.prepare();
        fixture
    }

    // The expected states here and below are the TS oracle's on the same setups.
    #[test]
    fn tightens_the_monic_from_its_factors() {
        let (mut fixture, _) = NlaFixture::mk_scenario(
            3,
            &[(2, &[0, 1])],
            &[
                (0, KIND_GE, 1),
                (0, KIND_LE, 2),
                (1, KIND_GE, 2),
                (1, KIND_LE, 3),
            ],
        );
        assert!(fixture.with_nla(|nla| MonomialBounds::tighten_lp_bounds(nla)));
        assert_eq!(
            show(&fixture),
            [
                "status 2",
                "values 1,2,0 toRefine 2",
                "bounds v0[1{0},2{1}] v1[2{2},3{3}] v2[2{0,2},6{3,0,1}]",
                "eqs  propagateEq 0",
            ]
        );
        assert!(show_lemmas(&fixture.core).is_empty());
    }

    #[test]
    fn tightens_a_factor_from_the_monic() {
        let (mut fixture, _) = NlaFixture::mk_scenario(
            3,
            &[(2, &[0, 1])],
            &[
                (0, KIND_GE, 2),
                (0, KIND_LE, 3),
                (2, KIND_GE, 4),
                (2, KIND_LE, 12),
            ],
        );
        assert!(fixture.with_nla(|nla| MonomialBounds::tighten_lp_bounds(nla)));
        assert_eq!(
            show(&fixture),
            [
                "status 2",
                "values 2,0,4 toRefine 2",
                "bounds v0[2{0},3{1}] v1[2{1,2,0},6{0,3}] v2[4{2},12{3}]",
                "eqs  propagateEq 0",
            ]
        );
    }

    #[test]
    fn tightens_the_root_of_a_square() {
        let (mut fixture, _) =
            NlaFixture::mk_scenario(2, &[(1, &[0, 0])], &[(1, KIND_LE, 9), (1, KIND_GE, 1)]);
        assert!(fixture.with_nla(|nla| MonomialBounds::tighten_lp_bounds(nla)));
        assert_eq!(
            show(&fixture),
            [
                "status 2",
                "values 0,1 toRefine 1",
                "bounds v0[-3{0},3{0}] v1[1{1},9{0}]",
                "eqs  propagateEq 0",
            ]
        );
    }

    // TS's callback filled monics_with_changed_bounds in find_feasible_solution; here the drain.
    #[test]
    fn propagates_the_changed_bounds() {
        let (mut fixture, _) = NlaFixture::mk_scenario(
            3,
            &[(2, &[0, 1])],
            &[
                (0, KIND_GE, 2),
                (0, KIND_LE, 2),
                (1, KIND_GE, 1),
                (1, KIND_LE, 5),
            ],
        );
        assert!(fixture.with_nla(|nla| {
            nla.drain_changed_bounds();
            MonomialBounds::propagate_changed_bounds(nla)
        }));
        assert_eq!(
            show(&fixture),
            [
                "status 2",
                "values 2,1,0,-2 toRefine 2",
                "bounds v0[2{0},2{1}] v1[1{2},5{3}] v2[2{0,2},10{3,0,1}] v3[0{0,1},0{0,1}]",
                "eqs  propagateEq 1",
            ]
        );
    }

    #[test]
    fn linearizes_a_violated_monomial_with_a_large_fixed_factor() {
        let (mut fixture, _) = NlaFixture::mk_scenario(
            3,
            &[(2, &[0, 1])],
            &[(0, KIND_GE, 100000), (0, KIND_LE, 100000), (2, KIND_GE, 1)],
        );
        assert!(fixture.with_nla(|nla| MonomialBounds::propagate_violated_linear_monomials(nla)));
        assert_eq!(
            show(&fixture),
            [
                "status 2",
                "values 100000,0,1,1 toRefine 2",
                "bounds v0[100000{0},100000{1}] v1[-,-] v2[1{2},-] v3[0{0,1},0{0,1}]",
                "eqs  propagateEq 1",
            ]
        );
    }

    #[test]
    fn leaves_a_small_fixed_product_to_branching() {
        let (mut fixture, _) = NlaFixture::mk_scenario(
            3,
            &[(2, &[0, 1])],
            &[(0, KIND_GE, 3), (0, KIND_LE, 3), (2, KIND_GE, 1)],
        );
        assert!(!fixture.with_nla(|nla| MonomialBounds::propagate_violated_linear_monomials(nla)));
        assert_eq!(
            show(&fixture),
            [
                "status 2",
                "values 3,0,1 toRefine 2",
                "bounds v0[3{0},3{1}] v1[-,-] v2[1{2},-]",
                "eqs  propagateEq 0",
            ]
        );
    }

    #[test]
    fn fixes_a_violated_monomial_of_fixed_factors() {
        let (mut fixture, _) = NlaFixture::mk_scenario(
            3,
            &[(2, &[0, 1])],
            &[
                (0, KIND_GE, 2),
                (0, KIND_LE, 2),
                (1, KIND_GE, 3),
                (1, KIND_LE, 3),
                (2, KIND_LE, 1),
            ],
        );
        assert!(fixture.with_nla(|nla| MonomialBounds::propagate_violated_linear_monomials(nla)));
        assert_eq!(
            show(&fixture),
            [
                "status 1",
                "values 2,3,0 toRefine 2",
                "bounds v0[2{0},2{1}] v1[3{2},3{3}] v2[-,1{4}]",
                "eqs v2=6{3,2,0,1} propagateEq 1",
            ]
        );
    }

    #[test]
    fn reports_the_conflict_of_a_factor_fixed_to_zero() {
        let (mut fixture, _) = NlaFixture::mk_scenario(
            3,
            &[(2, &[0, 1])],
            &[(0, KIND_GE, 0), (0, KIND_LE, 0), (2, KIND_GE, 1)],
        );
        assert!(fixture.with_nla(|nla| {
            let is_propagated = MonomialBounds::propagate_violated_linear_monomials(nla);
            nla.lra.find_feasible_solution();
            MonomialBounds::generate_lemmas(nla);
            is_propagated
        }));
        assert_eq!(
            show(&fixture),
            [
                "status 1",
                "values 0,0,1 toRefine 2",
                "bounds v0[0{0},0{1}] v1[-,-] v2[1{2},-]",
                "eqs v2=0{0,1} propagateEq 1",
            ]
        );
        assert_eq!(show_lemmas(&fixture.core), ["[] {2,0,1}"]);
    }

    #[test]
    fn optimizes_the_bounds_of_the_factors_over_the_tableau() {
        let mut fixture = mk_term_scenario(
            3,
            &[(&[(0, 1), (1, 1)], 3)],
            &[(2, &[0, 1])],
            &[(3, KIND_LE, 10), (0, KIND_GE, 0), (1, KIND_GE, 3)],
        );
        assert!(fixture.with_nla(|nla| MonomialBounds::optimize_nl_bounds(nla)));
        assert_eq!(
            show(&fixture),
            [
                "status 2",
                "values 0,10,0,10 toRefine ",
                "bounds v0[0{1},7{2,0}] v1[3{2},10{1,0}] v2[-,-] v3[-,10{0}]",
                "eqs  propagateEq 0",
            ]
        );
    }

    #[test]
    fn improves_no_bound_through_two_rows() {
        let mut fixture = mk_term_scenario(
            3,
            &[(&[(0, 2), (1, -3)], 3), (&[(0, 1), (1, 1)], 4)],
            &[(2, &[0, 1])],
            &[
                (3, KIND_LE, 6),
                (3, KIND_GE, -6),
                (4, KIND_GE, 1),
                (4, KIND_LE, 9),
                (0, KIND_GE, 0),
                (1, KIND_GE, 0),
            ],
        );
        assert!(!fixture.with_nla(|nla| MonomialBounds::optimize_nl_bounds(nla)));
        assert_eq!(
            show(&fixture),
            [
                "status 2",
                "values 5,4,0,-2,9 toRefine 2",
                "bounds v0[0{4},-] v1[0{5},-] v2[-,-] v3[-6{1},6{0}] v4[1{2},9{3}]",
                "eqs  propagateEq 0",
            ]
        );
    }
}
