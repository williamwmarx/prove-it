// Ported from Z3 (src/math/lp/nla_intervals.h, src/math/lp/nla_intervals.cpp), MIT license, see
// z3-license.txt. Evaluates a nex expression over the bounds of its variables. When the interval
// excludes zero, the expression cannot vanish, so the bounds behind the interval and the
// dependencies of the row conflict with the row's equation, and the conflict becomes a lemma.
//
// The TypeScript passes a report closure down the evaluation, which always adds the explanation
// as a lemma; here each function takes the view and adds it. The expressions are read from the
// arena of the creator that made them (nex.rs).
use prove_num::Rational;

use crate::lp::dep_intervals::{
    DepInterval, DepsMode, add, add_scalar, check_interval_for_conflict_on_zero, intersect,
    is_empty, mk_dep_interval, mul, mul_scalar, power, separated_from_zero, set, set_value,
    set_zero_interval_deps_for_mult,
};
use crate::lp::dependency::{Dependency, mk_join, mk_leaf};
use crate::lp::explanation::Explanation;
use crate::lp::lar_solver::LarSolver;
use crate::lp::lar_term::LarTerm;
use crate::lp::nex::{Nex, NexId, NexMul, NexSum, is_a_linear_term, is_elementary};
use crate::lp::nla_core::{Nla, NlaCore};
use crate::lp::nla_types::LemmaBuilder;

// The report of check_nex: the explanation becomes a lemma.
fn report(core: &mut NlaCore, explanation: &Explanation) {
    LemmaBuilder::new(core).add_explanation(core, explanation);
}

fn mk_explanation(constraints: Vec<u32>) -> Explanation {
    let mut explanation = Explanation::new();
    for constraint in constraints {
        explanation.push(constraint as usize);
    }
    explanation
}

// expression_to_normalized_term's result: the sum is coeff * term + constant.
struct NormalizedTerm {
    term: LarTerm,
    coeff: Rational,
    constant: Rational,
}

#[derive(Default)]
pub struct Intervals {}

impl Intervals {
    // check_nex: whether the expression's interval excludes zero, in which case a lemma explains it.
    pub fn check_nex(
        nla: &mut Nla<'_, '_>,
        nexes: &[Nex],
        expr: NexId,
        initial_deps: &Dependency,
    ) -> bool {
        let mut interval = mk_dep_interval();
        if !Intervals::interval_of_expr(nla, nexes, expr, 1, &mut interval, DepsMode::WithoutDeps) {
            return true;
        }
        if !separated_from_zero(&interval) {
            return false;
        }
        let mut interval_with_deps = mk_dep_interval();
        Intervals::interval_of_expr(
            nla,
            nexes,
            expr,
            1,
            &mut interval_with_deps,
            DepsMode::WithDeps,
        );
        check_interval_for_conflict_on_zero(
            &interval_with_deps,
            initial_deps,
            &mut |constraints| report(nla, &mk_explanation(constraints)),
        );
        true
    }

    fn has_zero_interval(nla: &Nla<'_, '_>, nexes: &[Nex], expr: NexId) -> bool {
        matches!(nexes[expr], Nex::Var(variable) if nla.var_is_fixed_to_zero(variable))
    }

    fn has_inf_interval(nla: &Nla<'_, '_>, nexes: &[Nex], expr: NexId) -> bool {
        match &nexes[expr] {
            Nex::Var(variable) => nla.no_bounds(*variable),
            Nex::Mul(product) => Intervals::mul_has_inf_interval(nla, nexes, product),
            Nex::Scalar(_) => false,
            Nex::Sum(sum) => sum
                .children
                .iter()
                .any(|child| Intervals::has_inf_interval(nla, nexes, *child)),
        }
    }

    fn mul_has_inf_interval(nla: &Nla<'_, '_>, nexes: &[Nex], product: &NexMul) -> bool {
        let mut has_inf = false;
        for child in &product.children {
            if !is_elementary(nexes, child.expr) {
                return false;
            }
            if Intervals::has_zero_interval(nla, nexes, child.expr) {
                return false;
            }
            has_inf = has_inf || Intervals::has_inf_interval(nla, nexes, child.expr);
        }
        has_inf
    }

    // expression_to_normalized_term: the sum a*t + b, where t is the linear part divided by the
    // coefficient of its smallest variable, which is a.
    fn expression_to_normalized_term(nexes: &[Nex], sum: &NexSum) -> NormalizedTerm {
        let mut pairs: Vec<(Rational, usize)> = Vec::new();
        let mut constant = Rational::zero();
        let mut smallest_var = 0;
        let mut coeff_index = None;
        for child in &sum.children {
            match &nexes[*child] {
                Nex::Scalar(value) => {
                    constant = constant.add(value);
                    continue;
                }
                Nex::Mul(product) => {
                    if let Nex::Var(variable) = nexes[product.children[0].expr] {
                        pairs.push((product.coeff.clone(), variable));
                    }
                }
                Nex::Var(variable) => pairs.push((Rational::one(), *variable)),
                Nex::Sum(_) => {}
            }
            let Some(last) = pairs.last() else {
                continue;
            };
            if pairs.len() == 1 || smallest_var > last.1 {
                smallest_var = last.1;
                coeff_index = Some(pairs.len() - 1);
            }
        }
        let coeff_index = coeff_index.expect("a linear term has a variable");
        let coeff = pairs[coeff_index].0.clone();
        let mut term = LarTerm::new();
        for (index, pair) in pairs.iter().enumerate() {
            if coeff == Rational::one() {
                term.add_monomial(&pair.0, pair.1);
            } else if index != coeff_index {
                term.add_monomial(&pair.0.div(&coeff), pair.1);
            } else {
                term.add_monomial(&Rational::one(), pair.1);
            }
        }
        NormalizedTerm {
            term,
            coeff,
            constant,
        }
    }

    pub fn set_var_interval(
        lra: &LarSolver<'_>,
        lp_var: usize,
        interval: &mut DepInterval,
        mode: DepsMode,
    ) {
        let is_column = lp_var < lra.columns.len();
        let lower_dep = if is_column {
            lra.get_lower_witness(lp_var).clone()
        } else {
            None
        };
        if lower_dep.is_some() {
            let bound = &lra.core.lower_bounds[lp_var];
            interval.lower = bound.x.clone();
            interval.is_lower_open = bound.y.is_positive();
            interval.is_lower_inf = false;
        } else {
            interval.is_lower_open = true;
            interval.is_lower_inf = true;
        }
        if mode == DepsMode::WithDeps {
            interval.lower_dep = lower_dep;
        }
        let upper_dep = if is_column {
            lra.get_upper_witness(lp_var).clone()
        } else {
            None
        };
        if upper_dep.is_some() {
            let bound = &lra.core.upper_bounds[lp_var];
            interval.upper = bound.x.clone();
            interval.is_upper_open = bound.y.is_negative();
            interval.is_upper_inf = false;
        } else {
            interval.is_upper_open = true;
            interval.is_upper_inf = true;
        }
        if mode == DepsMode::WithDeps {
            interval.upper_dep = upper_dep;
        }
    }

    // interval_from_term: the interval of a linear sum from the bounds of the term column that
    // equals it, or from an equivalence that fixes it.
    fn interval_from_term(
        nla: &mut Nla<'_, '_>,
        nexes: &[Nex],
        sum: &NexSum,
        interval: &mut DepInterval,
        mode: DepsMode,
    ) -> bool {
        let normalized = Intervals::expression_to_normalized_term(nexes, sum);
        let mut explanation = Explanation::new();
        if nla.explain_by_equiv(&normalized.term, &mut explanation) {
            set_value(interval, &normalized.constant);
            if mode == DepsMode::WithDeps {
                for constraint in explanation.iter() {
                    interval.lower_dep = mk_join(&interval.lower_dep, &mk_leaf(constraint as u32));
                }
                interval.upper_dep = interval.lower_dep.clone();
            }
            return true;
        }
        let Some(found) = nla.lra.fetch_normalized_term_column(&normalized.term) else {
            return false;
        };
        let found_coeff = found.coeff.clone();
        Intervals::set_var_interval(nla.lra, found.column, interval, mode);
        let mut scaled = mk_dep_interval();
        mul_scalar(
            &normalized.coeff.div(&found_coeff),
            interval,
            &mut scaled,
            mode,
        );
        add_scalar(&normalized.constant, &mut scaled);
        set(interval, &scaled, mode);
        true
    }

    fn interval_of_sum_no_term(
        nla: &mut Nla<'_, '_>,
        nexes: &[Nex],
        expr: NexId,
        interval: &mut DepInterval,
        mode: DepsMode,
    ) -> bool {
        if Intervals::has_inf_interval(nla, nexes, expr) {
            return true;
        }
        let Nex::Sum(sum) = &nexes[expr] else {
            panic!("nex {expr} is not a sum");
        };
        if !Intervals::interval_of_expr(nla, nexes, sum.children[0], 1, interval, mode) {
            return false;
        }
        for child in &sum.children[1..] {
            let mut child_interval = mk_dep_interval();
            if !Intervals::interval_of_expr(nla, nexes, *child, 1, &mut child_interval, mode) {
                return false;
            }
            let mut total = mk_dep_interval();
            add(interval, &child_interval, &mut total, mode);
            set(interval, &total, mode);
        }
        true
    }

    // conflict_u_l: whether first's upper bound is below second's lower bound. Like Z3, equal
    // bounds conflict when either upper bound is open.
    fn conflict_upper_lower(first: &DepInterval, second: &DepInterval) -> bool {
        if first.is_upper_inf || second.is_lower_inf {
            return false;
        }
        let comparison = first.upper.compare(&second.lower);
        if comparison.is_ne() {
            return comparison.is_lt();
        }
        first.is_upper_open || second.is_upper_open
    }

    fn interval_of_sum(
        nla: &mut Nla<'_, '_>,
        nexes: &[Nex],
        expr: NexId,
        interval: &mut DepInterval,
        mode: DepsMode,
    ) -> bool {
        if !Intervals::interval_of_sum_no_term(nla, nexes, expr, interval, mode) {
            return false;
        }
        let Nex::Sum(sum) = &nexes[expr] else {
            panic!("nex {expr} is not a sum");
        };
        if !is_a_linear_term(nexes, sum) {
            return true;
        }
        let mut from_term = mk_dep_interval();
        if !Intervals::interval_from_term(nla, nexes, sum, &mut from_term, mode) {
            return true;
        }
        let mut intersection = mk_dep_interval();
        intersect(interval, &from_term, &mut intersection, mode);
        if !is_empty(&intersection) {
            set(interval, &intersection, mode);
            return true;
        }
        if mode == DepsMode::WithDeps {
            let mut explanation = Explanation::new();
            let deps = if Intervals::conflict_upper_lower(interval, &from_term) {
                [&interval.upper_dep, &intersection.lower_dep]
            } else {
                [&intersection.upper_dep, &interval.lower_dep]
            };
            for dep in deps {
                explanation.push_dependency(dep);
            }
            report(nla, &explanation);
        } else {
            Intervals::interval_of_sum(
                nla,
                nexes,
                expr,
                &mut mk_dep_interval(),
                DepsMode::WithDeps,
            );
        }
        false
    }

    fn interval_of_mul(
        nla: &mut Nla<'_, '_>,
        nexes: &[Nex],
        product: &NexMul,
        interval: &mut DepInterval,
        mode: DepsMode,
    ) -> bool {
        let zero_child = product
            .children
            .iter()
            .find(|child| Intervals::has_zero_interval(nla, nexes, child.expr));
        if let Some(zero_child) = zero_child {
            Intervals::interval_of_expr(nla, nexes, zero_child.expr, 1, interval, mode);
            if mode == DepsMode::WithDeps {
                set_zero_interval_deps_for_mult(interval);
            }
            return true;
        }
        set_value(interval, &product.coeff);
        for child in &product.children {
            let mut child_interval = mk_dep_interval();
            if !Intervals::interval_of_expr(
                nla,
                nexes,
                child.expr,
                child.power,
                &mut child_interval,
                mode,
            ) {
                return false;
            }
            let mut result = mk_dep_interval();
            mul(interval, &child_interval, &mut result, mode);
            set(interval, &result, mode);
        }
        true
    }

    fn to_power(interval: &mut DepInterval, exponent: u32, mode: DepsMode) {
        if exponent == 1 {
            return;
        }
        let mut result = mk_dep_interval();
        power(interval, exponent, &mut result, mode);
        set(interval, &result, mode);
    }

    // interval_of_expr: false when a sum met a conflict, which became a lemma.
    fn interval_of_expr(
        nla: &mut Nla<'_, '_>,
        nexes: &[Nex],
        expr: NexId,
        exponent: u32,
        interval: &mut DepInterval,
        mode: DepsMode,
    ) -> bool {
        match &nexes[expr] {
            Nex::Scalar(value) => {
                set_value(interval, &value.pow(exponent));
                return true;
            }
            Nex::Sum(_) => {
                if !Intervals::interval_of_sum(nla, nexes, expr, interval, mode) {
                    return false;
                }
            }
            Nex::Mul(product) => {
                if !Intervals::interval_of_mul(nla, nexes, product, interval, mode) {
                    return false;
                }
            }
            Nex::Var(variable) => Intervals::set_var_interval(nla.lra, *variable, interval, mode),
        }
        Intervals::to_power(interval, exponent, mode);
        true
    }
}

// Expected lemmas from the TS oracle on the same setups.
#[cfg(test)]
mod tests {
    use prove_num::Rational;

    use super::Intervals;
    use crate::lp::constraints::{KIND_GE, KIND_LE};
    use crate::lp::nex_creator::{NexCreator, NexFactor};
    use crate::lp::nla_core::tests::{NlaFixture, show_lemmas};

    // Columns x and y, the term column t = coeff*x + coeff*y, registered, and the sum x + y.
    fn mk_term_fixture(coeff: i64) -> (NlaFixture<'static>, usize, NexCreator, usize) {
        let mut fixture = NlaFixture::new();
        for external in 0..2 {
            fixture.lra.add_var(external, true);
        }
        let term = fixture
            .lra
            .add_term(&[(0, Rational::from(coeff)), (1, Rational::from(coeff))], 2);
        fixture.lra.register_existing_terms();
        let mut creator = NexCreator::new();
        let x = creator.mk_var(0);
        let y = creator.mk_var(1);
        let sum = creator.mk_sum(&[x, y]);
        (fixture, term, creator, sum)
    }

    #[test]
    fn explains_the_bounds_that_separate_a_sum_of_products_from_zero() {
        let mut fixture = NlaFixture::new();
        for external in 0..3 {
            fixture.lra.add_var(external, true);
        }
        let constraints = [
            fixture.add_bound(0, KIND_GE, 1),
            fixture.add_bound(0, KIND_LE, 2),
            fixture.add_bound(1, KIND_GE, 1),
            fixture.add_bound(1, KIND_LE, 2),
            fixture.add_bound(2, KIND_GE, 5),
        ];
        fixture.lra.find_feasible_solution();
        let mut creator = NexCreator::new();
        let x = creator.mk_var(0);
        let y = creator.mk_var(1);
        let product = creator.mk_mul(&[NexFactor::Expr(x), NexFactor::Expr(y)]);
        let z = creator.mk_var(2);
        let sum = creator.mk_sum(&[product, z]);
        assert!(fixture.with_nla(|nla| Intervals::check_nex(nla, &creator.nexes, sum, &None)));
        assert_eq!(constraints, [0, 1, 2, 3, 4]);
        assert_eq!(fixture.show_state(), "values 1,1,5 toRefine ");
        assert_eq!(show_lemmas(&fixture.core), ["[] {0,2,4}"]);
    }

    #[test]
    fn bounds_a_linear_sum_by_its_term_column() {
        let (mut fixture, term, creator, sum) = mk_term_fixture(1);
        let constraints = [
            fixture.add_bound(0, KIND_GE, -5),
            fixture.add_bound(0, KIND_LE, 5),
            fixture.add_bound(1, KIND_GE, -5),
            fixture.add_bound(1, KIND_LE, 5),
            fixture.add_bound(term, KIND_GE, 1),
        ];
        fixture.lra.find_feasible_solution();
        assert!(fixture.with_nla(|nla| Intervals::check_nex(nla, &creator.nexes, sum, &None)));
        assert_eq!(constraints, [0, 1, 2, 3, 4]);
        assert_eq!(fixture.show_state(), "values 0,1,1 toRefine ");
        assert_eq!(show_lemmas(&fixture.core), ["[] {4}"]);
    }

    #[test]
    fn reports_a_sum_whose_interval_misses_its_term_columns() {
        let (mut fixture, term, creator, sum) = mk_term_fixture(2);
        let constraints = [
            fixture.add_bound(0, KIND_GE, 0),
            fixture.add_bound(0, KIND_LE, 1),
            fixture.add_bound(1, KIND_GE, 0),
            fixture.add_bound(1, KIND_LE, 1),
            fixture.add_bound(term, KIND_LE, -1),
        ];
        assert!(fixture.with_nla(|nla| Intervals::check_nex(nla, &creator.nexes, sum, &None)));
        assert_eq!(constraints, [0, 1, 2, 3, 4]);
        assert_eq!(fixture.show_state(), "values 0,0,0 toRefine ");
        assert_eq!(show_lemmas(&fixture.core), ["[] {0,2,4}"]);
    }
}
