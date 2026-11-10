// Ported from Z3 (src/math/lp/nla_grobner.h, src/math/lp/nla_grobner.cpp), MIT license, see
// z3-license.txt. nla's Grobner pass: the rows around the monomials to refine become polynomial
// equations, which dd::solver saturates, and the equations then yield lemmas: interval conflicts,
// quotient and residue bounds, failed gcd tests, fixed variables, factorizations, and new linear
// rows. Z3's nlsat conflict check (is_nla_conflict) is not ported, nor are the statistics.
//
// The TypeScript gives the solver `() => core.isCanceled()` when it is made; here the solver
// takes it on each call that checks it (pdd_solver.rs), made from the lar_solver's settings, as
// core.isCanceled is. The pdd manager is the solver's. An equation is its index in the solver's
// arena. The cross-nested search moves the creator out of the state for its run, as horner does.
use std::collections::HashMap;

use prove_num::{Rational, get_euclidean_mod, get_gcd, get_lcm};

use crate::lp::constraints::{KIND_EQ, KIND_GE, KIND_LE, KIND_LT, KIND_NE};
use crate::lp::containers::IndexedUintSet;
use crate::lp::core_solver::{COLUMN_BOXED, COLUMN_FIXED, COLUMN_LOWER, COLUMN_UPPER};
use crate::lp::cross_nested::CrossNested;
use crate::lp::dep_intervals::{
    DepInterval, DepsMode, add, check_interval_for_conflict_on_zero, mk_dep_interval, mul, power,
    separated_from_zero, set, set_value,
};
use crate::lp::dependency::{Dependency, mk_join};
use crate::lp::explanation::Explanation;
use crate::lp::lar_solver::{LarSolver, NULL_LPVAR};
use crate::lp::lar_term::LarTerm;
use crate::lp::nex::{Nex, NexId, get_degree};
use crate::lp::nex_creator::{NexCreator, NexFactor};
use crate::lp::nla_core::{NLA_PARAMS, Nla, NlaCore};
use crate::lp::nla_horner::CheckNexCallbacks;
use crate::lp::nla_intervals::Intervals;
use crate::lp::nla_types::{Ineq, LemmaBuilder, mk_ineq, mk_term_ineq};
use crate::lp::numeric_pair::Impq;
use crate::lp::pdd::{Pdd, PddManager, evaluate_pdd};
use crate::lp::pdd_interval::get_pdd_interval;
use crate::lp::pdd_solver::{PddSolver, get_default_pdd_solver_config};
use crate::util::error::SmtError;

const UINT_MAX: u64 = 0xffffffff;
const ADAPTIVE_UNIT: usize = 16;
const ADAPTIVE_MAX: usize = 4 * 16;
const ADAPTIVE_BUMP_AFTER: u64 = 2;
const DELAY_CAP: u64 = 1000000;

struct LinearTerm {
    term: LarTerm,
    offset: Rational,
}

struct SortedMonomial {
    coeff: Rational,
    vars: Vec<usize>,
}

fn get_rational_gcd(first: &Rational, second: &Rational) -> Rational {
    Rational::from(get_gcd(first.num(), second.num()))
}

fn get_rational_lcm(first: &Rational, second: &Rational) -> Rational {
    Rational::from(get_lcm(first.num(), second.num()))
}

fn get_denominator(value: &Rational) -> Rational {
    Rational::from(value.den().clone())
}

// divides: whether the integer a divides the integer b, where 0 divides only 0.
fn divides(divisor: &Rational, value: &Rational) -> bool {
    if divisor.is_zero() {
        value.is_zero()
    } else {
        (value.num() % divisor.num()).is_zero()
    }
}

// ps_root: the root a of a^2 * M^2, a perfect square with every variable of even multiplicity.
fn get_perfect_square_root(coeff: &Rational, vars: &[usize]) -> Option<Rational> {
    if vars.len() % 2 == 1 {
        return None;
    }
    let root = coeff.root(2)?;
    let mut index = 0;
    while index < vars.len() {
        let start = index;
        while index < vars.len() && vars[index] == vars[start] {
            index += 1;
        }
        if (index - start) % 2 == 1 {
            return None;
        }
    }
    Some(root)
}

// ps_cross: whether (c12, v12) is the cross term -2ab*M1*M2 of the perfect squares a^2*M1^2 and
// b^2*M2^2.
fn is_perfect_square_cross(
    first: &Rational,
    first_vars: &[usize],
    second: &Rational,
    second_vars: &[usize],
    cross_coeff: &Rational,
    cross_vars: &[usize],
) -> bool {
    if !cross_coeff.is_negative() {
        return false;
    }
    if *cross_coeff != Rational::from(-2i64).mul(first).mul(second) {
        return false;
    }
    if first_vars.len() + second_vars.len() != cross_vars.len() * 2 {
        return false;
    }
    let mut first_index = 0;
    let mut second_index = 0;
    for &cross_var in cross_vars {
        if first_index < first_vars.len() && first_vars[first_index] == cross_var {
            first_index += 2;
        } else if second_index < second_vars.len() && second_vars[second_index] == cross_var {
            second_index += 2;
        } else {
            return false;
        }
    }
    first_index >= first_vars.len() && second_index >= second_vars.len()
}

// Z3 catches every exception around the propagations, of which a failed pdd allocation is the one
// that can occur.
fn catch_memory_out(result: Result<bool, SmtError>) -> Result<bool, SmtError> {
    match result {
        Err(SmtError::PddMemoryOut) => Ok(false),
        other => other,
    }
}

pub struct Grobner {
    propagates_quotients: bool,
    has_gcd_test: bool,
    expands_terms: bool,
    solver: PddSolver,
    nex_creator: NexCreator,
    rows: IndexedUintSet,
    quota: u64,
    delay_base: u64,
    delay: u64,
    growth_boost: usize,
    hit_streak: u64,
    is_adding_all_eqs: bool,
    mon2var: HashMap<Vec<usize>, usize>,
}

impl Grobner {
    // TS makes its PddManager over the lar_solver's column count when nla is made.
    pub fn new(column_count: usize) -> Grobner {
        Grobner {
            propagates_quotients: NLA_PARAMS.grobner_propagate_quotients,
            has_gcd_test: NLA_PARAMS.grobner_gcd_test,
            expands_terms: NLA_PARAMS.grobner_expand_terms,
            solver: PddSolver::new(PddManager::new(column_count)),
            nex_creator: NexCreator::new(),
            rows: IndexedUintSet::new(),
            quota: NLA_PARAMS.gr_q,
            delay_base: 0,
            delay: 0,
            growth_boost: ADAPTIVE_UNIT,
            hit_streak: 0,
            is_adding_all_eqs: false,
            mon2var: HashMap::new(),
        }
    }

    // operator(): runs the pass, unless the quota of misses delays it.
    pub fn run(nla: &mut Nla<'_, '_>) -> Result<(), SmtError> {
        if nla.lra.get_column_count() > 5000 {
            return Ok(());
        }
        let grobner = &mut nla.core.grobner;
        if grobner.quota == 0 {
            grobner.quota = NLA_PARAMS.gr_q;
        }
        if grobner.quota == 1 {
            if NLA_PARAMS.grobner_exp_delay {
                if grobner.delay_base == 0 {
                    grobner.delay_base = 1;
                } else if grobner.delay_base < DELAY_CAP {
                    grobner.delay_base = (grobner.delay_base * 2).min(DELAY_CAP);
                }
                grobner.delay = grobner.delay_base;
            } else {
                grobner.delay_base += 1;
                grobner.delay = grobner.delay_base;
            }
            grobner.quota = NLA_PARAMS.gr_q;
        }
        if grobner.delay > 0 {
            grobner.delay -= 1;
            return Ok(());
        }
        Grobner::find_nl_cluster(nla)?;
        if !Grobner::configure(nla)? {
            return Ok(());
        }
        let mut is_productive = catch_memory_out(Grobner::propagate_gcd_test(nla))?;
        if !is_productive {
            let lra = &*nla.lra;
            nla.core
                .grobner
                .solver
                .saturate(&|| lra.settings().is_canceled())?;
            if nla.grobner.delay_base > 0 {
                nla.grobner.delay_base -= 1;
            }
            let propagate = |nla: &mut Nla<'_, '_>| -> Result<bool, SmtError> {
                Ok(Grobner::is_conflicting(nla)?
                    || Grobner::propagate_quotients(nla)?
                    || Grobner::propagate_gcd_test(nla)?
                    || Grobner::propagate_eqs(nla)?
                    || Grobner::propagate_factorization(nla)?
                    || Grobner::propagate_linear_equations(nla)?)
            };
            is_productive = catch_memory_out(propagate(nla))?;
        }
        let grobner = &mut nla.core.grobner;
        if NLA_PARAMS.grobner_adaptive {
            grobner.update_growth_boost(is_productive);
        }
        if is_productive {
            return Ok(());
        }
        grobner.delay_base += 1;
        if grobner.quota > 0 {
            grobner.quota -= 1;
        }
        Ok(())
    }

    // update_growth_boost: two productive runs in a row raise the boost by half, up to the cap, and a
    // miss takes back a quarter of the excess over the unit.
    fn update_growth_boost(&mut self, is_productive: bool) {
        if is_productive {
            self.hit_streak += 1;
            if self.hit_streak < ADAPTIVE_BUMP_AFTER {
                return;
            }
            self.growth_boost = (self.growth_boost + (self.growth_boost >> 1)).min(ADAPTIVE_MAX);
            self.hit_streak = 0;
            return;
        }
        self.hit_streak = 0;
        if self.growth_boost <= ADAPTIVE_UNIT {
            return;
        }
        let excess = self.growth_boost - ADAPTIVE_UNIT;
        self.growth_boost = (self.growth_boost - excess.div_ceil(4)).max(ADAPTIVE_UNIT);
    }

    fn count_propagations(
        nla: &mut Nla<'_, '_>,
        propagate: fn(&mut Nla<'_, '_>, usize) -> Result<bool, SmtError>,
    ) -> Result<bool, SmtError> {
        let mut changed = 0;
        for equation in nla.grobner.solver.equations() {
            if propagate(nla, equation)? {
                changed += 1;
                if changed >= nla.grobner.solver.config.number_of_conflicts_to_report {
                    return Ok(true);
                }
            }
        }
        Ok(changed > 0)
    }

    fn is_conflicting(nla: &mut Nla<'_, '_>) -> Result<bool, SmtError> {
        for equation in nla.grobner.solver.equations() {
            if Grobner::is_equation_conflicting(nla, equation)? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn propagate_eqs(nla: &mut Nla<'_, '_>) -> Result<bool, SmtError> {
        Grobner::count_propagations(nla, Grobner::propagate_fixed)
    }

    fn propagate_factorization(nla: &mut Nla<'_, '_>) -> Result<bool, SmtError> {
        Grobner::count_propagations(nla, Grobner::propagate_factorization_of)
    }

    fn propagate_gcd_test(nla: &mut Nla<'_, '_>) -> Result<bool, SmtError> {
        if !nla.grobner.has_gcd_test {
            return Ok(false);
        }
        Grobner::count_propagations(nla, Grobner::propagate_gcd_test_of)
    }

    fn propagate_quotients(nla: &mut Nla<'_, '_>) -> Result<bool, SmtError> {
        if !nla.grobner.propagates_quotients {
            return Ok(false);
        }
        Grobner::count_propagations(nla, Grobner::propagate_quotients_of)
    }

    fn get_poly(nla: &Nla<'_, '_>, equation: usize) -> Pdd {
        nla.grobner.solver.equation(equation).poly
    }

    fn manager<'g>(nla: &'g mut Nla<'_, '_>) -> &'g mut PddManager {
        &mut nla.core.grobner.solver.manager
    }

    // propagate_fixed: k*x = 0 gives x = 0, and x + b = 0 gives x = -b.
    fn propagate_fixed(nla: &mut Nla<'_, '_>, equation: usize) -> Result<bool, SmtError> {
        let poly = Grobner::get_poly(nla, equation);
        let manager = &nla.core.grobner.solver.manager;
        if manager.is_unary(poly) {
            let variable = manager.var(poly);
            if nla.var_is_fixed(variable) {
                return Ok(false);
            }
            return Ok(Grobner::add_lemma_unless_holds(
                nla,
                equation,
                mk_ineq(variable, KIND_EQ, Rational::zero()),
            ));
        }
        if !manager.is_offset(poly) {
            return Ok(false);
        }
        let variable = manager.var(poly);
        if nla.var_is_fixed(variable) {
            return Ok(false);
        }
        let coeff = manager.val(manager.hi(poly)).clone();
        let offset = manager.val(manager.lo(poly)).neg();
        let lcm = get_rational_lcm(&get_denominator(&coeff), &get_denominator(&offset));
        let ineq = mk_term_ineq(
            LarTerm::from_entries([(variable, &coeff.mul(&lcm))]),
            KIND_EQ,
            offset.mul(&lcm),
        );
        Ok(Grobner::add_lemma_unless_holds(nla, equation, ineq))
    }

    fn add_lemma_unless_holds(nla: &mut Nla<'_, '_>, equation: usize, ineq: Ineq) -> bool {
        if nla.ineq_holds(&ineq) {
            return false;
        }
        let lemma = LemmaBuilder::new(nla);
        Grobner::add_dependencies(nla, &lemma, equation);
        lemma.add_ineq(nla, ineq);
        true
    }

    // propagate_factorization: x*q = 0 gives x = 0 or q = 0, for a linear q.
    fn propagate_factorization_of(
        nla: &mut Nla<'_, '_>,
        equation: usize,
    ) -> Result<bool, SmtError> {
        let poly = Grobner::get_poly(nla, equation);
        let manager = Grobner::manager(nla);
        let factors = manager.var_factors(poly)?;
        if factors.vars.is_empty() || !manager.is_linear(factors.poly) {
            return Ok(false);
        }
        let linear = Grobner::linear_to_term(manager, factors.poly);
        let mut ineqs: Vec<Ineq> = factors
            .vars
            .iter()
            .map(|variable| mk_ineq(*variable, KIND_EQ, Rational::zero()))
            .collect();
        ineqs.push(mk_term_ineq(linear.term, KIND_EQ, linear.offset.neg()));
        if ineqs.iter().any(|ineq| nla.ineq_holds(ineq)) {
            return Ok(false);
        }
        let lemma = LemmaBuilder::new(nla);
        Grobner::add_dependencies(nla, &lemma, equation);
        for ineq in ineqs {
            lemma.add_ineq(nla, ineq);
        }
        Ok(true)
    }

    // linear_to_term: the linear polynomial times the lcm of its denominators, as a term and an
    // offset.
    fn linear_to_term(manager: &PddManager, poly: Pdd) -> LinearTerm {
        let mut lcm = Rational::one();
        let mut current = poly;
        while !manager.is_val(current) {
            lcm = get_rational_lcm(&lcm, &get_denominator(manager.val(manager.hi(current))));
            current = manager.lo(current);
        }
        lcm = get_rational_lcm(&get_denominator(manager.val(current)), &lcm);
        let mut term = LarTerm::new();
        current = poly;
        while !manager.is_val(current) {
            term.add_monomial(
                &lcm.mul(manager.val(manager.hi(current))),
                manager.var(current),
            );
            current = manager.lo(current);
        }
        LinearTerm {
            term,
            offset: lcm.mul(manager.val(current)),
        }
    }

    fn get_value(nla: &Nla<'_, '_>, poly: Pdd) -> Rational {
        evaluate_pdd(&nla.grobner.solver.manager, poly, &mut |variable| {
            nla.val(variable)
        })
    }

    fn is_int_poly(nla: &Nla<'_, '_>, poly: Pdd) -> bool {
        let manager = &nla.grobner.solver.manager;
        nla.var_is_int(manager.var(poly))
            && manager
                .free_vars(poly)
                .iter()
                .all(|variable| nla.var_is_int(*variable))
    }

    // propagate_gcd_test: x^k - y = 0 limits y modulo k^2. For each residue r of x modulo k, the
    // gcd of the coefficients of p with k*x + r for x must divide its constant term.
    fn propagate_gcd_test_of(nla: &mut Nla<'_, '_>, equation: usize) -> Result<bool, SmtError> {
        let mut poly = Grobner::get_poly(nla, equation);
        let manager = Grobner::manager(nla);
        if manager.is_linear(poly) || manager.is_val(poly) || !Grobner::is_int_poly(nla, poly) {
            return Ok(false);
        }
        if Grobner::get_value(nla, poly).is_zero() {
            return Ok(false);
        }
        let manager = Grobner::manager(nla);
        let powers = manager.get_powers(poly);
        if powers.is_empty() {
            return Ok(false);
        }
        let mut lcm = Rational::one();
        for value in manager.coefficients(poly) {
            lcm = get_rational_lcm(&lcm, &get_denominator(&value.coeff));
        }
        if lcm != Rational::one() {
            poly = manager.mul_val(poly, lcm)?;
        }
        let fails_gcd_test = |manager: &PddManager, substituted: Pdd| {
            let mut gcd = Rational::zero();
            let mut constant = Rational::zero();
            for value in manager.coefficients(substituted) {
                if value.is_constant {
                    constant = constant.add(&value.coeff);
                    continue;
                }
                gcd = get_rational_gcd(&gcd, &value.coeff);
                if gcd == Rational::one() {
                    return false;
                }
            }
            !constant.is_zero() && !divides(&gcd, &constant)
        };
        for entry in powers {
            if entry.degree > 4 {
                continue;
            }
            let variable_pdd = manager.mk_var(entry.var)?;
            let degree_pdd = manager.mk_val(Rational::from(entry.degree as i64))?;
            let scaled = manager.mul(variable_pdd, degree_pdd);
            let mut is_gcd_failing = true;
            let mut residue = 0;
            while is_gcd_failing && residue < entry.degree {
                let residue_pdd = manager.mk_val(Rational::from(residue as i64))?;
                let replacement = manager.add(scaled, residue_pdd);
                let substituted = manager.subst_pdd(poly, entry.var, replacement)?;
                if !fails_gcd_test(manager, substituted) {
                    is_gcd_failing = false;
                }
                residue += 1;
            }
            if is_gcd_failing {
                let lemma = LemmaBuilder::new(nla);
                Grobner::add_dependencies(nla, &lemma, equation);
                return Ok(true);
            }
        }
        Ok(false)
    }

    // propagate_quotients: for x*y + z = 0 over the integers, the residue of a linear variable and
    // bounds that relate a factor to the rest.
    fn propagate_quotients_of(nla: &mut Nla<'_, '_>, equation: usize) -> Result<bool, SmtError> {
        let poly = Grobner::get_poly(nla, equation);
        let manager = Grobner::manager(nla);
        if manager.is_linear(poly) || manager.is_val(poly) || !Grobner::is_int_poly(nla, poly) {
            return Ok(false);
        }
        if Grobner::get_value(nla, poly).is_zero() {
            return Ok(false);
        }
        // The TypeScript's Set of the variables, in insertion order.
        let mut nl_vars: Vec<usize> = Vec::new();
        let mut lcm = Rational::one();
        for monomial in nla.grobner.solver.manager.monomials(poly) {
            lcm = get_rational_lcm(&lcm, &get_denominator(&monomial.coeff));
            if monomial.vars.len() == 1 {
                continue;
            }
            for variable in monomial.vars {
                if !nl_vars.contains(&variable) {
                    nl_vars.push(variable);
                }
            }
        }
        if Grobner::propagate_mod_residue(nla, equation) {
            return Ok(true);
        }
        let mut is_lemma_found = false;
        for variable in nl_vars {
            let manager = Grobner::manager(nla);
            let factor = manager.factor(poly, variable, 1)?;
            if !manager.is_linear(factor.rest) {
                continue;
            }
            let lc = if lcm == Rational::one() {
                factor.lc
            } else {
                manager.mul_val(factor.lc, lcm.clone())?
            };
            let rest = if lcm == Rational::one() {
                factor.rest
            } else {
                manager.mul_val(factor.rest, lcm.clone())?
            };
            if Grobner::add_quotient_lemma(nla, equation, variable, lc, rest) {
                is_lemma_found = true;
            }
        }
        Ok(is_lemma_found)
    }

    // mod_residue: when every monomial but c_v*v is a multiple of M*c_v and the constant term is
    // K*c_v, then v = -K modulo M, so 0 <= v < M forces v to the residue.
    fn propagate_mod_residue(nla: &mut Nla<'_, '_>, equation: usize) -> bool {
        let poly = Grobner::get_poly(nla, equation);
        let monomials = nla.grobner.solver.manager.monomials(poly);
        for linear in &monomials {
            if linear.vars.len() != 1 {
                continue;
            }
            let variable = linear.vars[0];
            if !nla.var_is_int(variable) {
                continue;
            }
            let coeff = &linear.coeff;
            let mut modulus = Rational::zero();
            let mut constant = Rational::zero();
            let mut is_ok = true;
            for monomial in &monomials {
                if monomial.vars.len() == 1 && monomial.vars[0] == variable {
                    continue;
                }
                if monomial.vars.is_empty() {
                    constant = monomial.coeff.clone();
                    continue;
                }
                let quotient = monomial.coeff.div(coeff);
                if !quotient.is_int() {
                    is_ok = false;
                    break;
                }
                modulus = if modulus.is_zero() {
                    quotient.abs()
                } else {
                    get_rational_gcd(&modulus, &quotient.abs())
                };
                if modulus == Rational::one() {
                    is_ok = false;
                    break;
                }
            }
            if !is_ok || modulus.is_zero() {
                continue;
            }
            let offset = constant.div(coeff);
            if !offset.is_int() {
                continue;
            }
            let target = Rational::from(get_euclidean_mod(offset.neg().num(), modulus.num()));
            let value = nla.val(variable);
            if value.is_negative() || value.compare(&modulus).is_ge() || value == target {
                continue;
            }
            let lemma = LemmaBuilder::new(nla);
            Grobner::add_dependencies(nla, &lemma, equation);
            lemma.add_ineq(nla, mk_ineq(variable, KIND_LT, Rational::zero()));
            lemma.add_ineq(nla, mk_ineq(variable, KIND_GE, modulus));
            lemma.add_ineq(nla, mk_ineq(variable, KIND_EQ, target));
            return true;
        }
        false
    }

    // The lemmas of p = v*lc + r for a linear r, by the values of v, lc and r.
    fn add_quotient_lemma(
        nla: &mut Nla<'_, '_>,
        equation: usize,
        variable: usize,
        lc: Pdd,
        rest: Pdd,
    ) -> bool {
        let variable_value = nla.val(variable);
        let rest_value = Grobner::get_value(nla, rest);
        let lc_value = Grobner::get_value(nla, lc);
        if rest_value.is_zero() {
            if variable_value.is_zero()
                || lc_value.is_zero()
                || !Grobner::manager(nla).is_linear(lc)
            {
                return false;
            }
            // v = 0 or lc = 0 or r != 0
            let lc_term = Grobner::linear_to_term(&nla.grobner.solver.manager, lc);
            let rest_term = Grobner::linear_to_term(&nla.grobner.solver.manager, rest);
            let lemma = LemmaBuilder::new(nla);
            Grobner::add_dependencies(nla, &lemma, equation);
            lemma.add_ineq(nla, mk_ineq(variable, KIND_EQ, Rational::zero()));
            lemma.add_ineq(
                nla,
                mk_term_ineq(lc_term.term, KIND_EQ, lc_term.offset.neg()),
            );
            lemma.add_ineq(
                nla,
                mk_term_ineq(rest_term.term, KIND_NE, rest_term.offset.neg()),
            );
            return true;
        }
        if variable_value.is_zero() {
            // v = 0 => r = 0
            let lemma = LemmaBuilder::new(nla);
            Grobner::add_dependencies(nla, &lemma, equation);
            let rest_term = Grobner::linear_to_term(&nla.grobner.solver.manager, rest);
            lemma.add_ineq(nla, mk_ineq(variable, KIND_NE, Rational::zero()));
            lemma.add_ineq(
                nla,
                mk_term_ineq(rest_term.term, KIND_EQ, rest_term.offset.neg()),
            );
            return true;
        }
        if lc_value.is_zero() {
            if !Grobner::manager(nla).is_linear(lc) {
                return false;
            }
            // lc = 0 => r = 0
            let lemma = LemmaBuilder::new(nla);
            Grobner::add_dependencies(nla, &lemma, equation);
            let lc_term = Grobner::linear_to_term(&nla.grobner.solver.manager, lc);
            let rest_term = Grobner::linear_to_term(&nla.grobner.solver.manager, rest);
            lemma.add_ineq(
                nla,
                mk_term_ineq(lc_term.term, KIND_NE, lc_term.offset.neg()),
            );
            lemma.add_ineq(
                nla,
                mk_term_ineq(rest_term.term, KIND_EQ, rest_term.offset.neg()),
            );
            return true;
        }
        if divides(&variable_value, &rest_value) {
            return false;
        }
        let is_variable_positive = variable_value.is_positive();
        let is_rest_positive = rest_value.is_positive();
        let shift = Rational::from(if is_variable_positive == is_rest_positive {
            -1i64
        } else {
            1
        });
        if variable_value.abs().compare(&rest_value.abs()).is_gt() {
            // v*c + t = 0 with |v| > |t| != 0: v changes sign, t changes sign, or |v| <= |t|
            let lemma = LemmaBuilder::new(nla);
            let rest_term = Grobner::linear_to_term(&nla.grobner.solver.manager, rest);
            Grobner::add_dependencies(nla, &lemma, equation);
            let offset = rest_term.offset.neg();
            lemma.add_ineq(
                nla,
                mk_ineq(
                    variable,
                    if is_variable_positive {
                        KIND_LE
                    } else {
                        KIND_GE
                    },
                    Rational::zero(),
                ),
            );
            lemma.add_ineq(
                nla,
                mk_term_ineq(
                    rest_term.term,
                    if is_rest_positive { KIND_LE } else { KIND_GE },
                    offset.clone(),
                ),
            );
            let mut shifted = Grobner::linear_to_term(&nla.grobner.solver.manager, rest).term;
            shifted.add_monomial(&shift, variable);
            lemma.add_ineq(
                nla,
                mk_term_ineq(
                    shifted,
                    if is_rest_positive { KIND_GE } else { KIND_LE },
                    offset,
                ),
            );
            return true;
        }
        let one = Rational::one();
        if lc_value.abs().compare(&one).is_gt()
            && variable_value.abs().compare(&one).is_gt()
            && variable_value.abs().compare(&rest_value.abs()).is_ge()
        {
            // v*c + t = 0 & |c| > 1, |v| > 1 => |v| < |t|
            let lemma = LemmaBuilder::new(nla);
            let mut rest_term = Grobner::linear_to_term(&nla.grobner.solver.manager, rest);
            let lc_term = Grobner::linear_to_term(&nla.grobner.solver.manager, lc);
            Grobner::add_dependencies(nla, &lemma, equation);
            if lc_value.compare(&one).is_gt() {
                lemma.add_ineq(
                    nla,
                    mk_term_ineq(lc_term.term, KIND_LE, one.sub(&lc_term.offset)),
                );
            } else {
                lemma.add_ineq(
                    nla,
                    mk_term_ineq(
                        lc_term.term,
                        KIND_GE,
                        Rational::minus_one().sub(&lc_term.offset),
                    ),
                );
            }
            lemma.add_ineq(
                nla,
                if is_variable_positive {
                    mk_ineq(variable, KIND_LE, one.clone())
                } else {
                    mk_ineq(variable, KIND_GE, Rational::minus_one())
                },
            );
            rest_term.term.add_monomial(&shift, variable);
            lemma.add_ineq(
                nla,
                if is_rest_positive {
                    mk_term_ineq(rest_term.term, KIND_GE, one.sub(&rest_term.offset))
                } else {
                    mk_term_ineq(
                        rest_term.term,
                        KIND_LE,
                        Rational::minus_one().sub(&rest_term.offset),
                    )
                },
            );
            return true;
        }
        false
    }

    fn add_dependencies(core: &mut NlaCore, lemma: &LemmaBuilder, equation: usize) {
        let mut explanation = Explanation::new();
        explanation.push_dependency(&core.grobner.solver.equation(equation).dep);
        lemma.add_explanation(core, &explanation);
    }

    fn configure(nla: &mut Nla<'_, '_>) -> Result<bool, SmtError> {
        nla.grobner.solver.reset();
        let add_equations = |nla: &mut Nla<'_, '_>| -> Result<(), SmtError> {
            Grobner::set_level2var(nla);
            for lp_var in nla.active_var_set.elems.clone() {
                if nla.lra.is_base(lp_var) {
                    let row = nla.lra.core.heading[lp_var] as usize;
                    Grobner::add_row(nla, row)?;
                }
                if nla.is_monic_var(lp_var) && nla.var_is_fixed(lp_var) {
                    Grobner::add_fixed_monic(nla, lp_var)?;
                }
            }
            Ok(())
        };
        match add_equations(nla) {
            Err(SmtError::PddMemoryOut) => return Ok(false),
            result => result?,
        }
        let grobner = &mut nla.core.grobner;
        let mut config = get_default_pdd_solver_config();
        config.max_steps = grobner.solver.equations().len();
        config.max_simplified = NLA_PARAMS.grobner_max_simplified as usize;
        config.eqs_growth = NLA_PARAMS.grobner_eqs_growth as usize;
        config.expr_size_growth = NLA_PARAMS.grobner_expr_size_growth as usize;
        config.expr_degree_growth = NLA_PARAMS.grobner_expr_degree_growth as usize;
        if NLA_PARAMS.grobner_adaptive && grobner.growth_boost != ADAPTIVE_UNIT {
            let growth_boost = grobner.growth_boost;
            // In u64, as the TS numbers are: on 32-bit targets usize would overflow before the cap.
            let scale = |value: usize| {
                let scaled = value as u64 * growth_boost as u64 / ADAPTIVE_UNIT as u64;
                scaled.min(UINT_MAX) as usize
            };
            config.eqs_growth = scale(config.eqs_growth);
            config.expr_size_growth = scale(config.expr_size_growth);
            config.expr_degree_growth = scale(config.expr_degree_growth);
            config.max_simplified = scale(config.max_simplified);
        }
        config.number_of_conflicts_to_report = NLA_PARAMS.grobner_cnfl_to_report as usize;
        grobner.solver.config = config;
        grobner.solver.adjust_config();
        grobner.solver.manager.set_max_num_nodes(10000);
        Ok(true)
    }

    // equation_is_true: the equation holds at the values, or a free column can make it hold.
    fn is_equation_true(nla: &Nla<'_, '_>, equation: usize) -> bool {
        let poly = Grobner::get_poly(nla, equation);
        if nla
            .grobner
            .solver
            .manager
            .free_vars(poly)
            .iter()
            .any(|variable| nla.lra.is_free(*variable))
        {
            return true;
        }
        Grobner::get_value(nla, poly).is_zero()
    }

    fn get_var_interval(lra: &LarSolver<'_>, variable: usize, mode: DepsMode) -> DepInterval {
        let mut interval = mk_dep_interval();
        Intervals::set_var_interval(lra, variable, &mut interval, mode);
        interval
    }

    fn get_poly_interval(nla: &Nla<'_, '_>, poly: Pdd, mode: DepsMode) -> DepInterval {
        get_pdd_interval(
            &nla.grobner.solver.manager,
            poly,
            mode,
            &mut |variable, mode| Grobner::get_var_interval(nla.lra, variable, mode),
        )
    }

    // is_conflicting: the interval of the polynomial excludes 0, or a cross-nested form or a
    // perfect square shows that it does.
    fn is_equation_conflicting(nla: &mut Nla<'_, '_>, equation: usize) -> Result<bool, SmtError> {
        if Grobner::is_equation_true(nla, equation) {
            return Ok(false);
        }
        let poly = Grobner::get_poly(nla, equation);
        let interval = Grobner::get_poly_interval(nla, poly, DepsMode::WithoutDeps);
        if !separated_from_zero(&interval) {
            if Grobner::add_horner_conflict(nla, equation) {
                return Ok(true);
            }
            return Ok(NLA_PARAMS.grobner_perfect_squares
                && Grobner::add_perfect_square_conflict(nla, equation));
        }
        let interval_with_deps = Grobner::get_poly_interval(nla, poly, DepsMode::WithDeps);
        let dep = nla.grobner.solver.equation(equation).dep.clone();
        Ok(check_interval_for_conflict_on_zero(
            &interval_with_deps,
            &dep,
            &mut |constraints| Grobner::add_conflict(nla, constraints),
        ))
    }

    fn add_conflict(core: &mut NlaCore, constraints: Vec<u32>) {
        let mut explanation = Explanation::new();
        for constraint in constraints {
            explanation.push(constraint as usize);
        }
        LemmaBuilder::new(core).add_explanation(core, &explanation);
    }

    // monomial_interval: coeff times the product of the variables' intervals.
    fn get_monomial_interval(
        lra: &LarSolver<'_>,
        coeff: &Rational,
        vars: &[usize],
        mode: DepsMode,
    ) -> DepInterval {
        let mut result = mk_dep_interval();
        set_value(&mut result, coeff);
        let mut index = 0;
        while index < vars.len() {
            let variable = vars[index];
            let start = index;
            while index < vars.len() && vars[index] == variable {
                index += 1;
            }
            let mut powered = mk_dep_interval();
            power(
                &Grobner::get_var_interval(lra, variable, mode),
                (index - start) as u32,
                &mut powered,
                mode,
            );
            let mut product = mk_dep_interval();
            mul(&result, &powered, &mut product, mode);
            set(&mut result, &product, mode);
        }
        result
    }

    // add_perfect_square_conflict: a triple of monomials a^2*M1^2, b^2*M2^2 and -2ab*M1*M2 is
    // (a*M1 - b*M2)^2, at least 0, which replaces their interval when its lower bound is negative.
    fn add_perfect_square_conflict(nla: &mut Nla<'_, '_>, equation: usize) -> bool {
        let poly = Grobner::get_poly(nla, equation);
        let monomials: Vec<SortedMonomial> = nla
            .grobner
            .solver
            .manager
            .monomials(poly)
            .into_iter()
            .map(|monomial| {
                let mut vars = monomial.vars;
                vars.sort();
                SortedMonomial {
                    coeff: monomial.coeff,
                    vars,
                }
            })
            .collect();
        let count = monomials.len();
        if count < 3 {
            return false;
        }
        let get_sorted_interval = |monomial: &SortedMonomial| {
            Grobner::get_monomial_interval(
                nla.lra,
                &monomial.coeff,
                &monomial.vars,
                DepsMode::WithoutDeps,
            )
        };
        let mut is_deleted = vec![false; count];
        let mut is_found = false;
        for first in 0..count {
            if is_deleted[first] {
                continue;
            }
            let Some(first_root) =
                get_perfect_square_root(&monomials[first].coeff, &monomials[first].vars)
            else {
                continue;
            };
            let mut second = first + 1;
            while second < count && !is_deleted[first] {
                if is_deleted[second] {
                    second += 1;
                    continue;
                }
                let Some(second_root) =
                    get_perfect_square_root(&monomials[second].coeff, &monomials[second].vars)
                else {
                    second += 1;
                    continue;
                };
                for cross in first + 1..count {
                    if cross == second || is_deleted[cross] {
                        continue;
                    }
                    if !is_perfect_square_cross(
                        &first_root,
                        &monomials[first].vars,
                        &second_root,
                        &monomials[second].vars,
                        &monomials[cross].coeff,
                        &monomials[cross].vars,
                    ) {
                        continue;
                    }
                    let mut partial = mk_dep_interval();
                    let mut sum = mk_dep_interval();
                    add(
                        &get_sorted_interval(&monomials[first]),
                        &get_sorted_interval(&monomials[second]),
                        &mut partial,
                        DepsMode::WithoutDeps,
                    );
                    add(
                        &partial,
                        &get_sorted_interval(&monomials[cross]),
                        &mut sum,
                        DepsMode::WithoutDeps,
                    );
                    if sum.is_lower_inf || sum.lower.is_negative() {
                        is_deleted[first] = true;
                        is_deleted[second] = true;
                        is_deleted[cross] = true;
                        is_found = true;
                        break;
                    }
                }
                second += 1;
            }
        }
        if !is_found {
            return false;
        }
        // [0, oo) for the perfect squares is an unconditional bound, without a dependency.
        let mut sum = mk_dep_interval();
        sum.is_lower_inf = false;
        sum.lower = Rational::zero();
        sum.is_lower_open = false;
        for index in 0..count {
            if is_deleted[index] {
                continue;
            }
            let monomial = &monomials[index];
            let mut next = mk_dep_interval();
            add(
                &sum,
                &Grobner::get_monomial_interval(
                    nla.lra,
                    &monomial.coeff,
                    &monomial.vars,
                    DepsMode::WithDeps,
                ),
                &mut next,
                DepsMode::WithDeps,
            );
            set(&mut sum, &next, DepsMode::WithDeps);
        }
        let dep = nla.grobner.solver.equation(equation).dep.clone();
        check_interval_for_conflict_on_zero(&sum, &dep, &mut |constraints| {
            Grobner::add_conflict(nla, constraints)
        })
    }

    // add_horner_conflict: the cross-nested forms of the polynomial, whose intervals may exclude 0.
    fn add_horner_conflict(nla: &mut Nla<'_, '_>, equation: usize) -> bool {
        let poly = Grobner::get_poly(nla, equation);
        let mut creator = std::mem::take(&mut nla.grobner.nex_creator);
        // No expression outlives the run, so dropping the earlier ones (which TS's garbage
        // collector frees) changes nothing.
        creator.clear();
        let manager = &nla.core.grobner.solver.manager;
        let free_vars = manager.free_vars(poly);
        // The TypeScript's sparse array from a variable to its nex.
        let mut var2nex: HashMap<usize, NexId> = HashMap::new();
        for &variable in &free_vars {
            var2nex.insert(variable, creator.mk_var(variable));
        }
        creator
            .set_number_of_vars(free_vars.iter().fold(0, |max, variable| max.max(*variable)) + 1);
        let mut children: Vec<NexId> = Vec::new();
        for monomial in manager.monomials(poly) {
            if monomial.vars.is_empty() {
                children.push(creator.mk_scalar(monomial.coeff));
                continue;
            }
            let mut factors = vec![NexFactor::Scalar(monomial.coeff)];
            factors.extend(
                monomial
                    .vars
                    .iter()
                    .map(|inner_var| NexFactor::Expr(var2nex[inner_var])),
            );
            children.push(creator.mk_mul(&factors));
        }
        let sum = creator.mk_sum(&children);
        let expr = creator.simplify(sum);
        let is_done = if get_degree(&creator.nexes, expr) < 2
            || !matches!(creator.nexes[expr], Nex::Sum(_))
        {
            false
        } else {
            let dep = nla.grobner.solver.equation(equation).dep.clone();
            let random_seed = nla.random();
            let callbacks = CheckNexCallbacks {
                nla: &mut *nla,
                dep,
            };
            let mut cross_nested = CrossNested::new(callbacks, random_seed, &mut creator);
            cross_nested.run(expr);
            cross_nested.done()
        };
        nla.grobner.nex_creator = creator;
        is_done
    }

    // propagate_linear_equations: an equation whose monomials all have columns and that the values
    // violate becomes a new row fixed to its constant.
    fn propagate_linear_equations(nla: &mut Nla<'_, '_>) -> Result<bool, SmtError> {
        let core = &mut *nla.core;
        core.grobner.mon2var.clear();
        for monic in &core.emons.monics {
            core.grobner
                .mon2var
                .insert(monic.vars.clone(), monic.variable);
        }
        let mut changed = 0;
        for equation in nla.grobner.solver.equations() {
            if Grobner::propagate_linear_equation(nla, equation) {
                changed += 1;
            }
        }
        Ok(changed > 0)
    }

    fn propagate_linear_equation(nla: &mut Nla<'_, '_>, equation: usize) -> bool {
        if Grobner::is_equation_true(nla, equation) {
            return false;
        }
        let poly = Grobner::get_poly(nla, equation);
        let monomials = nla.grobner.solver.manager.monomials(poly);
        let mut value = Rational::zero();
        let mut columns: Vec<usize> = Vec::new();
        for monomial in &monomials {
            if monomial.vars.is_empty() {
                value = value.add(&monomial.coeff);
                continue;
            }
            // The monomial's column: Z3 looks up the variables in the pdd's order in the sorted
            // variables of the monics.
            let column = if monomial.vars.len() == 1 {
                Some(monomial.vars[0])
            } else {
                nla.grobner.mon2var.get(&monomial.vars).copied()
            };
            let Some(column) = column else {
                return false;
            };
            columns.push(column);
            value = value.add(&monomial.coeff.mul(&nla.val(column)));
        }
        if value.is_zero() {
            return false;
        }
        let mut lcm = Rational::one();
        for monomial in &monomials {
            lcm = get_rational_lcm(&get_denominator(&monomial.coeff), &lcm);
        }
        let mut coeffs: Vec<(usize, Rational)> = Vec::new();
        let mut offset = Rational::zero();
        for monomial in &monomials {
            let coeff = lcm.mul(&monomial.coeff);
            if monomial.vars.is_empty() {
                offset = offset.sub(&coeff);
            } else {
                coeffs.push((columns[coeffs.len()], coeff));
            }
        }
        let dep = nla.grobner.solver.equation(equation).dep.clone();
        let column = nla.lra.add_term(&coeffs, NULL_LPVAR);
        nla.lra
            .update_column_type_and_bound(column, KIND_EQ, &Impq::from_x(offset), dep);
        nla.is_check_feasible = true;
        true
    }

    // find_nl_cluster: the variables and rows reachable from the monomials to refine.
    fn find_nl_cluster(nla: &mut Nla<'_, '_>) -> Result<(), SmtError> {
        nla.grobner.rows.clear();
        nla.active_var_set.clear();
        let mut queue = nla.to_refine.elems.clone();
        while let Some(lp_var) = queue.pop() {
            Grobner::add_var_and_its_factors_to_queue(nla, lp_var, &mut queue)?;
        }
        Ok(())
    }

    // add_var_and_its_factors_to_q_and_collect_new_rows.
    fn add_var_and_its_factors_to_queue(
        nla: &mut Nla<'_, '_>,
        lp_var: usize,
        queue: &mut Vec<usize>,
    ) -> Result<(), SmtError> {
        if nla.active_var_set.has(lp_var) {
            return Ok(());
        }
        nla.active_var_set.add(lp_var);
        if nla.is_monic_var(lp_var) {
            let mut factorizations = nla.get_factorizations(nla.emons.get_index(lp_var));
            while let Some(factorization) = factorizations.next(nla) {
                for factor in &factorization.factors {
                    queue.push(factor.variable);
                }
            }
        } else if nla.lra.has_term(lp_var) {
            for (column, _) in nla.lra.get_term(lp_var)?.iter() {
                queue.push(column);
            }
        } else if nla.var_is_fixed(lp_var) {
            return Ok(());
        }
        let rows: Vec<usize> = nla.lra.core.matrix.columns[lp_var]
            .iter()
            .map(|cell| cell.row)
            .collect();
        for row in rows {
            if nla.grobner.rows.has(row) {
                continue;
            }
            nla.grobner.rows.add(row);
            let lra = &*nla.lra;
            let grobner = &nla.core.grobner;
            let basic = lra.core.basis[row];
            // A free column over the reals can be assigned.
            if lra.is_free(basic) && basic != lp_var {
                if !lra.is_int(basic) {
                    continue;
                }
                // Free integer columns count only for the gcd test, the quotients, or all equations.
                if !grobner.is_adding_all_eqs
                    && !grobner.has_gcd_test
                    && !grobner.propagates_quotients
                {
                    continue;
                }
                // A free integer column with integer coefficients can be assigned.
                if !grobner.is_adding_all_eqs
                    && lra
                        .get_row(row)
                        .iter()
                        .all(|row_cell| row_cell.coeff.is_int())
                {
                    continue;
                }
            }
            if !grobner.is_adding_all_eqs
                && lra.get_row(row).len() > NLA_PARAMS.horner_row_length_limit
            {
                continue;
            }
            let columns: Vec<usize> = lra.get_row(row).iter().map(|cell| cell.column).collect();
            for column in columns {
                Grobner::add_var_and_its_factors_to_queue(nla, column, queue)?;
            }
        }
        Ok(())
    }

    fn get_val_of_fixed_var_with_deps(
        lra: &LarSolver<'_>,
        lp_var: usize,
        dep: &mut Dependency,
    ) -> Rational {
        let witnesses = lra.get_bound_witnesses(lp_var);
        if witnesses.is_some() {
            *dep = mk_join(dep, &witnesses);
        }
        lra.get_lower_bound(lp_var).x.clone()
    }

    fn get_term_pdd(
        nla: &mut Nla<'_, '_>,
        term: Vec<(usize, Rational)>,
        dep: &mut Dependency,
    ) -> Result<Pdd, SmtError> {
        let mut result = Grobner::manager(nla).mk_val(Rational::zero())?;
        for entry in term {
            let pdd = Grobner::get_pdd(nla, entry.1, entry.0, dep)?;
            result = Grobner::manager(nla).add(result, pdd);
        }
        Ok(result)
    }

    // pdd_expr: coeff times the column, with fixed columns as values, terms expanded, and monics as
    // the products of their variables.
    fn get_pdd(
        nla: &mut Nla<'_, '_>,
        coeff: Rational,
        lp_var: usize,
        dep: &mut Dependency,
    ) -> Result<Pdd, SmtError> {
        let mut result = Grobner::manager(nla).mk_val(coeff)?;
        let mut vars = vec![lp_var];
        let mut zero_dep = dep.clone();
        while let Some(current) = vars.pop() {
            if NLA_PARAMS.grobner_subs_fixed > 0 && nla.var_is_fixed_to_zero(current) {
                let value =
                    Grobner::get_val_of_fixed_var_with_deps(nla.lra, current, &mut zero_dep);
                result = Grobner::manager(nla).mk_val(value)?;
                *dep = zero_dep;
                return Ok(result);
            }
            if NLA_PARAMS.grobner_subs_fixed == 1 && nla.var_is_fixed(current) {
                let value = Grobner::get_val_of_fixed_var_with_deps(nla.lra, current, dep);
                result = Grobner::manager(nla).mul_val(result, value)?;
            } else if nla.grobner.expands_terms && nla.lra.has_term(current) {
                let term: Vec<(usize, Rational)> = nla
                    .lra
                    .get_term(current)?
                    .iter()
                    .map(|entry| (entry.0, entry.1.clone()))
                    .collect();
                let term_pdd = Grobner::get_term_pdd(nla, term, dep)?;
                result = Grobner::manager(nla).mul(result, term_pdd);
            } else if !nla.is_monic_var(current) {
                let manager = Grobner::manager(nla);
                let variable_pdd = manager.mk_var(current)?;
                result = manager.mul(result, variable_pdd);
            } else {
                vars.extend_from_slice(&nla.emon(current).vars);
            }
        }
        Ok(result)
    }

    // is_solved: p = 0 as v = r, for a linear p where v is the only variable bounded on one side
    // while several are bounded on the other, so that r has no bound on that side.
    fn get_solved_form(nla: &mut Nla<'_, '_>, poly: Pdd) -> Result<Option<(usize, Pdd)>, SmtError> {
        let lra = &*nla.lra;
        let manager = &mut nla.core.grobner.solver.manager;
        if !manager.is_linear(poly) {
            return Ok(None);
        }
        let mut num_lo = 0;
        let mut num_hi = 0;
        let mut lo = 0;
        let mut hi = 0;
        let mut lo_coeff = Rational::zero();
        let mut hi_coeff = Rational::zero();
        let mut current = poly;
        while !manager.is_val(current) {
            let variable = manager.var(current);
            let value = manager.val(manager.hi(current)).clone();
            let column_type = lra.core.get_column_type(variable);
            if column_type == COLUMN_LOWER || column_type == COLUMN_UPPER {
                if value.is_positive() == (column_type == COLUMN_LOWER) {
                    num_lo += 1;
                    lo = variable;
                    lo_coeff = value;
                } else {
                    num_hi += 1;
                    hi = variable;
                    hi_coeff = value;
                }
            } else if column_type != COLUMN_FIXED && column_type != COLUMN_BOXED {
                return Ok(None);
            }
            if num_lo > 1 && num_hi > 1 {
                return Ok(None);
            }
            current = manager.lo(current);
        }
        let is_lo = num_lo == 1 && num_hi > 1;
        if !is_lo && !(num_hi == 1 && num_lo > 1) {
            return Ok(None);
        }
        let variable = if is_lo { lo } else { hi };
        let coeff = if is_lo { lo_coeff } else { hi_coeff };
        let variable_pdd = manager.mk_var(variable)?;
        let scaled = manager.mul_val(variable_pdd, coeff.clone())?;
        let solution = manager.sub(scaled, poly);
        Ok(Some((
            variable,
            if coeff == Rational::one() {
                solution
            } else {
                manager.mul_val(solution, Rational::one().div(&coeff))?
            },
        )))
    }

    // add_eq: adds the equation in solved form when it has one.
    fn add_eq(nla: &mut Nla<'_, '_>, poly: Pdd, dep: Dependency) -> Result<(), SmtError> {
        let (simplified, simplified_dep) = nla.grobner.solver.simplify(poly, dep)?;
        match Grobner::get_solved_form(nla, simplified)? {
            None => nla.grobner.solver.add(simplified, simplified_dep),
            Some((variable, solved)) => {
                let lra = &*nla.lra;
                nla.core
                    .grobner
                    .solver
                    .add_subst(variable, solved, simplified_dep, &|| {
                        lra.settings().is_canceled()
                    })?;
            }
        }
        Ok(())
    }

    fn add_fixed_monic(nla: &mut Nla<'_, '_>, lp_var: usize) -> Result<(), SmtError> {
        let mut dep: Dependency = None;
        let mut product = Grobner::manager(nla).mk_val(Rational::one())?;
        for factor in nla.emon(lp_var).vars.clone() {
            let factor_pdd = Grobner::get_pdd(nla, Rational::one(), factor, &mut dep)?;
            product = Grobner::manager(nla).mul(product, factor_pdd);
        }
        let value = Grobner::get_val_of_fixed_var_with_deps(nla.lra, lp_var, &mut dep);
        product = Grobner::manager(nla).sub_val(product, value)?;
        Grobner::add_eq(nla, product, dep)
    }

    fn add_row(nla: &mut Nla<'_, '_>, row: usize) -> Result<(), SmtError> {
        let mut dep: Dependency = None;
        let mut sum = Grobner::manager(nla).mk_val(Rational::zero())?;
        let cells: Vec<(Rational, usize)> = nla
            .lra
            .get_row(row)
            .iter()
            .map(|cell| (cell.coeff.clone(), cell.column))
            .collect();
        for cell in cells {
            let cell_pdd = Grobner::get_pdd(nla, cell.0, cell.1, &mut dep)?;
            sum = Grobner::manager(nla).add(sum, cell_pdd);
        }
        Grobner::add_eq(nla, sum, dep)
    }

    // set_level2var: the columns by weight, then index, from the lowest level.
    fn set_level2var(nla: &mut Nla<'_, '_>) {
        let count = nla.lra.get_column_count();
        let mut weights: Vec<u32> = (0..count)
            .map(|lp_var| nla.get_var_weight(lp_var))
            .collect();
        for lp_var in 0..count {
            if !nla.is_monic_var(lp_var) || !nla.to_refine.has(lp_var) {
                continue;
            }
            for &factor in &nla.emon(lp_var).vars {
                weights[factor] += 6;
            }
        }
        let mut level2var: Vec<usize> = (0..count).collect();
        level2var.sort_by(|first, second| {
            weights[*first]
                .cmp(&weights[*second])
                .then(first.cmp(second))
        });
        Grobner::manager(nla).reset(&level2var);
    }
}

#[cfg(test)]
mod tests {
    use prove_num::Rational;

    use super::Grobner;
    use crate::lp::constraints::{KIND_EQ, KIND_GE, KIND_LE};
    use crate::lp::lar_solver::LarSolver;
    use crate::lp::nla_core::NlaCore;
    use crate::lp::nla_core::tests::{NlaFixture, show_lemmas};
    use crate::lp::nla_types::is_conflict_lemma;

    // tests/unit/smt-pdd.test.ts's getCore: x*x is the monic m, and the constraints that
    // add_bounds makes are activated.
    fn get_core(
        is_x_int: bool,
        add_bounds: impl FnOnce(&mut LarSolver<'static>, usize, usize) -> Vec<usize>,
    ) -> (NlaFixture<'static>, Vec<usize>) {
        let mut lra = LarSolver::new(Box::new(|| false));
        let x = lra.add_var(0, is_x_int);
        let m = lra.add_var(1, true);
        let core = NlaCore::new(&mut lra);
        let mut fixture = NlaFixture { lra, core };
        fixture.with_nla(|nla| nla.add_monic(m, &[x, x]));
        let constraints = add_bounds(&mut fixture.lra, m, x);
        for &constraint in &constraints {
            fixture.lra.activate(constraint);
        }
        fixture.lra.find_feasible_solution();
        fixture.with_nla(|nla| {
            nla.drain_changed_bounds();
            nla.init_to_refine();
        });
        (fixture, constraints)
    }

    #[test]
    fn finds_that_x_squared_equals_4y_plus_2_fails_the_gcd_test() {
        let (mut fixture, constraints) = get_core(true, |lra, m, _| {
            let y = lra.add_var(2, true);
            let term = lra.add_term(&[(m, Rational::from(1)), (y, Rational::from(-4))], 3);
            vec![
                lra.mk_var_bound(y, KIND_GE, &Rational::from(0)),
                lra.mk_var_bound(y, KIND_LE, &Rational::from(10)),
                lra.mk_var_bound(term, KIND_EQ, &Rational::from(2)),
            ]
        });
        fixture.with_nla(Grobner::run).unwrap();
        assert_eq!(fixture.core.lemmas.len(), 1);
        let lemma = &fixture.core.lemmas[0];
        assert!(is_conflict_lemma(lemma));
        assert_eq!(lemma.expl.iter().collect::<Vec<_>>(), [constraints[2]]);
    }

    #[test]
    fn finds_that_x_squared_equals_minus_1_has_no_real_solution() {
        let (mut fixture, constraints) = get_core(false, |lra, m, x| {
            vec![
                lra.mk_var_bound(x, KIND_GE, &Rational::from(-5)),
                lra.mk_var_bound(m, KIND_EQ, &Rational::from(-1)),
            ]
        });
        fixture.with_nla(Grobner::run).unwrap();
        assert_eq!(fixture.core.lemmas.len(), 1);
        let lemma = &fixture.core.lemmas[0];
        assert!(is_conflict_lemma(lemma));
        assert!(
            lemma
                .expl
                .iter()
                .any(|constraint| constraint == constraints[1])
        );
    }

    // Expected lemmas from the TS oracle on the same setup: x*y - 7 is in [2, 18].
    #[test]
    fn finds_that_the_interval_of_a_fixed_monic_excludes_its_value() {
        let (mut fixture, constraints) = NlaFixture::mk_scenario(
            3,
            &[(2, &[0, 1])],
            &[
                (0, KIND_GE, 3),
                (0, KIND_LE, 5),
                (1, KIND_GE, 3),
                (1, KIND_LE, 5),
                (2, KIND_GE, 7),
                (2, KIND_LE, 7),
            ],
        );
        fixture.with_nla(Grobner::run).unwrap();
        assert_eq!(constraints, [0, 1, 2, 3, 4, 5]);
        assert_eq!(fixture.show_state(), "values 3,3,7 toRefine 2");
        assert_eq!(show_lemmas(&fixture.core), ["[] {0,2,4,5}"]);
    }

    // Expected lemmas from the TS oracle on the same setup: t = x*y - 2z fixed to 3 at y = 0, so
    // the quotient lemma y = 0 => -2z = 3, for each of x and y.
    #[test]
    fn propagates_the_quotient_of_a_row() {
        let mut fixture = NlaFixture::new();
        for external in 0..4 {
            fixture.lra.add_var(external, true);
        }
        fixture.with_nla(|nla| nla.add_monic(3, &[0, 1]));
        let term = fixture
            .lra
            .add_term(&[(3, Rational::from(1)), (2, Rational::from(-2))], 4);
        let constraints = [
            fixture.add_bound(0, KIND_GE, 2),
            fixture.add_bound(0, KIND_LE, 9),
            fixture.add_bound(1, KIND_GE, -9),
            fixture.add_bound(1, KIND_LE, 9),
            fixture.add_bound(2, KIND_GE, -9),
            fixture.add_bound(2, KIND_LE, 9),
            fixture.add_bound(term, KIND_GE, 3),
            fixture.add_bound(term, KIND_LE, 3),
        ];
        fixture.prepare();
        fixture.with_nla(Grobner::run).unwrap();
        assert_eq!(constraints, [0, 1, 2, 3, 4, 5, 6, 7]);
        assert_eq!(fixture.show_state(), "values 2,0,0,3,3 toRefine 3");
        assert_eq!(
            show_lemmas(&fixture.core),
            [
                "[1*v1 3 0 | -2*v2 0 3] {6,7}",
                "[1*v1 3 0 | -2*v2 0 3] {6,7}"
            ]
        );
        assert!(!fixture.core.is_check_feasible);
        assert_eq!(fixture.lra.get_column_count(), 5);
    }
}
