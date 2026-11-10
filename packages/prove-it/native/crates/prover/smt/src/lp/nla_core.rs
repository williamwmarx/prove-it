// Ported from Z3 (src/math/lp/nla_core.h, src/math/lp/nla_core.cpp, src/math/lp/nla_common.cpp,
// src/math/lp/nla_explanations.cpp, src/math/lp/factorization.cpp,
// src/math/lp/factorization_factory_imp.cpp, src/math/lp/nla_solver.cpp), MIT license, see
// z3-license.txt. The nonlinear core over lar_solver: the monomials whose values disagree with the
// products of their factors' values are refined by lemmas, which the passes below generate, and
// by literals to split on, and by nlsat's search on what they leave open, see nra_solver.rs.
//
// How the TypeScript's object graph is held here (the architecture of every nla_*.rs file):
// - `NlaCore` owns all of nla's state: every field of the TS class, and the state of each helper
//   class (`basics`, `tangents`, `order`, `monotone`, `divisions`, `intervals`, `monomial_bounds`,
//   `patcher`, `horner`, `grobner`, `nra`). The theory owns the `NlaCore`, as it owns the
//   `LarSolver`. NlaCore holds neither the lar_solver, the resource limit nor the theory's
//   is_relevant closure, which TS keeps on it.
// - `Nla<'a, 'l>` is the short-lived view that holds the borrows TS reaches through `this`:
//   `core: &mut NlaCore`, `lra: &mut LarSolver<'l>`, `limit: &ResourceLimit` (the
//   manager's resource limit) and `is_relevant`. It
//   derefs to `NlaCore`, so TS's `this.x` stays `self.x`, and `this.lra` is `self.lra`. The theory
//   builds one per call: `Nla { core: &mut nla, lra: &mut solver, limit, is_relevant: &|lp_var|
//   … }.check(level)`. When a borrow through the deref conflicts with another field (a method of
//   `emons` taking `&var_eqs`, say), name the fields through `self.core.x`, which borrowck splits.
// - TS's NlaCore methods are `impl Nla` methods here; those that read only nla's own state (no
//   lar_solver) are `impl NlaCore` methods, which the view reaches by deref.
// - A helper class with `private core: NlaCore` keeps its state in its `NlaCore` field and its
//   methods are associated functions taking the view: `this.core.basics.basicLemma(true)` reads
//   `Basics::basic_lemma(self, true)`, and its state is `nla.basics.field`. NlaThrottle's state
//   lives in the lar_solver, so its functions take `&mut LarSolver` (nla_throttle.rs).
// - A TS `Monic` object is a monic index into `emons.monics` (nla_emonics.rs): every method that
//   takes a Monic takes `monic: usize`. `emon(lp_var)` gives the `&Monic` to read, and
//   `emons.get_index(lp_var)` its index. `Factorization.mon` is a monic index.
// - Values are returned owned (`val` clones the lar_solver's value), since a borrow of the view
//   would block the next mutable call; TS's rationals are immutable, so a clone is the same value.
// - The `getFactorizations` generator is the cursor `Factorizations`, as lazy as the generator:
//   `let mut factorizations = nla.get_factorizations(monic); while let Some(factorization) =
//   factorizations.next(nla) { … }`, and the caller may change nla between steps.
// - `LemmaBuilder` (nla_types.rs) pushes its lemma onto `lemmas` when it is made, as TS does, and
//   holds its index.
// - Undo: TS's closures on `emons.trail` are `CoreUndo`s that `Emonics::pop` returns; `Nla::pop`
//   applies them right after, in order (set_use_nra_model, the divisions' lists).
// - Errors: a pass that TS lets throw returns `Result<_, SmtError>`. NraSolver declines with
//   `SmtError::Unsupported` until nlsat is ported, and `check` propagates it.
//
// The changed-bounds callback. TS installs `lra.onChangedBounds`, which findFeasibleSolution calls
// at its end with the columns whose bounds changed, and which adds to `monics_with_changed_bounds`
// the monic variables among them and the monics using them. Here `NlaCore::new` sets
// `lra.is_reporting_changed_bounds`, find_feasible_solution appends those columns to
// `lra.changed_bounds_pending`, and `Nla::drain_changed_bounds` runs the callback's body on them,
// in order. INVARIANT: every pub entry point of `Nla` that the theory calls (push, pop, add_monic,
// check, propagate, incremental_propagate, has_relevant_monomial, check_bounded_divisions, the
// add functions of Divisions) drains first, and nla drains right after each
// `find_feasible_solution` it calls itself (monomial bounds' optimize_nl_bounds). This is
// equivalent to the callback: it only writes `monics_with_changed_bounds`, reading `emons` and the
// columns, and only nla code reads or changes those, so applying it before any nla code runs again
// gives the same state as applying it when find_feasible_solution returned. Any new entry point,
// and any new nla call of find_feasible_solution, must keep this invariant.
use std::cmp::Ordering;
use std::ops::{Deref, DerefMut};

use prove_num::Rational;

use crate::lp::constraints::{
    ConstraintKind, KIND_EQ, KIND_GE, KIND_GT, KIND_LE, KIND_LT, KIND_NE,
};
use crate::lp::containers::IndexedUintSet;
use crate::lp::core_solver::{
    COLUMN_BOXED, COLUMN_FIXED, COLUMN_FREE, COLUMN_LOWER, COLUMN_UPPER, LP_FEASIBLE, LP_OPTIMAL,
};
use crate::lp::explanation::Explanation;
use crate::lp::lar_solver::{LarSolver, NULL_LPVAR};
use crate::lp::lar_term::LarTerm;
use crate::lp::lp_settings::{LpSettings, LpStats};
use crate::lp::nla_backoff::{Backoff, SqueezeSchedule};
use crate::lp::nla_basics::Basics;
use crate::lp::nla_divisions::Divisions;
use crate::lp::nla_emonics::{CoreUndo, Emonics, Monic};
use crate::lp::nla_factorization::{Factor, Factorization, mk_factor, mk_mon_factorization};
use crate::lp::nla_grobner::Grobner;
use crate::lp::nla_horner::Horner;
use crate::lp::nla_intervals::Intervals;
use crate::lp::nla_monomial_bounds::MonomialBounds;
use crate::lp::nla_monotone::Monotone;
use crate::lp::nla_order::Order;
use crate::lp::nla_patcher::Patcher;
use crate::lp::nla_tangents::Tangents;
use crate::lp::nla_types::{
    Ineq, Lemma, LemmaBuilder, is_conflict_lemma, mk_ineq, mk_term_ineq, negate_kind,
};
use crate::lp::nla_var_eqs::{VarEqs, get_signed_var_var, is_signed_var_negated, mk_signed_var};
use crate::lp::nra_solver::NraSolver;
use crate::lp::numeric_pair::Impq;
use crate::util::error::SmtError;
use crate::util::lbool::LBool;
use crate::util::rlimit::ResourceLimit;

pub struct NlaParams {
    pub horner: bool,
    pub horner_subs_fixed: u64,
    pub horner_frequency: u64,
    pub horner_row_length_limit: usize,
    pub grobner: bool,
    pub grobner_row_length_limit: usize,
    pub grobner_frequency: u64,
    pub grobner_eqs_growth: u64,
    pub grobner_expr_size_growth: u64,
    pub grobner_expr_degree_growth: u64,
    pub grobner_max_simplified: u64,
    pub grobner_cnfl_to_report: u64,
    pub grobner_propagate_quotients: bool,
    pub grobner_gcd_test: bool,
    pub grobner_exp_delay: bool,
    pub grobner_adaptive: bool,
    pub gr_q: u64,
    pub grobner_subs_fixed: u64,
    pub grobner_expand_terms: bool,
    pub grobner_perfect_squares: bool,
    pub branching: bool,
    pub nra: bool,
    pub nra_check_assignment: bool,
    pub nra_check_assignment_max_fail: u64,
    pub order: bool,
    pub order_binomial_sign: bool,
    pub tangents: bool,
    pub tangents_box_corners: bool,
    pub expensive_patching: bool,
    pub expp: bool,
    pub monomial_sandwich: bool,
    pub monomial_sandwich_max_fanout: u64,
    pub monomial_binomial_sign: bool,
    pub reduce_pseudo_linear: bool,
    pub delay: u64,
    pub propagate_linear_monomials: bool,
    pub linearize_violated_monomials: bool,
    pub optimize_bounds: bool,
    pub optimize_bounds_lp_max_vars: usize,
    pub cross_nested: bool,
}

// The arith.nl parameters of Z3's defaults that nla reads.
pub const NLA_PARAMS: NlaParams = NlaParams {
    horner: true,
    horner_subs_fixed: 2,
    horner_frequency: 4,
    horner_row_length_limit: 10,
    grobner: true,
    grobner_row_length_limit: 10,
    grobner_frequency: 4,
    grobner_eqs_growth: 10,
    grobner_expr_size_growth: 2,
    grobner_expr_degree_growth: 2,
    grobner_max_simplified: 10000,
    grobner_cnfl_to_report: 1,
    grobner_propagate_quotients: true,
    grobner_gcd_test: true,
    grobner_exp_delay: true,
    grobner_adaptive: false,
    gr_q: 10,
    grobner_subs_fixed: 1,
    grobner_expand_terms: true,
    grobner_perfect_squares: true,
    branching: true,
    nra: true,
    nra_check_assignment: true,
    nra_check_assignment_max_fail: 7,
    order: true,
    order_binomial_sign: true,
    tangents: true,
    tangents_box_corners: false,
    expensive_patching: false,
    expp: false,
    monomial_sandwich: false,
    monomial_sandwich_max_fanout: 0,
    monomial_binomial_sign: false,
    reduce_pseudo_linear: true,
    delay: 10,
    propagate_linear_monomials: true,
    linearize_violated_monomials: true,
    optimize_bounds: true,
    optimize_bounds_lp_max_vars: 120,
    cross_nested: true,
};

pub struct NlaEquality {
    pub first: usize,
    pub second: usize,
    pub explanation: Explanation,
}

pub struct NlaFixedEquality {
    pub lp_var: usize,
    pub value: Rational,
    pub explanation: Explanation,
}

// The passes that check_weighted draws from, which TS passes as closures.
#[derive(Clone, Copy)]
enum WeightedCheck {
    Horner,
    Grobner,
    Bounds,
    Order,
    Monotone,
    Tangent,
}

// is_octagon_term's result: the term is +-first +-second, negated unless the signs differ.
struct OctagonTerm {
    first: usize,
    second: usize,
    is_negated: bool,
}

pub struct NlaCore {
    pub var_eqs: VarEqs,
    pub emons: Emonics,
    pub lemmas: Vec<Lemma>,
    pub literals: Vec<Ineq>,
    pub equalities: Vec<NlaEquality>,
    pub fixed_equalities: Vec<NlaFixedEquality>,
    pub to_refine: IndexedUintSet,
    pub monics_with_changed_bounds: IndexedUintSet,
    pub active_var_set: IndexedUintSet,
    pub is_check_feasible: bool,
    pub is_nla_satisfied: bool,
    pub tangents: Tangents,
    pub basics: Basics,
    pub order: Order,
    pub monotone: Monotone,
    pub divisions: Divisions,
    pub intervals: Intervals,
    pub monomial_bounds: MonomialBounds,
    pub patcher: Patcher,
    pub horner: Horner,
    pub grobner: Grobner,
    pub nra: NraSolver,
    // m_use_nra_model: whether the values of the last nra check stand for lar_solver's.
    pub is_using_nra_model: bool,
    nlsat_backoff: Backoff,
    check_assignment_fail_count: u64,
    squeeze_schedule: SqueezeSchedule,
}

// The view of nla that its methods run on, see the top of the file.
pub struct Nla<'a, 'l> {
    pub core: &'a mut NlaCore,
    pub lra: &'a mut LarSolver<'l>,
    pub limit: &'a ResourceLimit,
    pub is_relevant: &'a dyn Fn(usize) -> bool,
}

impl Deref for Nla<'_, '_> {
    type Target = NlaCore;

    fn deref(&self) -> &NlaCore {
        self.core
    }
}

impl DerefMut for Nla<'_, '_> {
    fn deref_mut(&mut self) -> &mut NlaCore {
        self.core
    }
}

// val of a column, for the code that holds the lar_solver without the view (the patcher's
// callbacks).
pub fn get_val<'s>(lra: &'s LarSolver<'_>, lp_var: usize) -> &'s Rational {
    &lra.get_value(lp_var).x
}

// mul_val: the product of the values of the monic's variables.
pub fn get_mul_val(lra: &LarSolver<'_>, monic: &Monic) -> Rational {
    let mut product = Rational::one();
    for lp_var in &monic.vars {
        product = product.mul(get_val(lra, *lp_var));
    }
    product
}

impl NlaCore {
    pub fn new(lra: &mut LarSolver<'_>) -> NlaCore {
        lra.is_reporting_changed_bounds = true;
        NlaCore {
            var_eqs: VarEqs::new(),
            emons: Emonics::new(),
            lemmas: Vec::new(),
            literals: Vec::new(),
            equalities: Vec::new(),
            fixed_equalities: Vec::new(),
            to_refine: IndexedUintSet::new(),
            monics_with_changed_bounds: IndexedUintSet::new(),
            active_var_set: IndexedUintSet::new(),
            is_check_feasible: false,
            is_nla_satisfied: false,
            tangents: Tangents::default(),
            basics: Basics::default(),
            order: Order::default(),
            monotone: Monotone::default(),
            divisions: Divisions::default(),
            intervals: Intervals::default(),
            monomial_bounds: MonomialBounds::default(),
            patcher: Patcher::default(),
            horner: Horner::default(),
            grobner: Grobner::new(lra.get_column_count()),
            nra: NraSolver::default(),
            is_using_nra_model: false,
            nlsat_backoff: Backoff::new(NLA_PARAMS.delay),
            check_assignment_fail_count: 0,
            squeeze_schedule: SqueezeSchedule::default(),
        }
    }

    // Monomials and their canonization.

    pub fn is_monic_var(&self, lp_var: usize) -> bool {
        self.emons.is_monic_var(lp_var)
    }

    pub fn emon(&self, lp_var: usize) -> &Monic {
        self.emons.get(lp_var)
    }

    pub fn map_to_root(&self, lp_var: usize) -> usize {
        get_signed_var_var(self.var_eqs.find_var(lp_var))
    }

    pub fn sorted_rvars(&self, factor: &Factor) -> Vec<usize> {
        if factor.is_mon {
            self.emons.get(factor.variable).rvars.clone()
        } else {
            vec![self.map_to_root(factor.variable)]
        }
    }

    pub fn canonize_sign_var(&self, lp_var: usize) -> bool {
        is_signed_var_negated(self.var_eqs.find_var(lp_var))
    }

    pub fn canonize_sign_factor(&self, factor: &Factor) -> bool {
        factor.is_negated
            != (if factor.is_mon {
                self.emons.get(factor.variable).rsign
            } else {
                self.canonize_sign_var(factor.variable)
            })
    }

    pub fn canonize_sign_factorization(&self, factorization: &Factorization) -> bool {
        let mut sign = false;
        for factor in &factorization.factors {
            sign = sign != self.canonize_sign_factor(factor);
        }
        sign
    }

    // The variable of the canonical monic of the variables.
    pub fn find_canonical_monic_of_vars(&self, vars: &[usize]) -> Option<usize> {
        self.emons
            .find_canonical(vars)
            .map(|monic| self.emons.monics[monic].variable)
    }

    pub fn is_canonical_monic(&self, lp_var: usize) -> bool {
        self.emons.is_canonical_monic(lp_var)
    }

    // divide: the factor b with bc = b * c, up to sign.
    pub fn divide(&self, product: usize, divisor: &Factor) -> Option<Factor> {
        let divisor_vars = self.sorted_rvars(divisor);
        let quotient_vars = get_vector_div(&self.emons.monics[product].rvars, &divisor_vars)?;
        let mut quotient = if quotient_vars.len() == 1 {
            mk_factor(quotient_vars[0], false)
        } else {
            let monic = self.emons.find_canonical(&quotient_vars)?;
            mk_factor(self.emons.monics[monic].variable, true)
        };
        quotient.is_negated = (self.canonize_sign_factor(&quotient)
            != self.canonize_sign_factor(divisor))
            != self.emons.monics[product].rsign;
        Some(quotient)
    }

    // The factorizations of a monic: into its variables first, then into two canonical factors.
    pub fn get_factorizations(&self, rooted: usize) -> Factorizations {
        let vars = self.emons.monics[rooted].rvars.clone();
        let mask = if vars.len() != 2 {
            vec![false; vars.len().saturating_sub(1)]
        } else {
            vec![true]
        };
        Factorizations {
            vars,
            monic: self.emons.get_index(self.emons.monics[rooted].variable),
            mask,
            is_full_returned: false,
            num_failures: 0,
            is_started: false,
            is_done: false,
        }
    }

    pub fn clear(&mut self) {
        self.lemmas = Vec::new();
        self.literals = Vec::new();
        self.fixed_equalities = Vec::new();
        self.equalities = Vec::new();
        self.is_check_feasible = false;
    }

    pub fn insert_to_refine(&mut self, lp_var: usize) {
        self.to_refine.add(lp_var);
    }

    pub fn erase_from_to_refine(&mut self, lp_var: usize) {
        if self.to_refine.has(lp_var) {
            self.to_refine.delete(lp_var);
        }
    }

    pub fn conflict_found(&self) -> bool {
        self.lemmas.iter().any(is_conflict_lemma)
    }

    // set_use_nra_model, undone on pop.
    pub fn set_use_nra_model(&mut self, is_using: bool) {
        if is_using == self.is_using_nra_model {
            return;
        }
        self.emons
            .push_core_undo(CoreUndo::SetUseNraModel(is_using));
        self.is_using_nra_model = is_using;
    }
}

impl<'l> Nla<'_, 'l> {
    pub fn settings(&self) -> &LpSettings<'l> {
        self.lra.settings()
    }

    pub fn stats(&mut self) -> &mut LpStats {
        &mut self.lra.settings_mut().stats
    }

    // onChangedBounds: the monic variables among the columns whose bounds changed, and the monics
    // using them, see the top of the file.
    pub fn drain_changed_bounds(&mut self) {
        let columns = std::mem::take(&mut self.lra.changed_bounds_pending);
        let core = &mut *self.core;
        for column in columns {
            if core.is_monic_var(column) {
                core.monics_with_changed_bounds.add(column);
            }
            let mut use_list = core.emons.get_use_list(column, &core.var_eqs);
            while let Some(monic) = use_list.next(&core.emons) {
                core.monics_with_changed_bounds
                    .add(core.emons.monics[monic].variable);
            }
        }
    }

    // Values and bounds.

    pub fn val(&self, lp_var: usize) -> Rational {
        get_val(self.lra, lp_var).clone()
    }

    pub fn var_val(&self, monic: usize) -> Rational {
        self.val(self.emons.monics[monic].variable)
    }

    pub fn mul_val(&self, monic: usize) -> Rational {
        get_mul_val(self.lra, &self.emons.monics[monic])
    }

    pub fn val_factor(&self, factor: &Factor) -> Rational {
        let value = self.val(factor.variable);
        if factor.is_negated {
            value.neg()
        } else {
            value
        }
    }

    pub fn compare_holds(&self, left: &Rational, cmp: ConstraintKind, right: &Rational) -> bool {
        let comparison = left.compare(right);
        match cmp {
            KIND_LE => comparison != Ordering::Greater,
            KIND_LT => comparison == Ordering::Less,
            KIND_GE => comparison != Ordering::Less,
            KIND_GT => comparison == Ordering::Greater,
            KIND_EQ => comparison == Ordering::Equal,
            _ => comparison != Ordering::Equal,
        }
    }

    pub fn value(&self, term: &LarTerm) -> Rational {
        let mut result = Rational::zero();
        for (column, coeff) in term.iter() {
            result = result.add(&coeff.mul(get_val(self.lra, column)));
        }
        result
    }

    pub fn ineq_holds(&self, ineq: &Ineq) -> bool {
        self.compare_holds(&self.value(&ineq.term), ineq.cmp, &ineq.rs)
    }

    pub fn has_upper_bound(&self, lp_var: usize) -> bool {
        self.lra.core.has_upper_bound(lp_var)
    }

    pub fn has_lower_bound(&self, lp_var: usize) -> bool {
        self.lra.core.has_lower_bound(lp_var)
    }

    pub fn get_upper_bound(&self, lp_var: usize) -> Rational {
        self.lra.get_upper_bound(lp_var).x.clone()
    }

    pub fn get_lower_bound(&self, lp_var: usize) -> Rational {
        self.lra.get_lower_bound(lp_var).x.clone()
    }

    pub fn no_bounds(&self, lp_var: usize) -> bool {
        !self.has_upper_bound(lp_var) && !self.has_lower_bound(lp_var)
    }

    pub fn zero_is_an_inner_point_of_bounds(&self, lp_var: usize) -> bool {
        if self.has_upper_bound(lp_var) && !self.get_upper_bound(lp_var).is_positive() {
            return false;
        }
        !(self.has_lower_bound(lp_var) && !self.get_lower_bound(lp_var).is_negative())
    }

    pub fn var_is_int(&self, lp_var: usize) -> bool {
        self.lra.is_int(lp_var)
    }

    pub fn var_is_fixed_to_zero(&self, lp_var: usize) -> bool {
        self.lra.is_fixed(lp_var) && self.lra.get_lower_bound(lp_var).is_zero()
    }

    pub fn var_is_fixed(&self, lp_var: usize) -> bool {
        self.lra.is_fixed(lp_var)
    }

    pub fn var_is_free(&self, lp_var: usize) -> bool {
        self.lra.is_free(lp_var)
    }

    pub fn var_has_positive_lower_bound(&self, lp_var: usize) -> bool {
        let lower = self.lra.get_lower_bound(lp_var);
        self.has_lower_bound(lp_var)
            && (lower.x.is_positive() || (lower.x.is_zero() && lower.y.is_positive()))
    }

    pub fn var_has_negative_upper_bound(&self, lp_var: usize) -> bool {
        let upper = self.lra.get_upper_bound(lp_var);
        self.has_upper_bound(lp_var)
            && (upper.x.is_negative() || (upper.x.is_zero() && upper.y.is_negative()))
    }

    pub fn var_is_big(&self, lp_var: usize) -> bool {
        !self.var_is_int(lp_var) && get_val(self.lra, lp_var).is_big()
    }

    pub fn has_big_num(&self, monic: usize) -> bool {
        let monic = &self.emons.monics[monic];
        self.var_is_big(monic.variable) || monic.vars.iter().any(|lp_var| self.var_is_big(*lp_var))
    }

    pub fn has_real(&self, monic: usize) -> bool {
        self.emons.monics[monic]
            .vars
            .iter()
            .any(|lp_var| !self.var_is_int(*lp_var))
    }

    pub fn has_real_factorization(&self, factorization: &Factorization) -> bool {
        factorization
            .factors
            .iter()
            .any(|factor| !self.var_is_int(factor.variable))
    }

    pub fn mon_has_zero(&self, vars: &[usize]) -> bool {
        vars.iter()
            .any(|lp_var| get_val(self.lra, *lp_var).is_zero())
    }

    pub fn get_monic_sign(&self, monic: usize) -> i32 {
        let mut sign = 1;
        for lp_var in &self.emons.monics[monic].vars {
            let value = get_val(self.lra, *lp_var);
            if value.is_negative() {
                sign = -sign;
            } else if !value.is_positive() {
                return 0;
            }
        }
        sign
    }

    pub fn add_monic(&mut self, lp_var: usize, vars: &[usize]) {
        self.drain_changed_bounds();
        let core = &mut *self.core;
        core.emons.add(lp_var, vars, &mut core.var_eqs);
        core.monics_with_changed_bounds.add(lp_var);
    }

    pub fn product_value(&self, monic: usize) -> Rational {
        self.mul_val(monic)
    }

    // check_monic: whether the value of the monic is the product of its factors' values.
    pub fn check_monic(&self, monic: usize) -> bool {
        let variable = self.emons.monics[monic].variable;
        let value = self.lra.get_value(variable);
        if self.lra.is_int(variable) && !value.x.is_int() {
            return true;
        }
        self.product_value(monic) == value.x
    }

    pub fn has_relevant_monomial(&mut self) -> bool {
        self.drain_changed_bounds();
        self.emons
            .monics
            .iter()
            .any(|monic| (self.is_relevant)(monic.variable))
    }

    pub fn get_var_weight(&self, lp_var: usize) -> u32 {
        let column_type = self.lra.core.get_column_type(lp_var);
        let mut weight = match column_type {
            COLUMN_FIXED => 0,
            COLUMN_BOXED => 3,
            COLUMN_LOWER | COLUMN_UPPER => 6,
            COLUMN_FREE => 9,
            _ => 0,
        };
        if self.is_monic_var(lp_var) {
            weight += 1;
            if self.to_refine.has(lp_var) {
                weight += 1;
            }
        }
        weight
    }

    // Lemma helpers.

    pub fn negate_relation(&mut self, lemma: &LemmaBuilder, lp_var: usize, value: &Rational) {
        let cmp = if self.val(lp_var).compare(value) == Ordering::Less {
            KIND_GE
        } else {
            KIND_LE
        };
        lemma.add_ineq(self, mk_ineq(lp_var, cmp, value.clone()));
    }

    // Explanations of inequalities by bounds.

    fn explain_coeff_bound(
        &self,
        column: usize,
        coeff: &Rational,
        is_upper: bool,
        explanation: &mut Explanation,
    ) -> Option<Rational> {
        let is_using_upper = if is_upper {
            !coeff.is_negative()
        } else {
            coeff.is_negative()
        };
        let dep = if is_using_upper {
            self.lra.get_upper_witness(column)
        } else {
            self.lra.get_lower_witness(column)
        };
        dep.as_ref()?;
        let bound = if is_using_upper {
            self.lra.get_upper_bound(column)
        } else {
            self.lra.get_lower_bound(column)
        };
        explanation.push_dependency(dep);
        Some(coeff.mul(&bound.x))
    }

    fn explain_bound(
        &self,
        term: &LarTerm,
        rs: &Rational,
        is_upper: bool,
        explanation: &mut Explanation,
    ) -> bool {
        let mut bound = Rational::zero();
        for (column, coeff) in term.iter() {
            let Some(coeff_bound) = self.explain_coeff_bound(column, coeff, is_upper, explanation)
            else {
                explanation.clear();
                return false;
            };
            bound = bound.add(&coeff_bound);
        }
        let is_violated = if is_upper {
            bound.compare(rs) == Ordering::Greater
        } else {
            bound.compare(rs) == Ordering::Less
        };
        if is_violated {
            explanation.clear();
            return false;
        }
        true
    }

    // explain_ineq: whether the bounds imply the negation of term cmp rs, added to the lemma.
    pub fn explain_ineq(
        &mut self,
        lemma: &LemmaBuilder,
        term: &LarTerm,
        cmp: ConstraintKind,
        rs: &Rational,
    ) -> bool {
        if term.size() == 0 && rs.is_zero() && (cmp == KIND_LT || cmp == KIND_GT || cmp == KIND_NE)
        {
            return true;
        }
        let mut explanation = Explanation::new();
        let one = Rational::one();
        let is_explained = match negate_kind(cmp) {
            KIND_LE => self.explain_bound(term, rs, true, &mut explanation),
            KIND_LT => self.explain_bound(term, &rs.sub(&one), true, &mut explanation),
            KIND_GE => self.explain_bound(term, rs, false, &mut explanation),
            KIND_GT => self.explain_bound(term, &rs.add(&one), false, &mut explanation),
            KIND_EQ => {
                (self.explain_bound(term, rs, false, &mut explanation)
                    && self.explain_bound(term, rs, true, &mut explanation))
                    || (rs.is_zero() && self.explain_by_equiv(term, &mut explanation))
            }
            _ => {
                self.explain_bound(term, &rs.add(&one), false, &mut explanation)
                    || self.explain_bound(term, &rs.sub(&one), true, &mut explanation)
            }
        };
        if !is_explained {
            return false;
        }
        lemma.add_explanation(self, &explanation);
        true
    }

    pub fn explain_by_equiv(&mut self, term: &LarTerm, explanation: &mut Explanation) -> bool {
        let Some(octagon) = get_octagon_term(term) else {
            return false;
        };
        let first = mk_signed_var(octagon.first, false);
        let second = mk_signed_var(octagon.second, octagon.is_negated);
        if self.var_eqs.find(first) != self.var_eqs.find(second) {
            return false;
        }
        self.var_eqs.explain(first, second, explanation);
        true
    }

    // collect_equivs: the term columns fixed to zero that equate or negate two variables.
    fn collect_equivs(&mut self) {
        for index in 0..self.lra.terms.len() {
            let term = &self.lra.terms[index];
            let column = term.column;
            if !self.lra.has_term(column) || !self.var_is_fixed_to_zero(column) {
                continue;
            }
            let Some(octagon) = get_octagon_term(term) else {
                continue;
            };
            let justification = vec![
                self.lra.get_upper_witness(column).clone(),
                self.lra.get_lower_witness(column).clone(),
            ];
            let core = &mut *self.core;
            if octagon.is_negated {
                core.var_eqs.merge_minus(
                    octagon.first,
                    octagon.second,
                    justification,
                    &mut core.emons,
                );
            } else {
                core.var_eqs.merge_plus(
                    octagon.first,
                    octagon.second,
                    justification,
                    &mut core.emons,
                );
            }
        }
        let core = &mut *self.core;
        core.emons.ensure_canonized(&core.var_eqs);
    }

    // The search.

    pub fn random(&mut self) -> u32 {
        self.lra.settings_mut().get_random_next()
    }

    // In production a step of the resource limit, so not a pure query.
    pub fn is_canceled(&self) -> bool {
        self.lra.settings().is_canceled()
    }

    // check_bounded_divisions: the lemmas of the divisions of bounded terms by numerals.
    pub fn check_bounded_divisions(&mut self) {
        self.drain_changed_bounds();
        self.clear();
        Divisions::check_bounded_divisions(self);
    }

    fn init_search(&mut self) {
        self.clear();
        self.collect_equivs();
    }

    pub fn init_to_refine(&mut self) {
        if self.lra.is_feasible() {
            self.lra.get_rid_of_inf_eps();
        }
        self.core.to_refine.clear();
        let offset = self.random() as usize;
        let size = self.emons.num_monics();
        for index in 0..size {
            let monic = (index + offset) % size;
            if !self.check_monic(monic) {
                let variable = self.emons.monics[monic].variable;
                self.insert_to_refine(variable);
            }
        }
    }

    pub fn done(&self) -> bool {
        self.lemmas.len() >= 10 || self.conflict_found() || self.is_canceled()
    }

    pub fn find_bfc_to_refine_on_monic(&self, monic: usize) -> Option<Factorization> {
        let mut factorizations = self.get_factorizations(monic);
        while let Some(factorization) = factorizations.next(self) {
            if factorization.factors.len() != 2 {
                continue;
            }
            let product = self
                .val_factor(&factorization.factors[0])
                .mul(&self.val_factor(&factorization.factors[1]));
            if self.var_val(monic) != product {
                return Some(factorization);
            }
        }
        None
    }

    // find_bfc_to_refine: a monic to refine (its index), with a binary factorization of it.
    pub fn find_bfc_to_refine(&mut self) -> Option<(usize, Factorization)> {
        let offset = self.random() as usize;
        let size = self.to_refine.size();
        for index in 0..size {
            let monic = self
                .emons
                .get_index(self.to_refine.elems[(index + offset) % size]);
            if self.has_real(monic) {
                continue;
            }
            let vars = &self.emons.monics[monic].vars;
            if vars.len() == 2 {
                let factorization = Factorization {
                    factors: vec![mk_factor(vars[0], false), mk_factor(vars[1], false)],
                    mon: Some(monic),
                };
                return Some((monic, factorization));
            }
            if let Some(factorization) = self.find_bfc_to_refine_on_monic(monic) {
                return Some((monic, factorization));
            }
        }
        None
    }

    // hasNoEffect of check: whether nothing so far has decided or refined the check.
    fn has_no_effect(&self, result: LBool) -> bool {
        result == LBool::Undef
            && !self.done()
            && !self.is_nla_satisfied
            && self.lemmas.is_empty()
            && self.literals.is_empty()
            && !self.is_check_feasible
    }

    fn run_check(
        &mut self,
        check: WeightedCheck,
        result: LBool,
        is_running_horner: bool,
    ) -> Result<(), SmtError> {
        match check {
            WeightedCheck::Horner => {
                if self.has_no_effect(result) && is_running_horner {
                    Horner::horner_lemmas(self);
                }
            }
            WeightedCheck::Grobner => {
                if self.has_no_effect(result) && NLA_PARAMS.grobner {
                    Grobner::run(self)?;
                }
            }
            WeightedCheck::Bounds => {
                if self.has_no_effect(result) && NLA_PARAMS.branching {
                    self.add_bounds();
                }
            }
            WeightedCheck::Order => Order::order_lemma(self),
            WeightedCheck::Monotone => Monotone::monotonicity_lemma(self),
            WeightedCheck::Tangent => Tangents::tangent_lemma(self),
        }
        Ok(())
    }

    // check_weighted: runs the checks in a random order weighted by their weights, until one yields.
    fn check_weighted(
        &mut self,
        checks: &[(u32, WeightedCheck)],
        result: LBool,
        is_running_horner: bool,
    ) -> Result<(), SmtError> {
        let mut bound: u32 = checks.iter().map(|check| check.0).sum();
        let mut is_seen = vec![false; checks.len()];
        while bound > 0 && !self.done() && self.lemmas.is_empty() {
            let mut draw = self.random() % bound;
            for index in 0..checks.len() {
                if is_seen[index] {
                    continue;
                }
                if draw < checks[index].0 {
                    is_seen[index] = true;
                    self.run_check(checks[index].1, result, is_running_horner)?;
                    bound -= checks[index].0;
                    break;
                }
                draw -= checks[index].0;
            }
        }
        Ok(())
    }

    // add_bounds: a split on a free variable of a monic to refine.
    fn add_bounds(&mut self) {
        let offset = self.random() as usize;
        let size = self.to_refine.size();
        for index in 0..size {
            let monic = self
                .emons
                .get_index(self.to_refine.elems[(index + offset) % size]);
            for var_index in 0..self.emons.monics[monic].vars.len() {
                let lp_var = self.emons.monics[monic].vars[var_index];
                if !self.var_is_free(lp_var) || self.emons.monics[monic].is_bound_propagated {
                    continue;
                }
                self.emons.set_bound_propagated(monic);
                self.literals
                    .push(mk_ineq(lp_var, KIND_EQ, Rational::zero()));
                self.stats().nla_add_bounds += 1;
                return;
            }
        }
    }

    fn on_to_refine_empty(&mut self) -> LBool {
        self.squeeze_schedule.on_nothing_to_refine();
        LBool::True
    }

    pub fn check(&mut self, level: u32) -> Result<LBool, SmtError> {
        self.drain_changed_bounds();
        self.stats().nla_calls += 1;
        self.lra.get_rid_of_inf_eps();
        if self.lra.status != LP_OPTIMAL && self.lra.status != LP_FEASIBLE {
            return Ok(LBool::Undef);
        }
        self.init_to_refine();
        Patcher::patch_monomials(self);
        self.set_use_nra_model(false);
        if self.to_refine.size() == 0 {
            return Ok(self.on_to_refine_empty());
        }
        self.init_search();
        self.is_nla_satisfied = false;
        let mut result = LBool::Undef;
        let is_running_grobner = NLA_PARAMS.grobner;
        let is_running_horner = NLA_PARAMS.horner
            && self
                .stats()
                .nla_calls
                .is_multiple_of(NLA_PARAMS.horner_frequency);
        let is_running_bounds = NLA_PARAMS.branching;
        // Model-based basic lemmas are effective on small systems, and branching on larger ones.
        let is_delaying_bounds = is_running_bounds && self.emons.num_monics() <= 8;
        if self.has_no_effect(result) {
            MonomialBounds::generate_lemmas(self);
        }
        if self.has_no_effect(result) && self.refine_pseudo_linear() {
            return Ok(LBool::False);
        }
        let is_squeeze_cadence = self
            .stats()
            .nla_calls
            .is_multiple_of(NLA_PARAMS.horner_frequency);
        if self.has_no_effect(result)
            && self.squeeze_schedule.is_enabled()
            && (is_running_horner || is_running_grobner)
            && (self.squeeze_schedule.is_eager() || is_squeeze_cadence)
        {
            let is_improved = MonomialBounds::optimize_nl_bounds(self);
            self.squeeze_schedule.on_squeeze(is_improved);
            if self.to_refine.size() == 0 {
                return Ok(self.on_to_refine_empty());
            }
        }
        let checks: &[(u32, WeightedCheck)] = if is_delaying_bounds {
            &[(1, WeightedCheck::Horner), (1, WeightedCheck::Grobner)]
        } else {
            &[
                (1, WeightedCheck::Horner),
                (1, WeightedCheck::Grobner),
                (1, WeightedCheck::Bounds),
            ]
        };
        self.check_weighted(checks, result, is_running_horner)?;
        if self.is_canceled() {
            return Ok(LBool::Undef);
        }
        if !self.lemmas.is_empty() || !self.literals.is_empty() || self.is_check_feasible {
            return Ok(LBool::False);
        }
        if self.is_nla_satisfied {
            return Ok(LBool::True);
        }
        if self.has_no_effect(result)
            && NLA_PARAMS.nra_check_assignment
            && self.check_assignment_fail_count < NLA_PARAMS.nra_check_assignment_max_fail
        {
            result = NraSolver::check_assignment(self)?;
            if result != LBool::True {
                self.core.check_assignment_fail_count += 1;
            }
        }
        if self.has_no_effect(result) && self.should_run_bounded_nlsat() {
            result = self.bounded_nlsat()?;
        }
        if self.has_no_effect(result) {
            Basics::basic_lemma(self, true);
        }
        if self.has_no_effect(result) && is_delaying_bounds {
            Basics::basic_lemma(self, false);
        }
        if self.has_no_effect(result) && is_delaying_bounds {
            self.add_bounds();
        }
        if self.has_no_effect(result) && !is_delaying_bounds {
            Basics::basic_lemma(self, false);
        }
        if self.has_no_effect(result) {
            Divisions::check(self);
        }
        if self.has_no_effect(result) {
            self.check_weighted(
                &[
                    (6, WeightedCheck::Order),
                    (2, WeightedCheck::Monotone),
                    (1, WeightedCheck::Tangent),
                ],
                result,
                is_running_horner,
            )?;
            let num_calls = self.stats().nla_calls;
            if !self.conflict_found()
                && NLA_PARAMS.nra
                && num_calls.is_multiple_of(50)
                && num_calls > 500
            {
                result = self.bounded_nlsat()?;
            }
        }
        if self.has_no_effect(result) && NLA_PARAMS.nra && level >= 2 {
            result = NraSolver::check(self, u64::MAX, u64::MAX)?;
            self.stats().nra_calls += 1;
        }
        if result == LBool::Undef && !self.has_no_effect(result) {
            result = LBool::False;
        }
        let num_lemmas = self.lemmas.len() as u64;
        self.stats().nla_lemmas += num_lemmas;
        Ok(result)
    }

    fn should_run_bounded_nlsat(&mut self) -> bool {
        NLA_PARAMS.nra && self.core.nlsat_backoff.should_run()
    }

    // bounded_nlsat: a run of nlsat capped at 100 conflicts and 100000 steps. A refutation, or a run
    // that took less than a tenth of the steps, makes the backoff run it again sooner.
    fn bounded_nlsat(&mut self) -> Result<LBool, SmtError> {
        let budget = 100000;
        let result = NraSolver::check(self, 100, budget)?;
        self.stats().nra_calls += 1;
        let is_success = result == LBool::False || self.nra.steps() < budget / 10;
        self.core.nlsat_backoff.update(is_success);
        if result == LBool::True {
            self.clear();
        }
        Ok(result)
    }

    // Propagation.

    pub fn propagate(&mut self) -> bool {
        self.drain_changed_bounds();
        self.clear();
        let mut is_propagated = false;
        if MonomialBounds::tighten_lp_bounds(self) {
            is_propagated = true;
        }
        if MonomialBounds::propagate_changed_bounds(self) {
            is_propagated = true;
        }
        if MonomialBounds::propagate_violated_linear_monomials(self) {
            is_propagated = true;
        }
        self.monics_with_changed_bounds.clear();
        if is_propagated {
            self.is_check_feasible = true;
        }
        is_propagated
    }

    pub fn incremental_propagate(&mut self) -> bool {
        self.drain_changed_bounds();
        self.clear();
        let is_propagated = MonomialBounds::propagate_changed_bounds(self);
        self.monics_with_changed_bounds.clear();
        if is_propagated {
            self.is_check_feasible = true;
        }
        is_propagated
    }

    // Pseudo-linear monomials: all but one factor are integers in a range of at most 4.

    fn is_pseudo_linear(&self, monic: usize) -> bool {
        let mut has_unbounded = false;
        for lp_var in &self.emons.monics[monic].vars {
            if self.is_small_int_range(*lp_var) {
                continue;
            }
            if has_unbounded {
                return false;
            }
            has_unbounded = true;
        }
        true
    }

    fn is_small_int_range(&self, lp_var: usize) -> bool {
        let lra = &self.lra;
        let column_type = lra.core.get_column_type(lp_var);
        if (column_type != COLUMN_BOXED && column_type != COLUMN_FIXED) || !lra.is_int(lp_var) {
            return false;
        }
        lra.get_upper_bound(lp_var)
            .sub(lra.get_lower_bound(lp_var))
            .compare(&Impq::from_x(Rational::from(4)))
            != Ordering::Greater
    }

    fn refine_pseudo_linear(&mut self) -> bool {
        if !NLA_PARAMS.reduce_pseudo_linear {
            return false;
        }
        for index in 0..self.to_refine.size() {
            let monic = self.emons.get_index(self.to_refine.elems[index]);
            if !self.is_pseudo_linear(monic) {
                continue;
            }
            self.refine_pseudo_linear_monic(monic);
            return true;
        }
        false
    }

    fn refine_pseudo_linear_monic(&mut self, monic: usize) {
        let lemma = LemmaBuilder::new(self);
        let vars = self.emons.monics[monic].vars.clone();
        let mut nl_var = NULL_LPVAR;
        let mut product = Rational::one();
        for (index, lp_var) in vars.iter().copied().enumerate() {
            if index == vars.len() - 1 && nl_var == NULL_LPVAR {
                nl_var = lp_var;
                break;
            }
            if self.is_small_int_range(lp_var) {
                let value = self.val(lp_var);
                lemma.add_ineq(self, mk_ineq(lp_var, KIND_NE, value));
                product = product.mul(&self.val(lp_var));
                continue;
            }
            nl_var = lp_var;
        }
        let term = LarTerm::from_entries([
            (self.emons.monics[monic].variable, &Rational::one()),
            (nl_var, &product.neg()),
        ]);
        lemma.add_ineq(self, mk_term_ineq(term, KIND_EQ, Rational::zero()));
    }

    // Scopes.

    pub fn push(&mut self) {
        self.drain_changed_bounds();
        let core = &mut *self.core;
        core.emons.push(&mut core.var_eqs);
    }

    pub fn pop(&mut self, count: usize) {
        self.drain_changed_bounds();
        let core = &mut *self.core;
        for undo in core.emons.pop(count, &mut core.var_eqs) {
            match undo {
                CoreUndo::SetUseNraModel(is_using) => core.is_using_nra_model = !is_using,
                CoreUndo::PopIdivision => {
                    core.divisions.idivisions.pop();
                }
                CoreUndo::PopBoundedDivision => {
                    core.divisions.bounded_divisions.pop();
                }
                CoreUndo::PopDivisibility => {
                    core.divisions.divisibility.pop();
                }
            }
        }
    }
}

// is_octagon_term: whether the term is +-x +-y, and whether its signs agree.
fn get_octagon_term(term: &LarTerm) -> Option<OctagonTerm> {
    if term.size() != 2 {
        return None;
    }
    let mut is_minus_seen = false;
    let mut is_plus_seen = false;
    let mut vars = Vec::new();
    for (column, coeff) in term.iter() {
        if *coeff == Rational::one() {
            is_plus_seen = true;
        } else if *coeff == Rational::minus_one() {
            is_minus_seen = true;
        } else {
            return None;
        }
        vars.push(column);
    }
    Some(OctagonTerm {
        first: vars[0],
        second: vars[1],
        is_negated: !(is_minus_seen && is_plus_seen),
    })
}

// vector_div: the multiset difference of sorted vectors, when the divisor is a proper factor.
fn get_vector_div(product: &[usize], divisor: &[usize]) -> Option<Vec<usize>> {
    if divisor.len() >= product.len() {
        return None;
    }
    let mut quotient = Vec::new();
    let mut divisor_index = 0;
    for lp_var in product {
        if divisor_index < divisor.len() && divisor[divisor_index] == *lp_var {
            divisor_index += 1;
        } else if divisor_index < divisor.len() && divisor[divisor_index] < *lp_var {
            return None;
        } else {
            quotient.push(*lp_var);
        }
    }
    (divisor_index == divisor.len()).then_some(quotient)
}

// The cursor of the getFactorizations generator: the factorization into the monic's variables,
// then each binary one by a mask over its rooted variables, the last always in the first factor.
// Each `next` runs the generator's body to its next yield, so it reads nla when it is called.
pub struct Factorizations {
    vars: Vec<usize>,
    // The monic index of emons.get(rooted.variable).
    monic: usize,
    mask: Vec<bool>,
    is_full_returned: bool,
    num_failures: u32,
    // Whether a factorization was yielded, so that `next` resumes after the yield.
    is_started: bool,
    is_done: bool,
}

impl Factorizations {
    pub fn next(&mut self, nla: &Nla<'_, '_>) -> Option<Factorization> {
        if self.is_done {
            return None;
        }
        if self.is_started {
            if self.is_full_returned {
                let index = self.mask.iter().position(|is_set| !is_set);
                let end = index.unwrap_or(self.mask.len());
                self.mask[..end].fill(false);
                if let Some(index) = index {
                    self.mask[index] = true;
                }
            } else {
                self.is_full_returned = true;
            }
        }
        if self.is_full_returned && self.mask.iter().all(|is_set| *is_set) {
            self.is_done = true;
            return None;
        }
        self.is_started = true;
        Some(if self.is_full_returned {
            self.get_binary(nla)
        } else {
            mk_mon_factorization(&nla.emons, self.monic)
        })
    }

    fn get_factor(&mut self, nla: &Nla<'_, '_>, factor_vars: &[usize]) -> Option<Factor> {
        if factor_vars.len() == 1 {
            return Some(mk_factor(factor_vars[0], false));
        }
        let Some(variable) = nla.find_canonical_monic_of_vars(factor_vars) else {
            self.num_failures += 1;
            return None;
        };
        Some(mk_factor(variable, true))
    }

    fn get_binary(&mut self, nla: &Nla<'_, '_>) -> Factorization {
        let empty = Factorization {
            factors: Vec::new(),
            mon: None,
        };
        let mut k_vars = vec![self.vars[self.vars.len() - 1]];
        let mut j_vars = Vec::new();
        for (index, is_set) in self.mask.iter().enumerate() {
            if *is_set {
                k_vars.push(self.vars[index]);
            } else {
                j_vars.push(self.vars[index]);
            }
        }
        k_vars.sort();
        j_vars.sort();
        if self.num_failures > 1000 {
            self.mask.fill(true);
            self.mask[0] = false;
            self.is_full_returned = true;
            return empty;
        }
        let Some(mut first) = self.get_factor(nla, &k_vars) else {
            return empty;
        };
        self.num_failures = 0;
        let Some(second) = self.get_factor(nla, &j_vars) else {
            return empty;
        };
        let mut factorization = Factorization {
            factors: vec![first, second],
            mon: None,
        };
        first.is_negated = first.is_negated
            != (nla.canonize_sign_factorization(&factorization)
                != nla.emons.monics[self.monic].rsign);
        factorization.factors[0] = first;
        factorization
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::lp::nla_divisions::Division;
    use crate::lp::nla_types::Lemma;
    use prove_decide::Limits;

    // What the TS printed for a lemma: its inequalities as `term cmp rs`, the term's entries in
    // their order, then its explanation's constraint indices.
    pub(crate) fn show_lemma(lemma: &Lemma) -> String {
        let ineqs: Vec<String> = lemma
            .ineqs
            .iter()
            .map(|ineq| {
                let entries: Vec<String> = ineq
                    .term
                    .iter()
                    .map(|(column, coeff)| format!("{coeff}*v{column}"))
                    .collect();
                format!("{} {} {}", entries.join("+"), ineq.cmp, ineq.rs)
            })
            .collect();
        let expl: Vec<String> = lemma.expl.iter().map(|index| index.to_string()).collect();
        format!("[{}] {{{}}}", ineqs.join(" | "), expl.join(","))
    }

    pub(crate) fn show_lemmas(core: &NlaCore) -> Vec<String> {
        core.lemmas.iter().map(show_lemma).collect()
    }

    // A LarSolver with an NlaCore over it, as smt-pdd.test.ts's nla tests build them: `with_nla`
    // runs a body on the view.
    pub(crate) struct NlaFixture<'l> {
        pub lra: LarSolver<'l>,
        pub core: NlaCore,
    }

    impl<'l> NlaFixture<'l> {
        pub(crate) fn new() -> NlaFixture<'l> {
            let mut lra = LarSolver::new(Box::new(|| false));
            let core = NlaCore::new(&mut lra);
            NlaFixture { lra, core }
        }

        // Adds and activates a bound, as the TS tests' activated constraints.
        pub(crate) fn add_bound(&mut self, column: usize, kind: ConstraintKind, rhs: i64) -> usize {
            let constraint = self.lra.mk_var_bound(column, kind, &Rational::from(rhs));
            self.lra.activate(constraint);
            constraint
        }

        // The TS oracle's scenario: columns 0..num_vars, the monics, the activated bounds, a
        // feasible solution, init_to_refine and init_search. Returns the bounds' constraints.
        pub(crate) fn mk_scenario(
            num_vars: usize,
            monics: &[(usize, &[usize])],
            bounds: &[(usize, ConstraintKind, i64)],
        ) -> (NlaFixture<'l>, Vec<usize>) {
            let mut fixture = NlaFixture::new();
            for external in 0..num_vars {
                fixture.lra.add_var(external, true);
            }
            fixture.with_nla(|nla| {
                for monic in monics {
                    nla.add_monic(monic.0, monic.1);
                }
            });
            let constraints = bounds
                .iter()
                .map(|bound| fixture.add_bound(bound.0, bound.1, bound.2))
                .collect();
            fixture.prepare();
            (fixture, constraints)
        }

        pub(crate) fn prepare(&mut self) {
            self.lra.find_feasible_solution();
            self.with_nla(|nla| {
                nla.init_to_refine();
                nla.init_search();
            });
        }

        // The values of the columns and the variables to refine, as the TS oracle printed them.
        pub(crate) fn show_state(&self) -> String {
            let values: Vec<String> = (0..self.lra.get_column_count())
                .map(|column| self.lra.get_value(column).to_string())
                .collect();
            let to_refine: Vec<String> = self
                .core
                .to_refine
                .elems
                .iter()
                .map(usize::to_string)
                .collect();
            format!(
                "values {} toRefine {}",
                values.join(","),
                to_refine.join(",")
            )
        }

        pub(crate) fn with_nla<T>(&mut self, body: impl FnOnce(&mut Nla<'_, 'l>) -> T) -> T {
            let limits = Limits::new(f64::INFINITY, None, None);
            let limit = ResourceLimit::new(&limits);
            let mut nla = Nla {
                core: &mut self.core,
                lra: &mut self.lra,
                limit: &limit,
                is_relevant: &|_| true,
            };
            body(&mut nla)
        }
    }

    #[test]
    fn drains_the_changed_bounds_into_the_monics_using_them() {
        let mut fixture = NlaFixture::new();
        let x = fixture.lra.add_var(0, true);
        let y = fixture.lra.add_var(1, true);
        let m = fixture.lra.add_var(2, true);
        let z = fixture.lra.add_var(3, true);
        fixture.with_nla(|nla| nla.add_monic(m, &[x, y]));
        fixture.core.monics_with_changed_bounds.clear();
        fixture.add_bound(y, KIND_GE, 1);
        fixture.add_bound(z, KIND_GE, 1);
        fixture.lra.find_feasible_solution();
        assert_eq!(fixture.lra.changed_bounds_pending, [y, z]);
        fixture.with_nla(|nla| nla.push());
        assert!(fixture.lra.changed_bounds_pending.is_empty());
        assert_eq!(fixture.core.monics_with_changed_bounds.elems, [m]);
    }

    // The order of the factorizations, from running the TS generator on x*y*z with the monics y*z
    // and x*z: the mask that puts x with z finds no monic x*y for the other factor.
    #[test]
    fn enumerates_the_factorizations_lazily() {
        let mut fixture = NlaFixture::new();
        let vars: Vec<usize> = (0..6)
            .map(|index| fixture.lra.add_var(index, true))
            .collect();
        let (x, y, z) = (vars[0], vars[1], vars[2]);
        fixture.with_nla(|nla| {
            nla.add_monic(vars[3], &[x, y, z]);
            nla.add_monic(vars[4], &[y, z]);
            nla.add_monic(vars[5], &[x, z]);
            let monic = nla.emons.get_index(vars[3]);
            let mut factorizations = nla.get_factorizations(monic);
            let mut shown = Vec::new();
            while let Some(factorization) = factorizations.next(nla) {
                let factors: Vec<String> = factorization
                    .factors
                    .iter()
                    .map(|factor| {
                        format!("{}{}{}", factor.variable, factor.is_mon, factor.is_negated)
                    })
                    .collect();
                shown.push(format!("{}:{:?}", factors.join(","), factorization.mon));
            }
            assert_eq!(
                shown,
                [
                    "0falsefalse,1falsefalse,2falsefalse:Some(0)",
                    ":None",
                    "5truefalse,1falsefalse:None",
                    "4truefalse,0falsefalse:None",
                ]
            );
        });
    }

    // Expected lemmas from the TS oracle on the same setup: t = x - y fixed to 0 makes x and y
    // equivalent, so x*z and y*z are one class, whose values 1 and 2 disagree.
    #[test]
    fn explains_the_derived_sign_lemma_by_the_equivalence() {
        let mut fixture = NlaFixture::new();
        for external in 0..5 {
            fixture.lra.add_var(external, true);
        }
        let term = fixture
            .lra
            .add_term(&[(0, Rational::one()), (1, Rational::minus_one())], 5);
        fixture.with_nla(|nla| {
            nla.add_monic(3, &[0, 2]);
            nla.add_monic(4, &[1, 2]);
        });
        let constraints = [
            fixture.add_bound(term, KIND_GE, 0),
            fixture.add_bound(term, KIND_LE, 0),
            fixture.add_bound(3, KIND_GE, 1),
            fixture.add_bound(4, KIND_GE, 2),
        ];
        fixture.prepare();
        fixture.with_nla(|nla| Basics::basic_lemma(nla, true));
        assert_eq!(constraints, [0, 1, 2, 3]);
        assert_eq!(fixture.show_state(), "values 0,0,0,1,2,0 toRefine 3,4");
        assert_eq!(
            show_lemmas(&fixture.core),
            ["[1*v3+-1*v4 0 0] {0,1}", "[-1*v3+1*v4 0 0] {0,1}"]
        );
    }

    // Here x >= 2, y >= 3 and x*y = 1: the patcher is blocked, and the bounds conflict before the
    // check reaches nra. The expected result and lemma are the TS oracle's.
    #[test]
    fn refutes_the_check_before_nra() {
        let (mut fixture, _) = NlaFixture::mk_scenario(
            3,
            &[(2, &[0, 1])],
            &[
                (0, KIND_GE, 2),
                (1, KIND_GE, 3),
                (2, KIND_GE, 1),
                (2, KIND_LE, 1),
            ],
        );
        assert_eq!(fixture.with_nla(|nla| nla.check(2)), Ok(LBool::False));
        assert_eq!(show_lemmas(&fixture.core), ["[] {0,1,2,3}"]);
    }

    #[test]
    fn undoes_the_nra_model_and_the_divisions_on_pop() {
        let mut fixture = NlaFixture::new();
        for external in 0..4 {
            fixture.lra.add_var(external, true);
        }
        let division = Division {
            quotient: 0,
            dividend: 1,
            divisor: 2,
            remainder: 3,
        };
        fixture.with_nla(|nla| {
            Divisions::add_idivision(nla, division);
            nla.push();
            nla.set_use_nra_model(true);
            Divisions::add_idivision(nla, division);
            Divisions::add_bounded_division(nla, division);
            Divisions::add_divisibility(nla, division);
            assert_eq!(nla.divisions.idivisions.len(), 2);
            nla.pop(1);
            assert!(!nla.is_using_nra_model);
            assert_eq!(nla.divisions.idivisions, [division]);
            assert!(nla.divisions.bounded_divisions.is_empty());
            assert!(nla.divisions.divisibility.is_empty());
        });
    }
}
