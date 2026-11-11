//! Ported from Z3 (src/smt/theory_lra.cpp), MIT license, see z3-license.txt, through
//! `theory-lra-propagate.ts`. How theory_lra propagates: asserted bounds go to the lp solver, the
//! tableau is made feasible, and implied bounds and equalities of fixed columns come back as
//! literals and equalities.
//!
//! The bound propagator calls back into the theory while it holds the lp solver: `LraView` is that
//! side of the theory, the fields of the context and the theory that the callbacks read and write,
//! borrowed apart from the solver for the call. `add_eq` lives on it, as the final check's lemmas
//! call it too.

use prove_num::Rational;

use crate::core::ast::{AstManager, OP_ITE, OP_SUB, SORT_BOOL};
use crate::core::clause::BJustification;
use crate::core::context::{Context, NewEq, TrailClosure};
use crate::core::enode::{EnodeId, Enodes, EqJustification, Justification, Justifications};
use crate::core::literal::{Literal, negate};
use crate::core::theory_lra_bounds::{get_atom_literal, get_bound_kind};
use crate::core::theory_lra_state::{
    ApiBound, TermBound, TheoryClosure, TheoryLra, get_lra, get_lra_mut, set_at,
};
use crate::lp::bound_propagator::{BoundPropagator, BoundPropagatorHost, get_implied_kind};
use crate::lp::constraints::{ConstraintKind, KIND_GE, KIND_GT, KIND_LE, KIND_LT};
use crate::lp::core_solver::LP_INFEASIBLE;
use crate::lp::dependency::{Dependency, linearize, mk_join, mk_leaf};
use crate::lp::explanation::Explanation;
use crate::lp::lar_solver::LarSolver;
use crate::lp::lar_term::LarTerm;
use crate::util::error::SmtError;
use crate::util::hashtable::{ObjMap, get_identity_hash};
use crate::util::lbool::LBool;

const NULL_THEORY_VAR: i32 = -1;

/// The theory variable of a column, -1 for a column without one.
pub(crate) fn get_external_var(solver: &LarSolver<'_>, column: usize) -> i32 {
    solver.get_external(column) as i32
}

/// is_bound_implied: the literal of the bound that the implied bound makes true or false.
fn is_bound_implied(kind: ConstraintKind, value: &Rational, bound: &ApiBound) -> Option<Literal> {
    let literal = get_atom_literal(bound);
    let comparison = value.compare(&bound.value);
    let is_upper_kind = kind == KIND_LE || kind == KIND_LT;
    let is_lower_kind = kind == KIND_GE || kind == KIND_GT;
    if is_upper_kind && !bound.is_lower && comparison.is_le() {
        return Some(literal);
    }
    if is_lower_kind && bound.is_lower && comparison.is_ge() {
        return Some(literal);
    }
    if kind == KIND_LE && bound.is_lower && comparison.is_lt() {
        return Some(negate(literal));
    }
    if kind == KIND_LT && bound.is_lower && comparison.is_le() {
        return Some(negate(literal));
    }
    if kind == KIND_GE && !bound.is_lower && comparison.is_gt() {
        return Some(negate(literal));
    }
    if kind == KIND_GT && !bound.is_lower && comparison.is_ge() {
        return Some(negate(literal));
    }
    None
}

/// The theory as the bound propagator and nla's equalities see it.
pub(crate) struct LraView<'a> {
    m: &'a AstManager,
    enodes: &'a Enodes,
    assignment: &'a [LBool],
    is_inconsistent: bool,
    var_enodes: &'a [EnodeId],
    unassigned_bounds: &'a [i32],
    bounds: &'a [Vec<usize>],
    api_bounds: &'a [ApiBound],
    constraint_sources: &'a [Option<Literal>],
    core_literals: &'a mut Vec<Literal>,
    justification_arena: &'a mut Justifications,
    eq_propagation_queue: &'a mut Vec<NewEq>,
}

impl LraView<'_> {
    fn get_enode(&self, th_var: i32) -> EnodeId {
        self.var_enodes[th_var as usize]
    }

    fn is_int_var(&self, th_var: i32) -> bool {
        self.m.is_int(self.enodes.get(self.get_enode(th_var)).owner)
    }

    fn is_equal_var(&self, first: i32, second: i32) -> bool {
        self.enodes.get(self.get_enode(first)).root == self.enodes.get(self.get_enode(second)).root
    }

    fn set_evidence(&mut self, constraint: usize) {
        if let Some(Some(literal)) = self.constraint_sources.get(constraint) {
            self.core_literals.push(*literal);
        }
    }

    fn assign_eq(&mut self, first: i32, second: i32) {
        let justification = self.justification_arena.mk(Justification::Theory {
            literals: self.core_literals.clone(),
            eqs: Vec::new(),
        });
        self.eq_propagation_queue.push(NewEq {
            lhs: self.get_enode(first),
            rhs: self.get_enode(second),
            justification: EqJustification::Justification { justification },
        });
    }

    /// add_eq: an equality that the lp solver implies, with its explanation.
    pub(crate) fn add_eq(
        &mut self,
        solver: &LarSolver<'_>,
        first: usize,
        second: usize,
        explanation: &Explanation,
        is_fixed: bool,
    ) -> bool {
        if self.is_inconsistent {
            return false;
        }
        let v1 = get_external_var(solver, first);
        let v2 = get_external_var(solver, second);
        if v1 == NULL_THEORY_VAR || v2 == NULL_THEORY_VAR {
            return false;
        }
        if self.is_equal_var(v1, v2) || self.is_int_var(v1) != self.is_int_var(v2) {
            return false;
        }
        let e1 = self.enodes.get(self.get_enode(v1)).owner;
        let e2 = self.enodes.get(self.get_enode(v2)).owner;
        if !is_fixed
            && !self.m.is_numeral(e1)
            && !self.m.is_numeral(e2)
            && (self.m.get_op(e1) == OP_ITE || self.m.get_op(e2) == OP_ITE)
        {
            return false;
        }
        self.core_literals.clear();
        for constraint in explanation.iter() {
            self.set_evidence(constraint);
        }
        self.assign_eq(v1, v2);
        true
    }
}

impl BoundPropagatorHost for LraView<'_> {
    fn column_is_interesting(&mut self, solver: &LarSolver<'_>, column: usize) -> bool {
        let th_var = get_external_var(solver, column);
        th_var != NULL_THEORY_VAR
            && (th_var as usize) < self.unassigned_bounds.len()
            && self.unassigned_bounds[th_var as usize] > 0
    }

    fn bound_is_interesting(
        &mut self,
        solver: &LarSolver<'_>,
        column: usize,
        kind: ConstraintKind,
        value: &Rational,
    ) -> bool {
        let th_var = get_external_var(solver, column);
        if th_var == NULL_THEORY_VAR || th_var as usize >= self.bounds.len() {
            return false;
        }
        if self.unassigned_bounds[th_var as usize] == 0 {
            return false;
        }
        self.bounds[th_var as usize].iter().any(|bound| {
            let bound = &self.api_bounds[*bound];
            self.assignment[get_atom_literal(bound) as usize] == LBool::Undef
                && is_bound_implied(kind, value, bound).is_some()
        })
    }

    fn is_equal(&mut self, _solver: &LarSolver<'_>, first: usize, second: usize) -> bool {
        self.is_equal_var(first as i32, second as i32)
    }

    fn add_eq(
        &mut self,
        solver: &LarSolver<'_>,
        first: usize,
        second: usize,
        explanation: &Explanation,
        is_fixed: bool,
    ) -> bool {
        LraView::add_eq(self, solver, first, second, explanation, is_fixed)
    }
}

/// term2coeffs: the coefficients of the theory variables of a term, with term columns expanded,
/// in the slot order of Z3's u_map. A column without a theory variable has the variable -1, which
/// no caller can use, so it is refused.
pub(crate) fn get_term_coeffs(
    solver: &LarSolver<'_>,
    term: &LarTerm,
) -> Result<Vec<(i32, Rational)>, SmtError> {
    fn visit(
        solver: &LarSolver<'_>,
        current: &LarTerm,
        coeff: &Rational,
        coeffs: &mut ObjMap<Rational>,
    ) -> Result<(), SmtError> {
        for (column, entry) in current.iter() {
            if solver.has_term(column) {
                visit(solver, solver.get_term(column)?, &coeff.mul(entry), coeffs)?;
                continue;
            }
            let th_var = get_external_var(solver, column) as u32;
            let hash = get_identity_hash(th_var);
            let sum = coeffs
                .get(th_var, hash)
                .cloned()
                .unwrap_or_else(Rational::zero)
                .add(&entry.mul(coeff));
            if coeffs.contains_key(th_var, hash) {
                coeffs.replace(th_var, hash, sum);
            } else {
                coeffs.insert(th_var, hash, sum);
            }
        }
        Ok(())
    }
    let mut coeffs = ObjMap::new();
    visit(solver, term, &Rational::one(), &mut coeffs)?;
    let result: Vec<(i32, Rational)> = coeffs
        .iter()
        .map(|(th_var, coeff)| (th_var as i32, coeff.clone()))
        .collect();
    if result.iter().any(|entry| entry.0 < 0) {
        return Err(SmtError::Invariant(
            "a term over a column without a theory variable".into(),
        ));
    }
    Ok(result)
}

impl Context {
    /// The bound propagator's view of the theory, with the lp solver and the propagator apart.
    pub(crate) fn lra_split_view(
        &mut self,
    ) -> (&mut LarSolver<'static>, &mut BoundPropagator, LraView<'_>) {
        let is_inconsistent = self.is_inconsistent();
        let theory = get_lra_mut(&mut self.theory);
        let TheoryLra {
            solver,
            bp,
            var_enodes,
            unassigned_bounds,
            bounds,
            api_bounds,
            constraint_sources,
            core_literals,
            ..
        } = theory;
        (
            solver,
            bp,
            LraView {
                m: &self.m,
                enodes: &self.enode_arena,
                assignment: &self.assignment,
                is_inconsistent,
                var_enodes,
                unassigned_bounds,
                bounds,
                api_bounds,
                constraint_sources,
                core_literals,
                justification_arena: &mut self.justification_arena,
                eq_propagation_queue: &mut self.eq_propagation_queue,
            },
        )
    }

    pub fn theory_can_propagate(&self) -> bool {
        let Some(theory) = self.theory.as_ref() else {
            return false;
        };
        theory.asserted_atoms.len() > theory.asserted_qhead
            || theory.is_new_def
            || theory.solver.columns_with_changed_bounds.size() > 0
            || theory.delay_ineqs_qhead < theory.delay_ineqs.len()
    }

    pub fn theory_propagate(&mut self) -> Result<(), SmtError> {
        if self.theory.is_none() {
            return Ok(());
        }
        self.lra_propagate_core()?;
        Ok(())
    }

    /// propagate_core: whether there was anything to propagate.
    pub(crate) fn lra_propagate_core(&mut self) -> Result<bool, SmtError> {
        self.lra_mut().is_model_initialized = false;
        self.lra_flush_bound_axioms()?;
        if self.is_inconsistent() {
            return Ok(true);
        }
        if !self.theory_can_propagate() {
            return Ok(false);
        }
        while self.lra().delay_ineqs_qhead < self.lra().delay_ineqs.len()
            && !self.is_inconsistent()
            && !self.check_canceled()
        {
            let saved = self.lra().delay_ineqs_qhead;
            self.push_trail(TrailClosure::Theory(TheoryClosure::DelayIneqsQhead {
                saved,
            }));
            let atom = self.lra().delay_ineqs[saved];
            let left = self.m.get_arg(atom, 0);
            let right = self.m.get_arg(atom, 1);
            let sort = self.m.sorts[left as usize];
            let zero = self.m.mk_numeral_of_sort(&Rational::zero(), sort);
            let difference = self.m.mk_app(OP_SUB, &[left, right], sort)?;
            let op = self.m.get_op(atom);
            let normalized = self.m.mk_app(op, &[difference, zero], SORT_BOOL)?;
            let first = self.lra_mk_literal(atom)?;
            let second = self.lra_mk_literal(normalized)?;
            self.lra_mk_axiom(&[negate(first), second])?;
            self.lra_mk_axiom(&[first, negate(second)])?;
            self.lra_mut().delay_ineqs_qhead += 1;
        }
        self.lra_mut().is_new_def = false;
        while self.lra().asserted_qhead < self.lra().asserted_atoms.len()
            && !self.is_inconsistent()
            && !self.check_canceled()
        {
            let theory = self.lra();
            let atom = theory.asserted_atoms[theory.asserted_qhead];
            let bound = theory
                .bool_var_to_bound
                .get(atom.bool_var as usize)
                .copied()
                .flatten();
            if let Some(bound) = bound
                && !self.lra_assert_bound(atom.is_true, bound)?
            {
                self.lra_set_infeasibility_conflict();
                return Ok(true);
            }
            self.lra_mut().asserted_qhead += 1;
        }
        if self.is_inconsistent() {
            return Ok(true);
        }
        let status = self.lra_make_feasible();
        if self.check_canceled() {
            return Ok(true);
        }
        if status == LBool::False {
            self.lra_set_infeasibility_conflict();
        } else if status == LBool::True {
            self.lra_propagate_nla(true)?;
            self.lra_propagate_bounds_with_lp_solver()?;
        }
        Ok(true)
    }

    pub(crate) fn lra_make_feasible(&mut self) -> LBool {
        let solver = &mut self.lra_mut().solver;
        let status = solver.find_feasible_solution();
        if solver.is_feasible() {
            return LBool::True;
        }
        if status == LP_INFEASIBLE {
            LBool::False
        } else {
            LBool::Undef
        }
    }

    fn lra_assert_bound(&mut self, is_true: bool, bound: usize) -> Result<bool, SmtError> {
        let theory = self.lra_mut();
        let api_bound = theory.api_bounds[bound].clone();
        let solver = &mut theory.solver;
        let constraint = if is_true {
            api_bound.constraint_true
        } else {
            api_bound.constraint_false
        };
        if solver.constraint_is_redundant(constraint) {
            return Ok(solver.status != LP_INFEASIBLE);
        }
        solver.activate(constraint);
        if solver.status == LP_INFEASIBLE {
            return Ok(false);
        }
        let kind = get_bound_kind(&api_bound, is_true);
        let value = if is_true {
            api_bound.value.clone()
        } else if api_bound.is_lower {
            api_bound.value.sub(&Rational::one())
        } else {
            api_bound.value.add(&Rational::one())
        };
        if api_bound.is_int || is_true {
            self.lra_propagate_eqs(api_bound.column, constraint, kind, &api_bound, &value)?;
        }
        Ok(true)
    }

    /// propagate_eqs: a bound that fixes a column, with the opposite bound of the same value.
    fn lra_propagate_eqs(
        &mut self,
        column: usize,
        constraint: usize,
        kind: ConstraintKind,
        bound: &ApiBound,
        value: &Rational,
    ) -> Result<(), SmtError> {
        let is_lower = kind == KIND_GE;
        if kind != KIND_GE && kind != KIND_LE {
            return Ok(());
        }
        if !self.lra_set_term_bound(column, constraint, value, is_lower) {
            return Ok(());
        }
        let Some(opposite) = self.lra_get_fixing_bound(column, value, !is_lower) else {
            return Ok(());
        };
        let dep = mk_join(&mk_leaf(constraint as u32), &opposite);
        self.lra_fixed_var_eh(bound.th_var, column, &dep, value)
    }

    /// set_bound: records the bound of a term column, or checks that a column has the bound.
    fn lra_set_term_bound(
        &mut self,
        column: usize,
        constraint: usize,
        value: &Rational,
        is_lower: bool,
    ) -> bool {
        let theory = self.lra_mut();
        if !theory.solver.has_term(column) {
            return theory
                .solver
                .get_bound(column, !is_lower)
                .is_some_and(|bound| !bound.is_strict && bound.value == *value);
        }
        let terms = if is_lower {
            &mut theory.lower_terms
        } else {
            &mut theory.upper_terms
        };
        let existing = terms.get(column).cloned().flatten();
        let is_replaced = existing.as_ref().is_none_or(|existing| {
            if is_lower {
                existing.value.compare(value).is_lt()
            } else {
                existing.value.compare(value).is_gt()
            }
        });
        if is_replaced {
            set_at(
                terms,
                column,
                Some(TermBound {
                    constraint,
                    value: value.clone(),
                }),
                None,
            );
            theory.term_bounds_trail.push(existing);
            self.push_trail(TrailClosure::Theory(TheoryClosure::TermBound {
                column,
                is_lower,
            }));
        }
        true
    }

    /// has_bound: the dependency of a bound of the column with the value, if it has one.
    fn lra_get_fixing_bound(
        &self,
        column: usize,
        value: &Rational,
        is_lower: bool,
    ) -> Option<Dependency> {
        let theory = self.lra();
        let solver = &theory.solver;
        if solver.has_term(column) {
            let th_var = get_external_var(solver, column);
            if th_var != NULL_THEORY_VAR {
                let expr = self.lra_get_expr(th_var);
                if self.m.is_numeral(expr) && self.m.get_rational_value(expr) == value {
                    return Some(None);
                }
            }
            let terms = if is_lower {
                &theory.lower_terms
            } else {
                &theory.upper_terms
            };
            let term_bound = terms.get(column)?.as_ref()?;
            if term_bound.value != *value {
                return None;
            }
            return Some(mk_leaf(term_bound.constraint as u32));
        }
        let bound = solver.get_bound(column, !is_lower)?;
        if bound.value != *value || bound.is_strict {
            return None;
        }
        Some(bound.dep)
    }

    pub(crate) fn lra_is_equal(&self, first: i32, second: i32) -> bool {
        self.root(self.theory_get_enode(first)) == self.root(self.theory_get_enode(second))
    }

    /// report_equality_of_fixed_vars: two columns fixed to the same value are equal.
    pub(crate) fn lra_report_equality_of_fixed_vars(
        &mut self,
        first: usize,
        second: usize,
    ) -> Result<(), SmtError> {
        let solver = &self.lra().solver;
        let v1 = get_external_var(solver, first);
        let v2 = get_external_var(solver, second);
        // Z3 assumes both columns have theory variables, but a cut column has none.
        if v1 == NULL_THEORY_VAR || v2 == NULL_THEORY_VAR {
            return Ok(());
        }
        if self.lra_is_equal(v1, v2) || self.lra_is_int_var(v1) != self.lra_is_int_var(v2) {
            return Ok(());
        }
        let value = Rational::zero();
        let deps = [
            self.lra_get_fixing_bound(first, &value, true),
            self.lra_get_fixing_bound(first, &value, false),
            self.lra_get_fixing_bound(second, &value, true),
            self.lra_get_fixing_bound(second, &value, false),
        ];
        if deps.iter().any(Option::is_none) {
            return Ok(());
        }
        self.lra_reset_evidence();
        for dep in deps.iter().flatten() {
            self.lra_set_evidence_of_dep(dep);
        }
        self.lra_assign_eq(v1, v2);
        Ok(())
    }

    /// fixed_var_eh: a column fixed to a value is equal to an offset term, or to the variable of
    /// the numeral with that value.
    fn lra_fixed_var_eh(
        &mut self,
        th_var: i32,
        column: usize,
        dep: &Dependency,
        value: &Rational,
    ) -> Result<(), SmtError> {
        if self.lra_propagate_offset_eq(column, dep, value)? {
            return Ok(());
        }
        let is_int = self.lra_is_int_var(th_var);
        let theory = self.lra();
        let other = match theory.value2var.get(&(is_int, value.clone())) {
            Some(other) => *other,
            None if value.is_zero() => get_external_var(
                &theory.solver,
                if is_int {
                    theory.zero_var
                } else {
                    theory.real_zero_var
                },
            ),
            None if *value == Rational::one() => get_external_var(
                &theory.solver,
                if is_int {
                    theory.one_var
                } else {
                    theory.real_one_var
                },
            ),
            None => return Ok(()),
        };
        if self.lra_is_int_var(other) != is_int || self.lra_is_equal(th_var, other) {
            return Ok(());
        }
        self.lra_reset_evidence();
        self.lra_set_evidence_of_dep(dep);
        self.lra_assign_eq(th_var, other);
        Ok(())
    }

    /// propagate_offset_eq: x - y fixed to 0 makes x and y equal.
    fn lra_propagate_offset_eq(
        &mut self,
        column: usize,
        dep: &Dependency,
        value: &Rational,
    ) -> Result<bool, SmtError> {
        let solver = &self.lra().solver;
        if !value.is_zero() || !solver.has_term(column) {
            return Ok(false);
        }
        let coeffs = get_term_coeffs(solver, solver.get_term(column)?)?;
        if coeffs.len() != 2 {
            return Ok(false);
        }
        let first = &coeffs[0];
        let second = &coeffs[1];
        if !first.1.add(&second.1).is_zero() || first.0 == second.0 {
            return Ok(false);
        }
        if self.lra_is_equal(first.0, second.0) {
            return Ok(false);
        }
        if self.lra_is_int_var(first.0) != self.lra_is_int_var(second.0) {
            return Ok(false);
        }
        self.lra_reset_evidence();
        self.lra_set_evidence_of_dep(dep);
        self.lra_assign_eq(first.0, second.0);
        Ok(true)
    }

    fn lra_assign_eq(&mut self, first: i32, second: i32) {
        let (_, _, mut view) = self.lra_split_view();
        view.assign_eq(first, second);
    }

    fn lra_propagate_bounds_with_lp_solver(&mut self) -> Result<(), SmtError> {
        let (solver, bp, mut view) = self.lra_split_view();
        bp.init();
        bp.propagate_bounds_for_touched_rows(solver, &mut view);
        if self.check_canceled() {
            return Ok(());
        }
        if self.lra().solver.status == LP_INFEASIBLE {
            self.lra_set_infeasibility_conflict();
            return Ok(());
        }
        for index in 0..self.lra().bp.ibounds.len() {
            if self.is_inconsistent() {
                break;
            }
            self.lra_propagate_lp_solver_bound(index);
        }
        Ok(())
    }

    /// The implied bound at index in the propagator's list.
    fn lra_propagate_lp_solver_bound(&mut self, index: usize) {
        let theory = self.lra();
        let implied = &theory.bp.ibounds[index];
        let th_var = get_external_var(&theory.solver, implied.column);
        if th_var == NULL_THEORY_VAR || theory.unassigned_bounds[th_var as usize] == 0 {
            return;
        }
        let kind = get_implied_kind(implied);
        let implied_bound = implied.bound.clone();
        let mut is_first = true;
        for position in 0..self.lra().bounds[th_var as usize].len() {
            let theory = self.lra();
            let bound = &theory.api_bounds[theory.bounds[th_var as usize][position]];
            if self.get_assignment(get_atom_literal(bound)) != LBool::Undef {
                continue;
            }
            let Some(literal) = is_bound_implied(kind, &implied_bound, bound) else {
                continue;
            };
            if is_first {
                is_first = false;
                let entries = theory.bp.ibounds[index].explain(&theory.solver);
                let theory = self.lra_mut();
                theory.core_literals = Vec::new();
                theory.explanation.clear();
                for entry in entries {
                    for constraint in linearize(&[entry.1]) {
                        let constraint = constraint as usize;
                        if let Some(Some(literal)) = theory.constraint_sources.get(constraint) {
                            theory.core_literals.push(*literal);
                        }
                        theory.explanation.add_pair(constraint, entry.0.clone());
                    }
                }
            }
            let justification = self.justification_arena.mk(Justification::Theory {
                literals: self.lra().core_literals.clone(),
                eqs: Vec::new(),
            });
            self.assign(literal, BJustification::Justification(justification), false);
        }
    }

    pub(crate) fn lra_reset_evidence(&mut self) {
        self.lra_mut().core_literals = Vec::new();
    }

    fn lra_set_evidence_of_dep(&mut self, dep: &Dependency) {
        for constraint in linearize(std::slice::from_ref(dep)) {
            self.lra_set_evidence(constraint as usize);
        }
    }

    pub(crate) fn lra_set_evidence(&mut self, constraint: usize) {
        let theory = self.lra_mut();
        if let Some(Some(literal)) = theory.constraint_sources.get(constraint) {
            theory.core_literals.push(*literal);
        }
    }

    pub(crate) fn lra_set_infeasibility_conflict(&mut self) {
        let theory = self.lra_mut();
        theory
            .solver
            .get_infeasibility_explanation(&mut theory.explanation);
        self.lra_set_conflict();
    }

    pub(crate) fn lra_set_conflict(&mut self) {
        let theory = get_lra_mut(&mut self.theory);
        theory.core_literals = Vec::new();
        theory.num_conflicts += 1;
        let constraints: Vec<usize> = theory.explanation.iter().collect();
        for constraint in constraints {
            self.lra_set_evidence(constraint);
        }
        let justification = self.justification_arena.mk(Justification::Theory {
            literals: get_lra(&self.theory).core_literals.clone(),
            eqs: Vec::new(),
        });
        self.set_conflict(BJustification::Justification(justification), None);
    }
}
