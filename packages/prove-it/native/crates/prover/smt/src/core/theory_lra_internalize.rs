//! Ported from Z3 (src/smt/theory_lra.cpp), MIT license, see z3-license.txt, through
//! `theory-lra-internalize.ts`. How theory_lra internalizes terms: a term becomes a column of the
//! lp solver, a linear sum becomes a term column, nonlinear products and divisions go to nla, and
//! numerals are fixed columns.
//!
//! The terms of a nesting depth (`m_internalize_states`) are reached by their depth, since a
//! nested internalization may add depths while one is in use.

use std::collections::HashMap;

use prove_num::{Int, Rational};

use crate::core::ast::{
    Expr, FAMILY_ARITH, OP_ADD, OP_DIV, OP_DIV0, OP_IDIV, OP_IDIV0, OP_MOD, OP_MOD0, OP_MUL,
    OP_NUM, OP_SUB, OP_TO_INT, OP_TO_REAL, OP_UMINUS, SORT_INT, SORT_REAL,
};
use crate::core::clause::BJustification;
use crate::core::context::{Context, TrailClosure};
use crate::core::enode::EnodeId;
use crate::core::literal::get_var;
use crate::core::ref_vector::RefVector;
use crate::core::relevancy::RelevancyPropagator;
use crate::core::theory_lra_state::{TheoryClosure, get_lra_mut, set_at};
use crate::lp::constraints::{ConstraintKind, KIND_GE, KIND_LE};
use crate::lp::lar_solver::NULL_LPVAR;
use crate::lp::nla_core::{Nla, NlaCore};
use crate::lp::nla_divisions::{Division, Divisions};
use crate::util::error::SmtError;

/// The theory variables of a linear sum and their coefficients.
struct LinearizedSum {
    vars: Vec<i32>,
    coeffs: Vec<Rational>,
}

/// Which of nla's three lists of divisions a division goes to.
#[derive(Clone, Copy)]
enum DivisionKind {
    Idivision,
    Bounded,
    Divisibility,
}

impl Context {
    /// init: the constants 1 and 0, integer and then real, each in a scope of its own. The context
    /// runs it once, when it registers the theory.
    pub fn theory_init(&mut self) -> Result<(), SmtError> {
        if self.theory.is_none() {
            return Err(SmtError::Invariant("the theory is not set up".into()));
        }
        let one = self.m.mk_numeral(&Int::one());
        let one_var = self.lra_add_const(one)?;
        self.lra_mut().one_var = one_var;
        let real_one = self.m.mk_real_numeral(&Rational::one());
        let real_one_var = self.lra_add_const(real_one)?;
        self.lra_mut().real_one_var = real_one_var;
        let zero = self.m.mk_numeral(&Int::zero());
        let zero_var = self.lra_add_const(zero)?;
        self.lra_mut().zero_var = zero_var;
        let real_zero = self.m.mk_real_numeral(&Rational::zero());
        let real_zero_var = self.lra_add_const(real_zero)?;
        self.lra_mut().real_zero_var = real_zero_var;
        Ok(())
    }

    fn lra_add_const(&mut self, expr: Expr) -> Result<usize, SmtError> {
        let value = self.m.get_rational_value(expr).clone();
        self.lra_mk_enode(expr)?;
        let th_var = self.lra_mk_var(expr)?;
        let is_int = self.lra_is_int_expr(expr);
        let solver = &mut self.lra_mut().solver;
        let column = solver.add_var(th_var as usize, is_int);
        solver.push();
        self.lra_add_def_constraint_and_equality(column, KIND_GE, &value)?;
        self.lra_add_def_constraint_and_equality(column, KIND_LE, &value)?;
        Ok(column)
    }

    pub(crate) fn lra_is_attached_to_var(&self, node: EnodeId) -> bool {
        let th_var = self.node(node).th_var;
        th_var >= 0 && self.lra().var_enodes.get(th_var as usize) == Some(&node)
    }

    pub fn theory_is_attached_to_var(&self, node: EnodeId) -> bool {
        self.theory.is_some() && self.lra_is_attached_to_var(node)
    }

    fn lra_mk_var(&mut self, expr: Expr) -> Result<i32, SmtError> {
        let node = self.lra_get_internalized_enode(expr)?;
        if self.lra_is_attached_to_var(node) {
            return Ok(self.node(node).th_var);
        }
        let theory = self.lra_mut();
        let th_var = theory.var_enodes.len();
        theory.var_enodes.push(node);
        while theory.bounds.len() <= th_var {
            theory.bounds.push(Vec::new());
            theory.unassigned_bounds.push(0);
        }
        self.attach_th_var(node, th_var as i32)?;
        Ok(th_var as i32)
    }

    pub(crate) fn lra_register_var(&mut self, th_var: i32) -> usize {
        let is_int = self.lra_is_int_var(th_var);
        let solver = &mut self.lra_mut().solver;
        let column = solver.external_to_local_column(th_var as usize);
        if column != NULL_LPVAR {
            column
        } else {
            solver.add_var(th_var as usize, is_int)
        }
    }

    /// mk_enode: the arguments, which become relevant, then the term.
    pub(crate) fn lra_mk_enode(&mut self, expr: Expr) -> Result<(), SmtError> {
        for index in 0..self.m.get_num_args(expr) {
            let arg = self.m.get_arg(expr, index);
            if self.is_e_internalized(arg) {
                continue;
            }
            self.internalize(arg, false)?;
            self.mark_as_relevant(arg)?;
        }
        if self.is_e_internalized(expr) {
            return Ok(());
        }
        let op = self.m.get_op(expr);
        let is_arith = self.m.get_family(expr) == FAMILY_ARITH;
        self.mk_enode(
            expr,
            false,
            false,
            !(is_arith && (op == OP_ADD || op == OP_MUL)),
        )?;
        Ok(())
    }

    fn lra_internalize_args(&mut self, expr: Expr) -> Result<(), SmtError> {
        for index in 0..self.m.get_num_args(expr) {
            let arg = self.m.get_arg(expr, index);
            if !self.is_e_internalized(arg) {
                self.internalize(arg, false)?;
            }
        }
        Ok(())
    }

    /// found_unsupported: the list of unsupported terms is on the trail.
    pub(crate) fn lra_found_unsupported(&mut self, expr: Expr) {
        self.lra_mut().unsupported_terms.push(expr);
        self.push_trail(TrailClosure::Theory(TheoryClosure::PopUnsupportedTerm));
    }

    /// found_underspecified: a division by a term or by zero equals the division by zero it stands
    /// for, which the model interprets freely.
    fn lra_found_underspecified(&mut self, expr: Expr) -> Result<(), SmtError> {
        self.lra_mut().underspecified_terms.push(expr);
        self.push_trail(TrailClosure::Theory(TheoryClosure::PopUnderspecifiedTerm));
        let op = self.m.get_op(expr);
        let zero = self.m.mk_numeral(&Int::zero());
        let dividend = if op == OP_MOD {
            self.m
                .mk_app(OP_MOD, &[self.m.get_arg(expr, 0), zero], SORT_INT)?
        } else {
            expr
        };
        let by_zero = if op == OP_DIV {
            let args = self.m.get_args(expr);
            self.m.mk_app(OP_DIV0, &args, SORT_REAL)?
        } else if op == OP_IDIV {
            let args = self.m.get_args(expr);
            self.m.mk_app(OP_IDIV0, &args, SORT_INT)?
        } else {
            self.m
                .mk_app(OP_MOD0, &[self.m.get_arg(expr, 0), zero], SORT_INT)?
        };
        let literal = self.lra_mk_eq(by_zero, dividend)?;
        if self.relevancy.is_enabled {
            let target = self.bool_var2expr[get_var(literal) as usize];
            RelevancyPropagator::add_dependency(self, dividend, target)?;
        }
        self.assign(literal, BJustification::Decision, false);
        Ok(())
    }

    fn lra_register_fixed_var(&mut self, th_var: i32, value: &Rational) {
        let key = (self.lra_is_int_var(th_var), value.clone());
        let theory = self.lra_mut();
        if theory.value2var.contains_key(&key) {
            return;
        }
        theory.value2var.insert(key.clone(), th_var);
        theory.value2var_trail.push(key);
        self.push_trail(TrailClosure::Theory(TheoryClosure::DeleteValue2Var));
    }

    fn lra_internalize_numeral(&mut self, expr: Expr, value: &Rational) -> Result<i32, SmtError> {
        if !self.is_e_internalized(expr) {
            self.lra_mk_enode(expr)?;
        }
        let th_var = self.lra_mk_var(expr)?;
        if self.lra().solver.external_to_local_column(th_var as usize) == NULL_LPVAR {
            let is_int = self.lra_is_int_expr(expr);
            let column = self.lra_mut().solver.add_var(th_var as usize, is_int);
            self.lra_add_def_constraint_and_equality(column, KIND_GE, value)?;
            self.lra_add_def_constraint_and_equality(column, KIND_LE, value)?;
            self.lra_register_fixed_var(th_var, value);
        }
        Ok(th_var)
    }

    /// internalize_mul: a product of terms is a variable whose arguments have variables.
    fn lra_internalize_mul(&mut self, expr: Expr) -> Result<i32, SmtError> {
        self.lra_internalize_args(expr)?;
        let has_var = self.is_e_internalized(expr) && self.lra_is_attached_expr(expr);
        self.lra_mk_enode(expr)?;
        let th_var = self.lra_mk_var(expr)?;
        if !has_var {
            let mut vars = Vec::new();
            for index in 0..self.m.get_num_args(expr) {
                let arg = self.m.get_arg(expr, index);
                self.lra_internalize_term_core(arg)?;
                let arg_var = self.lra_mk_var(arg)?;
                vars.push(self.lra_register_var(arg_var));
            }
            self.lra_mut().solver.register_existing_terms();
            self.lra_ensure_nla();
            let column = self.lra_register_var(th_var);
            self.lra_with_nla(|nla| nla.add_monic(column, &vars));
        }
        Ok(th_var)
    }

    /// ensure_nla: the nonlinear solver, made on the first nonlinear term, in the current scopes.
    /// Its is_relevant is built per call (lra_with_nla).
    fn lra_ensure_nla(&mut self) {
        let theory = self.lra_mut();
        if theory.nla.is_some() {
            return;
        }
        theory.nla = Some(NlaCore::new(&mut theory.solver));
        let num_scopes = theory.scopes.len();
        for _ in 0..num_scopes {
            self.lra_with_nla(|nla| nla.push());
        }
    }

    /// Runs body on the view of nla, if the theory made it, with is_relevant answered from the
    /// relevancy of each column's term as it is now: nla reads the relevancy of the columns of
    /// theory variables and changes neither them nor the relevancy.
    pub(crate) fn lra_with_nla<T>(
        &mut self,
        body: impl FnOnce(&mut Nla<'_, 'static>) -> T,
    ) -> Option<T> {
        let theory = get_lra_mut(&mut self.theory);
        let core = theory.nla.as_mut()?;
        let solver = &mut theory.solver;
        let relevant: Vec<bool> = (0..solver.get_column_count())
            .map(|column| {
                theory
                    .var_enodes
                    .get(solver.get_external(column))
                    .is_some_and(|node| {
                        self.relevancy
                            .is_relevant(self.enode_arena.get(*node).owner)
                    })
            })
            .collect();
        let is_relevant = |lp_var: usize| relevant.get(lp_var).copied().unwrap_or(false);
        let mut nla = Nla {
            core,
            lra: solver,
            limit: &self.m.limit,
            is_relevant: &is_relevant,
        };
        Some(body(&mut nla))
    }

    /// The columns of a quotient, its dividend and divisor, and the remainder, internalized in
    /// that order.
    fn lra_register_division(
        &mut self,
        quotient: Expr,
        remainder: Expr,
    ) -> Result<Division, SmtError> {
        let quotient_column = self.lra_register_expr(quotient)?;
        let dividend_column = self.lra_register_expr(self.m.get_arg(quotient, 0))?;
        let divisor_column = self.lra_register_expr(self.m.get_arg(quotient, 1))?;
        let remainder_column = self.lra_register_expr(remainder)?;
        Ok(Division {
            quotient: quotient_column,
            dividend: dividend_column,
            divisor: divisor_column,
            remainder: remainder_column,
        })
    }

    fn lra_register_expr(&mut self, expr: Expr) -> Result<usize, SmtError> {
        self.lra_internalize_term_core(expr)?;
        let th_var = self.lra_mk_var(expr)?;
        Ok(self.lra_register_var(th_var))
    }

    fn lra_add_division(&mut self, kind: DivisionKind, division: Division) {
        self.lra_with_nla(|nla| match kind {
            DivisionKind::Idivision => Divisions::add_idivision(nla, division),
            DivisionKind::Bounded => Divisions::add_bounded_division(nla, division),
            DivisionKind::Divisibility => Divisions::add_divisibility(nla, division),
        });
    }

    fn lra_is_nonzero_numeral(&self, expr: Expr) -> bool {
        self.m.is_numeral(expr) && !self.m.get_rational_value(expr).is_zero()
    }

    /// arith_util::is_bounded: a numeral, a mod by a numeral, or a div by a numeral of a bounded
    /// term.
    fn lra_is_bounded(&self, expr: Expr) -> bool {
        let mut current = expr;
        loop {
            let op = self.m.get_op(current);
            if op == OP_IDIV && self.m.is_numeral(self.m.get_arg(current, 1)) {
                current = self.m.get_arg(current, 0);
                continue;
            }
            return (op == OP_MOD && self.m.is_numeral(self.m.get_arg(current, 1)))
                || self.m.is_numeral(current);
        }
    }

    fn lra_is_attached_expr(&self, expr: Expr) -> bool {
        self.get_enode(expr)
            .is_some_and(|node| self.lra_is_attached_to_var(node))
    }

    /// scoped_internalize_state: the depth of the next terms, reset. The caller decrements the
    /// head.
    pub(crate) fn lra_push_internalize_state(&mut self) -> Result<usize, SmtError> {
        let theory = get_lra_mut(&mut self.theory);
        let depth = theory.internalize_head;
        if theory.internalize_states.len() <= depth {
            theory
                .internalize_states
                .resize_with(depth + 1, RefVector::new);
        }
        theory.internalize_head += 1;
        theory.internalize_states[depth].reset(&mut self.m)?;
        Ok(depth)
    }

    fn lra_terms_push(&mut self, depth: usize, expr: Expr) {
        let theory = get_lra_mut(&mut self.theory);
        theory.internalize_states[depth].push(&mut self.m, expr);
    }

    fn lra_terms_set(&mut self, depth: usize, index: usize, expr: Expr) -> Result<(), SmtError> {
        let theory = get_lra_mut(&mut self.theory);
        theory.internalize_states[depth].set(&mut self.m, index, expr)
    }

    fn lra_terms_pop(&mut self, depth: usize) -> Result<(), SmtError> {
        let theory = get_lra_mut(&mut self.theory);
        theory.internalize_states[depth].pop(&mut self.m)
    }

    fn lra_terms(&self, depth: usize) -> &[Expr] {
        &self.lra().internalize_states[depth].items
    }

    /// linearize: the theory variables of a weighted sum of terms, with their coefficients.
    fn lra_linearize(
        &mut self,
        depth: usize,
        mut coeffs: Vec<Rational>,
    ) -> Result<LinearizedSum, SmtError> {
        let mut vars: Vec<i32> = Vec::new();
        let mut to_ensure_enode: Vec<Expr> = Vec::new();
        let mut to_ensure_var: Vec<Expr> = Vec::new();
        let add_var = |vars: &mut Vec<i32>, coeffs: &mut Vec<Rational>, index: usize, th_var| {
            coeffs[vars.len()] = coeffs[index].clone();
            vars.push(th_var);
        };
        let mut index = 0;
        while index < self.lra_terms(depth).len() {
            let term = self.lra_terms(depth)[index];
            to_ensure_enode.push(term);
            let op = self.m.get_op(term);
            if op == OP_ADD {
                for arg_index in 0..self.m.get_num_args(term) {
                    let arg = self.m.get_arg(term, arg_index);
                    self.lra_terms_push(depth, arg);
                    coeffs.push(coeffs[index].clone());
                }
                let size = self.lra_terms(depth).len();
                if size != index + 1 {
                    let last = self.lra_terms(depth)[size - 1];
                    self.lra_terms_set(depth, index, last)?;
                    coeffs[index] = coeffs[coeffs.len() - 1].clone();
                    self.lra_terms_pop(depth)?;
                    coeffs.pop();
                }
            } else if op == OP_SUB {
                self.lra_terms_set(depth, index, self.m.get_arg(term, 0))?;
                for position in 1..self.m.get_num_args(term) {
                    self.lra_terms_push(depth, self.m.get_arg(term, position));
                    coeffs.push(coeffs[index].neg());
                }
            } else if op == OP_MUL
                && self.m.get_num_args(term) == 2
                && self.m.is_numeral(self.m.get_arg(term, 0))
            {
                coeffs[index] =
                    coeffs[index].mul(self.m.get_rational_value(self.m.get_arg(term, 0)));
                self.lra_terms_set(depth, index, self.m.get_arg(term, 1))?;
                to_ensure_enode.push(self.m.get_arg(term, 0));
            } else if op == OP_MUL
                && self.m.get_num_args(term) == 2
                && self.m.is_numeral(self.m.get_arg(term, 1))
            {
                coeffs[index] =
                    coeffs[index].mul(self.m.get_rational_value(self.m.get_arg(term, 1)));
                self.lra_terms_set(depth, index, self.m.get_arg(term, 0))?;
                to_ensure_enode.push(self.m.get_arg(term, 1));
            } else if op == OP_MUL {
                let th_var = self.lra_internalize_mul(term)?;
                add_var(&mut vars, &mut coeffs, index, th_var);
                index += 1;
            } else if op == OP_NUM {
                let value = self.m.get_rational_value(term).clone();
                let th_var = self.lra_internalize_numeral(term, &value)?;
                add_var(&mut vars, &mut coeffs, index, th_var);
                index += 1;
            } else if op == OP_UMINUS {
                coeffs[index] = coeffs[index].neg();
                self.lra_terms_set(depth, index, self.m.get_arg(term, 0))?;
            } else if op == OP_TO_REAL {
                let arg = self.m.get_arg(term, 0);
                self.lra_terms_set(depth, index, arg)?;
                if !self.is_e_internalized(term) {
                    self.lra_internalize_term_core(arg)?;
                    self.lra_mk_enode(term)?;
                    let term_var = self.lra_mk_var(term)?;
                    let column = self.lra_register_var(term_var);
                    let arg_var = self.lra_mk_var(arg)?;
                    let arg_column = self.lra_register_var(arg_var);
                    let theory = self.lra_mut();
                    for constraint in theory.solver.add_equality(column, arg_column) {
                        set_at(&mut theory.constraint_sources, constraint, None, None);
                    }
                }
            } else if self.m.get_family(term) == FAMILY_ARITH {
                let is_first = !self.is_e_internalized(term);
                self.lra_internalize_args(term)?;
                self.lra_mk_enode(term)?;
                let th_var = self.lra_mk_var(term)?;
                add_var(&mut vars, &mut coeffs, index, th_var);
                index += 1;
                if is_first {
                    self.lra_internalize_first_arith_term(term, op, &mut to_ensure_var)?;
                }
            } else {
                self.lra_internalize_args(term)?;
                let th_var = self.lra_mk_var(term)?;
                add_var(&mut vars, &mut coeffs, index, th_var);
                index += 1;
            }
        }
        for position in (0..to_ensure_enode.len()).rev() {
            self.lra_mk_enode(to_ensure_enode[position])?;
        }
        for position in (0..to_ensure_var.len()).rev() {
            self.lra_internalize_term_core(to_ensure_var[position])?;
        }
        coeffs.truncate(vars.len());
        Ok(LinearizedSum { vars, coeffs })
    }

    /// The divisions, the unsupported terms and the axioms of an arithmetic term that linearize
    /// meets first.
    fn lra_internalize_first_arith_term(
        &mut self,
        term: Expr,
        op: i32,
        to_ensure_var: &mut Vec<Expr>,
    ) -> Result<(), SmtError> {
        if op == OP_DIV {
            let arg = self.m.get_arg(term, 1);
            let divisor = self.rewriter.rewrite(&mut self.m, arg)?;
            if !self.lra_is_nonzero_numeral(divisor) {
                self.lra_found_underspecified(term)?;
            }
            for arg_index in 0..self.m.get_num_args(term) {
                to_ensure_var.push(self.m.get_arg(term, arg_index));
            }
        } else if op == OP_IDIV {
            if !self.lra_is_nonzero_numeral(self.m.get_arg(term, 1)) {
                self.lra_found_underspecified(term)?;
            }
            let args = self.m.get_args(term);
            let remainder = self.m.mk_app(OP_MOD, &args, SORT_INT)?;
            self.internalize(remainder, false)?;
            if self.relevancy.is_enabled {
                RelevancyPropagator::add_dependency(self, term, remainder)?;
            }
            if self.lra().nla.is_some() && !self.m.is_numeral(self.m.get_arg(term, 1)) {
                let division = self.lra_register_division(term, remainder)?;
                self.lra_add_division(DivisionKind::Idivision, division);
            }
            if self.m.is_numeral(self.m.get_arg(term, 1))
                && self.lra_is_bounded(self.m.get_arg(term, 0))
            {
                self.lra_ensure_nla();
                let division = self.lra_register_division(term, remainder)?;
                self.lra_add_division(DivisionKind::Bounded, division);
            }
        } else if op == OP_MOD {
            let is_nonzero_divisor = self.lra_is_nonzero_numeral(self.m.get_arg(term, 1));
            if !is_nonzero_divisor {
                self.lra_found_underspecified(term)?;
            }
            // Without relevancy, Z3 makes the axioms before it registers the division with nla.
            if !self.relevancy.is_enabled {
                self.lra_mk_idiv_mod_axioms(self.m.get_arg(term, 0), self.m.get_arg(term, 1))?;
            }
            if self.lra().nla.is_some() && is_nonzero_divisor {
                let args = self.m.get_args(term);
                let quotient = self.m.mk_app(OP_IDIV, &args, SORT_INT)?;
                self.internalize(quotient, false)?;
                let division = self.lra_register_division(quotient, term)?;
                self.lra_add_division(DivisionKind::Bounded, division);
            }
            if !self.m.is_numeral(self.m.get_arg(term, 1))
                && !self.lra_is_zero_numeral(self.m.get_arg(term, 0))
            {
                self.lra_ensure_nla();
                let args = self.m.get_args(term);
                let quotient = self.m.mk_app(OP_IDIV, &args, SORT_INT)?;
                self.internalize(quotient, false)?;
                let division = self.lra_register_division(quotient, term)?;
                self.lra_add_division(DivisionKind::Divisibility, division);
            }
        } else if op == OP_IDIV0 || op == OP_MOD0 {
            for arg_index in 0..self.m.get_num_args(term) {
                to_ensure_var.push(self.m.get_arg(term, arg_index));
            }
        } else if op != OP_TO_INT && op != OP_DIV0 {
            self.lra_found_unsupported(term);
            for arg_index in 0..self.m.get_num_args(term) {
                to_ensure_var.push(self.m.get_arg(term, arg_index));
            }
        }
        if !self.relevancy.is_enabled && op != OP_MOD {
            self.theory_relevant_eh(term)?;
        }
        Ok(())
    }

    /// init_left_side: the coefficients of the variables summed, in the order of the variables.
    fn lra_init_left_side(&mut self, vars: &[i32], coeffs: &[Rational]) -> Vec<(usize, Rational)> {
        let mut sums: HashMap<i32, Rational> = HashMap::new();
        for (index, th_var) in vars.iter().enumerate() {
            let sum = sums
                .get(th_var)
                .cloned()
                .unwrap_or_else(Rational::zero)
                .add(&coeffs[index]);
            sums.insert(*th_var, sum);
        }
        let mut left_side = Vec::new();
        for th_var in vars {
            let Some(sum) = sums.get(th_var).cloned() else {
                continue;
            };
            if sum.is_zero() {
                continue;
            }
            left_side.push((self.lra_register_var(*th_var), sum));
            sums.remove(th_var);
        }
        left_side
    }

    /// internalize_def: the variable of a term, with a column for its linear combination.
    pub(crate) fn lra_internalize_def(&mut self, expr: Expr) -> Result<i32, SmtError> {
        let depth = self.lra_push_internalize_state()?;
        self.lra_terms_push(depth, expr);
        let linearized = self.lra_linearize(depth, vec![Rational::one()])?;
        let th_var = self.lra_internalize_linearized_def(expr, &linearized)?;
        self.lra_mut().internalize_head -= 1;
        Ok(th_var)
    }

    /// internalize_linearized_def: term - v = 0, unless the term is its own variable.
    fn lra_internalize_linearized_def(
        &mut self,
        expr: Expr,
        linearized: &LinearizedSum,
    ) -> Result<i32, SmtError> {
        let th_var = self.lra_mk_var(expr)?;
        if linearized.vars.len() == 1
            && linearized.coeffs[0] == Rational::one()
            && th_var == linearized.vars[0]
        {
            return Ok(th_var);
        }
        let left_side = self.lra_init_left_side(&linearized.vars, &linearized.coeffs);
        if self.lra().solver.external_to_local_column(th_var as usize) != NULL_LPVAR {
            return Ok(th_var);
        }
        if left_side.is_empty() {
            let is_int = self.lra_is_int_expr(expr);
            let column = self.lra_mut().solver.add_var(th_var as usize, is_int);
            self.lra_add_def_constraint_and_equality(column, KIND_GE, &Rational::zero())?;
            self.lra_add_def_constraint_and_equality(column, KIND_LE, &Rational::zero())?;
        } else {
            self.lra_mut().solver.add_term(&left_side, th_var as usize);
        }
        Ok(th_var)
    }

    fn lra_internalize_term_core(&mut self, expr: Expr) -> Result<(), SmtError> {
        if self.m.get_family(expr) != FAMILY_ARITH && self.m.is_bool(expr) {
            return Ok(());
        }
        if self.is_e_internalized(expr) && self.lra_is_attached_expr(expr) {
            return Ok(());
        }
        self.lra_internalize_def(expr)?;
        Ok(())
    }

    /// Whether the theory took the term.
    pub fn theory_internalize_term(&mut self, expr: Expr) -> Result<bool, SmtError> {
        if self.theory.is_none() {
            return Err(SmtError::Invariant("the theory is not set up".into()));
        }
        self.lra_internalize_term_core(expr)?;
        Ok(true)
    }

    fn lra_add_def_constraint_and_equality(
        &mut self,
        column: usize,
        kind: ConstraintKind,
        bound: &Rational,
    ) -> Result<(), SmtError> {
        let theory = self.lra_mut();
        let index = theory.solver.mk_var_bound(column, kind, bound);
        let equal = theory.solver.activate_check_on_equal(index);
        set_at(&mut theory.constraint_sources, index, None, None);
        if equal != NULL_LPVAR {
            self.lra_report_equality_of_fixed_vars(column, equal)?;
        }
        self.lra_mut().is_new_def = true;
        Ok(())
    }
}
