//! Ported from Z3 (src/smt/theory_lra.cpp), MIT license, see z3-license.txt, through
//! `theory-lra-final-check.ts`. The final check of theory_lra: the integer solver and its branches
//! and cuts, then nla on nonlinear terms, whose lemmas become clauses.
//!
//! nla's lemmas, literals and equalities are read one at a time by index, as making their literals
//! internalizes atoms, which reaches the theory (and nla) again; nothing that runs then replaces
//! them, as only nla's own entry points do.

use prove_num::{Int, Rational, get_gcd, get_lcm};

use crate::core::ast::{
    Expr, OP_ADD, OP_GE, OP_LE, OP_MUL, OP_TO_REAL, SORT_BOOL, SORT_INT, SORT_REAL,
};
use crate::core::clause::BJustification;
use crate::core::context::{Context, FC_CONTINUE, FC_DONE, FC_GIVEUP};
use crate::core::enode::Justification;
use crate::core::literal::{Literal, get_var, negate};
use crate::core::theory_lra_propagate::get_term_coeffs;
use crate::core::theory_lra_state::get_lra_mut;
use crate::lp::constraints::{KIND_EQ, KIND_GE, KIND_GT, KIND_LT, KIND_NE};
use crate::lp::explanation::Explanation;
use crate::lp::int_solver::{Lia, LiaMove};
use crate::lp::lar_term::LarTerm;
use crate::lp::nla_core::NlaCore;
use crate::lp::nla_types::{Ineq, Lemma};
use crate::util::error::SmtError;
use crate::util::lbool::LBool;

impl Context {
    /// An `FC_*` status.
    pub fn theory_final_check_eh(&mut self, level: u32) -> Result<u8, SmtError> {
        if self.theory.is_none() {
            return Ok(FC_DONE);
        }
        if self.lra_propagate_core()? {
            return Ok(FC_CONTINUE);
        }
        self.lra_mut().is_model_initialized = false;
        self.lra_propagate_nla(false)?;
        let solver = &self.lra().solver;
        let status = if !solver.is_feasible() || solver.columns_with_changed_bounds.size() > 0 {
            self.lra_make_feasible()
        } else {
            LBool::True
        };
        if status == LBool::False {
            self.lra_set_infeasibility_conflict();
            return Ok(FC_CONTINUE);
        }
        if status == LBool::Undef {
            return Ok(if self.check_canceled() {
                FC_GIVEUP
            } else {
                FC_CONTINUE
            });
        }
        if !self.lra_is_lia_sat()? || !self.lra_check_idiv_bounds()? {
            return Ok(FC_CONTINUE);
        }
        let mut result = FC_DONE;
        let nla_status = self.lra_check_nla(level)?;
        if nla_status == FC_CONTINUE {
            return Ok(FC_CONTINUE);
        }
        // Nonlinear bound optimization may invalidate integer feasibility.
        let is_using_nra_model = self
            .lra()
            .nla
            .as_ref()
            .is_some_and(|nla| nla.is_using_nra_model);
        if nla_status == FC_DONE && !is_using_nra_model && self.lra().solver.has_inf_int() {
            return Ok(FC_CONTINUE);
        }
        if nla_status == FC_GIVEUP {
            result = FC_GIVEUP;
        }
        if self.lra_assume_eqs()? {
            return Ok(FC_CONTINUE);
        }
        if !self.lra().unsupported_terms.is_empty() {
            self.lra_init_variable_values();
        }
        // eval_unsupported gives up on every term but powers, which are not supported here.
        let is_unsupported = self
            .lra()
            .unsupported_terms
            .iter()
            .any(|term| self.is_relevant(*term));
        Ok(if is_unsupported { FC_GIVEUP } else { result })
    }

    /// check_nla: whether the values of the monomials agree with their factors', or the lemmas
    /// that refine them.
    fn lra_check_nla(&mut self, level: u32) -> Result<u8, SmtError> {
        if self.check_canceled() {
            return Ok(FC_GIVEUP);
        }
        if !self
            .lra_with_nla(|nla| nla.has_relevant_monomial())
            .unwrap_or(false)
        {
            return Ok(FC_DONE);
        }
        let status = self
            .lra_with_nla(|nla| nla.check(level))
            .unwrap_or(Ok(LBool::True))?;
        if status == LBool::False {
            self.lra_add_lemmas()?;
            return Ok(FC_CONTINUE);
        }
        Ok(if status == LBool::True {
            FC_DONE
        } else {
            FC_GIVEUP
        })
    }

    /// check_idiv_bounds: the lemmas of the bounded divisions.
    fn lra_check_idiv_bounds(&mut self) -> Result<bool, SmtError> {
        if self
            .lra_with_nla(|nla| nla.check_bounded_divisions())
            .is_none()
        {
            return Ok(true);
        }
        self.lra_add_lemmas()?;
        Ok(self
            .lra()
            .nla
            .as_ref()
            .is_none_or(|nla| nla.lemmas.is_empty()))
    }

    /// propagate_nla and incremental_propagate_nla: the bounds nla derives for monomials.
    pub(crate) fn lra_propagate_nla(&mut self, is_incremental: bool) -> Result<(), SmtError> {
        if self.lra().nla.is_none() {
            return Ok(());
        }
        self.lra_with_nla(|nla| {
            if is_incremental {
                nla.incremental_propagate()
            } else {
                nla.propagate()
            }
        });
        self.lra_add_lemmas()?;
        self.lra_mut().solver.collect_more_rows_for_lp_propagation();
        Ok(())
    }

    fn lra_add_lemmas(&mut self) -> Result<(), SmtError> {
        let is_check_feasible = self
            .lra()
            .nla
            .as_ref()
            .is_some_and(|nla| nla.is_check_feasible);
        if is_check_feasible && self.lra_make_feasible() == LBool::False {
            self.lra_set_infeasibility_conflict();
            return Ok(());
        }
        let mut index = 0;
        while let Some(ineq) = self.lra_nla_item(|nla| nla.literals.get(index).cloned()) {
            let literal = self.lra_mk_nla_literal(&ineq)?;
            self.mark_literal_as_relevant(literal)?;
            self.set_true_first_flag(get_var(literal));
            index += 1;
        }
        let mut index = 0;
        while let Some(lemma) = self.lra_nla_item(|nla| nla.lemmas.get(index).cloned()) {
            self.lra_false_case_of_check_nla(&lemma)?;
            index += 1;
        }
        let mut index = 0;
        while let Some((lp_var, value, explanation)) = self.lra_nla_item(|nla| {
            nla.fixed_equalities.get(index).map(|equality| {
                (
                    equality.lp_var,
                    equality.value.clone(),
                    equality.explanation.clone(),
                )
            })
        }) {
            self.lra_add_equality(lp_var, &value, &explanation);
            index += 1;
        }
        let mut index = 0;
        while let Some((first, second, explanation)) = self.lra_nla_item(|nla| {
            nla.equalities.get(index).map(|equality| {
                (
                    equality.first,
                    equality.second,
                    equality.explanation.clone(),
                )
            })
        }) {
            let (solver, _, mut view) = self.lra_split_view();
            view.add_eq(solver, first, second, &explanation, false);
            index += 1;
        }
        Ok(())
    }

    /// An item of nla's lists, which the theory made.
    fn lra_nla_item<T>(&self, get: impl FnOnce(&NlaCore) -> Option<T>) -> Option<T> {
        self.lra().nla.as_ref().and_then(get)
    }

    /// add_equality: a column fixed to a value, equal to the variable of the value's numeral.
    fn lra_add_equality(&mut self, column: usize, value: &Rational, explanation: &Explanation) {
        let theory = self.lra();
        // The TypeScript reads the columns of the constants 1 and 0 as theory variables.
        let th_var = if *value == Rational::one() {
            Some(theory.one_var as i32)
        } else if value.is_zero() {
            Some(theory.zero_var as i32)
        } else {
            theory
                .value2var
                .get(&(true, value.clone()))
                .or_else(|| theory.value2var.get(&(false, value.clone())))
                .copied()
        };
        let Some(th_var) = th_var else {
            return;
        };
        if (theory.solver.get_external(column) as i32) < 0 {
            return;
        }
        let other = self.lra_register_var(th_var);
        let (solver, _, mut view) = self.lra_split_view();
        view.add_eq(solver, other, column, explanation, true);
    }

    /// mk_literal: the literal of an inequality of nla, over a bound or equality atom.
    fn lra_mk_nla_literal(&mut self, ineq: &Ineq) -> Result<Literal, SmtError> {
        // scoped_auxiliary: the bounds of the atom are auxiliary constraints.
        self.lra_mut().solver.constraints.is_auxiliary_mode = true;
        let literal = self.lra_mk_nla_literal_core(ineq)?;
        self.lra_mut().solver.constraints.is_auxiliary_mode = false;
        Ok(literal)
    }

    fn lra_mk_nla_literal_core(&mut self, ineq: &Ineq) -> Result<Literal, SmtError> {
        let kind = ineq.cmp;
        if kind == KIND_EQ || kind == KIND_NE {
            let atom = self.lra_mk_term_eq(&ineq.term, &ineq.rs)?;
            let literal = self.get_literal(atom)?;
            return Ok(if kind == KIND_NE {
                negate(literal)
            } else {
                literal
            });
        }
        let is_lower = kind == KIND_LT || kind == KIND_GE;
        let atom = self.lra_mk_bound(&ineq.term, &ineq.rs, is_lower)?;
        let literal = self.get_literal(atom)?;
        Ok(if kind == KIND_LT || kind == KIND_GT {
            negate(literal)
        } else {
            literal
        })
    }

    /// mk_eq: the atom term = offset.
    fn lra_mk_term_eq(&mut self, term: &LarTerm, offset: &Rational) -> Result<Expr, SmtError> {
        let coeffs = get_term_coeffs(&self.lra().solver, term)?;
        let is_int = offset.is_int()
            && coeffs
                .iter()
                .all(|entry| self.lra_is_int_var(entry.0) && entry.1.is_int());
        let left = self.lra_coeffs_to_app(&coeffs, is_int)?;
        let right = self
            .m
            .mk_numeral_of_sort(offset, if is_int { SORT_INT } else { SORT_REAL });
        if left == right {
            return Ok(self.m.true_expr);
        }
        let atom = self.m.mk_eq(left, right)?;
        self.internalize(atom, true)?;
        self.mark_as_relevant(atom)?;
        Ok(atom)
    }

    /// false_case_of_check_nla and set_conflict_or_lemma: the lemma as a theory axiom, unless one
    /// of its literals is already true.
    fn lra_false_case_of_check_nla(&mut self, lemma: &Lemma) -> Result<(), SmtError> {
        let mut literals = Vec::new();
        for ineq in &lemma.ineqs {
            literals.push(negate(self.lra_mk_nla_literal(ineq)?));
        }
        self.lra_reset_evidence();
        let theory = self.lra_mut();
        theory.core_literals.extend(literals);
        theory.num_conflicts += 1;
        for constraint in lemma.expl.iter() {
            self.lra_set_evidence(constraint);
        }
        let mut clause: Vec<Literal> = Vec::new();
        // The literals as they are now: marking one relevant may make the theory reset its
        // evidence.
        let core_literals = self.lra().core_literals.clone();
        for literal in core_literals {
            let negated = negate(literal);
            clause.push(negated);
            self.mark_literal_as_relevant(negated)?;
            if self.get_assignment(negated) == LBool::True {
                return Ok(());
            }
        }
        self.mk_th_axiom(&mut clause)
    }

    /// check_lia: whether the integer solver found the integer columns integral.
    fn lra_is_lia_sat(&mut self) -> Result<bool, SmtError> {
        if self.check_canceled() {
            return Ok(false);
        }
        let theory = get_lra_mut(&mut self.theory);
        let lia_move = Lia {
            lia: &mut theory.lia,
            lra: &mut theory.solver,
        }
        .check()?;
        match &lia_move {
            LiaMove::Branch { is_upper, offset } => {
                let term = self.lra().lia.term.clone();
                self.lra_mk_bound(&term, offset, !is_upper)?;
            }
            LiaMove::Cut { offset, is_upper } => {
                self.lra_reset_evidence();
                let constraints: Vec<usize> = self.lra().lia.explanation.iter().collect();
                for constraint in constraints {
                    self.lra_set_evidence(constraint);
                }
                let term = self.lra().lia.term.clone();
                let atom = self.lra_mk_bound(&term, offset, !is_upper)?;
                let literal = self.get_literal(atom)?;
                let justification = self.justification_arena.mk(Justification::Theory {
                    literals: self.lra().core_literals.clone(),
                    eqs: Vec::new(),
                });
                self.assign(literal, BJustification::Justification(justification), false);
            }
            LiaMove::Conflict => {
                let theory = self.lra_mut();
                theory.explanation.clear();
                theory.explanation.add_explanation(&theory.lia.explanation);
                self.lra_set_conflict();
            }
            _ => {}
        }
        Ok(lia_move == LiaMove::Sat)
    }

    /// mk_bound: the atom of a bound on an lp term, over the theory variables of its columns.
    fn lra_mk_bound(
        &mut self,
        lp_term: &LarTerm,
        input_offset: &Rational,
        input_is_lower: bool,
    ) -> Result<Expr, SmtError> {
        let mut coeffs = get_term_coeffs(&self.lra().solver, lp_term)?;
        let mut offset = input_offset.clone();
        let mut is_lower = input_is_lower;
        let mut lcm = offset.den().clone();
        let is_int = coeffs.iter().all(|entry| self.lra_is_int_var(entry.0));
        if is_int {
            for entry in &coeffs {
                lcm = get_lcm(&lcm, entry.1.den());
            }
            if lcm != Int::one() {
                let scale = Rational::from_int(lcm.clone());
                offset = offset.mul(&scale);
                coeffs = coeffs
                    .into_iter()
                    .map(|entry| (entry.0, entry.1.mul(&scale)))
                    .collect();
            }
            let mut gcd = Int::zero();
            for entry in &coeffs {
                gcd = get_gcd(&gcd, entry.1.num());
            }
            if !gcd.is_zero() && gcd != Int::one() {
                let divisor = Rational::from_int(gcd);
                coeffs = coeffs
                    .into_iter()
                    .map(|entry| (entry.0, entry.1.div(&divisor)))
                    .collect();
                offset = if is_lower {
                    offset.div(&divisor).ceil()
                } else {
                    offset.div(&divisor).floor()
                };
            }
        }
        if coeffs.first().is_some_and(|entry| entry.1.is_negative()) {
            offset = offset.neg();
            is_lower = !is_lower;
            coeffs = coeffs
                .into_iter()
                .map(|entry| (entry.0, entry.1.neg()))
                .collect();
        }
        let sort = if is_int { SORT_INT } else { SORT_REAL };
        let term = self.lra_coeffs_to_app(&coeffs, is_int)?;
        let numeral = self.m.mk_numeral_of_sort(&offset, sort);
        let atom = self.m.mk_app(
            if is_lower { OP_GE } else { OP_LE },
            &[term, numeral],
            SORT_BOOL,
        )?;
        self.internalize(atom, true)?;
        self.mark_as_relevant(atom)?;
        Ok(atom)
    }

    /// coeffs2app: the sum of the expressions of theory variables times coefficients, with Int
    /// expressions of a Real sum coerced to Real.
    fn lra_coeffs_to_app(
        &mut self,
        coeffs: &[(i32, Rational)],
        is_int: bool,
    ) -> Result<Expr, SmtError> {
        let sort = if is_int { SORT_INT } else { SORT_REAL };
        let mut summands = Vec::new();
        for entry in coeffs {
            if entry.1.is_zero() {
                continue;
            }
            let original = self.lra_get_expr(entry.0);
            let expr = if !is_int && self.m.is_int(original) {
                self.m.mk_app(OP_TO_REAL, &[original], SORT_REAL)?
            } else {
                original
            };
            summands.push(if entry.1 == Rational::one() {
                expr
            } else {
                let coeff = self.m.mk_numeral_of_sort(&entry.1, sort);
                self.m.mk_app(OP_MUL, &[coeff, expr], sort)?
            });
        }
        Ok(match summands.len() {
            0 => self.m.mk_numeral_of_sort(&Rational::zero(), sort),
            1 => summands[0],
            _ => self.m.mk_app(OP_ADD, &summands, sort)?,
        })
    }
}
