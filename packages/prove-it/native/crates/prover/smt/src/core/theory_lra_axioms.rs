//! Ported from Z3 (src/smt/theory_lra.cpp, src/smt/arith_eq_adapter.cpp), MIT license, see
//! z3-license.txt, through `theory-lra-axioms.ts`. The axioms of theory_lra: those of div, mod,
//! to_int and is_int, and the arith_eq_adapter axioms that tie an equality of terms to their two
//! inequalities.

use prove_num::{Int, Rational};

use crate::core::ast::{
    Expr, OP_ADD, OP_DIV, OP_GE, OP_IDIV, OP_IS_INT, OP_LE, OP_MOD, OP_MUL, OP_SUB, OP_TO_INT,
    OP_TO_REAL, SORT_BOOL, SORT_INT, SORT_REAL,
};
use crate::core::context::{Context, TrailClosure};
use crate::core::enode::EnodeId;
use crate::core::literal::{FALSE_LITERAL, Literal, TRUE_LITERAL, get_var, is_negated, negate};
use crate::core::relevancy::{RelevancyHandler, RelevancyPropagator};
use crate::core::theory_lra_state::TheoryClosure;
use crate::util::error::SmtError;

impl Context {
    /// The enode of a term, internalized first if it has none.
    pub(crate) fn lra_get_internalized_enode(&mut self, expr: Expr) -> Result<EnodeId, SmtError> {
        if !self.is_e_internalized(expr) {
            self.internalize(expr, false)?;
        }
        self.get_enode(expr)
            .ok_or_else(|| SmtError::Invariant("the term was not internalized".into()))
    }

    pub(crate) fn lra_is_zero_numeral(&self, expr: Expr) -> bool {
        self.m.is_numeral(expr) && self.m.get_rational_value(expr).is_zero()
    }

    pub(crate) fn lra_mk_eq_axioms(
        &mut self,
        input_first: EnodeId,
        input_second: EnodeId,
    ) -> Result<(), SmtError> {
        if input_first == input_second {
            return Ok(());
        }
        let is_swapped = self.m.ids[self.node(input_first).owner as usize]
            > self.m.ids[self.node(input_second).owner as usize];
        let (first, second) = if is_swapped {
            (input_second, input_first)
        } else {
            (input_first, input_second)
        };
        let mut t1 = self.node(first).owner;
        let mut t2 = self.node(second).owner;
        if self.m.is_numeral(t1) && self.m.is_numeral(t2) {
            return Ok(());
        }
        if !self.lra_mut().processed_eqs.insert((t1, t2)) {
            return Ok(());
        }
        self.push_trail(TrailClosure::Theory(TheoryClosure::DeleteProcessedEq {
            first: t1,
            second: t2,
        }));
        let eq = self.mk_eq_atom(t1, t2)?;
        if self.m.is_numeral(t1) {
            std::mem::swap(&mut t1, &mut t2);
        }
        let sort = self.m.sorts[t1 as usize];
        let (le, ge) = if self.m.is_numeral(t2) {
            (
                self.m.mk_app(OP_LE, &[t1, t2], SORT_BOOL)?,
                self.m.mk_app(OP_GE, &[t1, t2], SORT_BOOL)?,
            )
        } else {
            let minus_one = self.m.mk_numeral_of_sort(&Rational::minus_one(), sort);
            let zero = self.m.mk_numeral_of_sort(&Rational::zero(), sort);
            let product = self.m.mk_app(OP_MUL, &[minus_one, t2], sort)?;
            let difference = self.m.mk_app(OP_ADD, &[t1, product], sort)?;
            (
                self.m.mk_app(OP_LE, &[difference, zero], SORT_BOOL)?,
                self.m.mk_app(OP_GE, &[difference, zero], SORT_BOOL)?,
            )
        };
        self.internalize(eq, true)?;
        self.internalize(le, true)?;
        self.internalize(ge, true)?;
        let eq_literal = self.get_literal(eq)?;
        let le_literal = self.get_literal(le)?;
        let ge_literal = self.get_literal(ge)?;
        if self.is_true_first(get_var(eq_literal)) {
            self.set_true_first_flag(get_var(le_literal));
            self.set_true_first_flag(get_var(ge_literal));
        }
        self.mk_th_axiom(&mut vec![negate(eq_literal), le_literal])?;
        self.mk_th_axiom(&mut vec![negate(eq_literal), ge_literal])?;
        self.mk_th_axiom(&mut vec![
            eq_literal,
            negate(le_literal),
            negate(ge_literal),
        ])?;
        let first_owner = self.node(first).owner;
        let second_owner = self.node(second).owner;
        let handler = RelevancyHandler::EqAxioms {
            first: first_owner,
            second: second_owner,
            eq,
            le,
            ge,
        };
        RelevancyPropagator::add_handler(self, first_owner, handler)?;
        RelevancyPropagator::add_handler(self, second_owner, handler)?;
        if self.scope_level != self.base_level
            && self.node(first).iscope_level <= self.base_level
            && self.node(second).iscope_level <= self.base_level
        {
            self.lra_mut().restart_pairs.push((first, second));
        }
        Ok(())
    }

    pub fn theory_internalize_eq_eh(&mut self, expr: Expr) -> Result<(), SmtError> {
        if self.theory.is_none() {
            return Err(SmtError::Invariant("the theory is not set up".into()));
        }
        let first = self.get_enode(self.m.get_arg(expr, 0));
        let second = self.get_enode(self.m.get_arg(expr, 1));
        let (Some(first), Some(second)) = (first, second) else {
            return Ok(());
        };
        if self.node(first).th_var >= 0 && self.node(second).th_var >= 0 && first != second {
            self.lra_mk_eq_axioms(first, second)?;
        }
        Ok(())
    }

    pub fn theory_new_eq_eh(&mut self, first: i32, second: i32) -> Result<(), SmtError> {
        if self.theory.is_none() {
            return Err(SmtError::Invariant("the theory is not set up".into()));
        }
        self.lra_mk_eq_axioms(self.theory_get_enode(first), self.theory_get_enode(second))
    }

    pub fn theory_new_diseq_eh(&mut self, first: i32, second: i32) -> Result<(), SmtError> {
        if self.theory.is_none() {
            return Err(SmtError::Invariant("the theory is not set up".into()));
        }
        self.lra_mk_eq_axioms(self.theory_get_enode(first), self.theory_get_enode(second))
    }

    pub fn theory_relevant_eh(&mut self, expr: Expr) -> Result<(), SmtError> {
        if self.theory.is_none() {
            return Err(SmtError::Invariant("the theory is not set up".into()));
        }
        let op = self.m.get_op(expr);
        if op == OP_DIV {
            self.lra_mk_div_axiom(self.m.get_arg(expr, 0), self.m.get_arg(expr, 1))
        } else if op == OP_TO_INT {
            self.lra_mk_to_int_axiom(expr)
        } else if op == OP_IS_INT {
            self.lra_mk_is_int_axiom(expr)
        } else if op == OP_MOD {
            self.lra_mk_idiv_mod_axioms(self.m.get_arg(expr, 0), self.m.get_arg(expr, 1))
        } else {
            Ok(())
        }
    }

    /// mk_literal.
    pub(crate) fn lra_mk_literal(&mut self, atom: Expr) -> Result<Literal, SmtError> {
        if !self.is_e_internalized(atom) {
            self.internalize(atom, false)?;
        }
        self.get_literal(atom)
    }

    /// ensure_enode: the relevant enode of a term.
    fn lra_ensure_enode(&mut self, expr: Expr) -> Result<EnodeId, SmtError> {
        let node = self.lra_get_internalized_enode(expr)?;
        self.mark_as_relevant(expr)?;
        Ok(node)
    }

    /// mk_axiom: a theory axiom whose literals are relevant. Of two literals, the second becomes
    /// relevant only once the first is false. A unit axiom is the clause of false and the literal,
    /// so mk_clause drops false and the literal is justified by unit resolution with true, which
    /// lemma minimization can see through, rather than by an axiom.
    pub(crate) fn lra_mk_axiom(&mut self, literals: &[Literal]) -> Result<(), SmtError> {
        // mkThAxiom simplifies the literals it is given, which this reads after.
        let mut clause = if literals.len() == 1 {
            vec![FALSE_LITERAL, literals[0]]
        } else {
            literals.to_vec()
        };
        self.mk_th_axiom(&mut clause)?;
        if !self.relevancy.is_enabled {
            return Ok(());
        }
        if literals.len() != 2 {
            for literal in literals {
                self.mark_literal_as_relevant(*literal)?;
            }
            return Ok(());
        }
        self.mark_literal_as_relevant(literals[0])?;
        let consequent = self.bool_var2expr[get_var(literals[1]) as usize];
        let antecedent = self.bool_var2expr[get_var(literals[0]) as usize];
        // simple_relevancy_eh marks the consequent without propagating.
        RelevancyPropagator::add_watch(
            self,
            antecedent,
            is_negated(literals[0]),
            RelevancyHandler::MarkAsRelevant { target: consequent },
        )
    }

    /// mk_div_axiom: q = 0 or q * (p / q) = p.
    fn lra_mk_div_axiom(&mut self, dividend: Expr, divisor: Expr) -> Result<(), SmtError> {
        if self.lra_is_zero_numeral(divisor) {
            return Ok(());
        }
        let zero = self.m.mk_real_numeral(&Rational::zero());
        let is_zero = self.lra_mk_eq(divisor, zero)?;
        let quotient = self.m.mk_app(OP_DIV, &[dividend, divisor], SORT_REAL)?;
        let product = self.m.mk_app(OP_MUL, &[divisor, quotient], SORT_REAL)?;
        let is_product = self.lra_mk_eq(product, dividend)?;
        self.lra_mk_axiom(&[is_zero, is_product])
    }

    /// mk_to_int_axiom: to_int (to_real x) = x, and to_real (to_int x) <= x < to_real (to_int x)
    /// + 1.
    fn lra_mk_to_int_axiom(&mut self, term: Expr) -> Result<(), SmtError> {
        let arg = self.m.get_arg(term, 0);
        if self.m.get_op(arg) == OP_TO_REAL {
            let literal = self.lra_mk_eq(self.m.get_arg(arg, 0), term)?;
            return self.lra_mk_axiom(&[literal]);
        }
        let to_real = self.m.mk_app(OP_TO_REAL, &[term], SORT_REAL)?;
        let lower_difference = self.m.mk_app(OP_SUB, &[to_real, arg], SORT_REAL)?;
        let zero = self.m.mk_real_numeral(&Rational::zero());
        let lower = self.m.mk_app(OP_LE, &[lower_difference, zero], SORT_BOOL)?;
        let upper_difference = self.m.mk_app(OP_SUB, &[arg, to_real], SORT_REAL)?;
        let one = self.m.mk_real_numeral(&Rational::one());
        let upper = self.m.mk_app(OP_GE, &[upper_difference, one], SORT_BOOL)?;
        let lower_literal = self.lra_mk_literal(lower)?;
        let upper_literal = self.lra_mk_literal(upper)?;
        self.lra_mk_axiom(&[lower_literal])?;
        self.lra_mk_axiom(&[negate(upper_literal)])
    }

    /// mk_is_int_axiom: is_int x if and only if to_real (to_int x) = x.
    pub(crate) fn lra_mk_is_int_axiom(&mut self, atom: Expr) -> Result<(), SmtError> {
        let arg = self.m.get_arg(atom, 0);
        let to_int = self.m.mk_app(OP_TO_INT, &[arg], SORT_INT)?;
        let to_real = self.m.mk_app(OP_TO_REAL, &[to_int], SORT_REAL)?;
        let eq = self.lra_mk_eq(to_real, arg)?;
        let is_int = self.get_literal(atom)?;
        self.lra_mk_axiom(&[negate(is_int), eq])?;
        self.lra_mk_axiom(&[is_int, negate(eq)])
    }

    /// theory::mk_eq: the literal of an equality between two terms, internalized.
    pub(crate) fn lra_mk_eq(&mut self, first: Expr, second: Expr) -> Result<Literal, SmtError> {
        if first == second {
            return Ok(TRUE_LITERAL);
        }
        if self.m.is_unique_value(first) && self.m.is_unique_value(second) {
            return Ok(FALSE_LITERAL);
        }
        let atom = self.mk_eq_atom(first, second)?;
        self.internalize(atom, false)?;
        self.get_literal(atom)
    }

    /// mk_idiv_mod_axioms: q * (div p q) + (mod p q) = p and 0 <= (mod p q) < |q| when q is not 0.
    pub(crate) fn lra_mk_idiv_mod_axioms(
        &mut self,
        dividend: Expr,
        divisor: Expr,
    ) -> Result<(), SmtError> {
        if self.m.get_numeral(divisor).is_some_and(Int::is_zero) {
            return Ok(());
        }
        // The expr_refs of mk_idiv_mod_axioms, released in reverse when it returns.
        let mut refs = Vec::new();
        let outer = self.m.suspend_temporaries();
        let result = self.lra_mk_idiv_mod_axioms_core(dividend, divisor, &mut refs);
        self.m.restore_temporaries(outer);
        result?;
        for index in (0..refs.len()).rev() {
            self.m.dec_ref(refs[index])?;
        }
        Ok(())
    }

    fn lra_mk_idiv_mod_axioms_core(
        &mut self,
        dividend: Expr,
        divisor: Expr,
        refs: &mut Vec<Expr>,
    ) -> Result<(), SmtError> {
        let hold = |context: &mut Context, refs: &mut Vec<Expr>, expr: Expr| {
            context.m.inc_ref(expr);
            refs.push(expr);
            expr
        };
        let quotient = self.m.mk_app(OP_IDIV, &[dividend, divisor], SORT_INT)?;
        let quotient = hold(self, refs, quotient);
        let remainder = self.m.mk_app(OP_MOD, &[dividend, divisor], SORT_INT)?;
        let remainder = hold(self, refs, remainder);
        let zero = self.m.mk_numeral(&Int::zero());
        let zero = hold(self, refs, zero);
        if self.m.get_numeral(dividend).is_some_and(Int::is_zero) {
            // q != 0 implies div 0 q = 0 and mod 0 q = 0.
            let atom = self.m.mk_app(OP_GE, &[divisor, zero], SORT_BOOL)?;
            let is_divisor_nonnegative = self.lra_mk_literal(atom)?;
            let atom = self.m.mk_app(OP_LE, &[divisor, zero], SORT_BOOL)?;
            let is_divisor_nonpositive = self.lra_mk_literal(atom)?;
            let atoms = [
                self.m.mk_app(OP_GE, &[quotient, zero], SORT_BOOL)?,
                self.m.mk_app(OP_LE, &[quotient, zero], SORT_BOOL)?,
                self.m.mk_app(OP_GE, &[remainder, zero], SORT_BOOL)?,
                self.m.mk_app(OP_LE, &[remainder, zero], SORT_BOOL)?,
            ];
            let mut consequents = Vec::new();
            for atom in atoms {
                consequents.push(self.lra_mk_literal(atom)?);
            }
            for antecedent in [is_divisor_nonnegative, is_divisor_nonpositive] {
                for consequent in &consequents {
                    self.lra_mk_axiom(&[antecedent, *consequent])?;
                }
            }
            return Ok(());
        }
        let product = self.m.mk_app(OP_MUL, &[divisor, quotient], SORT_INT)?;
        let combination = self.m.mk_app(OP_ADD, &[product, remainder], SORT_INT)?;
        let combination = hold(self, refs, combination);
        let eq_atom = self.mk_eq_atom(combination, dividend)?;
        let eq_atom = hold(self, refs, eq_atom);
        self.internalize(eq_atom, false)?;
        let eq = self.get_literal(eq_atom)?;
        if let Some(divisor_value) = self.m.get_numeral(divisor).cloned() {
            let upper_value = &divisor_value.abs() - &Int::one();
            let upper = self.m.mk_numeral(&upper_value);
            let upper = hold(self, refs, upper);
            self.lra_mk_axiom(&[eq])?;
            let combination_node = self.lra_ensure_enode(combination)?;
            let dividend_node = self.lra_ensure_enode(dividend)?;
            self.lra_mk_eq_axioms(combination_node, dividend_node)?;
            let atom = self.m.mk_app(OP_GE, &[remainder, zero], SORT_BOOL)?;
            let literal = self.lra_mk_literal(atom)?;
            self.lra_mk_axiom(&[literal])?;
            let atom = self.m.mk_app(OP_LE, &[remainder, upper], SORT_BOOL)?;
            let literal = self.lra_mk_literal(atom)?;
            return self.lra_mk_axiom(&[literal]);
        }
        // q = 0 or (mod p q) >= 0, q >= 0 or (mod p q) + q <= -1, and q <= 0 or (mod p q) - q <=
        // -1.
        let minus_one = self.m.mk_numeral(&Int::from(-1));
        let minus_one = hold(self, refs, minus_one);
        let minus_divisor = self.m.mk_app(OP_MUL, &[minus_one, divisor], SORT_INT)?;
        let minus_divisor = hold(self, refs, minus_divisor);
        let atom = self.m.mk_eq(divisor, zero)?;
        let is_zero = self.lra_mk_literal(atom)?;
        let atom = self.m.mk_app(OP_GE, &[remainder, zero], SORT_BOOL)?;
        let is_remainder_nonnegative = self.lra_mk_literal(atom)?;
        self.lra_mk_axiom(&[is_zero, eq])?;
        self.lra_mk_axiom(&[is_zero, is_remainder_nonnegative])?;
        let atom = self.m.mk_app(OP_LE, &[divisor, zero], SORT_BOOL)?;
        let is_divisor_nonpositive = self.lra_mk_literal(atom)?;
        let sum = self
            .m
            .mk_app(OP_ADD, &[remainder, minus_divisor], SORT_INT)?;
        let atom = self.m.mk_app(OP_LE, &[sum, minus_one], SORT_BOOL)?;
        let is_below_divisor = self.lra_mk_literal(atom)?;
        self.lra_mk_axiom(&[is_divisor_nonpositive, is_below_divisor])?;
        let atom = self.m.mk_app(OP_GE, &[divisor, zero], SORT_BOOL)?;
        let is_divisor_nonnegative = self.lra_mk_literal(atom)?;
        let sum = self.m.mk_app(OP_ADD, &[remainder, divisor], SORT_INT)?;
        let atom = self.m.mk_app(OP_LE, &[sum, minus_one], SORT_BOOL)?;
        let is_below_negated_divisor = self.lra_mk_literal(atom)?;
        self.lra_mk_axiom(&[is_divisor_nonnegative, is_below_negated_divisor])?;
        let combination_node = self.lra_ensure_enode(combination)?;
        let dividend_node = self.lra_ensure_enode(dividend)?;
        self.lra_mk_eq_axioms(combination_node, dividend_node)?;
        // q = 0 or q * (div p q) <= p. The rewritten atom replaces the unrewritten one, which Z3
        // releases at once, and its own expr_ref goes at the end of the block.
        let product = self.m.mk_app(OP_MUL, &[divisor, quotient], SORT_INT)?;
        let difference = self.m.mk_app(OP_SUB, &[dividend, product], SORT_INT)?;
        let unrewritten = self.m.mk_app(OP_GE, &[difference, zero], SORT_BOOL)?;
        self.m.inc_ref(unrewritten);
        let is_product_below = self.rewriter.rewrite(&mut self.m, unrewritten)?;
        self.m.dec_ref(unrewritten)?;
        let literal = self.lra_mk_literal(is_product_below)?;
        self.lra_mk_axiom(&[is_zero, literal])?;
        self.m.dec_ref(is_product_below)
    }
}
