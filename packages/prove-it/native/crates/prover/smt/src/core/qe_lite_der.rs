//! Ported from Z3 (src/qe/lite/qe_lite_tactic.cpp, src/qe/mbp/mbp_solve_plugin.cpp), MIT license,
//! through `qe-lite-der.ts`. The eq_der of qe-lite: destructive equality resolution, which removes
//! the variables of a quantifier that its body defines by an equality, with the solve plugins for
//! Booleans and integer arithmetic.
//!
//! The TypeScript's sparse arrays indexed by variable (`map`, `inx2var`, `var2pos`) are vectors
//! that grow to the largest index set, so their lengths are the arrays'. The recursions of the
//! solve plugins stop past `MAX_RECURSION_DEPTH` (design/smt-core.md, recursion).

use std::collections::HashSet;

use prove_num::Int;

use crate::core::ast::{
    AstManager, Expr, KIND_VAR, OP_ADD, OP_AND, OP_EQ, OP_IDIV, OP_ITE, OP_MOD, OP_MUL, OP_SUB,
    OP_UMINUS, SORT_BOOL, SORT_INT,
};
use crate::core::ast_util::{flatten_and_vector, mk_not};
use crate::core::der::is_occurring;
use crate::core::expr_ref::{assign, assign_owned, release};
use crate::core::ref_vector::RefVector;
use crate::core::rewriter::{Rewriter, TACTIC_REWRITER_OPTIONS};
use crate::core::rewriter_tpl::{BetaReducer, MAX_RECURSION_DEPTH};
use crate::util::error::SmtError;

fn mk_recursion_error() -> SmtError {
    SmtError::Unsupported("qe-lite's solver nests too deeply".into())
}

// A summand of a linear equation and whether it is on the left-hand side.
#[derive(Clone, Copy, Debug)]
struct SignedExpr {
    is_left: bool,
    expr: Expr,
}

struct SolvedVar {
    variable: Expr,
    // Held by a reference that the receiver releases.
    term: Expr,
}

// A variable times an invertible coefficient.
struct InvertibleMul {
    variable: Expr,
    coefficient: Int,
}

// The definitions find_definitions found.
struct FoundDefinitions {
    num_defs: usize,
    largest_index: usize,
}

// The slot of a sparse array, which grows to hold it.
fn set_at(items: &mut Vec<Expr>, index: usize, value: Expr) {
    if items.len() <= index {
        items.resize(index + 1, -1);
    }
    items[index] = value;
}

fn get_at(items: &[Expr], index: usize) -> Expr {
    items.get(index).copied().unwrap_or(-1)
}

/// eq_der: destructive equality resolution on a conjunction.
#[derive(Clone, Debug)]
pub struct EqDer {
    subst: BetaReducer,
    subst_map: RefVector,
    new_exprs: RefVector,
    rewriter: Rewriter,
    map: Vec<Expr>,
    pos2var: Vec<i32>,
    var2pos: Vec<Expr>,
    inx2var: Vec<Expr>,
    order: Vec<usize>,
    /// is_variable_test: the variables of the quantifier at hand are those below this index.
    pub num_vars: i32,
}

impl EqDer {
    pub fn new(m: &AstManager) -> EqDer {
        EqDer {
            subst: BetaReducer::new(m),
            subst_map: RefVector::new(),
            new_exprs: RefVector::new(),
            rewriter: Rewriter::new(m, TACTIC_REWRITER_OPTIONS, false),
            map: Vec::new(),
            pos2var: Vec::new(),
            var2pos: Vec::new(),
            inx2var: Vec::new(),
            order: Vec::new(),
            num_vars: 0,
        }
    }

    fn is_variable(&self, m: &AstManager, expr: Expr) -> bool {
        m.kinds[expr as usize] == KIND_VAR && m.values[expr as usize] < self.num_vars
    }

    /// operator(): reduce_var_set until nothing changes.
    pub fn apply(&mut self, m: &mut AstManager, conjs: &mut RefVector) -> Result<(), SmtError> {
        while self.reduce_var_set(m, conjs)? {}
        self.new_exprs.reset(m)
    }

    /// ~eq_der.
    pub fn release(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.rewriter.release(m)?;
        self.new_exprs.reset(m)?;
        self.subst_map.reset(m)?;
        self.subst.release(m)
    }

    fn reduce_var_set(
        &mut self,
        m: &mut AstManager,
        conjs: &mut RefVector,
    ) -> Result<bool, SmtError> {
        // flatten_definitions: a false conjunct is the whole conjunction.
        if let Some(false_conj) = conjs.items.iter().copied().find(|conj| m.is_false(*conj)) {
            conjs.set(m, 0, false_conj)?;
            conjs.shrink(m, 1)?;
        }
        let mut is_reduced = false;
        let found = self.find_definitions(m, &conjs.items.clone())?;
        if found.num_defs > 0 {
            self.sort_vars(m)?;
            if !self.order.is_empty() {
                let conjunction = m.mk_app(OP_AND, &conjs.items, SORT_BOOL)?;
                m.inc_ref(conjunction);
                self.create_substitution(m, found.largest_index + 1)?;
                let bindings = self.subst_map.items.clone();
                let mut substituted =
                    self.subst
                        .rewrite_with_bindings(m, conjunction, &bindings)?;
                let rewritten = self.rewriter.rewrite(m, substituted)?;
                substituted = assign_owned(m, substituted, rewritten)?;
                conjs.reset(m)?;
                conjs.push(m, substituted);
                flatten_and_vector(m, conjs)?;
                is_reduced = true;
                m.dec_ref(substituted)?;
                m.dec_ref(conjunction)?;
            }
        }
        Ok(self.remove_unconstrained(m, conjs)? || is_reduced)
    }

    // find_definitions: one definition per variable, preferring values, then ground terms, then
    // constants.
    fn find_definitions(
        &mut self,
        m: &mut AstManager,
        args: &[Expr],
    ) -> Result<FoundDefinitions, SmtError> {
        let mut num_defs = 0;
        let mut largest_index = 0;
        self.map = Vec::new();
        self.pos2var = vec![-1; args.len()];
        self.var2pos = Vec::new();
        self.inx2var = Vec::new();
        for (position, arg) in args.iter().copied().enumerate() {
            m.limit.checkpoint()?;
            let mut vars: Vec<Expr> = Vec::new();
            let mut terms = RefVector::new();
            let mut term = -1;
            if self.get_var_eq(m, arg, &mut vars, &mut terms)? {
                for (index, variable) in vars.iter().copied().enumerate() {
                    term = assign(m, term, terms.items[index])?;
                    let rewritten = self.rewriter.rewrite(m, term)?;
                    term = assign_owned(m, term, rewritten)?;
                    if term != terms.items[index] {
                        self.new_exprs.push(m, term);
                    }
                    let var_index = m.values[variable as usize] as usize;
                    let old = get_at(&self.map, var_index);
                    if old == -1 {
                        set_at(&mut self.map, var_index, term);
                        set_at(&mut self.inx2var, var_index, variable);
                        self.pos2var[position] = var_index as i32;
                        set_at(&mut self.var2pos, var_index, position as Expr);
                        num_defs += 1;
                        largest_index = largest_index.max(var_index);
                    } else if m.is_unique_value(old)
                        || !(m.is_unique_value(term)
                            || (m.is_ground_app(term) && !m.is_ground_app(old))
                            || m.is_uninterpreted_const(term))
                    {
                        continue;
                    } else {
                        let old_position = get_at(&self.var2pos, var_index) as usize;
                        self.pos2var[old_position] = -1;
                        self.pos2var[position] = var_index as i32;
                        set_at(&mut self.var2pos, var_index, position as Expr);
                        set_at(&mut self.map, var_index, term);
                    }
                    self.new_exprs.push_owned(term);
                    term = -1;
                }
            }
            release(m, term)?;
            terms.reset(m)?;
        }
        Ok(FoundDefinitions {
            num_defs,
            largest_index,
        })
    }

    // is_var_eq: a variable and its definition from a literal, through the solve plugin of the
    // sort.
    fn get_var_eq(
        &mut self,
        m: &mut AstManager,
        expr: Expr,
        vars: &mut Vec<Expr>,
        terms: &mut RefVector,
    ) -> Result<bool, SmtError> {
        let is_eq = m.get_op(expr) == OP_EQ;
        if is_eq {
            let lhs = m.get_arg(expr, 0);
            let rhs = m.get_arg(expr, 1);
            let is_swapped = !self.is_variable(m, lhs);
            if self.is_variable(m, if is_swapped { rhs } else { lhs }) {
                vars.push(if is_swapped { rhs } else { lhs });
                terms.push(m, if is_swapped { lhs } else { rhs });
                return Ok(true);
            }
        }
        let sort = if is_eq {
            m.sorts[m.get_arg(expr, 0) as usize]
        } else {
            m.sorts[expr as usize]
        };
        if sort != SORT_BOOL && sort != SORT_INT {
            return Ok(false);
        }
        // solve_plugin::operator(): the arithmetic plugin only sees positive equalities.
        let is_negated = m.is_not(expr);
        let solved = if sort == SORT_INT {
            self.solve_arith_eq(m, expr)?
        } else {
            let atom = if is_negated { m.get_arg(expr, 0) } else { expr };
            self.solve_basic(m, atom, !is_negated, 0)?
        };
        let is_found = solved != expr
            && m.get_op(solved) == OP_EQ
            && self.is_variable(m, m.get_arg(solved, 0));
        if is_found {
            vars.push(m.get_arg(solved, 0));
            terms.push(m, m.get_arg(solved, 1));
        }
        m.dec_ref(solved)?;
        Ok(is_found)
    }

    // arith_solve_plugin::is_invertible_const: a numeral that a variable's coefficient may be.
    fn get_invertible_const(
        &self,
        m: &AstManager,
        expr: Expr,
        depth: usize,
    ) -> Result<Option<Int>, SmtError> {
        if m.get_op(expr) == OP_UMINUS {
            if depth >= MAX_RECURSION_DEPTH {
                return Err(mk_recursion_error());
            }
            let inner = self.get_invertible_const(m, m.get_arg(expr, 0), depth + 1)?;
            return Ok(inner.map(|value| -value));
        }
        Ok(m.get_numeral(expr)
            .filter(|value| **value == 1 || **value == -1)
            .cloned())
    }

    // arith_solve_plugin::is_invertible_mul: a variable times an invertible coefficient.
    fn get_invertible_mul(
        &self,
        m: &AstManager,
        expr: Expr,
    ) -> Result<Option<InvertibleMul>, SmtError> {
        if self.is_variable(m, expr) {
            return Ok(Some(InvertibleMul {
                variable: expr,
                coefficient: Int::from(1),
            }));
        }
        if m.get_op(expr) != OP_MUL || m.get_num_args(expr) != 2 {
            return Ok(None);
        }
        let first = m.get_arg(expr, 0);
        let second = m.get_arg(expr, 1);
        let second_value = self.get_invertible_const(m, second, 0)?;
        if let Some(coefficient) = second_value.filter(|_| self.is_variable(m, first)) {
            return Ok(Some(InvertibleMul {
                variable: first,
                coefficient,
            }));
        }
        let first_value = self.get_invertible_const(m, first, 0)?;
        if let Some(coefficient) = first_value.filter(|_| self.is_variable(m, second)) {
            return Ok(Some(InvertibleMul {
                variable: second,
                coefficient,
            }));
        }
        Ok(None)
    }

    // arith_solve_plugin::solve: lhs = rhs as variable = term.
    fn solve_linear(
        &self,
        m: &mut AstManager,
        lhs: Expr,
        rhs: Expr,
    ) -> Result<Option<SolvedVar>, SmtError> {
        if m.sorts[lhs as usize] != SORT_INT {
            return Ok(None);
        }
        let mut todo = vec![
            SignedExpr {
                is_left: true,
                expr: lhs,
            },
            SignedExpr {
                is_left: false,
                expr: rhs,
            },
        ];
        let mut done: Vec<SignedExpr> = Vec::new();
        while let Some(item) = todo.pop() {
            let op = m.get_op(item.expr);
            if op == OP_ADD {
                for index in 0..m.get_num_args(item.expr) {
                    todo.push(SignedExpr {
                        is_left: item.is_left,
                        expr: m.get_arg(item.expr, index),
                    });
                }
            } else if op == OP_SUB {
                todo.push(SignedExpr {
                    is_left: item.is_left,
                    expr: m.get_arg(item.expr, 0),
                });
                for index in 1..m.get_num_args(item.expr) {
                    todo.push(SignedExpr {
                        is_left: !item.is_left,
                        expr: m.get_arg(item.expr, index),
                    });
                }
            } else if op == OP_UMINUS {
                todo.push(SignedExpr {
                    is_left: !item.is_left,
                    expr: m.get_arg(item.expr, 0),
                });
            } else {
                let Some(mul) = self.get_invertible_mul(m, item.expr)? else {
                    done.push(item);
                    continue;
                };
                done.extend(todo.iter().copied());
                // mk_term: the other summands times the inverse of the coefficient, negated on the
                // variable's side.
                let coefficient = Int::from(1) / &mul.coefficient;
                let is_left = item.is_left;
                let mut terms = RefVector::new();
                for summand in &done {
                    let factor = if summand.is_left == is_left {
                        -&coefficient
                    } else {
                        coefficient.clone()
                    };
                    let summand_term = if factor == 1 {
                        summand.expr
                    } else {
                        let numeral = m.mk_numeral(&factor);
                        m.mk_app(OP_MUL, &[numeral, summand.expr], SORT_INT)?
                    };
                    terms.push(m, summand_term);
                }
                let term = if terms.is_empty() {
                    m.mk_numeral(&Int::from(0))
                } else if terms.len() == 1 {
                    terms.items[0]
                } else {
                    m.mk_app(OP_ADD, &terms.items, SORT_INT)?
                };
                m.inc_ref(term);
                terms.reset(m)?;
                return Ok(Some(SolvedVar {
                    variable: mul.variable,
                    term,
                }));
            }
        }
        Ok(None)
    }

    // arith_solve_plugin::mk_eq_core.
    fn mk_arith_eq_core(
        &self,
        m: &mut AstManager,
        input_left: Expr,
        input_right: Expr,
    ) -> Result<Expr, SmtError> {
        if let Some(solved) = self.solve_linear(m, input_left, input_right)? {
            let result = m.mk_eq(solved.variable, solved.term)?;
            m.inc_ref(result);
            m.dec_ref(solved.term)?;
            return Ok(result);
        }
        let is_zero = |m: &AstManager, expr: Expr| m.get_numeral(expr).is_some_and(Int::is_zero);
        let is_left_zero = is_zero(m, input_left);
        let left = if is_left_zero {
            input_right
        } else {
            input_left
        };
        let right = if is_left_zero {
            input_left
        } else {
            input_right
        };
        let is_binary_sum =
            is_zero(m, right) && m.get_op(left) == OP_ADD && m.get_num_args(left) == 2;
        let negated_second = if is_binary_sum {
            m.get_times_minus_one_arg(m.get_arg(left, 1))
        } else {
            None
        };
        let negated_first = if is_binary_sum {
            m.get_times_minus_one_arg(m.get_arg(left, 0))
        } else {
            None
        };
        let result = if let Some(negated_second) = negated_second {
            m.mk_eq(m.get_arg(left, 0), negated_second)?
        } else if let Some(negated_first) = negated_first {
            m.mk_eq(m.get_arg(left, 1), negated_first)?
        } else {
            m.mk_eq(left, right)?
        };
        m.inc_ref(result);
        Ok(result)
    }

    // arith_solve_plugin::try_int_mul_solve: k*y = x becomes y = x div k and x mod k = 0, or x = 0
    // when k is zero.
    fn try_int_mul_solve(&self, m: &mut AstManager, atom: Expr) -> Result<Expr, SmtError> {
        if m.sorts[m.get_arg(atom, 0) as usize] != SORT_INT {
            return Ok(-1);
        }
        let is_mul_on_left = m.get_op(m.get_arg(atom, 1)) != OP_MUL;
        if is_mul_on_left && m.get_op(m.get_arg(atom, 0)) != OP_MUL {
            return Ok(-1);
        }
        let lhs = m.get_arg(atom, if is_mul_on_left { 1 } else { 0 });
        let product = m.get_arg(atom, if is_mul_on_left { 0 } else { 1 });
        if m.get_num_args(product) != 2 {
            return Ok(-1);
        }
        let is_numeral_second = !m.is_numeral(m.get_arg(product, 0));
        if is_numeral_second && !m.is_numeral(m.get_arg(product, 1)) {
            return Ok(-1);
        }
        let first = m.get_arg(product, if is_numeral_second { 1 } else { 0 });
        let second = m.get_arg(product, if is_numeral_second { 0 } else { 1 });
        if m.get_numeral_value(first).is_zero() {
            let zero = m.mk_numeral(&Int::from(0));
            let result = m.mk_eq(lhs, zero)?;
            m.inc_ref(result);
            return Ok(result);
        }
        let mut held = RefVector::new();
        let quotient = m.mk_app(OP_IDIV, &[lhs, first], SORT_INT)?;
        let quotient_eq = m.mk_eq(second, quotient)?;
        held.push(m, quotient_eq);
        let zero = m.mk_numeral(&Int::from(0));
        held.push(m, zero);
        let remainder = m.mk_app(OP_MOD, &[lhs, first], SORT_INT)?;
        held.push(m, remainder);
        let remainder_eq = m.mk_eq(zero, remainder)?;
        held.push(m, remainder_eq);
        let result = m.mk_app(OP_AND, &[quotient_eq, remainder_eq], SORT_BOOL)?;
        m.inc_ref(result);
        held.items.reverse();
        held.reset(m)?;
        Ok(result)
    }

    // arith_solve_plugin::solve on a positive equality.
    fn solve_arith_eq(&self, m: &mut AstManager, atom: Expr) -> Result<Expr, SmtError> {
        let mul_solved = self.try_int_mul_solve(m, atom)?;
        if mul_solved != -1 {
            return Ok(mul_solved);
        }
        let lhs = m.get_arg(atom, 0);
        let rhs = m.get_arg(atom, 1);
        let mut variable = assign(m, -1, lhs)?;
        let mut term = assign(m, -1, rhs)?;
        if let Some(solved) = self.solve_linear(m, lhs, rhs)? {
            variable = assign(m, variable, solved.variable)?;
            term = assign_owned(m, term, solved.term)?;
        }
        let result = self.mk_arith_eq_core(m, variable, term)?;
        m.dec_ref(term)?;
        m.dec_ref(variable)?;
        Ok(result)
    }

    // basic_solve_plugin::solve.
    fn solve_basic(
        &self,
        m: &mut AstManager,
        atom: Expr,
        is_positive: bool,
        depth: usize,
    ) -> Result<Expr, SmtError> {
        if depth >= MAX_RECURSION_DEPTH {
            return Err(mk_recursion_error());
        }
        let mut result = assign(m, -1, atom)?;
        if m.get_op(atom) == OP_EQ {
            let lhs = m.get_arg(atom, 0);
            let rhs = m.get_arg(atom, 1);
            if m.is_not(lhs) && self.is_variable(m, m.get_arg(lhs, 0)) {
                let negated = mk_not(m, rhs)?;
                let eq = m.mk_eq(m.get_arg(lhs, 0), negated)?;
                result = assign(m, result, eq)?;
            } else if m.is_not(rhs) && self.is_variable(m, m.get_arg(rhs, 0)) {
                let negated = mk_not(m, lhs)?;
                let eq = m.mk_eq(m.get_arg(rhs, 0), negated)?;
                result = assign(m, result, eq)?;
            } else if self.is_variable(m, rhs) && !self.is_variable(m, lhs) {
                let eq = m.mk_eq(rhs, lhs)?;
                result = assign(m, result, eq)?;
            }
        }
        if m.get_op(atom) == OP_ITE {
            let condition = m.get_arg(atom, 0);
            let then_expr = m.get_arg(atom, 1);
            let else_expr = m.get_arg(atom, 2);
            let then_solved = self.solve_basic(m, then_expr, true, depth + 1)?;
            let else_solved = self.solve_basic(m, else_expr, true, depth + 1)?;
            if m.get_op(then_solved) == OP_EQ
                && m.get_op(else_solved) == OP_EQ
                && m.get_arg(then_solved, 0) == m.get_arg(else_solved, 0)
            {
                let then_term = m.get_arg(then_solved, 1);
                let sort = m.sorts[then_term as usize];
                let ite = m.mk_app(
                    OP_ITE,
                    &[condition, then_term, m.get_arg(else_solved, 1)],
                    sort,
                )?;
                let eq = m.mk_eq(m.get_arg(then_solved, 0), ite)?;
                result = assign(m, result, eq)?;
            }
            m.dec_ref(else_solved)?;
            m.dec_ref(then_solved)?;
        }
        if self.is_variable(m, atom) && m.sorts[atom as usize] == SORT_BOOL {
            let value = if is_positive {
                m.true_expr
            } else {
                m.false_expr
            };
            let eq = m.mk_eq(atom, value)?;
            return assign(m, result, eq);
        }
        if is_positive {
            return Ok(result);
        }
        let not_result = mk_not(m, result)?;
        let negated = assign(m, -1, not_result)?;
        m.dec_ref(result)?;
        Ok(negated)
    }

    // der_sort_vars: the definitions in an order where each only uses the ones before it, dropping
    // the definitions on a cycle.
    fn sort_vars(&mut self, m: &AstManager) -> Result<(), SmtError> {
        self.order = Vec::new();
        let mut is_found = false;
        for index in 0..self.map.len() {
            let definition = self.map[index];
            if definition == -1
                || m.has_quantifier_flags[definition as usize] != 0
                || is_occurring(
                    m,
                    m.values[self.inx2var[index] as usize] as usize,
                    definition,
                )?
            {
                self.map[index] = -1;
            } else {
                is_found = true;
            }
        }
        if !is_found {
            return Ok(());
        }
        let mut visiting = HashSet::new();
        let mut done = HashSet::new();
        for index in 0..self.map.len() {
            if get_at(&self.map, index) == -1 {
                continue;
            }
            let mut todo: Vec<(Expr, usize)> = vec![(self.inx2var[index], 0)];
            while let Some(&(expr, child)) = todo.last() {
                let top = todo.len() - 1;
                if done.contains(&expr) {
                    todo.pop();
                    continue;
                }
                if m.kinds[expr as usize] == KIND_VAR {
                    let var_index = m.values[expr as usize] as usize;
                    if child == 0 && get_at(&self.map, var_index) != -1 {
                        if !visiting.contains(&expr) {
                            visiting.insert(expr);
                            todo[top].1 = 1;
                            todo.push((get_at(&self.map, var_index), 0));
                            continue;
                        }
                        visiting.remove(&expr);
                        self.map[var_index] = -1;
                    } else if child == 1 {
                        visiting.remove(&expr);
                        if get_at(&self.map, var_index) != -1 {
                            self.order.push(var_index);
                        }
                    }
                } else {
                    let mut is_pushed = false;
                    while todo[top].1 < m.get_num_args(expr) && !is_pushed {
                        let arg = m.get_arg(expr, todo[top].1);
                        todo[top].1 += 1;
                        if !done.contains(&arg) {
                            todo.push((arg, 0));
                            is_pushed = true;
                        }
                    }
                    if is_pushed {
                        continue;
                    }
                }
                done.insert(expr);
                todo.pop();
            }
        }
        Ok(())
    }

    fn create_substitution(&mut self, m: &mut AstManager, size: usize) -> Result<(), SmtError> {
        self.subst_map.reset(m)?;
        self.subst_map.resize(m, size)?;
        self.subst.reset(m)?;
        self.subst.set_inv_bindings(&self.subst_map.items);
        for index in self.order.clone() {
            let definition = self.map[index];
            let result = if m.is_ground_app(definition) {
                assign(m, -1, definition)?
            } else {
                self.subst.rewrite(m, definition)?
            };
            let position = size - index - 1;
            self.subst.update_inv_binding_at(position, result);
            self.subst_map.set_owned(m, position, result)?;
        }
        Ok(())
    }

    // is_unconstrained: an integer variable that no other conjunct mentions.
    fn is_unconstrained(
        &self,
        m: &AstManager,
        variable: Expr,
        term: Expr,
        position: usize,
        conjs: &[Expr],
    ) -> Result<bool, SmtError> {
        let index = m.values[variable as usize] as usize;
        if m.sorts[variable as usize] != SORT_INT || is_occurring(m, index, term)? {
            return Ok(false);
        }
        for (other, conj) in conjs.iter().copied().enumerate() {
            if other != position && is_occurring(m, index, conj)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    // remove_unconstrained: a disequality on an unconstrained integer variable holds.
    fn remove_unconstrained(
        &self,
        m: &mut AstManager,
        conjs: &mut RefVector,
    ) -> Result<bool, SmtError> {
        let mut is_reduced = false;
        let mut is_changed = true;
        while is_changed {
            is_changed = false;
            for position in 0..conjs.len() {
                let conj = conjs.items[position];
                if !m.is_not(conj) || m.get_op(m.get_arg(conj, 0)) != OP_EQ {
                    continue;
                }
                let lhs = m.get_arg(m.get_arg(conj, 0), 0);
                let rhs = m.get_arg(m.get_arg(conj, 0), 1);
                if (self.is_variable(m, lhs)
                    && self.is_unconstrained(m, lhs, rhs, position, &conjs.items)?)
                    || (self.is_variable(m, rhs)
                        && self.is_unconstrained(m, rhs, lhs, position, &conjs.items)?)
                {
                    let true_expr = m.true_expr;
                    conjs.set(m, position, true_expr)?;
                    is_reduced = true;
                    is_changed = true;
                }
            }
        }
        Ok(is_reduced)
    }
}
