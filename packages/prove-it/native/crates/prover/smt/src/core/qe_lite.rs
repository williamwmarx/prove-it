//! Ported from Z3 (src/qe/lite/qe_lite_tactic.cpp, src/qe/mbp/mbp_solve_plugin.cpp), MIT license,
//! through `qe-lite.ts`. The qe-lite tactic of Z3's ufnia strategy: each quantifier, innermost
//! first, loses the variables that its body defines by an equality, Fourier-Motzkin elimination
//! removes integer variables that only occur in bounds, and a quantifier over a small integer range
//! becomes a finite disjunction. Like Z3, the port counts references, so that expressions are
//! created and deleted in Z3's order. Arrays, bit-vectors and datatypes are not ported, as tlapm's
//! encoding does not produce them.
//!
//! # Design
//!
//! The TypeScript's `ElimStar` is a rewriter whose `reduceQuantifier` calls back into `QeLite`,
//! which owns it. Here qe_lite::impl's state (eq_der, fm and the rewriter) is the configuration
//! [`ElimCfg`] of the rewriter `QeLite` owns, so the hook reaches it as `self`. The recursions of
//! `reduce_formula` and `collect_negative_equalities` stop past `MAX_RECURSION_DEPTH`
//! (design/smt-core.md, recursion).

use prove_num::Int;

use crate::core::ast::{
    AstManager, Expr, KIND_QUANTIFIER, KIND_VAR, OP_AND, OP_EQ, OP_GE, OP_GT, OP_LE, OP_LT, OP_NOT,
    OP_OR, SORT_BOOL, SORT_INT, Sort,
};
use crate::core::ast_util::{flatten_and_vector, flatten_or_vector, push_not_owned};
use crate::core::der::is_occurring;
use crate::core::expr_ref::{assign, assign_owned, release};
use crate::core::expr_safe_replace::ExprSafeReplace;
use crate::core::goal::Goal;
use crate::core::qe_lite_der::EqDer;
use crate::core::qe_lite_fm::Fm;
use crate::core::ref_vector::RefVector;
use crate::core::rewriter::{Rewriter, TACTIC_REWRITER_OPTIONS};
use crate::core::rewriter_tpl::{InvVarShifter, MAX_RECURSION_DEPTH, RewriterConfig, RewriterTpl};
use crate::core::var_subst::{VarSubst, collect_used_vars};
use crate::util::error::SmtError;
use crate::util::hashtable::ObjHashtable;

// qe_lite's EXPAND_BOUND_LIMIT: the largest integer range that is expanded.
const EXPAND_BOUND_LIMIT: i64 = 10000;

fn mk_recursion_error() -> SmtError {
    SmtError::Unsupported("qe-lite nests too deeply".into())
}

// An inclusive integer bound of a variable.
struct Bound {
    is_lower: bool,
    value: Int,
}

/// elim_cfg with qe_lite::impl's state: rewrites the quantifiers bottom-up.
#[derive(Clone, Debug)]
pub struct ElimCfg {
    der: EqDer,
    fm: Fm,
    rewriter: Rewriter,
}

impl RewriterConfig for ElimCfg {
    fn reduce_quantifier(
        &mut self,
        m: &mut AstManager,
        expr: Expr,
        body: Expr,
        patterns: &[Expr],
    ) -> Result<Expr, SmtError> {
        self.reduce_quantifier_core(m, expr, body, patterns)
    }
}

impl ElimCfg {
    // bool_rewriter's mk_and and mk_or, with a reference to the result.
    fn mk_and(&mut self, m: &mut AstManager, args: &[Expr]) -> Result<Expr, SmtError> {
        let rewriter = &mut self.rewriter;
        m.with_temporaries(|m| rewriter.mk_and(m, args))
    }

    fn mk_or(&mut self, m: &mut AstManager, args: &[Expr]) -> Result<Expr, SmtError> {
        let rewriter = &mut self.rewriter;
        m.with_temporaries(|m| rewriter.mk_or(m, args))
    }

    // elim_cfg::reduce_quantifier.
    fn reduce_quantifier_core(
        &mut self,
        m: &mut AstManager,
        expr: Expr,
        body: Expr,
        patterns: &[Expr],
    ) -> Result<Expr, SmtError> {
        let data = m.get_quantifier(expr)?.clone();
        let mut result = assign(m, -1, body)?;
        if data.is_forall {
            let negation = m.mk_app(OP_NOT, &[result], SORT_BOOL)?;
            result = assign(m, result, negation)?;
        }
        result = self.reduce_formula(m, data.sorts.len() as i32, result, 0)?;
        result = self.eliminate_diseq_vars(m, &data.sorts, result)?;
        let mut expanded = self.try_expand_bounded_quantifier(m, &data.sorts, result)?;
        if expanded != -1 {
            if data.is_forall {
                let pushed = push_not_owned(m, expanded)?;
                expanded = assign_owned(m, expanded, pushed)?;
            }
            let rewritten = self.rewriter.rewrite(m, expanded)?;
            result = assign_owned(m, result, rewritten)?;
            m.dec_ref(expanded)?;
            return Ok(result);
        }
        if data.is_forall {
            let pushed = push_not_owned(m, result)?;
            result = assign_owned(m, result, pushed)?;
        }
        let mut updated_data = data;
        updated_data.body = result;
        updated_data.patterns = patterns.to_vec();
        let quantifier = m.mk_quantifier(updated_data)?;
        let updated = assign(m, -1, quantifier)?;
        let rewritten = self.rewriter.rewrite(m, updated)?;
        result = assign_owned(m, result, rewritten)?;
        m.dec_ref(updated)?;
        Ok(result)
    }

    // operator()(index_set, index_of_bound, expr_ref&): each disjunct is a conjunction to reduce.
    // The formula comes with a reference, and so does the result.
    fn reduce_formula(
        &mut self,
        m: &mut AstManager,
        num_vars: i32,
        formula: Expr,
        depth: usize,
    ) -> Result<Expr, SmtError> {
        if depth >= MAX_RECURSION_DEPTH {
            return Err(mk_recursion_error());
        }
        let mut disjs = RefVector::new();
        let mut conjs = RefVector::new();
        disjs.push(m, formula);
        flatten_or_vector(m, &mut disjs)?;
        let mut result = formula;
        let size = disjs.len();
        for index in 0..size {
            conjs.reset(m)?;
            conjs.push(m, disjs.items[index]);
            self.reduce_conjs(m, num_vars, &mut conjs, depth)?;
            let conjunction = self.mk_and(m, &conjs.items)?;
            result = assign_owned(m, result, conjunction)?;
            disjs.set_owned(m, index, result)?;
            result = -1;
        }
        let disjunction = self.mk_or(m, &disjs.items)?;
        result = assign_owned(m, result, disjunction)?;
        conjs.reset(m)?;
        disjs.reset(m)?;
        Ok(result)
    }

    // operator()(index_set, index_of_bound, expr_ref_vector&): a single non-ground conjunct is
    // reduced as a disjunction, and otherwise eq_der and fm run.
    fn reduce_conjs(
        &mut self,
        m: &mut AstManager,
        num_vars: i32,
        fmls: &mut RefVector,
        depth: usize,
    ) -> Result<(), SmtError> {
        flatten_and_vector(m, fmls)?;
        let non_ground: Vec<usize> = fmls
            .items
            .iter()
            .enumerate()
            .filter(|(_, fml)| !m.is_ground_app(**fml))
            .map(|(index, _)| index)
            .collect();
        if fmls.len() > 1 && non_ground.len() == 1 {
            let index = non_ground[0];
            let formula = assign(m, -1, fmls.items[index])?;
            let reduced = self.reduce_formula(m, num_vars, formula, depth + 1)?;
            fmls.set(m, index, reduced)?;
            m.dec_ref(reduced)?;
            return Ok(());
        }
        self.der.num_vars = num_vars;
        self.fm.num_vars = num_vars;
        self.der.apply(m, fmls)?;
        self.fm.apply(m, fmls)?;
        // ar_der checks the limit for each formula. tlapm's formulas have no arrays for it to
        // solve.
        for _ in 0..fmls.len() {
            m.limit.checkpoint()?;
        }
        Ok(())
    }

    // collect_negative_equalities: whether every occurrence of the variable is in a negative
    // equality with a term without it, or outside any equality.
    fn collect_negative_equalities(
        &self,
        m: &AstManager,
        expr: Expr,
        index: usize,
        is_positive: bool,
        equalities: &mut ObjHashtable,
        depth: usize,
    ) -> Result<bool, SmtError> {
        if depth >= MAX_RECURSION_DEPTH {
            return Err(mk_recursion_error());
        }
        if m.is_ground_app(expr) {
            return Ok(true);
        }
        let kind = m.kinds[expr as usize];
        if kind == KIND_VAR {
            return Ok(m.values[expr as usize] as usize != index);
        }
        if kind == KIND_QUANTIFIER {
            let data = m.get_quantifier(expr)?;
            return Ok(!is_occurring(m, index + data.sorts.len(), data.body)?);
        }
        let op = m.get_op(expr);
        if m.is_not(expr) {
            return self.collect_negative_equalities(
                m,
                m.get_arg(expr, 0),
                index,
                !is_positive,
                equalities,
                depth + 1,
            );
        }
        if op == OP_AND || op == OP_OR {
            for arg_index in 0..m.get_num_args(expr) {
                if !self.collect_negative_equalities(
                    m,
                    m.get_arg(expr, arg_index),
                    index,
                    is_positive,
                    equalities,
                    depth + 1,
                )? {
                    return Ok(false);
                }
            }
            return Ok(true);
        }
        if op == OP_EQ {
            let is_var_at = |term: Expr| {
                m.kinds[term as usize] == KIND_VAR && m.values[term as usize] as usize == index
            };
            let is_left_var = is_var_at(m.get_arg(expr, 0));
            if is_left_var != is_var_at(m.get_arg(expr, 1)) {
                let value = if is_left_var {
                    m.get_arg(expr, 1)
                } else {
                    m.get_arg(expr, 0)
                };
                if !is_positive && !is_occurring(m, index, value)? {
                    equalities.insert(expr as u32, m.hashes[expr as usize]);
                    return Ok(true);
                }
            }
        }
        Ok(!is_occurring(m, index, expr)?)
    }

    // eliminate_diseq_vars: an integer variable that occurs only in negative equalities can avoid
    // every value they name, so those equalities are false. The body comes with a reference, and
    // so does the result.
    fn eliminate_diseq_vars(
        &mut self,
        m: &mut AstManager,
        sorts: &[Sort],
        body: Expr,
    ) -> Result<Expr, SmtError> {
        let mut replace = ExprSafeReplace::new();
        let mut is_changed = false;
        for index in 0..sorts.len() {
            let mut equalities = ObjHashtable::new();
            if self.collect_negative_equalities(m, body, index, true, &mut equalities, 0)?
                && !equalities.is_empty()
                && sorts[sorts.len() - index - 1] == SORT_INT
            {
                let false_expr = m.false_expr;
                for equality in equalities.iter().collect::<Vec<_>>() {
                    replace.insert(m, equality as Expr, false_expr);
                }
                is_changed = true;
            }
        }
        if !is_changed {
            replace.release(m)?;
            return Ok(body);
        }
        let replaced = replace.apply(m, body)?;
        let rewritten = self.rewriter.rewrite(m, replaced)?;
        let result = assign_owned(m, body, rewritten)?;
        m.dec_ref(replaced)?;
        replace.release(m)?;
        Ok(result)
    }

    // extract_var_bound: an inclusive integer bound of the variable that a conjunct states.
    fn get_bound(&self, m: &AstManager, expr: Expr, index: usize) -> Option<Bound> {
        let is_negated = m.is_not(expr);
        let atom = if is_negated { m.get_arg(expr, 0) } else { expr };
        let op = m.get_op(atom);
        if op != OP_LE && op != OP_GE && op != OP_LT && op != OP_GT {
            return None;
        }
        let is_swapped = op == OP_GE || op == OP_GT;
        let is_strict = op == OP_LT || op == OP_GT;
        let lhs = m.get_arg(atom, if is_swapped { 1 } else { 0 });
        let rhs = m.get_arg(atom, if is_swapped { 0 } else { 1 });
        if m.sorts[lhs as usize] != SORT_INT {
            return None;
        }
        let is_index = |term: Expr| {
            m.kinds[term as usize] == KIND_VAR && m.values[term as usize] as usize == index
        };
        let is_var_on_left = is_index(lhs) && m.is_numeral(rhs);
        if !is_var_on_left && !(is_index(rhs) && m.is_numeral(lhs)) {
            return None;
        }
        let numeral = m
            .get_numeral_value(if is_var_on_left { rhs } else { lhs })
            .clone();
        let one = Int::from(1);
        let value = match (is_var_on_left, is_strict) {
            (true, true) => numeral - &one,
            (false, true) => numeral + &one,
            _ => numeral,
        };
        if !is_negated {
            return Some(Bound {
                is_lower: !is_var_on_left,
                value,
            });
        }
        Some(Bound {
            is_lower: is_var_on_left,
            value: if is_var_on_left {
                value + &one
            } else {
                value - &one
            },
        })
    }

    // try_expand_bounded_quantifier: the disjunction of the body over every value of the integer
    // variables when their ranges are small, with a reference, or -1.
    fn try_expand_bounded_quantifier(
        &mut self,
        m: &mut AstManager,
        sorts: &[Sort],
        body: Expr,
    ) -> Result<Expr, SmtError> {
        let num_decls = sorts.len();
        if num_decls == 0 {
            return Ok(-1);
        }
        let used = collect_used_vars(m, body, num_decls)?;
        let remaining: Vec<usize> = used
            .iter()
            .enumerate()
            .filter(|(_, is_used)| **is_used)
            .map(|(index, _)| index)
            .collect();
        if remaining.is_empty() {
            return Ok(-1);
        }
        // Z3 checks the declaration at position i for the variable with de Bruijn index i, which
        // is another variable's sort. This port checks the variable's own sort.
        if remaining
            .iter()
            .any(|index| sorts[num_decls - 1 - index] != SORT_INT)
        {
            return Ok(-1);
        }
        let mut conjs = RefVector::new();
        conjs.push(m, body);
        flatten_and_vector(m, &mut conjs)?;
        let mut lowers: Vec<Option<Int>> = vec![None; num_decls];
        let mut uppers: Vec<Option<Int>> = vec![None; num_decls];
        let mut is_bound_conj = Vec::with_capacity(conjs.len());
        for conj in conjs.items.iter().copied() {
            let mut is_bound = false;
            for index in remaining.iter().copied() {
                let Some(bound) = self.get_bound(m, conj, index) else {
                    continue;
                };
                let bounds = if bound.is_lower {
                    &mut lowers
                } else {
                    &mut uppers
                };
                let is_better = match &bounds[index] {
                    None => true,
                    Some(old) => {
                        if bound.is_lower {
                            bound.value > *old
                        } else {
                            bound.value < *old
                        }
                    }
                };
                if is_better {
                    bounds[index] = Some(bound.value);
                }
                is_bound = true;
            }
            is_bound_conj.push(is_bound);
        }
        let mut domain_size = Int::from(1);
        for index in remaining.iter().copied() {
            let (Some(lower), Some(upper)) = (&lowers[index], &uppers[index]) else {
                conjs.reset(m)?;
                return Ok(-1);
            };
            let size = upper - lower + Int::from(1);
            if size <= 0 {
                conjs.reset(m)?;
                let false_expr = m.false_expr;
                return assign(m, -1, false_expr);
            }
            domain_size *= size;
            if domain_size > EXPAND_BOUND_LIMIT {
                conjs.reset(m)?;
                return Ok(-1);
            }
        }
        let mut payload = RefVector::new();
        for (position, conj) in conjs.items.iter().copied().enumerate() {
            if !is_bound_conj[position] {
                payload.push(m, conj);
            }
        }
        let mut subst_map = RefVector::new();
        subst_map.resize(m, num_decls)?;
        // Like Z3, an unused variable keeps the sort of the declaration at its index.
        for (index, is_used) in used.iter().copied().enumerate() {
            if !is_used {
                let variable = m.mk_var(index as i32, sorts[index]);
                subst_map.set(m, index, variable)?;
            }
        }
        let zero = Int::from(0);
        let get_bound_value =
            |bounds: &[Option<Int>], index: usize| bounds[index].clone().unwrap_or(zero.clone());
        let mut values: Vec<Int> = remaining
            .iter()
            .map(|index| get_bound_value(&lowers, *index))
            .collect();
        let mut subst = VarSubst::new(m, false);
        let mut shifter = InvVarShifter::new(m);
        let mut disjuncts = RefVector::new();
        loop {
            for (position, index) in remaining.iter().copied().enumerate() {
                let numeral = m.mk_numeral(&values[position]);
                subst_map.set(m, index, numeral)?;
            }
            let mut inst_conjs = RefVector::new();
            for conj in payload.items.clone() {
                let mut instance = subst.apply(m, conj, &subst_map.items)?;
                let shifted = shifter.shift(m, instance, num_decls as i32)?;
                instance = assign_owned(m, instance, shifted)?;
                inst_conjs.push(m, instance);
                m.dec_ref(instance)?;
            }
            let inst_body = self.mk_and(m, &inst_conjs.items)?;
            disjuncts.push(m, inst_body);
            m.dec_ref(inst_body)?;
            inst_conjs.reset(m)?;
            // The rightmost variable moves first.
            let mut is_done = true;
            for position in (0..remaining.len()).rev() {
                values[position] += Int::from(1);
                if values[position] <= get_bound_value(&uppers, remaining[position]) {
                    is_done = false;
                    break;
                }
                values[position] = get_bound_value(&lowers, remaining[position]);
            }
            if is_done {
                break;
            }
        }
        let result = self.mk_or(m, &disjuncts.items)?;
        disjuncts.reset(m)?;
        shifter.release(m)?;
        subst.release(m)?;
        subst_map.reset(m)?;
        payload.reset(m)?;
        conjs.reset(m)?;
        Ok(result)
    }
}

// qe_lite::impl.
struct QeLite {
    elim_star: RewriterTpl<ElimCfg>,
}

impl QeLite {
    fn new(m: &AstManager) -> QeLite {
        QeLite {
            elim_star: RewriterTpl::new(
                m,
                ElimCfg {
                    der: EqDer::new(m),
                    fm: Fm::new(),
                    rewriter: Rewriter::new(m, TACTIC_REWRITER_OPTIONS, false),
                },
            ),
        }
    }

    // operator()(expr_ref&): the result comes with a reference, which the caller releases.
    fn apply(&mut self, m: &mut AstManager, formula: Expr) -> Result<Expr, SmtError> {
        self.elim_star.rewrite(m, formula)
    }

    // ~impl. elim_cfg releases nothing of its own, so the rewriter's caches go after the
    // rewriter's, as the TypeScript releases them.
    fn release(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.elim_star.cfg.rewriter.release(m)?;
        self.elim_star.engine.release(m)?;
        self.elim_star.cfg.fm.release(m)?;
        self.elim_star.cfg.der.release(m)
    }
}

/// qe_lite_simplifier::reduce in a dependent_expr_state_tactic, on each formula with a
/// quantifier. The tactic's m_dep holds the formula it read last, until the tactic is done.
pub fn apply_qe_lite(m: &mut AstManager, goal: &mut Goal) -> Result<(), SmtError> {
    let mut qe = QeLite::new(m);
    let mut dep = -1;
    for form in goal.forms.items.clone() {
        dep = assign(m, dep, form)?;
    }
    if goal
        .forms
        .items
        .iter()
        .any(|form| m.has_quantifier_flags[*form as usize] != 0)
    {
        let mut formula = -1;
        let size = goal.forms.len();
        let mut index = 0;
        while index < size && !goal.is_inconsistent {
            let form = goal.forms.items[index];
            dep = assign(m, dep, form)?;
            if m.has_quantifier_flags[form as usize] != 0 {
                formula = assign(m, formula, form)?;
                let reduced = qe.apply(m, formula)?;
                formula = assign_owned(m, formula, reduced)?;
                if formula != form {
                    goal.update(m, index, formula)?;
                }
            }
            // The iterator of the simplifier's indices counts a step after each formula.
            m.limit.checkpoint()?;
            index += 1;
        }
        release(m, formula)?;
    }
    goal.elim_true(m)?;
    goal.elim_redundancies(m)?;
    qe.release(m)?;
    release(m, dep)
}
