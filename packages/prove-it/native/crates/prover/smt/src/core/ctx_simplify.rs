//! Ported from Z3 (src/tactic/core/ctx_simplify_tactic.cpp, src/ast/num_occurs.cpp,
//! src/tactic/goal_num_occurs.cpp), MIT license, through `ctx-simplify.ts`. The ctx-simplify
//! tactic with ctx_propagate_assertions: in the context of a formula or a branch, a shared term
//! that the context asserts becomes true, false or the value it equals.
//!
//! The recursion of `simplify` stops at `MAX_DEPTH`, as in Z3, so it needs no depth counter of the
//! port's own.

use std::collections::{HashMap, HashSet};

use crate::core::ast::{AstManager, Decl, Expr, KIND_APP, OP_AND, OP_EQ, OP_ITE, OP_OR, Sort};
use crate::core::goal::Goal;
use crate::core::ref_vector::RefVector;
use crate::core::rewriter::{Rewriter, TACTIC_REWRITER_OPTIONS};
use crate::util::error::SmtError;

// The max_depth and max_steps that mk_quant_preprocessor gives ctx-simplify.
const MAX_DEPTH: u32 = 30;
const MAX_STEPS: u64 = 5_000_000;

#[derive(Clone, Copy, Debug)]
struct CachedResult {
    to: Expr,
    level: usize,
}

struct CtxSimplifier {
    // goal_num_occurs: how often each term with more than one reference occurs outside
    // quantifiers. m_pinned holds the formulas it counted.
    occs: HashMap<Expr, u64>,
    pinned: RefVector,
    // ctx_propagate_assertions: the value of each shared term in the current context, and the
    // terms given one, which the trail holds.
    assertions: HashMap<Expr, Expr>,
    trail: RefVector,
    scopes: Vec<usize>,
    // m_cache: the results of a shared term, the innermost level last, and the terms cached at
    // each level. A cached term and its results are held.
    cache: HashMap<Expr, Vec<CachedResult>>,
    cache_undo: Vec<Vec<Expr>>,
    depth: u32,
    num_steps: u64,
    // m_mk_app: mk_simplified_app, one reduction of the theory rewriters.
    rewriter: Rewriter,
}

impl CtxSimplifier {
    fn new(m: &AstManager) -> CtxSimplifier {
        CtxSimplifier {
            occs: HashMap::new(),
            pinned: RefVector::new(),
            assertions: HashMap::new(),
            trail: RefVector::new(),
            scopes: Vec::new(),
            cache: HashMap::new(),
            cache_undo: Vec::new(),
            depth: 0,
            num_steps: 0,
            rewriter: Rewriter::new(m, TACTIC_REWRITER_OPTIONS, false),
        }
    }

    // operator(): a forward pass over the formulas, then a backward pass that also counts the
    // occurrences of the forward pass's results.
    fn apply(&mut self, m: &mut AstManager, goal: &mut Goal) -> Result<(), SmtError> {
        if goal.is_inconsistent {
            return Ok(());
        }
        self.count_occurrences(m, goal);
        let size = goal.forms.len();
        let mut index = 0;
        while !goal.is_inconsistent && index < size {
            self.depth = 0;
            let result = self.simplify(m, goal.forms.items[index])?;
            if index < size - 1 && !m.is_true(result) && !m.is_false(result) {
                self.assert_expr(m, result, false);
            }
            goal.update(m, index, result)?;
            m.dec_ref(result)?;
            index += 1;
        }
        self.pop(m, self.scopes.len())?;
        self.count_occurrences(m, goal);
        let mut index = goal.forms.len();
        while !goal.is_inconsistent && index > 0 {
            self.depth = 0;
            index -= 1;
            let result = self.simplify(m, goal.forms.items[index])?;
            if index > 0 && !m.is_true(result) && !m.is_false(result) {
                self.assert_expr(m, result, false);
            }
            goal.update(m, index, result)?;
            m.dec_ref(result)?;
        }
        self.pop(m, self.scopes.len())
    }

    // cleanup: ~imp releases the cache, and then goal_num_occurs its formulas.
    fn release(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.restore_cache(m, 0)?;
        self.pinned.reset(m)
    }

    // goal_num_occurs::operator() with ignore_ref_count1 and ignore_quantifiers.
    fn count_occurrences(&mut self, m: &mut AstManager, goal: &Goal) {
        let mut visited = HashSet::new();
        let mut stack: Vec<Expr> = Vec::new();
        let occs = &mut self.occs;
        let mut visit = |m: &AstManager, expr: Expr, stack: &mut Vec<Expr>| {
            if m.get_ref_count(expr) > 1 {
                *occs.entry(expr).or_insert(0) += 1;
            }
            if visited.contains(&expr) {
                return;
            }
            visited.insert(expr);
            stack.push(expr);
        };
        for form in goal.forms.items.iter().copied() {
            self.pinned.push(m, form);
            visit(m, form, &mut stack);
            while let Some(expr) = stack.pop() {
                if m.kinds[expr as usize] != KIND_APP {
                    continue;
                }
                for index in (0..m.get_num_args(expr)).rev() {
                    visit(m, m.get_arg(expr, index), &mut stack);
                }
            }
        }
    }

    fn is_shared(&self, m: &AstManager, expr: Expr) -> bool {
        m.get_ref_count(expr) > 1 && self.occs.get(&expr).copied().unwrap_or(0) > 1
    }

    // ctx_propagate_assertions::assert_expr: a shared atom gets its truth value, and a shared term
    // that a positive equality equates with a value gets the value.
    fn assert_expr(&mut self, m: &mut AstManager, expr: Expr, is_negated: bool) {
        let mut atom = expr;
        let mut is_false = is_negated;
        while m.is_not(atom) {
            atom = m.get_arg(atom, 0);
            is_false = !is_false;
        }
        let mut is_making_scope = true;
        if self.is_shared(m, atom) || self.is_shared(m, expr) {
            self.scopes.push(self.trail.len());
            is_making_scope = false;
            let value = if is_false { m.false_expr } else { m.true_expr };
            self.assert_eq_core(m, atom, value);
        }
        if is_false || m.get_op(atom) != OP_EQ {
            return;
        }
        let lhs = m.get_arg(atom, 0);
        let rhs = m.get_arg(atom, 1);
        let is_rhs_value = m.is_unique_value(rhs);
        if !is_rhs_value && !m.is_unique_value(lhs) {
            return;
        }
        let term = if is_rhs_value { lhs } else { rhs };
        if !self.is_shared(m, term) {
            return;
        }
        if is_making_scope {
            self.scopes.push(self.trail.len());
        }
        self.assert_eq_core(m, term, if is_rhs_value { rhs } else { lhs });
    }

    fn assert_eq_core(&mut self, m: &mut AstManager, term: Expr, value: Expr) {
        if self.assertions.contains_key(&term) {
            return;
        }
        self.assertions.insert(term, value);
        self.trail.push(m, term);
    }

    // pop: the assertions of the scopes, and then the results cached in them, the innermost
    // first.
    fn pop(&mut self, m: &mut AstManager, num_scopes: usize) -> Result<(), SmtError> {
        if num_scopes == 0 {
            return Ok(());
        }
        let mut level = self.scopes.len();
        let size = self.scopes[level - num_scopes];
        while self.trail.len() > size {
            self.assertions
                .remove(&self.trail.items[self.trail.len() - 1]);
            self.trail.pop(m)?;
        }
        self.scopes.truncate(self.scopes.len() - num_scopes);
        for _ in 0..num_scopes {
            self.restore_cache(m, level)?;
            level -= 1;
        }
        Ok(())
    }

    fn restore_cache(&mut self, m: &mut AstManager, level: usize) -> Result<(), SmtError> {
        let Some(keys) = self.cache_undo.get_mut(level) else {
            return Ok(());
        };
        let keys = std::mem::take(keys);
        for key in keys.iter().rev() {
            let Some(results) = self.cache.get_mut(key) else {
                return Err(SmtError::Invariant(
                    "an undone key has no cached results".into(),
                ));
            };
            let Some(result) = results.pop() else {
                return Err(SmtError::Invariant("an undone key has no result".into()));
            };
            let is_empty = results.is_empty();
            m.dec_ref(result.to)?;
            if !is_empty {
                continue;
            }
            self.cache.remove(key);
            m.dec_ref(*key)?;
        }
        Ok(())
    }

    fn cache_result(&mut self, m: &mut AstManager, from: Expr, to: Expr) {
        if !self.is_shared(m, from) {
            return;
        }
        let level = self.scopes.len();
        match self.cache.get_mut(&from) {
            None => {
                self.cache.insert(from, vec![CachedResult { to, level }]);
                m.inc_ref(from);
            }
            Some(results) => results.push(CachedResult { to, level }),
        }
        m.inc_ref(to);
        if self.cache_undo.len() <= level {
            self.cache_undo.resize(level + 1, Vec::new());
        }
        self.cache_undo[level].push(from);
    }

    fn get_cached(&self, expr: Expr) -> Option<Expr> {
        self.cache
            .get(&expr)
            .and_then(|results| results.last())
            .filter(|top| top.level == self.scopes.len())
            .map(|top| top.to)
    }

    // m_mk_app, with a reference to the result.
    fn mk_app(
        &mut self,
        m: &mut AstManager,
        decl: Decl,
        args: &[Expr],
        sort: Sort,
    ) -> Result<Expr, SmtError> {
        let rewriter = &mut self.rewriter;
        m.with_temporaries(|m| rewriter.mk_app(m, decl, args, sort))
    }

    // The result comes with a reference, which the caller releases.
    fn simplify(&mut self, m: &mut AstManager, expr: Expr) -> Result<Expr, SmtError> {
        if self.depth >= MAX_DEPTH
            || self.num_steps >= MAX_STEPS
            || m.kinds[expr as usize] != KIND_APP
        {
            m.inc_ref(expr);
            return Ok(expr);
        }
        // tactic::checkpoint.
        m.limit.checkpoint()?;
        let known = self
            .get_cached(expr)
            .or_else(|| self.assertions.get(&expr).copied());
        if let Some(known) = known {
            m.inc_ref(known);
            return Ok(known);
        }
        self.num_steps += 1;
        self.depth += 1;
        let op = m.get_op(expr);
        let result = if op == OP_OR || op == OP_AND {
            self.simplify_or_and(m, expr, op == OP_OR)?
        } else if op == OP_ITE {
            self.simplify_ite(m, expr)?
        } else {
            self.simplify_app(m, expr)?
        };
        self.depth -= 1;
        Ok(result)
    }

    // simplify_or_and: each argument is simplified in the context of the others before it, then of
    // those after it. A disjunct is asserted false and a conjunct true.
    fn simplify_or_and(
        &mut self,
        m: &mut AstManager,
        expr: Expr,
        is_or: bool,
    ) -> Result<Expr, SmtError> {
        let level = self.scopes.len();
        let is_neutral = |m: &AstManager, arg: Expr| {
            if is_or {
                m.is_false(arg)
            } else {
                m.is_true(arg)
            }
        };
        let is_absorbing = |m: &AstManager, arg: Expr| {
            if is_or {
                m.is_true(arg)
            } else {
                m.is_false(arg)
            }
        };
        let mut is_modified = false;
        let mut passes = [RefVector::new(), RefVector::new()];
        for pass in 0..2 {
            let args = if pass == 0 {
                m.get_args(expr)
            } else {
                passes[0].items.iter().rev().copied().collect()
            };
            for (index, arg) in args.iter().copied().enumerate() {
                let new_arg = self.simplify(m, arg)?;
                if new_arg != arg {
                    is_modified = true;
                }
                if index < args.len() - 1 && !m.is_true(new_arg) && !m.is_false(new_arg) {
                    self.assert_expr(m, new_arg, is_or);
                }
                if is_neutral(m, new_arg) {
                    is_modified = true;
                    m.dec_ref(new_arg)?;
                    continue;
                }
                if is_absorbing(m, new_arg) {
                    self.pop(m, self.scopes.len() - level)?;
                    self.cache_result(m, expr, new_arg);
                    passes[1].reset(m)?;
                    passes[0].reset(m)?;
                    return Ok(new_arg);
                }
                passes[pass].push_owned(new_arg);
            }
            self.pop(m, self.scopes.len() - level)?;
        }
        let new_args = &passes[1].items;
        let result = if !is_modified {
            expr
        } else if new_args.is_empty() {
            if is_or { m.false_expr } else { m.true_expr }
        } else if new_args.len() == 1 {
            new_args[0]
        } else {
            -1
        };
        if result != -1 {
            m.inc_ref(result);
        }
        let simplified = if result == -1 {
            let reversed: Vec<Expr> = new_args.iter().rev().copied().collect();
            let decl = m.decls[expr as usize];
            let sort = m.sorts[expr as usize];
            self.mk_app(m, decl, &reversed, sort)?
        } else {
            result
        };
        self.cache_result(m, expr, simplified);
        passes[1].reset(m)?;
        passes[0].reset(m)?;
        Ok(simplified)
    }

    // simplify_ite: the branches are simplified in the context of the condition and its negation.
    fn simplify_ite(&mut self, m: &mut AstManager, expr: Expr) -> Result<Expr, SmtError> {
        let condition = m.get_arg(expr, 0);
        let then_branch = m.get_arg(expr, 1);
        let else_branch = m.get_arg(expr, 2);
        let level = self.scopes.len();
        let new_condition = self.simplify(m, condition)?;
        let result = if m.is_true(new_condition) {
            self.simplify(m, then_branch)?
        } else if m.is_false(new_condition) {
            self.simplify(m, else_branch)?
        } else {
            self.assert_expr(m, new_condition, false);
            let new_then = self.simplify(m, then_branch)?;
            self.pop(m, self.scopes.len() - level)?;
            self.assert_expr(m, new_condition, true);
            let new_else = self.simplify(m, else_branch)?;
            self.pop(m, self.scopes.len() - level)?;
            let result =
                if condition == new_condition && then_branch == new_then && else_branch == new_else
                {
                    m.inc_ref(expr);
                    expr
                } else if new_then == new_else {
                    m.inc_ref(new_then);
                    new_then
                } else {
                    let decl = m.decls[expr as usize];
                    let sort = m.sorts[expr as usize];
                    self.mk_app(m, decl, &[new_condition, new_then, new_else], sort)?
                };
            m.dec_ref(new_else)?;
            m.dec_ref(new_then)?;
            result
        };
        self.cache_result(m, expr, result);
        m.dec_ref(new_condition)?;
        Ok(result)
    }

    fn simplify_app(&mut self, m: &mut AstManager, expr: Expr) -> Result<Expr, SmtError> {
        let mut new_args = RefVector::new();
        let mut is_modified = false;
        for index in 0..m.get_num_args(expr) {
            let arg = m.get_arg(expr, index);
            let new_arg = self.simplify(m, arg)?;
            if new_arg != arg {
                is_modified = true;
            }
            new_args.push_owned(new_arg);
        }
        if !is_modified {
            m.inc_ref(expr);
        }
        let result = if is_modified {
            let decl = m.decls[expr as usize];
            let sort = m.sorts[expr as usize];
            self.mk_app(m, decl, &new_args.items, sort)?
        } else {
            expr
        };
        new_args.reset(m)?;
        Ok(result)
    }
}

/// The ctx-simplify tactic, which the clean tactical resets when it is done.
pub fn ctx_simplify(m: &mut AstManager, goal: &mut Goal) -> Result<(), SmtError> {
    let mut simplifier = CtxSimplifier::new(m);
    simplifier.apply(m, goal)?;
    simplifier.release(m)
}
