//! Ported from Z3 (src/solver/assertions/asserted_formulas.cpp), MIT license, through
//! `asserted-formulas.ts`. The preprocessing that the SMT kernel runs on its assertions before
//! search.
//!
//! # Design
//!
//! - The TypeScript's `Substitution` keeps a map that it shares with the kernel's rewriter, which
//!   `flushCache` passes to `setSubstitution`. Here the rewriter owns the map (rewriter.rs), so
//!   [`Substitution`] keeps the trail and its scopes, and its methods take the map, the
//!   rewriter's `get_substitution_mut`; `flush_cache` resets the rewriter, as `setSubstitution`
//!   with the same map does.
//! - `PatternInferenceRw extends RewriterTpl` is the configuration [`PatternInferenceRwCfg`].
//! - `simplifyFormulas` takes a closure over one of the rewriters, here a [`Simplifier`].
//! - The recursions of `pushAssertion` and `isGreater` stop past `MAX_RECURSION_DEPTH`
//!   (design/smt-core.md, recursion).

use std::collections::HashMap;

use crate::core::ast::{
    AstManager, Expr, KIND_APP, OP_AND, OP_EQ, OP_ITE, OP_NOT, OP_OR, SORT_BOOL,
};
use crate::core::ast_util::mk_not;
use crate::core::maximize_ac_sharing::{MaxBvSharing, MaxBvSharingConfig};
use crate::core::nnf::{DefinedNames, Nnf};
use crate::core::pattern_inference::PatternInference;
use crate::core::pull_quant::{PullQuant, PullQuantConfig};
use crate::core::ref_vector::RefVector;
use crate::core::rewriter::{KERNEL_REWRITER_OPTIONS, Rewriter};
use crate::core::rewriter_tpl::{MAX_RECURSION_DEPTH, RewriterConfig, RewriterTpl};
use crate::util::error::SmtError;
use crate::util::ordered_map::OrderedMap;

fn mk_recursion_error() -> SmtError {
    SmtError::Unsupported("the asserted formulas nest too deeply".into())
}

/// pattern_inference_rw: infers the patterns of each universal quantifier without patterns. Its
/// cache lives as long as the assertions, like Z3's.
#[derive(Clone, Debug)]
pub struct PatternInferenceRwCfg {
    inference: PatternInference,
}

impl RewriterConfig for PatternInferenceRwCfg {
    fn reduce_quantifier(
        &mut self,
        m: &mut AstManager,
        expr: Expr,
        body: Expr,
        _patterns: &[Expr],
    ) -> Result<Expr, SmtError> {
        let data = m.get_quantifier(expr)?.clone();
        if !data.is_forall || !data.patterns.is_empty() {
            return Ok(-1);
        }
        let inference = &mut self.inference;
        let quantifier = m.with_temporaries(|m| {
            let inferred = inference.infer(m, data.sorts.len(), body, data.weight)?;
            let mut with_patterns = data.clone();
            with_patterns.body = body;
            with_patterns.patterns = inferred.patterns.clone();
            let with_patterns = m.mk_quantifier(with_patterns)?;
            if inferred.weight == data.weight {
                return Ok(with_patterns);
            }
            let mut weighted = data.clone();
            weighted.body = body;
            weighted.patterns = inferred.patterns;
            weighted.weight = inferred.weight;
            m.mk_quantifier(weighted)
        })?;
        if !m.get_quantifier(quantifier)?.patterns.is_empty() {
            return Ok(quantifier);
        }
        // pi_pull_quantifiers: pulling the nested quantifiers out may give the body a pattern.
        // The quantifier with the new patterns replaces new_q at once, and the pulled quantifier
        // and pull_quant's cache go when reduce_quantifier returns.
        let mut pull = PullQuant::new(m, PullQuantConfig::new(m));
        let pulled = pull.rewrite(m, quantifier)?;
        let result = if pulled == quantifier {
            -1
        } else {
            let pulled_data = m.get_quantifier(pulled)?.clone();
            m.with_temporaries_keeping(
                |m| {
                    let patterns =
                        inference.infer_pulled(m, pulled_data.sorts.len(), pulled_data.body)?;
                    if patterns.is_empty() {
                        return Ok(-1);
                    }
                    let mut with_patterns = pulled_data;
                    with_patterns.patterns = patterns;
                    m.mk_quantifier(with_patterns)
                },
                |inner_result| {
                    if *inner_result == -1 {
                        Vec::new()
                    } else {
                        vec![*inner_result]
                    }
                },
            )?
        };
        if result != -1 {
            m.dec_ref(quantifier)?;
        }
        m.dec_ref(pulled)?;
        pull.release(m)?;
        Ok(if result == -1 { quantifier } else { result })
    }
}

// Z3's Knuth-Bendix style order for propagate_values: values are smallest, then deeper terms are
// greater.
fn is_greater(m: &AstManager, left: Expr, right: Expr, depth: usize) -> Result<bool, SmtError> {
    if left == right {
        return Ok(false);
    }
    let is_left_value = m.is_unique_value(left);
    let is_right_value = m.is_unique_value(right);
    if !is_left_value && is_right_value {
        return Ok(true);
    }
    if is_left_value && !is_right_value {
        return Ok(false);
    }
    if m.depths[left as usize] != m.depths[right as usize] {
        return Ok(m.depths[left as usize] > m.depths[right as usize]);
    }
    if m.kinds[left as usize] != KIND_APP || m.kinds[right as usize] != KIND_APP {
        return Ok(false);
    }
    let left_decl_id = m.get_decl_id(left)?;
    let right_decl_id = m.get_decl_id(right)?;
    if left_decl_id != right_decl_id {
        return Ok(left_decl_id > right_decl_id);
    }
    if m.get_num_args(left) != m.get_num_args(right) {
        return Ok(m.get_num_args(left) > m.get_num_args(right));
    }
    for index in 0..m.get_num_args(left) {
        if m.get_arg(left, index) != m.get_arg(right, index) {
            if depth >= MAX_RECURSION_DEPTH {
                return Err(mk_recursion_error());
            }
            return is_greater(
                m,
                m.get_arg(left, index),
                m.get_arg(right, index),
                depth + 1,
            );
        }
    }
    Ok(false)
}

/// expr_substitution under scoped_expr_substitution: the first entry for a key wins, and pop
/// removes the entries since the matching push. The map and the trail hold their keys and values.
/// The map is the rewriter's, which each method takes.
#[derive(Clone, Debug, Default)]
pub struct Substitution {
    trail: RefVector,
    trail_lims: Vec<usize>,
}

impl Substitution {
    pub fn new() -> Substitution {
        Substitution::default()
    }

    pub fn insert(
        &mut self,
        m: &mut AstManager,
        map: &mut OrderedMap<Expr, Expr>,
        key: Expr,
        value: Expr,
    ) {
        if map.contains_key(&key) {
            return;
        }
        m.inc_ref(key);
        m.inc_ref(value);
        map.insert(key, value);
        self.trail.push(m, key);
    }

    pub fn push(&mut self) {
        self.trail_lims.push(self.trail.len());
    }

    pub fn pop(
        &mut self,
        m: &mut AstManager,
        map: &mut OrderedMap<Expr, Expr>,
    ) -> Result<(), SmtError> {
        let Some(size) = self.trail_lims.pop() else {
            return Err(SmtError::Invariant(
                "the substitution pops a scope it did not push".into(),
            ));
        };
        for key in self.trail.items[size..].iter().copied() {
            let Some(value) = map.get(&key).copied() else {
                return Err(SmtError::Invariant(
                    "a trailed key has no substitution".into(),
                ));
            };
            m.dec_ref(value)?;
            map.remove(&key);
            m.dec_ref(key)?;
        }
        self.trail.shrink(m, size)
    }

    /// update_substitution: a ground equality is oriented by the order, and any other formula maps
    /// to true, or its atom to false.
    pub fn update(
        &mut self,
        m: &mut AstManager,
        map: &mut OrderedMap<Expr, Expr>,
        expr: Expr,
    ) -> Result<(), SmtError> {
        if m.is_ground(expr) && m.get_op(expr) == OP_EQ {
            let left = m.get_arg(expr, 0);
            let right = m.get_arg(expr, 1);
            if is_greater(m, left, right, 0)? {
                self.insert(m, map, left, right);
                return Ok(());
            }
            if is_greater(m, right, left, 0)? {
                self.insert(m, map, right, left);
                return Ok(());
            }
        }
        if m.is_not(expr) {
            let atom = m.get_arg(expr, 0);
            let false_expr = m.false_expr;
            self.insert(m, map, atom, false_expr);
        } else {
            let true_expr = m.true_expr;
            self.insert(m, map, expr, true_expr);
        }
        Ok(())
    }
}

// A pushed scope: the number of formulas when it began, and m_inconsistent_old.
#[derive(Clone, Copy, Debug)]
struct AssertedScope {
    num_formulas: usize,
    is_inconsistent: bool,
}

// The rewriter that simplify_fmls applies.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Simplifier {
    Rewriter,
    PatternInference,
    BvSharing,
}

/// asserted_formulas: the assertions of a context. Each assertion is rewritten when it is
/// asserted, and reduce preprocesses the new ones. Their units and oriented equalities then
/// rewrite the later assertions. Like Z3, it holds its formulas, so that expressions are deleted
/// in Z3's order.
#[derive(Clone, Debug)]
pub struct AssertedFormulas {
    formulas: RefVector,
    qhead: usize,
    substitution: Substitution,
    rewriter: Rewriter,
    is_eliminating_and: bool,
    is_reduce_pending: bool,
    names: DefinedNames,
    pattern_inference: RewriterTpl<PatternInferenceRwCfg>,
    bv_sharing: MaxBvSharing,
    has_quantifiers: bool,
    /// m_inconsistent: whether a formula is false, after which no formula is added or
    /// preprocessed.
    pub is_inconsistent: bool,
    // The scopes that are pushed only when a formula is asserted, and the pushed scopes.
    num_lazy_scopes: usize,
    scopes: Vec<AssertedScope>,
}

impl AssertedFormulas {
    pub fn new(m: &AstManager) -> AssertedFormulas {
        AssertedFormulas {
            formulas: RefVector::new(),
            qhead: 0,
            substitution: Substitution::new(),
            rewriter: Rewriter::new(m, KERNEL_REWRITER_OPTIONS, false),
            is_eliminating_and: false,
            is_reduce_pending: true,
            names: DefinedNames::new(),
            pattern_inference: RewriterTpl::new(
                m,
                PatternInferenceRwCfg {
                    inference: PatternInference::new(),
                },
            ),
            bv_sharing: MaxBvSharing::new(m, MaxBvSharingConfig::new()),
            has_quantifiers: false,
            is_inconsistent: false,
            num_lazy_scopes: 0,
            scopes: Vec::new(),
        }
    }

    /// push_scope: the scope is pushed when a formula is asserted in it.
    pub fn push(&mut self) {
        self.num_lazy_scopes += 1;
    }

    /// pop_scope: removes the formulas, names and substitutions since the matching push.
    pub fn pop(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        if self.num_lazy_scopes > 0 {
            self.num_lazy_scopes -= 1;
            return Ok(());
        }
        let Some(scope) = self.scopes.pop() else {
            return Err(SmtError::Invariant(
                "the asserted formulas pop a scope they did not push".into(),
            ));
        };
        self.is_inconsistent = scope.is_inconsistent;
        self.bv_sharing.cfg.pop_scope(m)?;
        self.names.pop(m)?;
        self.substitution
            .pop(m, self.rewriter.get_substitution_mut())?;
        self.formulas.shrink(m, scope.num_formulas)?;
        self.qhead = scope.num_formulas;
        self.flush_cache(m)
    }

    // force_push: the pushed formulas are already reduced and committed.
    fn force_push(&mut self) {
        while self.num_lazy_scopes > 0 {
            self.substitution.push();
            self.scopes.push(AssertedScope {
                num_formulas: self.formulas.len(),
                is_inconsistent: self.is_inconsistent,
            });
            self.names.push();
            self.bv_sharing.cfg.push_scope();
            self.num_lazy_scopes -= 1;
        }
    }

    pub fn assert_expr(&mut self, m: &mut AstManager, expr: Expr) -> Result<(), SmtError> {
        self.force_push();
        if self.is_inconsistent || m.is_true(expr) {
            return Ok(());
        }
        self.set_eliminate_and(m, false)?;
        let rewritten = self.rewriter.rewrite(m, expr)?;
        if m.has_quantifier_flags[expr as usize] != 0 {
            self.has_quantifiers = true;
        }
        let mut formulas = std::mem::take(&mut self.formulas);
        let pushed = self.push_assertion(m, rewritten, &mut formulas, 0);
        self.formulas = formulas;
        pushed?;
        m.dec_ref(rewritten)?;
        self.is_reduce_pending = true;
        Ok(())
    }

    pub fn get_num_formulas(&self) -> usize {
        self.formulas.len()
    }

    /// reduce and commit: the new formulas after preprocessing, which the context internalizes.
    /// Like internalize_assertions, nothing is committed once the formulas are inconsistent. The
    /// asserted formulas keep holding them.
    pub fn reduce(&mut self, m: &mut AstManager) -> Result<Vec<Expr>, SmtError> {
        if self.qhead == self.formulas.len() {
            return Ok(Vec::new());
        }
        if !self.is_inconsistent {
            self.reduce_core(m)?;
        }
        if self.is_inconsistent {
            return Ok(Vec::new());
        }
        let result = self.formulas.items[self.qhead..].to_vec();
        for formula in result.iter().copied() {
            self.substitution
                .update(m, self.rewriter.get_substitution_mut(), formula)?;
        }
        self.qhead = self.formulas.len();
        Ok(result)
    }

    // asserted_formulas::reduce: each step but the last stops the preprocessing when a formula is
    // false.
    fn reduce_core(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.set_eliminate_and(m, false)?;
        self.propagate_values(m)?;
        if self.is_inconsistent {
            return Ok(());
        }
        self.is_reduce_pending = true;
        self.nnf_cnf(m)?;
        if self.is_inconsistent {
            return Ok(());
        }
        self.set_eliminate_and(m, true)?;
        self.reduce_asserted(m)?;
        if self.is_inconsistent {
            return Ok(());
        }
        if self.has_quantifiers && self.simplify_formulas(m, Simplifier::PatternInference)? {
            self.is_reduce_pending = true;
        }
        if self.is_inconsistent {
            return Ok(());
        }
        // max_bv_sharing, whose post_op reduces the formulas again.
        if self.simplify_formulas(m, Simplifier::BvSharing)? {
            self.is_reduce_pending = true;
        }
        if self.is_inconsistent {
            return Ok(());
        }
        self.reduce_asserted(m)?;
        if self.is_inconsistent {
            return Ok(());
        }
        self.is_reduce_pending = true;
        self.flatten_clauses(m)?;
        if self.is_inconsistent {
            return Ok(());
        }
        self.flush_cache(m)
    }

    // push_assertion: splits conjunctions and negated disjunctions. A false formula makes the
    // assertions inconsistent.
    fn push_assertion(
        &mut self,
        m: &mut AstManager,
        expr: Expr,
        result: &mut RefVector,
        depth: usize,
    ) -> Result<(), SmtError> {
        if self.is_inconsistent || m.is_true(expr) {
            return Ok(());
        }
        if m.is_false(expr) {
            result.push(m, expr);
            self.is_inconsistent = true;
            return Ok(());
        }
        if depth >= MAX_RECURSION_DEPTH {
            return Err(mk_recursion_error());
        }
        let op = m.get_op(expr);
        if op == OP_AND {
            for index in 0..m.get_num_args(expr) {
                let arg = m.get_arg(expr, index);
                self.push_assertion(m, arg, result, depth + 1)?;
            }
            return Ok(());
        }
        if op == OP_NOT && m.get_op(m.get_arg(expr, 0)) == OP_OR {
            let disjunction = m.get_arg(expr, 0);
            for index in 0..m.get_num_args(disjunction) {
                // narg holds the negation while it is pushed.
                let negation = mk_not(m, m.get_arg(disjunction, index))?;
                m.inc_ref(negation);
                self.push_assertion(m, negation, result, depth + 1)?;
                m.dec_ref(negation)?;
            }
            return Ok(());
        }
        result.push(m, expr);
        Ok(())
    }

    // flush_cache: the rewriter is reset, with the committed substitution.
    fn flush_cache(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.rewriter.reset(m)
    }

    fn set_eliminate_and(
        &mut self,
        m: &mut AstManager,
        is_eliminating_and: bool,
    ) -> Result<(), SmtError> {
        if self.is_eliminating_and == is_eliminating_and {
            return Ok(());
        }
        self.is_eliminating_and = is_eliminating_and;
        self.is_reduce_pending = true;
        self.rewriter.set_eliminating_and(is_eliminating_and);
        self.flush_cache(m)
    }

    // swap_asserted_formulas: the new formulas replace those from qhead on.
    fn swap_formulas(
        &mut self,
        m: &mut AstManager,
        formulas: &mut RefVector,
    ) -> Result<(), SmtError> {
        self.formulas.shrink(m, self.qhead)?;
        for formula in formulas.items.iter().copied() {
            self.formulas.push(m, formula);
        }
        formulas.reset(m)
    }

    // simplify_fmls: a formula that simplify changes is split again. simplify returns its result
    // with a reference. Whether a formula changed.
    fn simplify_formulas(
        &mut self,
        m: &mut AstManager,
        simplifier: Simplifier,
    ) -> Result<bool, SmtError> {
        let mut formulas = RefVector::new();
        let mut is_changed = false;
        for index in self.qhead..self.formulas.len() {
            let formula = self.formulas.items[index];
            let result = match simplifier {
                Simplifier::Rewriter => self.rewriter.rewrite(m, formula)?,
                Simplifier::PatternInference => self.pattern_inference.rewrite(m, formula)?,
                Simplifier::BvSharing => self.bv_sharing.rewrite(m, formula)?,
            };
            if result == formula {
                formulas.push(m, formula);
            } else {
                self.push_assertion(m, result, &mut formulas, 0)?;
                is_changed = true;
            }
            m.dec_ref(result)?;
        }
        self.swap_formulas(m, &mut formulas)?;
        Ok(is_changed)
    }

    // reduce_asserted_formulas: the rewriter rewrites the formulas, unless they are already in its
    // normal form.
    fn reduce_asserted(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        if !self.is_reduce_pending {
            return Ok(());
        }
        self.simplify_formulas(m, Simplifier::Rewriter)?;
        self.is_reduce_pending = false;
        Ok(())
    }

    // propagate: the formula at index, rewritten with the committed substitution and the units
    // before it, which it then joins.
    fn propagate(
        &mut self,
        m: &mut AstManager,
        index: usize,
        num_propagated: &mut usize,
    ) -> Result<(), SmtError> {
        let formula = self.formulas.items[index];
        m.inc_ref(formula);
        let rewritten = self.rewriter.rewrite(m, formula)?;
        self.formulas.set(m, index, rewritten)?;
        if m.is_false(rewritten) {
            self.is_inconsistent = true;
        }
        self.substitution
            .update(m, self.rewriter.get_substitution_mut(), rewritten)?;
        if rewritten != formula {
            *num_propagated += 1;
        }
        m.dec_ref(rewritten)?;
        m.dec_ref(formula)
    }

    // asserted_formulas::propagate_values: a forward and a backward pass that rewrite each formula
    // with the committed substitution and the units of the formulas before it. Z3 stops after one
    // round, since the passes add no formula. When a formula changed, reduce-asserted rewrites them
    // all.
    fn propagate_values(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        let size = self.formulas.len();
        let mut num_propagated = 0;
        self.flush_cache(m)?;
        self.substitution.push();
        for index in self.qhead..size {
            self.propagate(m, index, &mut num_propagated)?;
        }
        self.flush_cache(m)?;
        self.substitution
            .pop(m, self.rewriter.get_substitution_mut())?;
        self.substitution.push();
        for index in (self.qhead..size).rev() {
            self.propagate(m, index, &mut num_propagated)?;
        }
        self.substitution
            .pop(m, self.rewriter.get_substitution_mut())?;
        self.flush_cache(m)?;
        if num_propagated > 0 {
            self.reduce_asserted(m)?;
        }
        Ok(())
    }

    // asserted_formulas::nnf_cnf: one NNF object normalizes every formula, and the rewriter, which
    // does not eliminate and yet, rewrites each normal form and the definitions of the names it
    // introduced.
    fn nnf_cnf(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        let mut nnf = Nnf::new(m);
        let mut formulas = RefVector::new();
        let mut todo = RefVector::new();
        for index in self.qhead..self.formulas.len() {
            todo.reset(m)?;
            let formula = self.formulas.items[index];
            let mut result = nnf.apply(m, &mut self.names, formula, &mut todo)?;
            todo.push(m, result);
            for position in 0..todo.len() {
                let rewritten = self.rewriter.rewrite(m, todo.items[position])?;
                m.dec_ref(result)?;
                result = rewritten;
                self.push_assertion(m, result, &mut formulas, 0)?;
            }
            m.dec_ref(result)?;
        }
        self.swap_formulas(m, &mut formulas)?;
        todo.reset(m)?;
        nnf.release(m)
    }

    // asserted_formulas::flatten_clauses: an ite at the top becomes two clauses, and a conjunction
    // that occurs in one binary clause is distributed.
    fn flatten_clauses(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        let mk_negation = |m: &mut AstManager, expr: Expr| -> Result<Expr, SmtError> {
            if m.is_not(expr) {
                Ok(m.get_arg(expr, 0))
            } else {
                m.mk_app(OP_NOT, &[expr], SORT_BOOL)
            }
        };
        let is_conjunction =
            |m: &AstManager, expr: Expr| m.is_not(expr) && m.get_op(m.get_arg(expr, 0)) == OP_OR;
        let mut is_changed = true;
        while is_changed {
            is_changed = false;
            let mut formulas = RefVector::new();
            let mut occurrences: HashMap<Expr, usize> = HashMap::new();
            for index in self.qhead..self.formulas.len() {
                let formula = self.formulas.items[index];
                if m.get_op(formula) != OP_OR || m.get_num_args(formula) != 2 {
                    continue;
                }
                for arg_index in 0..2 {
                    let arg = m.get_arg(formula, arg_index);
                    if is_conjunction(m, arg) {
                        *occurrences.entry(arg).or_insert(0) += 1;
                    }
                }
            }
            for index in self.qhead..self.formulas.len() {
                let formula = self.formulas.items[index];
                if m.get_op(formula) == OP_OR && m.get_num_args(formula) == 2 {
                    let conjunction_index = [1, 0].into_iter().find(|position| {
                        let arg = m.get_arg(formula, *position);
                        is_conjunction(m, arg) && occurrences.get(&arg) == Some(&1)
                    });
                    if let Some(conjunction_index) = conjunction_index {
                        let other = m.get_arg(formula, 1 - conjunction_index);
                        let disjunction = m.get_arg(m.get_arg(formula, conjunction_index), 0);
                        for arg_index in 0..m.get_num_args(disjunction) {
                            let negation = mk_negation(m, m.get_arg(disjunction, arg_index))?;
                            let clause = m.mk_app(OP_OR, &[other, negation], SORT_BOOL)?;
                            formulas.push(m, clause);
                        }
                        is_changed = true;
                        continue;
                    }
                }
                if m.get_op(formula) == OP_ITE {
                    let condition = m.get_arg(formula, 0);
                    let negation = mk_negation(m, condition)?;
                    let then_clause =
                        m.mk_app(OP_OR, &[negation, m.get_arg(formula, 1)], SORT_BOOL)?;
                    formulas.push(m, then_clause);
                    let else_clause =
                        m.mk_app(OP_OR, &[condition, m.get_arg(formula, 2)], SORT_BOOL)?;
                    formulas.push(m, else_clause);
                    is_changed = true;
                    continue;
                }
                formulas.push(m, formula);
            }
            self.swap_formulas(m, &mut formulas)?;
        }
        Ok(())
    }
}
