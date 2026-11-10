//! Ported from Z3 (src/ast/rewriter/th_rewriter.cpp, bool_rewriter.cpp, arith_rewriter.cpp), MIT
//! license, through `rewriter.ts`. Only the rewrites that tlapm's encoding exercises are ported.
//!
//! # Design
//!
//! The TypeScript's `Rewriter extends RewriterTpl` is rewriter_tpl with th_rewriter_cfg: its
//! hooks are [`ThRewriterCfg`]'s implementation of [`RewriterConfig`], and [`Rewriter`] owns the
//! configuration beside the main loop, as `RewriterTpl<C>` does, with the TypeScript's public
//! methods. Like every class of the core, neither keeps the manager.
//!
//! - `releaseResult`, which try_ite_value calls to write the m_r of the rewriter that applies this
//!   one, is the [`LastResult`] the configuration's methods take: the main loop passes its own,
//!   [`Rewriter`]'s methods pass the rewriter's, and [`Rewriter::reduce_app_core`] takes the one to
//!   write, as the model evaluator, which sets `releaseResult` to its own `setLastResult(-1)`,
//!   passes its m_r.
//! - `setSubstitution` takes a map that its caller keeps extending between rewrites. Here the
//!   rewriter owns the map, and [`Rewriter::get_substitution_mut`] extends it.
//! - The rewrites of bool_rewriter call each other by recursion (mk_not, mk_eq, try_ite_value),
//!   and so does apply_subst on the patterns: each stops past `MAX_RECURSION_DEPTH`
//!   (design/smt-core.md, recursion).
//! - The internal rewrites return [`Reduced`], whose `Failed` is the TypeScript's undefined or -1,
//!   with no reference; only `reduce_app` returns its result with a reference.

use std::collections::{HashMap, HashSet};

use crate::core::arith_rewriter::{ArithRewriter, KERNEL_ARITH_OPTIONS, TACTIC_ARITH_OPTIONS};
use crate::core::ast::{
    AstManager, Decl, Expr, FAMILY_ARITH, FAMILY_BASIC, KIND_APP, KIND_QUANTIFIER, KIND_VAR,
    OP_ABS, OP_ADD, OP_AND, OP_DISTINCT, OP_DIV, OP_EQ, OP_GE, OP_GT, OP_IDIV, OP_IMPLIES,
    OP_IS_INT, OP_ITE, OP_LE, OP_LT, OP_MOD, OP_MUL, OP_NOT, OP_OR, OP_SUB, OP_TO_INT, OP_TO_REAL,
    OP_UMINUS, OP_UNINTERPRETED, OP_XOR, QuantifierData, SORT_BOOL, Sort, is_arith_sort,
};
use crate::core::ast_lt::is_ast_less;
use crate::core::der::Der;
use crate::core::poly_rewriter::{ArithRewriterOptions, get_reduced_expr};
use crate::core::rewriter_tpl::{
    LastResult, MAX_RECURSION_DEPTH, Reduced, Rewrite, RewriterConfig, RewriterEngine,
    UNBOUNDED_DEPTH, get_rewrite_depth,
};
use crate::core::var_subst::UnusedVarsEliminator;
use crate::util::error::SmtError;
use crate::util::ordered_map::OrderedMap;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RewriterOptions {
    /// Replaces (and a b) with (not (or (not a) (not b))), as Z3's asserted_formulas does after
    /// NNF.
    pub is_eliminating_and: bool,
    pub arith: ArithRewriterOptions,
    /// rewrite_patterns: the patterns of a quantifier are rewritten like its body. The kernel's
    /// rewriters set it, and the tactics' leave it off.
    pub is_rewriting_patterns: bool,
    /// pull_cheap_ite: a binary predicate or a function of an ite with values distributes over
    /// the ite. Optional in the TypeScript, where absent is false.
    pub is_pulling_cheap_ite: bool,
}

/// The parameters that asserted_formulas gives the kernel's rewriters.
pub const KERNEL_REWRITER_OPTIONS: RewriterOptions = RewriterOptions {
    is_eliminating_and: false,
    arith: KERNEL_ARITH_OPTIONS,
    is_rewriting_patterns: true,
    is_pulling_cheap_ite: false,
};

/// th_rewriter's defaults, which the tactics and the model use.
pub const TACTIC_REWRITER_OPTIONS: RewriterOptions = RewriterOptions {
    is_eliminating_and: false,
    arith: TACTIC_ARITH_OPTIONS,
    is_rewriting_patterns: false,
    is_pulling_cheap_ite: false,
};

// A term that reduce_to is rewriting: the depth left for its arguments, its next argument, and
// where its arguments' results start.
struct ReduceFrame {
    expr: Expr,
    depth: u32,
    child_index: usize,
    spos: usize,
}

fn mk_recursion_error() -> SmtError {
    SmtError::Unsupported("the rewriter nests too deeply".into())
}

/// th_rewriter_cfg: the hooks of [`Rewriter`] and the rewrites of bool_rewriter and
/// arith_rewriter.
#[derive(Clone, Debug)]
pub struct ThRewriterCfg {
    pub options: RewriterOptions,
    is_nested_der: bool,
    arith: ArithRewriter,
    substitution: OrderedMap<Expr, Expr>,
    unused_vars_eliminator: UnusedVarsEliminator,
    der: Der,
}

impl RewriterConfig for ThRewriterCfg {
    const IS_SUBSTITUTING: bool = true;

    /// flat_assoc: th_rewriter flattens and, or and + into an enclosing application of the same
    /// operator.
    fn is_flat_assoc(&self, m: &AstManager, decl: Decl) -> bool {
        let op = m.func_decls[decl as usize].op;
        op == OP_AND || op == OP_OR || op == OP_ADD
    }

    fn is_rewriting_patterns(&self) -> bool {
        self.options.is_rewriting_patterns
    }

    fn get_subst(&mut self, _m: &mut AstManager, expr: Expr) -> Result<Option<Expr>, SmtError> {
        Ok(self.get_subst_of(expr))
    }

    fn reduce_app(
        &mut self,
        m: &mut AstManager,
        last_result: &mut LastResult,
        decl: Decl,
        args: &[Expr],
        sort: Sort,
    ) -> Result<Reduced, SmtError> {
        // An uninterpreted application only reduces by pull_ite, which needs two arguments.
        if m.func_decls[decl as usize].op == OP_UNINTERPRETED
            && (args.len() != 2 || !self.options.is_pulling_cheap_ite)
        {
            return Ok(Reduced::Failed);
        }
        let outer = m.begin_temporaries();
        let result = self.reduce_app_top(m, last_result, decl, args, sort)?;
        if let Some(expr) = get_reduced_expr(result) {
            m.inc_ref(expr);
        }
        m.end_temporaries(outer)?;
        Ok(result)
    }

    fn reduce_quantifier(
        &mut self,
        m: &mut AstManager,
        expr: Expr,
        body: Expr,
        patterns: &[Expr],
    ) -> Result<Expr, SmtError> {
        m.with_temporaries(|m| self.reduce_quantifier_core(m, expr, body, patterns))
    }

    /// ~imp: the members of th_rewriter_cfg go before the caches of rewriter_tpl.
    fn release(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.unused_vars_eliminator.release(m)?;
        self.der.release(m)
    }
}

impl ThRewriterCfg {
    pub fn new(m: &AstManager, options: RewriterOptions, is_nested_der: bool) -> ThRewriterCfg {
        ThRewriterCfg {
            options,
            is_nested_der,
            arith: ArithRewriter::new(options.arith),
            substitution: OrderedMap::new(),
            unused_vars_eliminator: UnusedVarsEliminator::new(m),
            der: Der::new(m),
        }
    }

    /// getSubst.
    pub fn get_subst_of(&self, expr: Expr) -> Option<Expr> {
        if self.substitution.is_empty() {
            None
        } else {
            self.substitution.get(&expr).copied()
        }
    }

    // Rewrites the top depth levels of a term, outside the main loop. Like rewriter_tpl, it keeps
    // its frames on an explicit stack, so a deep term or a long chain of rewrites cannot overflow
    // the call stack.
    fn reduce_to(
        &mut self,
        m: &mut AstManager,
        last_result: &mut LastResult,
        expr: Expr,
        depth: u32,
    ) -> Result<Expr, SmtError> {
        let mut frames: Vec<ReduceFrame> = Vec::new();
        let mut results: Vec<Expr> = Vec::new();
        let visit = |m: &AstManager,
                     frames: &mut Vec<ReduceFrame>,
                     results: &mut Vec<Expr>,
                     term: Expr,
                     term_depth: u32| {
            if term_depth == 0 || m.kinds[term as usize] != KIND_APP || m.get_num_args(term) == 0 {
                results.push(term);
            } else {
                frames.push(ReduceFrame {
                    expr: term,
                    // Infinity - 1 is Infinity.
                    depth: if term_depth == UNBOUNDED_DEPTH {
                        term_depth
                    } else {
                        term_depth - 1
                    },
                    child_index: 0,
                    spos: results.len(),
                });
            }
        };
        visit(m, &mut frames, &mut results, expr, depth);
        while let Some(frame) = frames.last_mut() {
            if frame.child_index < m.get_num_args(frame.expr) {
                let arg = m.get_arg(frame.expr, frame.child_index);
                frame.child_index += 1;
                let frame_depth = frame.depth;
                visit(m, &mut frames, &mut results, arg, frame_depth);
                continue;
            }
            let (frame_expr, spos) = (frame.expr, frame.spos);
            frames.pop();
            let decl = m.decls[frame_expr as usize];
            let new_args = results.split_off(spos);
            let sort = m.sorts[frame_expr as usize];
            match self.reduce_app_top(m, last_result, decl, &new_args, sort)? {
                Reduced::Failed => results.push(m.mk_app(decl, &new_args, sort)?),
                Reduced::Done(reduced) => results.push(reduced),
                Reduced::Rewrite(rewrite) => visit(
                    m,
                    &mut frames,
                    &mut results,
                    rewrite.expr,
                    get_rewrite_depth(&rewrite),
                ),
            }
        }
        results
            .first()
            .copied()
            .ok_or_else(|| SmtError::Invariant("reduce_to has no result".into()))
    }

    /// updt_params with elim_and, which asserted_formulas turns on after NNF. The caller resets the
    /// rewriter.
    pub fn set_eliminating_and(&mut self, is_eliminating_and: bool) {
        self.options = RewriterOptions {
            is_eliminating_and,
            ..self.options
        };
    }

    // th_rewriter_cfg::reduce_quantifier: a bound Boolean variable among the conjuncts of a
    // universal body or the disjuncts of an existential one decides the quantifier. Otherwise it
    // merges a directly nested quantifier of the same kind when neither has patterns, eliminates
    // unused variables, and applies der to pattern-free quantifiers.
    fn reduce_quantifier_core(
        &mut self,
        m: &mut AstManager,
        expr: Expr,
        body: Expr,
        new_patterns: &[Expr],
    ) -> Result<Expr, SmtError> {
        let data = m.get_quantifier(expr)?.clone();
        let is_negated = m.is_not(body);
        let junction = if is_negated { m.get_arg(body, 0) } else { body };
        let junction_op = if data.is_forall != is_negated {
            OP_AND
        } else {
            OP_OR
        };
        if m.get_op(junction) == junction_op
            && m.some_arg(junction, |arg, _| {
                let atom = if m.is_not(arg) {
                    m.get_arg(arg, 0)
                } else {
                    arg
                };
                m.kinds[atom as usize] == KIND_VAR
                    && (m.values[atom as usize] as usize) < data.sorts.len()
            })
        {
            return Ok(if data.is_forall {
                m.false_expr
            } else {
                m.true_expr
            });
        }
        let nested = if m.kinds[body as usize] == KIND_QUANTIFIER {
            Some(m.get_quantifier(body)?.clone())
        } else {
            None
        };
        // remove_duplicates.
        let mut patterns: Vec<Expr> = Vec::new();
        for pattern in new_patterns {
            if !patterns.contains(pattern) {
                patterns.push(*pattern);
            }
        }
        let merged = match nested {
            Some(nested)
                if nested.is_forall == data.is_forall
                    && data.patterns.is_empty()
                    && nested.patterns.is_empty() =>
            {
                let mut sorts = data.sorts.clone();
                sorts.extend_from_slice(&nested.sorts);
                let mut names = data.names.clone();
                names.extend_from_slice(&nested.names);
                m.mk_quantifier(QuantifierData {
                    sorts,
                    names,
                    body: nested.body,
                    patterns: Vec::new(),
                    weight: data.weight.min(nested.weight),
                    ..data
                })?
            }
            _ => {
                let patterns = self.substitute_patterns(m, &patterns)?;
                m.mk_quantifier(QuantifierData {
                    body,
                    patterns,
                    ..data
                })?
            }
        };
        let reduced = self.unused_vars_eliminator.apply(m, merged)?;
        m.release_later(reduced)?;
        if m.kinds[reduced as usize] != KIND_QUANTIFIER
            || !m.get_quantifier(reduced)?.patterns.is_empty()
        {
            return Ok(reduced);
        }
        let eliminated = self.der.apply(m, reduced)?;
        if eliminated == reduced || self.is_nested_der {
            return Ok(eliminated);
        }
        let mut nested_rewriter = Rewriter::new(m, self.options, true);
        let rewritten = nested_rewriter.rewrite(m, eliminated)?;
        nested_rewriter.release(m)?;
        m.release_later(rewritten)?;
        Ok(rewritten)
    }

    // th_rewriter_cfg::apply_subst: the substitution replaces terms in the patterns without
    // rewriting them, like expr_safe_replace.
    fn substitute_patterns(
        &self,
        m: &mut AstManager,
        patterns: &[Expr],
    ) -> Result<Vec<Expr>, SmtError> {
        if self.substitution.is_empty() {
            return Ok(patterns.to_vec());
        }
        let mut cache: HashMap<Expr, Expr> = HashMap::new();
        let mut result = Vec::new();
        for pattern in patterns {
            let mut terms = Vec::new();
            for index in 0..m.get_num_args(*pattern) {
                let arg = m.get_arg(*pattern, index);
                terms.push(self.replace_in_pattern(m, &mut cache, arg, 0)?);
            }
            result.push(m.mk_pattern(&terms)?);
        }
        Ok(result)
    }

    fn replace_in_pattern(
        &self,
        m: &mut AstManager,
        cache: &mut HashMap<Expr, Expr>,
        expr: Expr,
        depth: usize,
    ) -> Result<Expr, SmtError> {
        if let Some(replacement) = self.substitution.get(&expr) {
            return Ok(*replacement);
        }
        if m.kinds[expr as usize] != KIND_APP || m.get_num_args(expr) == 0 {
            return Ok(expr);
        }
        if let Some(cached) = cache.get(&expr) {
            return Ok(*cached);
        }
        if depth >= MAX_RECURSION_DEPTH {
            return Err(mk_recursion_error());
        }
        let mut args = Vec::new();
        for index in 0..m.get_num_args(expr) {
            let arg = m.get_arg(expr, index);
            args.push(self.replace_in_pattern(m, cache, arg, depth + 1)?);
        }
        let result = m.mk_app(m.decls[expr as usize], &args, m.sorts[expr as usize])?;
        cache.insert(expr, result);
        Ok(result)
    }

    /// th_rewriter::mk_app: one reduction, without rewriting what it returns.
    pub fn mk_app(
        &mut self,
        m: &mut AstManager,
        last_result: &mut LastResult,
        decl: Decl,
        args: &[Expr],
        sort: Sort,
    ) -> Result<Expr, SmtError> {
        match self.reduce_app_top(m, last_result, decl, args, sort)? {
            Reduced::Failed => m.mk_app(decl, args, sort),
            Reduced::Done(reduced) => Ok(reduced),
            Reduced::Rewrite(rewrite) => Ok(rewrite.expr),
        }
    }

    /// th_rewriter's mk_app, with the result of a Rewrite rewritten again.
    pub fn mk_app_core(
        &mut self,
        m: &mut AstManager,
        last_result: &mut LastResult,
        decl: Decl,
        args: &[Expr],
        sort: Sort,
    ) -> Result<Expr, SmtError> {
        match self.reduce_app_top(m, last_result, decl, args, sort)? {
            Reduced::Failed => m.mk_app(decl, args, sort),
            Reduced::Done(reduced) => Ok(reduced),
            Reduced::Rewrite(rewrite) => {
                self.reduce_to(m, last_result, rewrite.expr, get_rewrite_depth(&rewrite))
            }
        }
    }

    // th_rewriter_cfg::reduce_app: reduce_app_core, then pull_ite with pull_cheap_ite.
    fn reduce_app_top(
        &mut self,
        m: &mut AstManager,
        last_result: &mut LastResult,
        decl: Decl,
        args: &[Expr],
        sort: Sort,
    ) -> Result<Reduced, SmtError> {
        let reduced = self.reduce_app_core(m, last_result, decl, args)?;
        if matches!(reduced, Reduced::Rewrite(_)) || !self.options.is_pulling_cheap_ite {
            return Ok(reduced);
        }
        let Reduced::Done(result) = reduced else {
            let pulled = if args.len() == 2 {
                self.pull_ite(m, decl, args[0], args[1], sort)?
            } else {
                None
            };
            return Ok(pulled.map_or(Reduced::Failed, Reduced::Rewrite));
        };
        if m.kinds[result as usize] == KIND_APP && m.get_num_args(result) == 2 {
            let pulled = self.pull_ite(
                m,
                m.decls[result as usize],
                m.get_arg(result, 0),
                m.get_arg(result, 1),
                m.sorts[result as usize],
            )?;
            return Ok(pulled.map_or(Reduced::Done(result), Reduced::Rewrite));
        }
        Ok(reduced)
    }

    // pull_ite: (p (ite c a b) v) is (ite c (p a v) (p b v)) for a value v, and likewise for
    // (p (ite c a b) (ite c a' b')) and a value first, for a p of two arguments.
    fn pull_ite(
        &mut self,
        m: &mut AstManager,
        decl: Decl,
        first: Expr,
        second: Expr,
        sort: Sort,
    ) -> Result<Option<Rewrite>, SmtError> {
        if sort == SORT_BOOL && m.sorts[first as usize] != SORT_BOOL {
            if self.is_ite(m, first) {
                if m.is_unique_value(second) && m.get_ref_count(first) == 1 {
                    return Ok(Some(
                        self.pull_ite_core(m, decl, first, second, sort, false)?,
                    ));
                }
                if self.is_ite(m, second) && m.get_arg(first, 0) == m.get_arg(second, 0) {
                    let mut branches = Vec::new();
                    for index in [1, 2] {
                        let args = [m.get_arg(first, index), m.get_arg(second, index)];
                        branches.push(m.mk_app(decl, &args, sort)?);
                    }
                    let expr = m.mk_app(
                        OP_ITE,
                        &[m.get_arg(first, 0), branches[0], branches[1]],
                        SORT_BOOL,
                    )?;
                    return Ok(Some(Rewrite { expr, depth: 2 }));
                }
            }
            if self.is_ite(m, second) && m.is_unique_value(first) && m.get_ref_count(second) == 1 {
                return Ok(Some(
                    self.pull_ite_core(m, decl, second, first, sort, true)?,
                ));
            }
        }
        let family = m.func_decls[decl as usize].family;
        if family != FAMILY_BASIC && family != FAMILY_ARITH {
            return Ok(None);
        }
        if m.is_unique_value(first) && self.is_ite_value_tree(m, second) {
            return Ok(Some(
                self.pull_ite_core(m, decl, second, first, sort, true)?,
            ));
        }
        if m.is_unique_value(second) && self.is_ite_value_tree(m, first) {
            return Ok(Some(
                self.pull_ite_core(m, decl, first, second, sort, false)?,
            ));
        }
        Ok(None)
    }

    // pull_ite_core: the value comes first when is_swapped. An equality of a branch and the value
    // is decided when the branch is a value.
    fn pull_ite_core(
        &mut self,
        m: &mut AstManager,
        decl: Decl,
        ite: Expr,
        value: Expr,
        sort: Sort,
        is_swapped: bool,
    ) -> Result<Rewrite, SmtError> {
        let mut branches = Vec::new();
        for branch in [m.get_arg(ite, 1), m.get_arg(ite, 2)] {
            branches.push(if m.func_decls[decl as usize].op == OP_EQ {
                if branch == value {
                    m.true_expr
                } else if self.are_distinct(m, branch, value) {
                    m.false_expr
                } else {
                    m.mk_eq(branch, value)?
                }
            } else {
                let args = if is_swapped {
                    [value, branch]
                } else {
                    [branch, value]
                };
                m.mk_app(decl, &args, sort)?
            });
        }
        let expr = m.mk_app(OP_ITE, &[m.get_arg(ite, 0), branches[0], branches[1]], sort)?;
        Ok(Rewrite { expr, depth: 2 })
    }

    // is_ite_value_tree: an unshared ite whose leaves are values, through unshared ites.
    fn is_ite_value_tree(&self, m: &AstManager, expr: Expr) -> bool {
        if !self.is_ite(m, expr) || m.get_ref_count(expr) != 1 {
            return false;
        }
        let mut todo = vec![expr];
        while let Some(ite) = todo.pop() {
            for branch in [m.get_arg(ite, 1), m.get_arg(ite, 2)] {
                if self.is_ite(m, branch) && m.get_ref_count(branch) == 1 {
                    todo.push(branch);
                } else if !m.is_unique_value(branch) {
                    return false;
                }
            }
        }
        true
    }

    /// The reductions of the Boolean and arithmetic rewriters, which the model evaluator applies
    /// too.
    pub fn reduce_app_core(
        &mut self,
        m: &mut AstManager,
        last_result: &mut LastResult,
        decl: Decl,
        args: &[Expr],
    ) -> Result<Reduced, SmtError> {
        let op = m.func_decls[decl as usize].op;
        match op {
            OP_AND => self.mk_and_core(m, last_result, args),
            OP_OR => Ok(Reduced::Done(self.mk_or(m, args)?)),
            OP_NOT => Ok(Reduced::Done(self.mk_not(m, last_result, args[0])?)),
            OP_IMPLIES => {
                let negation = self.mk_not(m, last_result, args[0])?;
                Ok(Reduced::Done(self.mk_or(m, &[negation, args[1]])?))
            }
            OP_XOR => {
                let negation = self.mk_not(m, last_result, args[0])?;
                Ok(Reduced::Done(self.mk_eq(
                    m,
                    last_result,
                    negation,
                    args[1],
                )?))
            }
            OP_EQ => {
                if is_arith_sort(m.sorts[args[0] as usize]) {
                    let reduced = self.arith.mk_eq(m, args[0], args[1])?;
                    if reduced != Reduced::Failed {
                        return Ok(reduced);
                    }
                }
                self.mk_eq_core(m, last_result, args[0], args[1], 0)
            }
            OP_DISTINCT => self.mk_distinct(m, last_result, args),
            OP_ITE => self.mk_ite(m, last_result, args[0], args[1], args[2]),
            OP_LE => self.arith.mk_le(m, args[0], args[1]),
            OP_GE => self.arith.mk_ge(m, args[0], args[1]),
            OP_LT => self.arith.mk_lt(m, args[0], args[1]),
            OP_GT => self.arith.mk_gt(m, args[0], args[1]),
            OP_ADD => Ok(self
                .arith
                .mk_add(m, args)?
                .map_or(Reduced::Failed, Reduced::Done)),
            OP_SUB => self.arith.mk_sub(m, args),
            OP_UMINUS => self.arith.mk_uminus(m, args[0]),
            OP_MUL => self.arith.mk_mul(m, args),
            OP_IDIV => self.arith.mk_idiv(m, args[0], args[1]),
            OP_MOD => self.arith.mk_mod(m, args[0], args[1]),
            OP_ABS => self.arith.mk_abs(m, args[0]),
            OP_DIV => self.arith.mk_div(m, args[0], args[1]),
            OP_TO_REAL => self.arith.mk_to_real(m, args[0]),
            OP_TO_INT => self.arith.mk_to_int(m, args[0]),
            OP_IS_INT => self.arith.mk_is_int(m, args[0]),
            _ => Ok(Reduced::Failed),
        }
    }

    /// bool_rewriter::mk_not: (not (= a b)) of Booleans is (= (not a) b).
    pub fn mk_not(
        &mut self,
        m: &mut AstManager,
        last_result: &mut LastResult,
        arg: Expr,
    ) -> Result<Expr, SmtError> {
        self.mk_not_at(m, last_result, arg, 0)
    }

    fn mk_not_at(
        &mut self,
        m: &mut AstManager,
        last_result: &mut LastResult,
        arg: Expr,
        depth: usize,
    ) -> Result<Expr, SmtError> {
        if m.is_not(arg) {
            return Ok(m.get_arg(arg, 0));
        }
        if m.get_op(arg) == OP_EQ && m.sorts[m.get_arg(arg, 0) as usize] == SORT_BOOL {
            if depth >= MAX_RECURSION_DEPTH {
                return Err(mk_recursion_error());
            }
            let negation = self.mk_not_at(m, last_result, m.get_arg(arg, 0), depth + 1)?;
            return self.mk_eq_at(m, last_result, negation, m.get_arg(arg, 1), depth + 1);
        }
        m.mk_not(arg)
    }

    /// bool_rewriter::mk_flat_or_core and mk_nflat_or_core: lifts the disjuncts of nested
    /// disjunctions one level, drops false and duplicates, and detects true or a complementary
    /// pair. With sort_disjunctions, a disjunction that changed or is out of ast_lt's order is
    /// stably sorted by id.
    pub fn mk_or(&mut self, m: &mut AstManager, args: &[Expr]) -> Result<Expr, SmtError> {
        let is_nested = args.iter().any(|arg| m.get_op(*arg) == OP_OR);
        let flat_args = if is_nested {
            self.flatten_args(m, args, OP_OR)
        } else {
            args.to_vec()
        };
        m.flat_literals.clear();
        for arg in flat_args.iter().copied() {
            if m.is_true(arg) {
                return Ok(m.true_expr);
            }
            if m.is_false(arg) {
                continue;
            }
            if m.flat_literals_add(arg) {
                return Ok(m.true_expr);
            }
        }
        let mut result = m.flat_literals.list.clone();
        let mut is_out_of_order = false;
        for index in 1..result.len() {
            if is_ast_less(m, result[index], result[index - 1])? {
                is_out_of_order = true;
                break;
            }
        }
        // Dropping false or a duplicate disjunct also sets mk_nflat_or_core's s.
        if is_nested || result.len() != flat_args.len() || is_out_of_order {
            result.sort_by_key(|arg| m.ids[*arg as usize]);
        }
        m.mk_or(&result)
    }

    // bool_rewriter::mk_and_core: with elim_and, mk_and_as_or. Otherwise mk_flat_and_core lifts
    // the conjuncts of nested conjunctions one level, and has the result rewritten again.
    fn mk_and_core(
        &mut self,
        m: &mut AstManager,
        last_result: &mut LastResult,
        args: &[Expr],
    ) -> Result<Reduced, SmtError> {
        if self.options.is_eliminating_and {
            return Ok(Reduced::Done(self.mk_and_as_or(m, last_result, args)?));
        }
        if !args.iter().any(|arg| m.get_op(*arg) == OP_AND) {
            return Ok(Reduced::Done(self.mk_nflat_and(m, args)?));
        }
        let flat_args = self.flatten_args(m, args, OP_AND);
        let expr = self.mk_nflat_and(m, &flat_args)?;
        Ok(Reduced::Rewrite(Rewrite { expr, depth: 1 }))
    }

    // The arguments with those that apply op replaced by their own arguments, one level deep.
    fn flatten_args(&self, m: &AstManager, args: &[Expr], op: i32) -> Vec<Expr> {
        let mut flat_args = Vec::new();
        for arg in args {
            if m.get_op(*arg) == op {
                m.push_args(*arg, &mut flat_args);
            } else {
                flat_args.push(*arg);
            }
        }
        flat_args
    }

    /// bool_rewriter::mk_and, which takes the result of mk_and_core as it is.
    pub fn mk_and(
        &mut self,
        m: &mut AstManager,
        last_result: &mut LastResult,
        args: &[Expr],
    ) -> Result<Expr, SmtError> {
        let result = self.mk_and_core(m, last_result, args)?;
        get_reduced_expr(result).ok_or_else(|| SmtError::Invariant("mk_and failed".into()))
    }

    // bool_rewriter::mk_nflat_and_core: drops true and duplicates, and detects false or a
    // complementary pair.
    fn mk_nflat_and(&self, m: &mut AstManager, args: &[Expr]) -> Result<Expr, SmtError> {
        m.flat_literals.clear();
        for arg in args.iter().copied() {
            if m.is_true(arg) {
                continue;
            }
            if m.is_false(arg) || m.flat_literals_add(arg) {
                return Ok(m.false_expr);
            }
        }
        let result = m.flat_literals.list.clone();
        match result.len() {
            0 => Ok(m.true_expr),
            1 => Ok(result[0]),
            _ => m.mk_and(&result),
        }
    }

    // bool_rewriter::mk_and_as_or: the negation of the disjunction of the negated conjuncts. Each
    // negation is built with its own temporaries, and the negations outlive the disjunction.
    fn mk_and_as_or(
        &mut self,
        m: &mut AstManager,
        last_result: &mut LastResult,
        args: &[Expr],
    ) -> Result<Expr, SmtError> {
        let mut negations = Vec::new();
        for arg in args.iter().copied() {
            negations.push(m.with_temporaries(|m| self.mk_not(m, last_result, arg))?);
        }
        let result = m.with_temporaries(|m| {
            let disjunction = self.mk_or(m, &negations)?;
            self.mk_not(m, last_result, disjunction)
        })?;
        for negation in &negations {
            m.dec_ref(*negation)?;
        }
        m.release_later(result)?;
        Ok(result)
    }

    // try_ite_eq: (ite c t e) = t is c when e is a value distinct from t, and likewise for e. The
    // main loop rewrites the result again.
    fn try_ite_eq(
        &self,
        m: &mut AstManager,
        ite: Expr,
        other: Expr,
    ) -> Result<Option<Rewrite>, SmtError> {
        if !self.is_ite(m, ite) {
            return Ok(None);
        }
        if m.get_arg(ite, 1) == other && self.are_distinct(m, m.get_arg(ite, 2), other) {
            return Ok(Some(Rewrite {
                expr: m.get_arg(ite, 0),
                depth: 1,
            }));
        }
        if m.get_arg(ite, 2) == other && self.are_distinct(m, m.get_arg(ite, 1), other) {
            return Ok(Some(Rewrite {
                expr: m.mk_not(m.get_arg(ite, 0))?,
                depth: 1,
            }));
        }
        Ok(None)
    }

    fn is_ite(&self, m: &AstManager, expr: Expr) -> bool {
        m.get_op(expr) == OP_ITE
    }

    fn are_distinct(&self, m: &AstManager, first: Expr, second: Expr) -> bool {
        first != second && m.is_unique_value(first) && m.is_unique_value(second)
    }

    // The ite_extra_rules of mk_eq_core: an ite against a value, or two ites of values.
    fn mk_ite_value_eq(
        &mut self,
        m: &mut AstManager,
        last_result: &mut LastResult,
        left: Expr,
        right: Expr,
        depth: usize,
    ) -> Result<Reduced, SmtError> {
        if self.is_ite(m, left) && m.is_unique_value(right) {
            return self.try_ite_value(m, last_result, left, right, depth);
        }
        if self.is_ite(m, right) && m.is_unique_value(left) {
            return self.try_ite_value(m, last_result, right, left, depth);
        }
        if !self.is_ite(m, left)
            || !self.is_ite(m, right)
            || ![
                m.get_arg(left, 1),
                m.get_arg(left, 2),
                m.get_arg(right, 1),
                m.get_arg(right, 2),
            ]
            .iter()
            .all(|arg| m.is_unique_value(*arg))
        {
            return Ok(Reduced::Failed);
        }
        let mk_or = |m: &mut AstManager, args: &[Expr]| m.mk_app(OP_OR, args, SORT_BOOL);
        let (left_condition, right_condition) = (m.get_arg(left, 0), m.get_arg(right, 0));
        let else_eq = m.mk_eq(m.get_arg(left, 2), m.get_arg(right, 2))?;
        let mut clauses = vec![mk_or(m, &[left_condition, right_condition, else_eq])?];
        let left_not = m.mk_not(left_condition)?;
        let right_not = m.mk_not(right_condition)?;
        let then_eq = m.mk_eq(m.get_arg(left, 1), m.get_arg(right, 1))?;
        clauses.push(mk_or(m, &[left_not, right_not, then_eq])?);
        let then_else_eq = m.mk_eq(m.get_arg(left, 1), m.get_arg(right, 2))?;
        clauses.push(mk_or(m, &[left_not, right_condition, then_else_eq])?);
        let else_then_eq = m.mk_eq(m.get_arg(left, 2), m.get_arg(right, 1))?;
        clauses.push(mk_or(m, &[left_condition, right_not, else_then_eq])?);
        Ok(Reduced::Rewrite(Rewrite {
            expr: m.mk_app(OP_AND, &clauses, SORT_BOOL)?,
            depth: UNBOUNDED_DEPTH,
        }))
    }

    // try_ite_value: (ite c t e) = v for a value v. It builds its results without rewriting them,
    // and the main loop rewrites them again.
    fn try_ite_value(
        &mut self,
        m: &mut AstManager,
        last_result: &mut LastResult,
        ite: Expr,
        value: Expr,
        depth: usize,
    ) -> Result<Reduced, SmtError> {
        if depth >= MAX_RECURSION_DEPTH {
            return Err(mk_recursion_error());
        }
        let condition = m.get_arg(ite, 0);
        let then_expr = m.get_arg(ite, 1);
        let else_expr = m.get_arg(ite, 2);
        // An equality of a branch is the first write to the result: write releases m_r after the
        // equality is made.
        // Z3 rewrites the equality of a branch only below depth 500.
        let mk_branch_eq =
            |this: &mut Self, m: &mut AstManager, last_result: &mut LastResult, branch: Expr| {
                let eq = if m.depths[branch as usize] < 500 {
                    this.mk_eq_at(m, last_result, branch, value, depth + 1)?
                } else {
                    m.mk_eq(branch, value)?
                };
                last_result.set(m, -1)?;
                Ok::<_, SmtError>(eq)
            };
        // mk_eq_plain.
        let mk_plain_eq = |this: &Self, m: &mut AstManager, branch: Expr| {
            if branch == value {
                Ok(m.true_expr)
            } else if this.are_distinct(m, branch, value) {
                Ok(m.false_expr)
            } else {
                m.mk_eq(branch, value)
            }
        };
        if self.are_distinct(m, value, else_expr) {
            let eq = mk_branch_eq(self, m, last_result, then_expr)?;
            let expr = m.mk_app(OP_AND, &[eq, condition], SORT_BOOL)?;
            return Ok(Reduced::Rewrite(Rewrite { expr, depth: 2 }));
        }
        if self.are_distinct(m, value, then_expr) {
            let eq = mk_branch_eq(self, m, last_result, else_expr)?;
            let negation = m.mk_not(condition)?;
            let expr = m.mk_app(OP_AND, &[eq, negation], SORT_BOOL)?;
            return Ok(Reduced::Rewrite(Rewrite { expr, depth: 2 }));
        }
        if value == then_expr {
            if value == else_expr {
                return Ok(Reduced::Done(m.true_expr));
            }
            let eq = self.mk_eq_at(m, last_result, else_expr, value, depth + 1)?;
            last_result.set(m, -1)?;
            let expr = m.mk_app(OP_OR, &[eq, condition], SORT_BOOL)?;
            return Ok(Reduced::Rewrite(Rewrite { expr, depth: 2 }));
        }
        if value == else_expr {
            let eq = self.mk_eq_at(m, last_result, then_expr, value, depth + 1)?;
            last_result.set(m, -1)?;
            let negation = m.mk_not(condition)?;
            let expr = m.mk_app(OP_OR, &[eq, negation], SORT_BOOL)?;
            return Ok(Reduced::Rewrite(Rewrite { expr, depth: 2 }));
        }
        let is_value_ite = |this: &Self, m: &AstManager, expr: Expr| {
            this.is_ite(m, expr)
                && m.is_unique_value(m.get_arg(expr, 1))
                && m.is_unique_value(m.get_arg(expr, 2))
        };
        let then_eq = if is_value_ite(self, m, then_expr) {
            self.try_ite_value(m, last_result, then_expr, value, depth + 1)?
        } else {
            Reduced::Failed
        };
        if let Some(then_eq) = get_reduced_expr(then_eq) {
            let else_eq = mk_plain_eq(self, m, else_expr)?;
            let expr = m.mk_app(OP_ITE, &[condition, then_eq, else_eq], SORT_BOOL)?;
            return Ok(Reduced::Rewrite(Rewrite { expr, depth: 2 }));
        }
        let else_eq = if is_value_ite(self, m, else_expr) {
            self.try_ite_value(m, last_result, else_expr, value, depth + 1)?
        } else {
            Reduced::Failed
        };
        if let Some(else_eq) = get_reduced_expr(else_eq) {
            let then_eq = mk_plain_eq(self, m, then_expr)?;
            let expr = m.mk_app(OP_ITE, &[condition, then_eq, else_eq], SORT_BOOL)?;
            return Ok(Reduced::Rewrite(Rewrite { expr, depth: 2 }));
        }
        // simplify_eq_ite's result is written even when it is null.
        last_result.set(m, -1)?;
        Ok(if self.is_disjoint_from(m, ite, value) {
            Reduced::Done(m.false_expr)
        } else {
            Reduced::Failed
        })
    }

    // simplify_eq_ite: whether every leaf of a tree of ites is a value distinct from the value.
    fn is_disjoint_from(&self, m: &AstManager, ite: Expr, value: Expr) -> bool {
        let mut visited: HashSet<Expr> = HashSet::new();
        let mut todo = vec![ite];
        while let Some(expr) = todo.pop() {
            if !visited.insert(expr) {
                continue;
            }
            if self.are_distinct(m, expr, value) {
                continue;
            }
            if !self.is_ite(m, expr) {
                return false;
            }
            todo.push(m.get_arg(expr, 1));
            todo.push(m.get_arg(expr, 2));
        }
        true
    }

    /// bool_rewriter::mk_eq, which does not rewrite the result of mk_eq_core again.
    pub fn mk_eq(
        &mut self,
        m: &mut AstManager,
        last_result: &mut LastResult,
        left: Expr,
        right: Expr,
    ) -> Result<Expr, SmtError> {
        self.mk_eq_at(m, last_result, left, right, 0)
    }

    fn mk_eq_at(
        &mut self,
        m: &mut AstManager,
        last_result: &mut LastResult,
        left: Expr,
        right: Expr,
        depth: usize,
    ) -> Result<Expr, SmtError> {
        match self.mk_eq_core(m, last_result, left, right, depth)? {
            Reduced::Failed => m.mk_eq(left, right),
            Reduced::Done(result) => Ok(result),
            Reduced::Rewrite(rewrite) => Ok(rewrite.expr),
        }
    }

    // bool_rewriter::mk_eq_core, after arith_rewriter::mk_eq_core folds numerals.
    fn mk_eq_core(
        &mut self,
        m: &mut AstManager,
        last_result: &mut LastResult,
        input_left: Expr,
        input_right: Expr,
        depth: usize,
    ) -> Result<Reduced, SmtError> {
        if depth >= MAX_RECURSION_DEPTH {
            return Err(mk_recursion_error());
        }
        if input_left == input_right {
            return Ok(Reduced::Done(m.true_expr));
        }
        if m.is_unique_value(input_left) && m.is_unique_value(input_right) {
            return Ok(Reduced::Done(m.false_expr));
        }
        let ite_eq = match self.try_ite_eq(m, input_left, input_right)? {
            Some(ite_eq) => Some(ite_eq),
            None => self.try_ite_eq(m, input_right, input_left)?,
        };
        if let Some(ite_eq) = ite_eq {
            return Ok(Reduced::Rewrite(ite_eq));
        }
        let ite_value_eq = self.mk_ite_value_eq(m, last_result, input_left, input_right, depth)?;
        if ite_value_eq != Reduced::Failed {
            return Ok(ite_value_eq);
        }
        if m.sorts[input_left as usize] != SORT_BOOL {
            return Ok(Reduced::Failed);
        }
        let is_unfolded = m.is_not(input_left) && m.is_not(input_right);
        let left = if is_unfolded {
            m.get_arg(input_left, 0)
        } else {
            input_left
        };
        let right = if is_unfolded {
            m.get_arg(input_right, 0)
        } else {
            input_right
        };
        if m.is_true(left) {
            return Ok(Reduced::Done(right));
        }
        if m.is_false(left) {
            return Ok(Reduced::Done(self.mk_not_at(
                m,
                last_result,
                right,
                depth + 1,
            )?));
        }
        if m.is_true(right) {
            return Ok(Reduced::Done(left));
        }
        if m.is_false(right) {
            return Ok(Reduced::Done(self.mk_not_at(
                m,
                last_result,
                left,
                depth + 1,
            )?));
        }
        if m.is_complement(left, right) {
            return Ok(Reduced::Done(m.false_expr));
        }
        let is_swapped = m.is_not(right);
        let lhs = if is_swapped { right } else { left };
        let rhs = if is_swapped { left } else { right };
        if m.is_not(lhs) {
            let eq = m.mk_eq(m.get_arg(lhs, 0), rhs)?;
            return Ok(Reduced::Rewrite(Rewrite {
                expr: m.mk_not(eq)?,
                depth: 2,
            }));
        }
        if is_unfolded {
            return Ok(Reduced::Rewrite(Rewrite {
                expr: m.mk_eq(lhs, rhs)?,
                depth: 1,
            }));
        }
        // (= (= a b) (= a (not b))) is false.
        if m.get_op(lhs) == OP_EQ && m.get_op(rhs) == OP_EQ {
            let is_negation_of =
                |expr: Expr, other: Expr| m.is_not(expr) && m.get_arg(expr, 0) == other;
            let (lhs0, lhs1) = (m.get_arg(lhs, 0), m.get_arg(lhs, 1));
            let (rhs0, rhs1) = (m.get_arg(rhs, 0), m.get_arg(rhs, 1));
            if (lhs0 == rhs0 && (is_negation_of(rhs1, lhs1) || is_negation_of(lhs1, rhs1)))
                || (lhs1 == rhs1 && (is_negation_of(rhs0, lhs0) || is_negation_of(lhs0, rhs0)))
            {
                return Ok(Reduced::Done(m.false_expr));
            }
        }
        Ok(Reduced::Failed)
    }

    // bool_rewriter::mk_distinct_core: two arguments become a disequality, which the main loop
    // rewrites again, since mk_eq may dispatch to other rewriters. Z3 keeps a longer distinct,
    // which tlapm does not send, and this port expands it into disequalities.
    fn mk_distinct(
        &mut self,
        m: &mut AstManager,
        last_result: &mut LastResult,
        args: &[Expr],
    ) -> Result<Reduced, SmtError> {
        if args.len() == 2 {
            let eq = self.mk_eq(m, last_result, args[0], args[1])?;
            let expr = self.mk_not(m, last_result, eq)?;
            return Ok(Reduced::Rewrite(Rewrite { expr, depth: 2 }));
        }
        let mut pairs: Vec<Expr> = Vec::new();
        for left in 0..args.len() {
            for right in left + 1..args.len() {
                let eq = self.mk_eq(m, last_result, args[left], args[right])?;
                pairs.push(self.mk_not(m, last_result, eq)?);
            }
        }
        Ok(Reduced::Done(self.mk_and(m, last_result, &pairs)?))
    }

    // bool_rewriter::mk_ite_core with elim_ite and ite_extra_rules. It applies the rules that
    // change only the condition or a branch in sequence, and a result that it builds from new
    // terms comes as a Rewrite for the main loop.
    fn mk_ite(
        &mut self,
        m: &mut AstManager,
        last_result: &mut LastResult,
        input_condition: Expr,
        input_then: Expr,
        input_else: Expr,
    ) -> Result<Reduced, SmtError> {
        let is_negated = m.is_not(input_condition);
        let condition = if is_negated {
            m.get_arg(input_condition, 0)
        } else {
            input_condition
        };
        let else_candidate = if is_negated { input_then } else { input_else };
        let then_candidate = if is_negated { input_else } else { input_then };
        // (ite c (ite c t1 t2) t3) is (ite c t1 t3).
        let then_expr =
            if self.is_ite(m, then_candidate) && m.get_arg(then_candidate, 0) == condition {
                m.get_arg(then_candidate, 1)
            } else {
                then_candidate
            };
        let sort = m.sorts[then_expr as usize];
        // (ite c t1 (ite c2 t1 t2)) is (ite (or c c2) t1 t2).
        if self.is_ite(m, else_candidate) && m.get_arg(else_candidate, 1) == then_expr {
            let disjunction =
                m.mk_app(OP_OR, &[condition, m.get_arg(else_candidate, 0)], SORT_BOOL)?;
            let expr = m.mk_app(
                OP_ITE,
                &[disjunction, then_expr, m.get_arg(else_candidate, 2)],
                sort,
            )?;
            return Ok(Reduced::Rewrite(Rewrite { expr, depth: 3 }));
        }
        // (ite c t1 (ite c t2 t3)) is (ite c t1 t3).
        let else_expr =
            if self.is_ite(m, else_candidate) && m.get_arg(else_candidate, 0) == condition {
                m.get_arg(else_candidate, 2)
            } else {
                else_candidate
            };
        if m.is_true(condition) {
            return Ok(Reduced::Done(then_expr));
        }
        if m.is_false(condition) {
            return Ok(Reduced::Done(else_expr));
        }
        if then_expr == else_expr {
            return Ok(Reduced::Done(then_expr));
        }
        if sort == SORT_BOOL {
            if m.is_true(then_expr) {
                return Ok(Reduced::Done(if m.is_false(else_expr) {
                    condition
                } else {
                    self.mk_or(m, &[condition, else_expr])?
                }));
            }
            if m.is_false(then_expr) {
                if m.is_true(else_expr) {
                    return Ok(Reduced::Done(self.mk_not(m, last_result, condition)?));
                }
                let negation = self.mk_not(m, last_result, condition)?;
                let expr = self.mk_and(m, last_result, &[negation, else_expr])?;
                return Ok(Reduced::Rewrite(Rewrite { expr, depth: 1 }));
            }
            if m.is_true(else_expr) {
                let negation = self.mk_not(m, last_result, condition)?;
                return Ok(Reduced::Done(self.mk_or(m, &[negation, then_expr])?));
            }
            if m.is_false(else_expr) || else_expr == condition {
                let expr = self.mk_and(m, last_result, &[condition, then_expr])?;
                return Ok(Reduced::Rewrite(Rewrite { expr, depth: 1 }));
            }
            if then_expr == condition {
                return Ok(Reduced::Done(self.mk_or(m, &[condition, else_expr])?));
            }
            // is_complement_core: one branch is the negation of the other.
            if (m.is_not(then_expr) && m.get_arg(then_expr, 0) == else_expr)
                || (m.is_not(else_expr) && m.get_arg(else_expr, 0) == then_expr)
            {
                return Ok(Reduced::Done(self.mk_eq(
                    m,
                    last_result,
                    condition,
                    then_expr,
                )?));
            }
        }
        let is_else_ite = self.is_ite(m, else_expr);
        if self.is_ite(m, then_expr) {
            // (ite c1 (ite c2 t1 t2) t1) is (ite (and c1 (not c2)) t2 t1).
            if else_expr == m.get_arg(then_expr, 1) {
                let negation = self.mk_not(m, last_result, m.get_arg(then_expr, 0))?;
                let conjunction = self.mk_and(m, last_result, &[condition, negation])?;
                let expr = m.mk_app(
                    OP_ITE,
                    &[conjunction, m.get_arg(then_expr, 2), else_expr],
                    sort,
                )?;
                return Ok(Reduced::Rewrite(Rewrite { expr, depth: 2 }));
            }
            // (ite c1 (ite c2 t1 t2) t2) is (ite (and c1 c2) t1 t2).
            if else_expr == m.get_arg(then_expr, 2) {
                let conjunction =
                    self.mk_and(m, last_result, &[condition, m.get_arg(then_expr, 0)])?;
                let expr = m.mk_app(
                    OP_ITE,
                    &[conjunction, m.get_arg(then_expr, 1), else_expr],
                    sort,
                )?;
                return Ok(Reduced::Rewrite(Rewrite { expr, depth: 2 }));
            }
            // (ite c1 (ite c2 t1 t2) (ite c3 t1 t2)) is
            // (ite (or (and c1 c2) (and (not c1) c3)) t1 t2), and with (ite c3 t2 t1) the last
            // conjunct is (not c3).
            let is_same_branches = is_else_ite
                && m.get_arg(then_expr, 1) == m.get_arg(else_expr, 1)
                && m.get_arg(then_expr, 2) == m.get_arg(else_expr, 2);
            let is_swapped_branches = is_else_ite
                && m.get_arg(then_expr, 1) == m.get_arg(else_expr, 2)
                && m.get_arg(then_expr, 2) == m.get_arg(else_expr, 1);
            if is_same_branches || is_swapped_branches {
                let first = self.mk_and(m, last_result, &[condition, m.get_arg(then_expr, 0)])?;
                let negation = self.mk_not(m, last_result, condition)?;
                let last = if is_same_branches {
                    m.get_arg(else_expr, 0)
                } else {
                    self.mk_not(m, last_result, m.get_arg(else_expr, 0))?
                };
                let second = self.mk_and(m, last_result, &[negation, last])?;
                let disjunction = self.mk_or(m, &[first, second])?;
                let expr = m.mk_app(
                    OP_ITE,
                    &[
                        disjunction,
                        m.get_arg(then_expr, 1),
                        m.get_arg(then_expr, 2),
                    ],
                    sort,
                )?;
                return Ok(Reduced::Rewrite(Rewrite { expr, depth: 3 }));
            }
        }
        if is_else_ite {
            // (ite c1 t1 (ite c2 t1 t2)) is (ite (or c1 c2) t1 t2).
            if then_expr == m.get_arg(else_expr, 1) {
                let disjunction = self.mk_or(m, &[condition, m.get_arg(else_expr, 0)])?;
                let expr = m.mk_app(
                    OP_ITE,
                    &[disjunction, then_expr, m.get_arg(else_expr, 2)],
                    sort,
                )?;
                return Ok(Reduced::Rewrite(Rewrite { expr, depth: 1 }));
            }
            // (ite c1 t1 (ite c2 t2 t1)) is (ite (or c1 (not c2)) t1 t2).
            if then_expr == m.get_arg(else_expr, 2) {
                let negation = self.mk_not(m, last_result, m.get_arg(else_expr, 0))?;
                let disjunction = self.mk_or(m, &[condition, negation])?;
                let expr = m.mk_app(
                    OP_ITE,
                    &[disjunction, then_expr, m.get_arg(else_expr, 1)],
                    sort,
                )?;
                return Ok(Reduced::Rewrite(Rewrite { expr, depth: 1 }));
            }
        }
        Ok(Reduced::Done(m.mk_app(
            OP_ITE,
            &[condition, then_expr, else_expr],
            sort,
        )?))
    }

    /// poly_rewriter::mk_add and mk_sub with a result: arith_rewriter's sum or difference, which
    /// is not rewritten again.
    pub fn mk_add(&mut self, m: &mut AstManager, args: &[Expr]) -> Result<Expr, SmtError> {
        match self.arith.mk_add(m, args)? {
            Some(result) => Ok(result),
            None => self.arith.mk_add_app(m, args),
        }
    }

    pub fn mk_sub(
        &mut self,
        m: &mut AstManager,
        first: Expr,
        second: Expr,
    ) -> Result<Expr, SmtError> {
        let result = self.arith.mk_sub(m, &[first, second])?;
        get_reduced_expr(result).ok_or_else(|| SmtError::Invariant("mk_sub failed".into()))
    }
}

/// rewriter_tpl with th_rewriter_cfg: `RewriterTpl<ThRewriterCfg>` with the TypeScript
/// `Rewriter`'s methods.
#[derive(Clone, Debug)]
pub struct Rewriter {
    pub cfg: ThRewriterCfg,
    pub engine: RewriterEngine,
}

impl Rewriter {
    /// `new Rewriter(manager, options, isNestedDer = false)`.
    pub fn new(m: &AstManager, options: RewriterOptions, is_nested_der: bool) -> Rewriter {
        Rewriter {
            cfg: ThRewriterCfg::new(m, options, is_nested_der),
            engine: RewriterEngine::new(m),
        }
    }

    /// ~imp: the members of th_rewriter_cfg go before the caches of rewriter_tpl.
    pub fn release(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.cfg.release(m)?;
        self.engine.release(m)
    }

    pub fn reset(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.engine.reset(m)
    }

    pub fn cleanup(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.engine.cleanup(m)
    }

    /// The result comes with a reference, which the caller releases.
    pub fn rewrite(&mut self, m: &mut AstManager, expr: Expr) -> Result<Expr, SmtError> {
        self.engine.rewrite(m, &mut self.cfg, expr)
    }

    pub fn rewrite_with_bindings(
        &mut self,
        m: &mut AstManager,
        expr: Expr,
        bindings: &[Expr],
    ) -> Result<Expr, SmtError> {
        self.engine
            .rewrite_with_bindings(m, &mut self.cfg, expr, bindings)
    }

    /// releaseResult: try_ite_value writes the result of reduce_app, which is the m_r of the
    /// rewriter that applies this one, as it goes: the first write releases what m_r held.
    pub fn release_result(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.engine.set_last_result(m, -1)
    }

    /// updt_params with elim_and, which asserted_formulas turns on after NNF. The caller resets the
    /// rewriter.
    pub fn set_eliminating_and(&mut self, is_eliminating_and: bool) {
        self.cfg.set_eliminating_and(is_eliminating_and);
    }

    /// th_rewriter::set_substitution: rewrites replace each key of the substitution with its
    /// value, and the rewriter is reset. The caller may extend the substitution between rewrites
    /// without a reset, through `get_substitution_mut`.
    pub fn set_substitution(
        &mut self,
        m: &mut AstManager,
        substitution: OrderedMap<Expr, Expr>,
    ) -> Result<(), SmtError> {
        self.cfg.substitution = substitution;
        self.reset(m)
    }

    /// The substitution, which the caller extends between rewrites as the TypeScript's caller
    /// extends the map it passed.
    pub fn get_substitution_mut(&mut self) -> &mut OrderedMap<Expr, Expr> {
        &mut self.cfg.substitution
    }

    pub fn get_subst(&self, expr: Expr) -> Option<Expr> {
        self.cfg.get_subst_of(expr)
    }

    pub fn is_flat_assoc(&self, m: &AstManager, decl: Decl) -> bool {
        self.cfg.is_flat_assoc(m, decl)
    }

    pub fn is_rewriting_patterns(&self) -> bool {
        self.cfg.is_rewriting_patterns()
    }

    /// The result comes with a reference.
    pub fn reduce_app(
        &mut self,
        m: &mut AstManager,
        decl: Decl,
        args: &[Expr],
        sort: Sort,
    ) -> Result<Reduced, SmtError> {
        self.cfg
            .reduce_app(m, self.engine.last_result_mut(), decl, args, sort)
    }

    /// The result comes with a reference.
    pub fn reduce_quantifier(
        &mut self,
        m: &mut AstManager,
        expr: Expr,
        body: Expr,
        patterns: &[Expr],
    ) -> Result<Expr, SmtError> {
        self.cfg.reduce_quantifier(m, expr, body, patterns)
    }

    /// th_rewriter::mk_app: one reduction, without rewriting what it returns.
    pub fn mk_app(
        &mut self,
        m: &mut AstManager,
        decl: Decl,
        args: &[Expr],
        sort: Sort,
    ) -> Result<Expr, SmtError> {
        self.cfg
            .mk_app(m, self.engine.last_result_mut(), decl, args, sort)
    }

    /// th_rewriter's mk_app, with the result of a Rewrite rewritten again.
    pub fn mk_app_core(
        &mut self,
        m: &mut AstManager,
        decl: Decl,
        args: &[Expr],
        sort: Sort,
    ) -> Result<Expr, SmtError> {
        self.cfg
            .mk_app_core(m, self.engine.last_result_mut(), decl, args, sort)
    }

    /// The reductions of the Boolean and arithmetic rewriters, which the model evaluator applies
    /// too. last_result is the m_r that try_ite_value writes: the model evaluator's own, which its
    /// `releaseResult` writes in the TypeScript.
    pub fn reduce_app_core(
        &mut self,
        m: &mut AstManager,
        last_result: &mut LastResult,
        decl: Decl,
        args: &[Expr],
    ) -> Result<Reduced, SmtError> {
        self.cfg.reduce_app_core(m, last_result, decl, args)
    }

    pub fn mk_not(&mut self, m: &mut AstManager, arg: Expr) -> Result<Expr, SmtError> {
        self.cfg.mk_not(m, self.engine.last_result_mut(), arg)
    }

    pub fn mk_or(&mut self, m: &mut AstManager, args: &[Expr]) -> Result<Expr, SmtError> {
        self.cfg.mk_or(m, args)
    }

    pub fn mk_and(&mut self, m: &mut AstManager, args: &[Expr]) -> Result<Expr, SmtError> {
        self.cfg.mk_and(m, self.engine.last_result_mut(), args)
    }

    pub fn mk_eq(&mut self, m: &mut AstManager, left: Expr, right: Expr) -> Result<Expr, SmtError> {
        self.cfg
            .mk_eq(m, self.engine.last_result_mut(), left, right)
    }

    pub fn mk_add(&mut self, m: &mut AstManager, args: &[Expr]) -> Result<Expr, SmtError> {
        self.cfg.mk_add(m, args)
    }

    pub fn mk_sub(
        &mut self,
        m: &mut AstManager,
        first: Expr,
        second: Expr,
    ) -> Result<Expr, SmtError> {
        self.cfg.mk_sub(m, first, second)
    }
}
