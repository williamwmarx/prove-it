//! Ported from Z3 (src/ast/rewriter/rewriter.h, rewriter.cpp, rewriter_def.h), MIT license, through
//! `rewriter-tpl.ts`. The main loop of Z3's rewriters, ported step for step with Z3's references:
//! the result stack, the caches and m_r hold their expressions, so that expressions are created and
//! deleted in Z3's order. A configuration overrides the hooks of default_rewriter_cfg.
//!
//! # Design
//!
//! The TypeScript's `RewriterTpl` is default_rewriter_cfg, which a configuration subclasses to
//! override its hooks, and it owns a `RewriterEngine`, the main loop, which calls them. Here the
//! hooks are the trait [`RewriterConfig`], each with the TypeScript base class's default, and
//! [`RewriterTpl<C>`] owns a configuration `cfg: C` beside its `engine: RewriterEngine`. The
//! engine is not generic: each of its methods that calls a hook takes `cfg: &mut C`, so that a
//! hook may change the configuration's own state while the engine runs, and the caller can reach
//! the configuration as `rewriter.cfg` (as the TypeScript calls a configuration's own methods,
//! such as th_rewriter's `reduceQuantifier`, on the rewriter object). Like every class of the core,
//! none of them keeps the manager: each method takes `m: &mut AstManager`.
//!
//! - The TypeScript tests whether a configuration overrides `getSubst` and `getMacro`, and skips
//!   the calls when it does not. A configuration says so with the associated constants
//!   [`RewriterConfig::IS_SUBSTITUTING`] and [`RewriterConfig::IS_EXPANDING_MACROS`].
//! - `reduceApp` returns `number | Rewrite`, with -1 for BR_FAILED: here [`Reduced`].
//! - A configuration's `setLastResult(-1)` (th_rewriter's `releaseResult`, which writes the m_r of
//!   the rewriter that applies it) is the [`LastResult`] that `reduce_app` receives: the engine
//!   passes its own m_r, and a configuration that applies another one's `reduce_app` passes it on.
//! - `mkNested` returns a rewriter with the same configuration for a constant that rewrites to a
//!   term with arguments. Here it returns the configuration, `None` for the default one (the
//!   TypeScript's base `new RewriterTpl(manager)`), and the engine builds the nested rewriter.
//! - A configuration's `release`, which runs before the engine's caches are released (`~imp`), is
//!   [`RewriterConfig::release`].
//! - The depth of a rewrite, `Infinity` in the TypeScript, is [`UNBOUNDED_DEPTH`].
//! - `VarShifterCore`'s abstract `processVar` is the `ShiftMode` its two shifters set.
//!
//! The main loops keep their frames on a stack of their own; the one recursion, the nested
//! rewriter of a constant, stops past [`MAX_RECURSION_DEPTH`] (design/smt-core.md, recursion).

use crate::core::act_cache::ActCache;
use crate::core::ast::{
    AstManager, Decl, Expr, KIND_APP, KIND_QUANTIFIER, KIND_VAR, OP_ITE, QuantifierData, Sort,
};
use crate::util::error::SmtError;
use crate::util::ordered_map::OrderedSet;

/// The depth past which the port's recursions stop with `SmtError::Unsupported`, where the
/// TypeScript's would overflow the stack and the solver answer unknown.
pub const MAX_RECURSION_DEPTH: usize = 50_000;

/// The depth of a rewrite without a bound, the TypeScript's `Infinity`.
pub const UNBOUNDED_DEPTH: u32 = u32::MAX;

/// A result that the main loop rewrites again to depth levels, like Z3's BR_REWRITE1 (depth 1) to
/// BR_REWRITE_FULL (depth [`UNBOUNDED_DEPTH`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Rewrite {
    pub expr: Expr,
    pub depth: u32,
}

/// What `reduce_app` returns: BR_FAILED, a result, or a result to rewrite again. A result comes
/// with a reference.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Reduced {
    Failed,
    Done(Expr),
    Rewrite(Rewrite),
}

/// The depth to rewrite a Rewrite's result to. A frame keeps its depth in two bits, where 3 is
/// RW_UNBOUNDED_DEPTH, so BR_REWRITE3 rewrites the result without a bound.
pub fn get_rewrite_depth(rewrite: &Rewrite) -> u32 {
    if rewrite.depth >= 3 {
        UNBOUNDED_DEPTH
    } else {
        rewrite.depth
    }
}

/// m_r: the last result of a rewriter, which Z3 holds until it assigns the next one.
#[derive(Clone, Copy, Debug)]
pub struct LastResult {
    expr: Expr,
}

impl LastResult {
    pub fn new() -> LastResult {
        LastResult { expr: -1 }
    }

    pub fn get(&self) -> Expr {
        self.expr
    }

    /// setLastResult: the new value gains a reference before the old one loses its own.
    pub fn set(&mut self, m: &mut AstManager, expr: Expr) -> Result<(), SmtError> {
        if expr != -1 {
            m.inc_ref(expr);
        }
        if self.expr != -1 {
            m.dec_ref(self.expr)?;
        }
        self.expr = expr;
        Ok(())
    }
}

impl Default for LastResult {
    fn default() -> LastResult {
        LastResult::new()
    }
}

/// The hooks of default_rewriter_cfg, which a configuration overrides. The results of
/// `reduce_app` and `reduce_quantifier` come with a reference, and -1 is Z3's false.
pub trait RewriterConfig: Sized {
    /// Whether the configuration overrides `get_subst`. Otherwise nothing is substituted and the
    /// call is skipped.
    const IS_SUBSTITUTING: bool = false;
    /// Whether the configuration overrides `get_macro`. Otherwise nothing is expanded and the call
    /// is skipped.
    const IS_EXPANDING_MACROS: bool = false;

    fn is_flat_assoc(&self, _m: &AstManager, _decl: Decl) -> bool {
        false
    }

    fn is_rewriting_patterns(&self) -> bool {
        true
    }

    fn get_subst(&mut self, _m: &mut AstManager, _expr: Expr) -> Result<Option<Expr>, SmtError> {
        Ok(None)
    }

    /// reduce_app: last_result is the m_r of the rewriter that applies the configuration.
    fn reduce_app(
        &mut self,
        _m: &mut AstManager,
        _last_result: &mut LastResult,
        _decl: Decl,
        _args: &[Expr],
        _sort: Sort,
    ) -> Result<Reduced, SmtError> {
        Ok(Reduced::Failed)
    }

    /// get_macro: the definition of decl over (:var i) for argument i, or -1.
    fn get_macro(&mut self, _m: &mut AstManager, _decl: Decl) -> Result<Expr, SmtError> {
        Ok(-1)
    }

    /// reduce_macro: whether a ground definition is rewritten rather than taken as it is.
    fn is_reducing_macro(&self) -> bool {
        false
    }

    fn reduce_quantifier(
        &mut self,
        _m: &mut AstManager,
        _expr: Expr,
        _body: Expr,
        _patterns: &[Expr],
    ) -> Result<Expr, SmtError> {
        Ok(-1)
    }

    /// The configuration of a rewriter like this one, for a constant that rewrites to a term with
    /// arguments; `None` for default_rewriter_cfg.
    fn mk_nested(&mut self, _m: &mut AstManager) -> Result<Option<Self>, SmtError> {
        Ok(None)
    }

    /// The configuration's part of `~imp`, before the caches of rewriter_tpl.
    fn release(&mut self, _m: &mut AstManager) -> Result<(), SmtError> {
        Ok(())
    }
}

/// default_rewriter_cfg, which overrides nothing.
#[derive(Clone, Copy, Debug, Default)]
pub struct DefaultRewriterConfig;

impl RewriterConfig for DefaultRewriterConfig {}

// rewriter_tpl's frame states.
const PROCESS_CHILDREN: u8 = 0;
const REWRITE_BUILTIN: u8 = 1;
const EXPAND_DEF: u8 = 2;

// A rewrite still to finish: its expression, state, next child, the depth left to rewrite, where
// its children's results start on the result stack, whether to cache its result, and whether a
// child changed.
#[derive(Clone, Copy, Debug)]
struct Frame {
    curr: Expr,
    state: u8,
    child_index: usize,
    max_depth: u32,
    spos: usize,
    is_caching: bool,
    has_new_child: bool,
}

#[derive(Clone, Copy, Debug)]
struct Scope {
    root: Expr,
    num_qvars: i32,
}

// rewriter_core: the frames, the result stack and one cache per quantifier scope.
#[derive(Clone, Debug)]
struct RewriterCore {
    // m_frame_stack: the first num_frames frames are open. Like the svector, the stack keeps the
    // frames past them, which push_frame writes over.
    frames: Vec<Frame>,
    num_frames: usize,
    result_stack: Vec<Expr>,
    caches: Vec<ActCache>,
    scopes: Vec<Scope>,
    root: Expr,
    num_qvars: i32,
}

impl RewriterCore {
    fn new(m: &AstManager) -> RewriterCore {
        RewriterCore {
            frames: Vec::new(),
            num_frames: 0,
            result_stack: Vec::new(),
            caches: vec![ActCache::new(m.get_num_asts())],
            scopes: Vec::new(),
            root: -1,
            num_qvars: 0,
        }
    }

    fn cache(&mut self) -> &mut ActCache {
        let index = self.scopes.len();
        &mut self.caches[index]
    }

    // must_cache: the result of a shared application with arguments or quantifier.
    fn is_caching(&self, m: &AstManager, expr: Expr) -> bool {
        m.get_ref_count(expr) > 1
            && expr != self.root
            && (m.kinds[expr as usize] == KIND_QUANTIFIER
                || (m.kinds[expr as usize] == KIND_APP && m.get_num_args(expr) > 0))
    }

    fn push_result(&mut self, m: &mut AstManager, expr: Expr) {
        m.inc_ref(expr);
        self.result_stack.push(expr);
    }

    fn shrink_results(&mut self, m: &mut AstManager, size: usize) -> Result<(), SmtError> {
        for index in size..self.result_stack.len() {
            m.dec_ref(self.result_stack[index])?;
        }
        self.result_stack.truncate(size);
        Ok(())
    }

    fn set_new_child_flag(&mut self, old_expr: Expr, new_expr: Expr) {
        if old_expr != new_expr && self.num_frames > 0 {
            self.frames[self.num_frames - 1].has_new_child = true;
        }
    }

    fn push_frame(&mut self, expr: Expr, is_caching: bool, max_depth: u32) {
        let frame = Frame {
            curr: expr,
            state: PROCESS_CHILDREN,
            child_index: 0,
            max_depth,
            spos: self.result_stack.len(),
            is_caching,
            has_new_child: false,
        };
        if self.num_frames == self.frames.len() {
            self.frames.push(frame);
        } else {
            self.frames[self.num_frames] = frame;
        }
        self.num_frames += 1;
    }

    // begin_scope: each quantifier level gets its own cache, which starts empty.
    fn begin_scope(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.scopes.push(Scope {
            root: self.root,
            num_qvars: self.num_qvars,
        });
        if self.scopes.len() == self.caches.len() {
            self.caches.push(ActCache::new(m.get_num_asts()));
        }
        self.cache().reset(m)
    }

    fn end_scope(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.cache().reset(m)?;
        let scope = self
            .scopes
            .pop()
            .ok_or_else(|| SmtError::Invariant("the rewriter has no scope to end".into()))?;
        self.root = scope.root;
        self.num_qvars = scope.num_qvars;
        Ok(())
    }

    // rewriter_core::reset: releases the outermost cache and the result stack.
    fn reset_core(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.caches[0].reset(m)?;
        self.num_frames = 0;
        self.shrink_results(m, 0)?;
        self.root = -1;
        self.num_qvars = 0;
        self.scopes = Vec::new();
        Ok(())
    }

    // del_cache_stack: releases every cache, the outermost first.
    fn release_caches(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        for cache in &mut self.caches {
            cache.reset(m)?;
        }
        Ok(())
    }

    // rewriter_core::cleanup.
    fn cleanup_core(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.release_caches(m)?;
        self.shrink_results(m, 0)?;
        self.caches = vec![ActCache::new(m.get_num_asts())];
        self.frames = Vec::new();
        self.num_frames = 0;
        self.scopes = Vec::new();
        self.root = -1;
        self.num_qvars = 0;
        Ok(())
    }

    // The result of main_loop: the top of the result stack, whose reference passes to the caller.
    fn pop_result(&mut self) -> Result<Expr, SmtError> {
        self.result_stack
            .pop()
            .ok_or_else(|| SmtError::Invariant("the rewriter has no result".into()))
    }
}

// The child of a quantifier at index: its body, then its patterns.
fn get_quantifier_child(m: &AstManager, quantifier: Expr, index: usize) -> Result<Expr, SmtError> {
    let data = m.get_quantifier(quantifier)?;
    Ok(if index == 0 {
        data.body
    } else {
        data.patterns[index - 1]
    })
}

// What processVar does in each subclass of var_shifter_core.
#[derive(Clone, Copy, Debug)]
enum ShiftMode {
    // var_shifter: a free variable with index at least bound moves up by shift1, any other by
    // shift2.
    Shift {
        bound: i32,
        shift1: i32,
        shift2: i32,
    },
    // inv_var_shifter: the free variables move down by amount.
    Inv {
        amount: i32,
    },
}

/// var_shifter_core: rebuilds an expression with its free variables renamed by process_var.
#[derive(Clone, Debug)]
struct VarShifterCore {
    core: RewriterCore,
    mode: ShiftMode,
}

impl VarShifterCore {
    fn new(m: &AstManager, mode: ShiftMode) -> VarShifterCore {
        VarShifterCore {
            core: RewriterCore::new(m),
            mode,
        }
    }

    fn process_var(&mut self, m: &mut AstManager, variable: Expr) {
        let index = m.values[variable as usize];
        if index < self.core.num_qvars {
            self.core.push_result(m, variable);
            return;
        }
        let shifted = match self.mode {
            ShiftMode::Shift {
                bound,
                shift1,
                shift2,
            } => {
                index
                    + if index - self.core.num_qvars >= bound {
                        shift1
                    } else {
                        shift2
                    }
            }
            ShiftMode::Inv { amount } => index - amount,
        };
        let sort = m.sorts[variable as usize];
        let result = m.mk_var(shifted, sort);
        self.core.push_result(m, result);
        self.core.set_new_child_flag(variable, -1);
    }

    fn visit(&mut self, m: &mut AstManager, expr: Expr) -> bool {
        if m.is_ground_app(expr) {
            self.core.push_result(m, expr);
            return true;
        }
        let is_caching = self.core.is_caching(m, expr);
        if is_caching && let Some(cached) = self.core.cache().find(m, expr, 0) {
            self.core.push_result(m, cached);
            self.core.set_new_child_flag(expr, cached);
            return true;
        }
        if m.kinds[expr as usize] == KIND_VAR {
            self.process_var(m, expr);
            return true;
        }
        self.core.push_frame(expr, is_caching, UNBOUNDED_DEPTH);
        false
    }

    fn process_app(&mut self, m: &mut AstManager, expr: Expr, top: usize) -> Result<(), SmtError> {
        let num_args = m.get_num_args(expr);
        while self.core.frames[top].child_index < num_args {
            let arg = m.get_arg(expr, self.core.frames[top].child_index);
            self.core.frames[top].child_index += 1;
            if !self.visit(m, arg) {
                return Ok(());
            }
        }
        let frame = self.core.frames[top];
        let result = if frame.has_new_child {
            m.mk_app(
                m.decls[expr as usize],
                &self.core.result_stack[frame.spos..],
                m.sorts[expr as usize],
            )?
        } else {
            expr
        };
        self.finish(m, expr, frame, result)?;
        if frame.is_caching {
            self.core.cache().insert(m, expr, 0, result)?;
        }
        Ok(())
    }

    fn process_quantifier(
        &mut self,
        m: &mut AstManager,
        expr: Expr,
        top: usize,
    ) -> Result<(), SmtError> {
        let (body, num_decls, num_children) = {
            let data = m.get_quantifier(expr)?;
            (data.body, data.sorts.len(), 1 + data.patterns.len())
        };
        if self.core.frames[top].child_index == 0 {
            self.core.begin_scope(m)?;
            self.core.num_qvars += num_decls as i32;
            self.core.root = body;
        }
        while self.core.frames[top].child_index < num_children {
            let child = get_quantifier_child(m, expr, self.core.frames[top].child_index)?;
            self.core.frames[top].child_index += 1;
            if !self.visit(m, child) {
                return Ok(());
            }
        }
        let frame = self.core.frames[top];
        let result = if frame.has_new_child {
            let data = m.get_quantifier(expr)?;
            let data = QuantifierData {
                body: self.core.result_stack[frame.spos],
                patterns: self.core.result_stack[frame.spos + 1..].to_vec(),
                ..data.clone()
            };
            m.mk_quantifier(data)?
        } else {
            expr
        };
        self.finish(m, expr, frame, result)?;
        self.core.end_scope(m)?;
        if frame.is_caching {
            self.core.cache().insert(m, expr, 0, result)?;
        }
        Ok(())
    }

    fn finish(
        &mut self,
        m: &mut AstManager,
        expr: Expr,
        frame: Frame,
        result: Expr,
    ) -> Result<(), SmtError> {
        self.core.shrink_results(m, frame.spos)?;
        self.core.push_result(m, result);
        self.core.num_frames -= 1;
        self.core.set_new_child_flag(expr, result);
        Ok(())
    }

    // main_loop: the result comes with a reference, which the caller releases.
    fn main_loop(&mut self, m: &mut AstManager, expr: Expr) -> Result<Expr, SmtError> {
        self.core.root = expr;
        if !self.visit(m, expr) {
            while self.core.num_frames > 0 {
                let top = self.core.num_frames - 1;
                let frame = self.core.frames[top];
                let curr = frame.curr;
                if frame.child_index == 0
                    && frame.is_caching
                    && let Some(cached) = self.core.cache().find(m, curr, 0)
                {
                    self.core.push_result(m, cached);
                    self.core.num_frames -= 1;
                    self.core.set_new_child_flag(curr, cached);
                    continue;
                }
                if m.kinds[curr as usize] == KIND_APP {
                    self.process_app(m, curr, top)?;
                } else {
                    self.process_quantifier(m, curr, top)?;
                }
            }
        }
        self.core.pop_result()
    }

    fn reset(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.core.reset_core(m)
    }

    fn cleanup(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.core.cleanup_core(m)
    }

    fn release(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.core.release_caches(m)
    }
}

/// var_shifter: a free variable with index at least bound moves up by shift1, any other by shift2.
#[derive(Clone, Debug)]
pub struct VarShifter {
    inner: VarShifterCore,
}

impl VarShifter {
    pub fn new(m: &AstManager) -> VarShifter {
        VarShifter {
            inner: VarShifterCore::new(
                m,
                ShiftMode::Shift {
                    bound: 0,
                    shift1: 0,
                    shift2: 0,
                },
            ),
        }
    }

    /// Returns the result with a reference, which the caller releases.
    pub fn shift(
        &mut self,
        m: &mut AstManager,
        expr: Expr,
        bound: i32,
        shift1: i32,
        shift2: i32,
    ) -> Result<Expr, SmtError> {
        if m.is_ground_app(expr) {
            m.inc_ref(expr);
            return Ok(expr);
        }
        self.inner.core.caches[0].reset(m)?;
        self.inner.mode = ShiftMode::Shift {
            bound,
            shift1,
            shift2,
        };
        self.inner.main_loop(m, expr)
    }

    pub fn reset(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.inner.reset(m)
    }

    pub fn cleanup(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.inner.cleanup(m)
    }

    pub fn release(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.inner.release(m)
    }
}

/// inv_var_shifter: the free variables move down by amount.
#[derive(Clone, Debug)]
pub struct InvVarShifter {
    inner: VarShifterCore,
}

impl InvVarShifter {
    pub fn new(m: &AstManager) -> InvVarShifter {
        InvVarShifter {
            inner: VarShifterCore::new(m, ShiftMode::Inv { amount: 0 }),
        }
    }

    /// Returns the result with a reference, which the caller releases.
    pub fn shift(&mut self, m: &mut AstManager, expr: Expr, amount: i32) -> Result<Expr, SmtError> {
        if m.is_ground_app(expr) || amount == 0 {
            m.inc_ref(expr);
            return Ok(expr);
        }
        self.inner.core.caches[0].reset(m)?;
        self.inner.mode = ShiftMode::Inv { amount };
        self.inner.main_loop(m, expr)
    }

    pub fn reset(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.inner.reset(m)
    }

    pub fn cleanup(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.inner.cleanup(m)
    }

    pub fn release(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.inner.release(m)
    }
}

// The bindings of rewriter_tpl's substitution.
#[derive(Clone, Debug, Default)]
struct SubstCore {
    // m_bindings and m_shifts: the binding of each variable of the substitution, innermost last,
    // and the number of bindings when it was bound.
    bindings: Vec<Expr>,
    shifts: Vec<usize>,
}

impl SubstCore {
    /// set_inv_bindings: (:var i) becomes bindings[n - 1 - i], and -1 keeps it.
    fn set_inv_bindings(&mut self, bindings: &[Expr]) {
        self.bindings.clear();
        self.shifts.clear();
        for binding in bindings {
            self.bindings.push(*binding);
            self.shifts.push(bindings.len());
        }
    }

    /// set_bindings: (:var i) becomes bindings[i].
    fn set_bindings(&mut self, bindings: &[Expr]) {
        self.bindings.clear();
        self.shifts.clear();
        for binding in bindings.iter().rev() {
            self.bindings.push(*binding);
            self.shifts.push(bindings.len());
        }
    }

    fn update_inv_binding_at(&mut self, index: usize, binding: Expr) {
        self.bindings[index] = binding;
    }

    fn clear(&mut self) {
        self.bindings.clear();
        self.shifts.clear();
    }

    fn truncate(&mut self, count: usize) {
        self.bindings.truncate(self.bindings.len() - count);
        self.shifts.truncate(self.shifts.len() - count);
    }

    // The binding of (:var index), and the number of quantifiers entered since it was bound, or
    // None when the variable keeps.
    fn get_binding(&self, index: i32) -> Option<(Expr, usize)> {
        let index = usize::try_from(index).ok()?;
        if index >= self.bindings.len() {
            return None;
        }
        let position = self.bindings.len() - index - 1;
        let binding = self.bindings[position];
        (binding != -1).then(|| (binding, self.bindings.len() - self.shifts[position]))
    }
}

// process_var of rewriter_tpl and beta_reducer: a bound variable becomes its binding, shifted
// over the quantifiers entered since it was bound. It returns whether the variable was replaced,
// which the caller marks as a new child, and sets is_shifted when the shifter was used.
fn process_subst_var(
    m: &mut AstManager,
    core: &mut RewriterCore,
    subst: &SubstCore,
    shifter: &mut VarShifter,
    is_shifted: &mut bool,
    variable: Expr,
) -> Result<bool, SmtError> {
    let Some((binding, amount)) = subst.get_binding(m.values[variable as usize]) else {
        core.push_result(m, variable);
        return Ok(false);
    };
    if m.is_ground_app(binding) || amount == 0 {
        core.push_result(m, binding);
    } else if let Some(cached) = core.cache().find(m, binding, amount as u32) {
        core.push_result(m, cached);
    } else {
        *is_shifted = true;
        let shifted = shifter.shift(m, binding, 0, amount as i32, 0)?;
        core.push_result(m, shifted);
        core.cache().insert(m, binding, amount as u32, shifted)?;
        m.dec_ref(shifted)?;
    }
    Ok(true)
}

/// rewriter_tpl's main loop, which calls the hooks of its configuration.
#[derive(Clone, Debug)]
pub struct RewriterEngine {
    core: RewriterCore,
    subst: SubstCore,
    // m_r: the last result, which Z3 holds until it assigns the next one.
    last_result: LastResult,
    new_args: Vec<Expr>,
    shifter: VarShifter,
    inv_shifter: InvVarShifter,
    /// m_blocked: the constants that a nested rewriter does not expand.
    pub blocked: OrderedSet<Expr>,
}

impl RewriterEngine {
    pub fn new(m: &AstManager) -> RewriterEngine {
        RewriterEngine {
            core: RewriterCore::new(m),
            subst: SubstCore::default(),
            last_result: LastResult::new(),
            new_args: Vec::new(),
            shifter: VarShifter::new(m),
            inv_shifter: InvVarShifter::new(m),
            blocked: OrderedSet::new(),
        }
    }

    pub fn set_inv_bindings(&mut self, bindings: &[Expr]) {
        self.subst.set_inv_bindings(bindings);
    }

    pub fn set_bindings(&mut self, bindings: &[Expr]) {
        self.subst.set_bindings(bindings);
    }

    pub fn update_inv_binding_at(&mut self, index: usize, binding: Expr) {
        self.subst.update_inv_binding_at(index, binding);
    }

    /// reset: releases the outermost cache and the bindings.
    pub fn reset(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.core.reset_core(m)?;
        self.subst.clear();
        self.shifter.reset(m)?;
        self.inv_shifter.reset(m)
    }

    /// cleanup: releases every cache.
    pub fn cleanup(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.core.cleanup_core(m)?;
        self.subst.bindings = Vec::new();
        self.shifter.cleanup(m)?;
        self.inv_shifter.cleanup(m)?;
        self.subst.shifts = Vec::new();
        Ok(())
    }

    /// ~rewriter_tpl: the shifters' caches go first, the inverse shifter's before the other's, then
    /// the rewriter's.
    pub fn release(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.inv_shifter.release(m)?;
        self.shifter.release(m)?;
        self.core.release_caches(m)
    }

    /// m_r, for a configuration that writes it.
    pub fn last_result_mut(&mut self) -> &mut LastResult {
        &mut self.last_result
    }

    /// setLastResult.
    pub fn set_last_result(&mut self, m: &mut AstManager, expr: Expr) -> Result<(), SmtError> {
        self.last_result.set(m, expr)
    }

    /// operator(): the result comes with a reference, which the caller releases.
    pub fn rewrite<C: RewriterConfig>(
        &mut self,
        m: &mut AstManager,
        cfg: &mut C,
        expr: Expr,
    ) -> Result<Expr, SmtError> {
        m.without_temporaries(|m| self.rewrite_core(m, cfg, expr))
    }

    fn rewrite_core<C: RewriterConfig>(
        &mut self,
        m: &mut AstManager,
        cfg: &mut C,
        expr: Expr,
    ) -> Result<Expr, SmtError> {
        if self.core.num_frames > 0 || !self.core.scopes.is_empty() {
            self.core.num_frames = 0;
            self.core.shrink_results(m, 0)?;
            self.core.scopes = Vec::new();
            self.core.caches[0].reset(m)?;
        }
        self.core.root = expr;
        self.core.num_qvars = 0;
        // main_loop and each step of resume_core count a step of the resource limit, and stop
        // with SmtError::Canceled when it cancels the rewrite.
        m.limit.checkpoint()?;
        if !self.visit(m, cfg, expr, UNBOUNDED_DEPTH)? {
            while self.core.num_frames > 0 {
                m.limit.checkpoint()?;
                let top = self.core.num_frames - 1;
                let frame = self.core.frames[top];
                let curr = frame.curr;
                if frame.child_index == 0
                    && frame.state == PROCESS_CHILDREN
                    && frame.is_caching
                    && let Some(cached) = self.core.cache().find(m, curr, 0)
                {
                    self.core.push_result(m, cached);
                    self.core.num_frames -= 1;
                    self.core.set_new_child_flag(curr, cached);
                    continue;
                }
                let kind = m.kinds[curr as usize];
                if kind == KIND_APP {
                    self.process_app(m, cfg, curr, top)?;
                } else if kind == KIND_QUANTIFIER {
                    self.process_quantifier(m, cfg, curr, top)?;
                } else {
                    // A definition that is a variable gets a frame of its own.
                    self.core.num_frames -= 1;
                    self.process_var(m, curr)?;
                }
            }
        }
        self.core.pop_result()
    }

    /// operator() with bindings: resets the rewriter and substitutes bindings[n - 1 - i] for
    /// (:var i).
    pub fn rewrite_with_bindings<C: RewriterConfig>(
        &mut self,
        m: &mut AstManager,
        cfg: &mut C,
        expr: Expr,
        bindings: &[Expr],
    ) -> Result<Expr, SmtError> {
        self.reset(m)?;
        self.set_inv_bindings(bindings);
        self.rewrite(m, cfg, expr)
    }

    fn cache_result(
        &mut self,
        m: &mut AstManager,
        expr: Expr,
        result: Expr,
        is_caching: bool,
    ) -> Result<(), SmtError> {
        if is_caching {
            self.core.cache().insert(m, expr, 0, result)?;
        }
        Ok(())
    }

    // visit: whether expr is rewritten and its result is on the result stack. Otherwise it pushes a
    // frame for expr.
    fn visit<C: RewriterConfig>(
        &mut self,
        m: &mut AstManager,
        cfg: &mut C,
        expr: Expr,
        max_depth: u32,
    ) -> Result<bool, SmtError> {
        let replacement = if C::IS_SUBSTITUTING {
            cfg.get_subst(m, expr)?
        } else {
            None
        };
        if let Some(replacement) = replacement {
            self.core.push_result(m, replacement);
            self.core.set_new_child_flag(expr, replacement);
            return Ok(true);
        }
        if max_depth == 0 {
            self.core.push_result(m, expr);
            return Ok(true);
        }
        let is_caching = self.core.is_caching(m, expr);
        if is_caching && let Some(cached) = self.core.cache().find(m, expr, 0) {
            self.core.push_result(m, cached);
            self.core.set_new_child_flag(expr, cached);
            return Ok(true);
        }
        let kind = m.kinds[expr as usize];
        if kind == KIND_VAR {
            self.process_var(m, expr)?;
            return Ok(true);
        }
        if kind == KIND_APP && m.get_num_args(expr) == 0 {
            if !self.process_const(m, cfg, expr)? {
                self.rewrite_const_result(m, cfg, expr)?;
            }
            return Ok(true);
        }
        self.core.push_frame(
            expr,
            is_caching,
            if max_depth == UNBOUNDED_DEPTH {
                max_depth
            } else {
                max_depth - 1
            },
        );
        Ok(false)
    }

    // process_const: a constant is reduced, and a constant it rewrites to is reduced again. It
    // returns false when the constant rewrites to a term with arguments, which m_r holds. The
    // constant being reduced is held, like Z3's t.
    fn process_const<C: RewriterConfig>(
        &mut self,
        m: &mut AstManager,
        cfg: &mut C,
        expr: Expr,
    ) -> Result<bool, SmtError> {
        let mut current = expr;
        m.inc_ref(current);
        let mut is_retried = false;
        loop {
            let decl = m.decls[current as usize];
            let sort = m.sorts[current as usize];
            let reduced = cfg.reduce_app(m, &mut self.last_result, decl, &[], sort)?;
            match reduced {
                Reduced::Done(result) | Reduced::Rewrite(Rewrite { expr: result, .. }) => {
                    self.last_result.set(m, result)?;
                    m.dec_ref(result)?;
                }
                Reduced::Failed => {}
            }
            if reduced == Reduced::Failed && !is_retried {
                self.core.push_result(m, current);
                m.dec_ref(current)?;
                return Ok(true);
            }
            let result = match reduced {
                Reduced::Failed | Reduced::Done(_) => {
                    if reduced == Reduced::Failed {
                        self.last_result.set(m, current)?;
                    }
                    let last = self.last_result.get();
                    self.core.push_result(m, last);
                    self.last_result.set(m, -1)?;
                    self.core.set_new_child_flag(expr, -1);
                    m.dec_ref(current)?;
                    return Ok(true);
                }
                Reduced::Rewrite(rewrite) => rewrite.expr,
            };
            if m.kinds[result as usize] != KIND_APP || m.get_num_args(result) > 0 {
                m.dec_ref(current)?;
                return Ok(false);
            }
            m.inc_ref(result);
            m.dec_ref(current)?;
            current = result;
            is_retried = true;
        }
    }

    // A constant that rewrites to a term with arguments: a rewriter with the same configuration
    // rewrites the term, with the constant blocked so that it is not expanded again. m_r keeps the
    // result.
    fn rewrite_const_result<C: RewriterConfig>(
        &mut self,
        m: &mut AstManager,
        cfg: &mut C,
        expr: Expr,
    ) -> Result<(), SmtError> {
        if !self.blocked.contains(&expr) {
            if self.blocked.len() >= MAX_RECURSION_DEPTH {
                return Err(SmtError::Unsupported(
                    "the rewriter nests too deeply".into(),
                ));
            }
            let result = match cfg.mk_nested(m)? {
                Some(nested) => self.rewrite_nested(m, nested, expr)?,
                None => self.rewrite_nested(m, DefaultRewriterConfig, expr)?,
            };
            self.last_result.set(m, result)?;
            m.dec_ref(result)?;
        }
        self.core.set_new_child_flag(expr, -1);
        let last = self.last_result.get();
        self.core.push_result(m, last);
        Ok(())
    }

    fn rewrite_nested<N: RewriterConfig>(
        &mut self,
        m: &mut AstManager,
        cfg: N,
        expr: Expr,
    ) -> Result<Expr, SmtError> {
        let mut nested = RewriterTpl::new(m, cfg);
        for blocked in self.blocked.iter() {
            nested.engine.blocked.insert(*blocked);
        }
        nested.engine.blocked.insert(expr);
        let result = nested.rewrite(m, self.last_result.get())?;
        nested.release(m)?;
        Ok(result)
    }

    // process_var: a bound variable becomes its binding, shifted over the quantifiers entered since
    // it was bound.
    fn process_var(&mut self, m: &mut AstManager, variable: Expr) -> Result<(), SmtError> {
        let mut is_shifted = false;
        if process_subst_var(
            m,
            &mut self.core,
            &self.subst,
            &mut self.shifter,
            &mut is_shifted,
            variable,
        )? {
            self.core.set_new_child_flag(variable, -1);
        }
        Ok(())
    }

    fn process_app<C: RewriterConfig>(
        &mut self,
        m: &mut AstManager,
        cfg: &mut C,
        expr: Expr,
        top: usize,
    ) -> Result<(), SmtError> {
        let state = self.core.frames[top].state;
        if state == REWRITE_BUILTIN {
            return self.finish_rewrite_builtin(m, expr, top);
        }
        if state == EXPAND_DEF {
            return self.finish_expand_def(m, expr, top);
        }
        let num_args = m.get_num_args(expr);
        // visit pushes a child at depth 0 as it is when the config substitutes nothing.
        if self.core.frames[top].max_depth == 0 && !C::IS_SUBSTITUTING && m.get_op(expr) != OP_ITE {
            while self.core.frames[top].child_index < num_args {
                let arg = m.get_arg(expr, self.core.frames[top].child_index);
                self.core.push_result(m, arg);
                self.core.frames[top].child_index += 1;
            }
        }
        while self.core.frames[top].child_index < num_args {
            if self.is_constant_folded(m, cfg, expr, top)? {
                return Ok(());
            }
            let arg = m.get_arg(expr, self.core.frames[top].child_index);
            self.core.frames[top].child_index += 1;
            let max_depth = self.core.frames[top].max_depth;
            if !self.visit(m, cfg, arg, max_depth)? {
                return Ok(());
            }
        }
        let decl = m.decls[expr as usize];
        if cfg.is_flat_assoc(m, decl) && m.get_ref_count(expr) <= 1 && self.core.num_frames > 1 {
            let previous = self.core.frames[self.core.num_frames - 2];
            if m.kinds[previous.curr as usize] == KIND_APP
                && m.decls[previous.curr as usize] == decl
                && previous.state == PROCESS_CHILDREN
            {
                self.core.num_frames -= 1;
                self.core.set_new_child_flag(expr, -1);
                return Ok(());
            }
        }
        // new_args: Z3 passes the results on the stack itself. Nothing rewrites with this engine
        // before the arguments are used, so one buffer holds them.
        let spos = self.core.frames[top].spos;
        self.new_args.clear();
        self.new_args
            .extend_from_slice(&self.core.result_stack[spos..]);
        let sort = m.sorts[expr as usize];
        let reduced = cfg.reduce_app(m, &mut self.last_result, decl, &self.new_args, sort)?;
        let reduced = match reduced {
            Reduced::Rewrite(rewrite) => {
                // BR_REWRITE: the result replaces the arguments and is rewritten to the depth it
                // asks for.
                self.last_result.set(m, rewrite.expr)?;
                m.dec_ref(rewrite.expr)?;
                self.core.shrink_results(m, spos)?;
                self.core.push_result(m, rewrite.expr);
                self.core.frames[top].state = REWRITE_BUILTIN;
                if self.visit(m, cfg, rewrite.expr, get_rewrite_depth(&rewrite))? {
                    self.finish_rewrite_builtin(m, expr, top)?;
                }
                self.last_result.set(m, -1)?;
                return Ok(());
            }
            Reduced::Done(result) => result,
            Reduced::Failed => -1,
        };
        let definition = if reduced == -1 && C::IS_EXPANDING_MACROS {
            cfg.get_macro(m, decl)?
        } else {
            -1
        };
        if definition != -1 && (!m.is_ground_app(definition) || cfg.is_reducing_macro()) {
            // The definition is rewritten with the arguments bound to its variables.
            self.core.frames[top].state = EXPAND_DEF;
            let size = self.subst.bindings.len();
            for index in (0..self.new_args.len()).rev() {
                self.subst.bindings.push(self.new_args[index]);
                self.subst.shifts.push(size);
            }
            self.core.push_result(m, definition);
            self.core.begin_scope(m)?;
            self.core.num_qvars += self.new_args.len() as i32;
            self.core.root = definition;
            self.core.push_frame(definition, false, UNBOUNDED_DEPTH);
            return Ok(());
        }
        if definition != -1 {
            self.last_result.set(m, definition)?;
        } else if reduced == -1 {
            let result = if self.core.frames[top].has_new_child {
                m.mk_app(decl, &self.new_args, sort)?
            } else {
                expr
            };
            self.last_result.set(m, result)?;
        } else {
            self.last_result.set(m, reduced)?;
            m.dec_ref(reduced)?;
        }
        let result = self.last_result.get();
        let frame = self.core.frames[top];
        self.core.shrink_results(m, frame.spos)?;
        self.core.push_result(m, result);
        self.cache_result(m, expr, result, frame.is_caching)?;
        self.core.num_frames -= 1;
        self.core.set_new_child_flag(expr, result);
        self.last_result.set(m, -1)
    }

    // REWRITE_BUILTIN: the result of the rewritten term replaces the term on the result stack.
    fn finish_rewrite_builtin(
        &mut self,
        m: &mut AstManager,
        expr: Expr,
        top: usize,
    ) -> Result<(), SmtError> {
        let result = self.core.pop_result()?;
        self.core.result_stack.push(result);
        self.last_result.set(m, result)?;
        let size = self.core.result_stack.len() - 1;
        self.core.shrink_results(m, size)?;
        let size = self.core.result_stack.len().saturating_sub(1);
        self.core.shrink_results(m, size)?;
        self.core.push_result(m, result);
        let is_caching = self.core.frames[top].is_caching;
        self.cache_result(m, expr, result, is_caching)?;
        self.core.num_frames -= 1;
        self.core.set_new_child_flag(expr, -1);
        Ok(())
    }

    // EXPAND_DEF: the rewritten definition, with its variables moved back down, replaces the term.
    // m_r keeps it until the next result.
    fn finish_expand_def(
        &mut self,
        m: &mut AstManager,
        expr: Expr,
        top: usize,
    ) -> Result<(), SmtError> {
        let num_args = m.get_num_args(expr);
        self.subst.truncate(num_args);
        self.core.num_qvars -= num_args as i32;
        self.core.end_scope(m)?;
        let rewritten = self.core.pop_result()?;
        self.core.result_stack.push(rewritten);
        if m.is_ground_app(rewritten) {
            self.last_result.set(m, rewritten)?;
        } else {
            let shifted = self.inv_shifter.shift(m, rewritten, num_args as i32)?;
            self.last_result.set(m, shifted)?;
            m.dec_ref(shifted)?;
        }
        let result = self.last_result.get();
        let frame = self.core.frames[top];
        self.core.shrink_results(m, frame.spos)?;
        self.core.push_result(m, result);
        self.cache_result(m, expr, result, frame.is_caching)?;
        self.core.num_frames -= 1;
        self.core.set_new_child_flag(expr, -1);
        Ok(())
    }

    // constant_fold: an ite whose condition rewrote to true or false becomes the chosen branch.
    fn is_constant_folded<C: RewriterConfig>(
        &mut self,
        m: &mut AstManager,
        cfg: &mut C,
        expr: Expr,
        top: usize,
    ) -> Result<bool, SmtError> {
        let frame = self.core.frames[top];
        if frame.child_index != 1 || m.get_op(expr) != OP_ITE {
            return Ok(false);
        }
        let condition = self.core.result_stack[frame.spos];
        let arg = if m.is_true(condition) {
            m.get_arg(expr, 1)
        } else if m.is_false(condition) {
            m.get_arg(expr, 2)
        } else {
            return Ok(false);
        };
        self.core.shrink_results(m, frame.spos)?;
        self.core.push_result(m, arg);
        self.core.frames[top].state = REWRITE_BUILTIN;
        if self.visit(m, cfg, arg, frame.max_depth)? {
            self.finish_rewrite_builtin(m, expr, top)?;
        }
        self.last_result.set(m, -1)?;
        Ok(true)
    }

    fn process_quantifier<C: RewriterConfig>(
        &mut self,
        m: &mut AstManager,
        cfg: &mut C,
        expr: Expr,
        top: usize,
    ) -> Result<(), SmtError> {
        let (body, num_decls, num_patterns) = {
            let data = m.get_quantifier(expr)?;
            (data.body, data.sorts.len(), data.patterns.len())
        };
        if self.core.frames[top].child_index == 0 {
            self.core.begin_scope(m)?;
            self.core.root = body;
            let size = self.subst.bindings.len();
            for _ in 0..num_decls {
                self.subst.bindings.push(-1);
                self.subst.shifts.push(size);
            }
            self.core.num_qvars += num_decls as i32;
        }
        let is_rewriting_patterns = cfg.is_rewriting_patterns();
        let num_children = if is_rewriting_patterns {
            1 + num_patterns
        } else {
            1
        };
        while self.core.frames[top].child_index < num_children {
            let child = get_quantifier_child(m, expr, self.core.frames[top].child_index)?;
            self.core.frames[top].child_index += 1;
            let max_depth = self.core.frames[top].max_depth;
            if !self.visit(m, cfg, child, max_depth)? {
                return Ok(());
            }
        }
        let frame = self.core.frames[top];
        let new_body = self.core.result_stack[frame.spos];
        // new_pats: the patterns, which Z3 holds until the quantifier is done.
        let patterns = if is_rewriting_patterns {
            self.core.result_stack[frame.spos + 1..].to_vec()
        } else {
            m.get_quantifier(expr)?.patterns.clone()
        };
        for pattern in &patterns {
            m.inc_ref(*pattern);
        }
        let reduced = cfg.reduce_quantifier(m, expr, new_body, &patterns)?;
        if reduced == -1 {
            let result = if frame.has_new_child {
                let data = m.get_quantifier(expr)?;
                let data = QuantifierData {
                    body: new_body,
                    patterns: patterns.clone(),
                    ..data.clone()
                };
                m.mk_quantifier(data)?
            } else {
                expr
            };
            self.last_result.set(m, result)?;
        } else {
            self.last_result.set(m, reduced)?;
            m.dec_ref(reduced)?;
        }
        let result = self.last_result.get();
        self.core.shrink_results(m, frame.spos)?;
        self.core.push_result(m, result);
        self.subst.truncate(num_decls);
        self.core.end_scope(m)?;
        self.cache_result(m, expr, result, frame.is_caching)?;
        self.last_result.set(m, -1)?;
        self.core.num_frames -= 1;
        self.core.set_new_child_flag(expr, result);
        for pattern in &patterns {
            m.dec_ref(*pattern)?;
        }
        Ok(())
    }
}

/// rewriter_tpl with a configuration, default_rewriter_cfg's hooks overridden by `C`.
#[derive(Clone, Debug)]
pub struct RewriterTpl<C: RewriterConfig> {
    pub cfg: C,
    pub engine: RewriterEngine,
}

impl<C: RewriterConfig> RewriterTpl<C> {
    pub fn new(m: &AstManager, cfg: C) -> RewriterTpl<C> {
        RewriterTpl {
            cfg,
            engine: RewriterEngine::new(m),
        }
    }

    pub fn set_inv_bindings(&mut self, bindings: &[Expr]) {
        self.engine.set_inv_bindings(bindings);
    }

    pub fn set_bindings(&mut self, bindings: &[Expr]) {
        self.engine.set_bindings(bindings);
    }

    pub fn update_inv_binding_at(&mut self, index: usize, binding: Expr) {
        self.engine.update_inv_binding_at(index, binding);
    }

    pub fn reset(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.engine.reset(m)
    }

    pub fn cleanup(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.engine.cleanup(m)
    }

    /// The configuration's release, then the engine's caches.
    pub fn release(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.cfg.release(m)?;
        self.engine.release(m)
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

    pub fn set_last_result(&mut self, m: &mut AstManager, expr: Expr) -> Result<(), SmtError> {
        self.engine.set_last_result(m, expr)
    }
}

// The flags of a BetaReducer frame: whether to cache its result, whether a child changed, and
// whether it waits for the branch that an ite folded to, REWRITE_BUILTIN.
const FRAME_CACHING: u8 = 1;
const FRAME_NEW_CHILD: u8 = 2;
const FRAME_FOLDED: u8 = 4;

#[derive(Clone, Copy, Debug)]
struct BetaFrame {
    expr: Expr,
    child_index: usize,
    start: usize,
    flags: u8,
}

/// beta_reducer: rewriter_tpl with beta_reducer_cfg, which substitutes bindings for variables and
/// rewrites nothing else. Its main loop is RewriterEngine's with the config's hooks folded in:
/// pre_visit skips a ground term, and nothing reduces, expands or rewrites to a depth. So a frame
/// needs no depth and only the ite folding's state.
#[derive(Clone, Debug)]
pub struct BetaReducer {
    core: RewriterCore,
    subst: SubstCore,
    // m_r: the last result, which Z3 holds until it assigns the next one.
    last_result: LastResult,
    shifter: VarShifter,
    // Whether the shifter's cache has entries, which reset releases.
    is_shifted: bool,
    // The frames, of which the first core.num_frames are open; the TypeScript's typed arrays.
    beta_frames: Vec<BetaFrame>,
}

impl BetaReducer {
    pub fn new(m: &AstManager) -> BetaReducer {
        BetaReducer {
            core: RewriterCore::new(m),
            subst: SubstCore::default(),
            last_result: LastResult::new(),
            shifter: VarShifter::new(m),
            is_shifted: false,
            beta_frames: Vec::new(),
        }
    }

    pub fn set_inv_bindings(&mut self, bindings: &[Expr]) {
        self.subst.set_inv_bindings(bindings);
    }

    pub fn set_bindings(&mut self, bindings: &[Expr]) {
        self.subst.set_bindings(bindings);
    }

    pub fn update_inv_binding_at(&mut self, index: usize, binding: Expr) {
        self.subst.update_inv_binding_at(index, binding);
    }

    /// reset: releases the outermost cache and the bindings. The inverse shifter of rewriter_tpl
    /// only shifts an expanded definition, so it is always empty and left out.
    pub fn reset(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.core.reset_core(m)?;
        self.subst.clear();
        if !self.is_shifted {
            return Ok(());
        }
        self.shifter.reset(m)?;
        self.is_shifted = false;
        Ok(())
    }

    /// ~rewriter_tpl: the shifter's cache goes first, then the rewriter's.
    pub fn release(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.shifter.release(m)?;
        self.core.release_caches(m)
    }

    /// operator(): the result comes with a reference, which the caller releases.
    pub fn rewrite(&mut self, m: &mut AstManager, expr: Expr) -> Result<Expr, SmtError> {
        m.without_temporaries(|m| self.rewrite_core(m, expr))
    }

    fn rewrite_core(&mut self, m: &mut AstManager, expr: Expr) -> Result<Expr, SmtError> {
        if self.core.num_frames > 0 || !self.core.scopes.is_empty() {
            self.core.num_frames = 0;
            self.core.shrink_results(m, 0)?;
            self.core.scopes = Vec::new();
            self.core.caches[0].reset(m)?;
        }
        self.core.root = expr;
        self.core.num_qvars = 0;
        // main_loop and each step of resume_core count a step of the resource limit, and stop
        // with SmtError::Canceled when it cancels the rewrite.
        m.limit.checkpoint()?;
        if !self.visit(m, expr)? {
            while self.core.num_frames > 0 {
                m.limit.checkpoint()?;
                let top = self.core.num_frames - 1;
                let frame = self.beta_frames[top];
                let curr = frame.expr;
                if frame.child_index == 0
                    && (frame.flags & (FRAME_CACHING | FRAME_FOLDED)) == FRAME_CACHING
                    && let Some(cached) = self.core.cache().find(m, curr, 0)
                {
                    self.core.push_result(m, cached);
                    self.core.num_frames -= 1;
                    self.mark_new_child(curr, cached);
                    continue;
                }
                if m.kinds[curr as usize] == KIND_APP {
                    self.process_app(m, curr, top)?;
                } else {
                    self.process_quantifier(m, curr, top)?;
                }
            }
        }
        self.core.pop_result()
    }

    /// operator() with bindings: resets the rewriter and substitutes bindings[n - 1 - i] for
    /// (:var i).
    pub fn rewrite_with_bindings(
        &mut self,
        m: &mut AstManager,
        expr: Expr,
        bindings: &[Expr],
    ) -> Result<Expr, SmtError> {
        self.reset(m)?;
        self.set_inv_bindings(bindings);
        self.rewrite(m, expr)
    }

    fn mark_new_child(&mut self, old_expr: Expr, new_expr: Expr) {
        if old_expr != new_expr && self.core.num_frames > 0 {
            self.beta_frames[self.core.num_frames - 1].flags |= FRAME_NEW_CHILD;
        }
    }

    fn open_frame(&mut self, expr: Expr, is_caching: bool) {
        let index = self.core.num_frames;
        let frame = BetaFrame {
            expr,
            child_index: 0,
            start: self.core.result_stack.len(),
            flags: if is_caching { FRAME_CACHING } else { 0 },
        };
        if index == self.beta_frames.len() {
            self.beta_frames.push(frame);
        } else {
            self.beta_frames[index] = frame;
        }
        self.core.num_frames += 1;
    }

    // visit: whether expr is rewritten and its result is on the result stack. Otherwise it opens a
    // frame for expr. pre_visit's test for a ground term comes before the cache's, which holds no
    // ground term.
    fn visit(&mut self, m: &mut AstManager, expr: Expr) -> Result<bool, SmtError> {
        if m.is_ground_app(expr) {
            self.core.push_result(m, expr);
            return Ok(true);
        }
        let is_caching = self.core.is_caching(m, expr);
        if is_caching && let Some(cached) = self.core.cache().find(m, expr, 0) {
            self.core.push_result(m, cached);
            self.mark_new_child(expr, cached);
            return Ok(true);
        }
        if m.kinds[expr as usize] == KIND_VAR {
            self.process_var(m, expr)?;
            return Ok(true);
        }
        self.open_frame(expr, is_caching);
        Ok(false)
    }

    // process_var: a bound variable becomes its binding, shifted over the quantifiers entered since
    // it was bound.
    fn process_var(&mut self, m: &mut AstManager, variable: Expr) -> Result<(), SmtError> {
        if process_subst_var(
            m,
            &mut self.core,
            &self.subst,
            &mut self.shifter,
            &mut self.is_shifted,
            variable,
        )? {
            self.mark_new_child(variable, -1);
        }
        Ok(())
    }

    fn process_app(&mut self, m: &mut AstManager, expr: Expr, top: usize) -> Result<(), SmtError> {
        if self.beta_frames[top].flags & FRAME_FOLDED != 0 {
            return self.finish_folded(m, expr, top);
        }
        let num_args = m.get_num_args(expr);
        while self.beta_frames[top].child_index < num_args {
            let child_index = self.beta_frames[top].child_index;
            if child_index == 1 && self.is_constant_folded(m, expr, top)? {
                return Ok(());
            }
            self.beta_frames[top].child_index = child_index + 1;
            let arg = m.get_arg(expr, child_index);
            if !self.visit(m, arg)? {
                return Ok(());
            }
        }
        let frame = self.beta_frames[top];
        let spos = frame.start;
        let result = if frame.flags & FRAME_NEW_CHILD != 0 {
            m.mk_app(
                m.decls[expr as usize],
                &self.core.result_stack[spos..],
                m.sorts[expr as usize],
            )?
        } else {
            expr
        };
        self.last_result.set(m, result)?;
        let result = self.last_result.get();
        self.core.shrink_results(m, spos)?;
        self.core.push_result(m, result);
        if frame.flags & FRAME_CACHING != 0 {
            self.core.cache().insert(m, expr, 0, result)?;
        }
        self.core.num_frames -= 1;
        self.mark_new_child(expr, result);
        self.last_result.set(m, -1)
    }

    // REWRITE_BUILTIN: the result of the folded branch replaces the ite on the result stack.
    fn finish_folded(
        &mut self,
        m: &mut AstManager,
        expr: Expr,
        top: usize,
    ) -> Result<(), SmtError> {
        let result = self.core.pop_result()?;
        self.core.result_stack.push(result);
        self.last_result.set(m, result)?;
        let size = self.core.result_stack.len() - 1;
        self.core.shrink_results(m, size)?;
        let size = self.core.result_stack.len().saturating_sub(1);
        self.core.shrink_results(m, size)?;
        self.core.push_result(m, result);
        if self.beta_frames[top].flags & FRAME_CACHING != 0 {
            self.core.cache().insert(m, expr, 0, result)?;
        }
        self.core.num_frames -= 1;
        self.mark_new_child(expr, -1);
        Ok(())
    }

    // constant_fold: an ite whose condition rewrote to true or false becomes the chosen branch.
    fn is_constant_folded(
        &mut self,
        m: &mut AstManager,
        expr: Expr,
        top: usize,
    ) -> Result<bool, SmtError> {
        if m.get_op(expr) != OP_ITE {
            return Ok(false);
        }
        let spos = self.beta_frames[top].start;
        let condition = self.core.result_stack[spos];
        let arg = if m.is_true(condition) {
            m.get_arg(expr, 1)
        } else if m.is_false(condition) {
            m.get_arg(expr, 2)
        } else {
            return Ok(false);
        };
        self.core.shrink_results(m, spos)?;
        self.core.push_result(m, arg);
        self.beta_frames[top].flags |= FRAME_FOLDED;
        if self.visit(m, arg)? {
            self.finish_folded(m, expr, top)?;
        }
        self.last_result.set(m, -1)?;
        Ok(true)
    }

    fn process_quantifier(
        &mut self,
        m: &mut AstManager,
        expr: Expr,
        top: usize,
    ) -> Result<(), SmtError> {
        let (body, num_decls, num_patterns) = {
            let data = m.get_quantifier(expr)?;
            (data.body, data.sorts.len(), data.patterns.len())
        };
        if self.beta_frames[top].child_index == 0 {
            self.core.begin_scope(m)?;
            self.core.root = body;
            let size = self.subst.bindings.len();
            for _ in 0..num_decls {
                self.subst.bindings.push(-1);
                self.subst.shifts.push(size);
            }
            self.core.num_qvars += num_decls as i32;
        }
        while self.beta_frames[top].child_index <= num_patterns {
            let child_index = self.beta_frames[top].child_index;
            self.beta_frames[top].child_index = child_index + 1;
            let child = get_quantifier_child(m, expr, child_index)?;
            if !self.visit(m, child)? {
                return Ok(());
            }
        }
        let frame = self.beta_frames[top];
        let spos = frame.start;
        let new_body = self.core.result_stack[spos];
        // new_pats: the patterns, which Z3 holds until the quantifier is done.
        let patterns = self.core.result_stack[spos + 1..].to_vec();
        for pattern in &patterns {
            m.inc_ref(*pattern);
        }
        let result = if frame.flags & FRAME_NEW_CHILD != 0 {
            let data = m.get_quantifier(expr)?;
            let data = QuantifierData {
                body: new_body,
                patterns: patterns.clone(),
                ..data.clone()
            };
            m.mk_quantifier(data)?
        } else {
            expr
        };
        self.last_result.set(m, result)?;
        let result = self.last_result.get();
        self.core.shrink_results(m, spos)?;
        self.core.push_result(m, result);
        self.subst.truncate(num_decls);
        self.core.end_scope(m)?;
        if frame.flags & FRAME_CACHING != 0 {
            self.core.cache().insert(m, expr, 0, result)?;
        }
        self.last_result.set(m, -1)?;
        self.core.num_frames -= 1;
        self.mark_new_child(expr, result);
        for pattern in &patterns {
            m.dec_ref(*pattern)?;
        }
        Ok(())
    }
}
