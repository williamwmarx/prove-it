//! Ported from Z3 (src/model/model_evaluator.cpp), MIT license, through `model-evaluator.ts`.
//! Evaluates an expression in a model with rewriter_tpl and evaluator_cfg: uninterpreted symbols
//! take their interpretations, the interpretation of a function is expanded like a macro, and the
//! rewriters fold the interpreted operators. With model completion, a symbol without an
//! interpretation gets some value, so a ground expression always evaluates to a value. The cache
//! persists between evaluations until the model completion flag changes.
//!
//! # Design
//!
//! The TypeScript's `ModelEvaluator extends RewriterTpl` keeps its model, which keeps the
//! evaluator. Here [`ModelEvaluator`] is the main loop and evaluator_cfg's own state, and the model
//! lends itself to each evaluation: `ProtoModel::eval` takes the evaluator out of the model and
//! passes the model to [`ModelEvaluator::rewrite`], which runs the main loop with an
//! [`EvaluatorCfg`] that borrows both. The nested evaluator of a constant whose value has an
//! equality (`mkNested`) borrows the same model, with a state of its own.
//!
//! th_rewriter's `releaseResult`, which the TypeScript sets to the evaluator's
//! `setLastResult(-1)`, is the `LastResult` the main loop passes to `reduce_app`, which the
//! evaluator passes on to `Rewriter::reduce_app_core`.

use std::collections::HashSet;

use prove_num::Rational;

use crate::core::ast::{
    AstManager, Decl, Expr, FAMILY_ARITH, FAMILY_USER, KIND_APP, KIND_QUANTIFIER, OP_AND, OP_DIV,
    OP_DIV0, OP_EQ, OP_IDIV, OP_IDIV0, OP_ITE, OP_LE, OP_MOD, OP_MOD0, SORT_BOOL, Sort,
};
use crate::core::proto_model::{FuncInterp, ProtoModel};
use crate::core::rewriter::{Rewriter, TACTIC_REWRITER_OPTIONS};
use crate::core::rewriter_tpl::{
    LastResult, Reduced, Rewrite, RewriterConfig, RewriterEngine, UNBOUNDED_DEPTH,
    rewrite_nested_with,
};
use crate::core::var_subst::VarSubst;
use crate::util::error::SmtError;
use crate::util::ordered_map::OrderedSet;

// The division by zero that a division stands for when its divisor is zero.
fn get_by_zero_op(op: i32) -> Option<i32> {
    match op {
        OP_DIV => Some(OP_DIV0),
        OP_IDIV => Some(OP_IDIV0),
        OP_MOD => Some(OP_MOD0),
        _ => None,
    }
}

/// evaluator_cfg's own state: a th_rewriter with the default parameters, m_b_rw and m_a_rw, whose
/// reductions it applies, the model completion flag, and the arguments of a reduced arithmetic
/// term, reused across evaluations.
#[derive(Clone, Debug)]
pub struct EvaluatorState {
    rewriter: Rewriter,
    is_model_completion: bool,
    reduced_args: Vec<Expr>,
}

impl EvaluatorState {
    fn new(m: &AstManager, is_model_completion: bool) -> EvaluatorState {
        EvaluatorState {
            rewriter: Rewriter::new(m, TACTIC_REWRITER_OPTIONS, false),
            is_model_completion,
            reduced_args: Vec::new(),
        }
    }
}

/// model_evaluator: rewriter_tpl with evaluator_cfg, whose model each evaluation lends.
#[derive(Clone, Debug)]
pub struct ModelEvaluator {
    engine: RewriterEngine,
    state: EvaluatorState,
}

impl ModelEvaluator {
    pub fn new(m: &AstManager) -> ModelEvaluator {
        ModelEvaluator {
            engine: RewriterEngine::new(m),
            state: EvaluatorState::new(m, false),
        }
    }

    /// set_model_completion: the cache is reset when the flag changes.
    pub fn set_model_completion(
        &mut self,
        m: &mut AstManager,
        is_model_completion: bool,
    ) -> Result<(), SmtError> {
        if self.state.is_model_completion == is_model_completion {
            return Ok(());
        }
        self.engine.reset(m)?;
        self.state.is_model_completion = is_model_completion;
        Ok(())
    }

    /// The value of expr in model, which the caller holds a reference to.
    pub fn rewrite(
        &mut self,
        m: &mut AstManager,
        model: &mut ProtoModel,
        expr: Expr,
    ) -> Result<Expr, SmtError> {
        let mut cfg = EvaluatorCfg {
            model,
            state: &mut self.state,
        };
        self.engine.rewrite(m, &mut cfg, expr)
    }

    /// ~imp: evaluator_cfg goes before the caches of rewriter_tpl.
    pub fn release(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.state.rewriter.release(m)?;
        self.engine.release(m)
    }
}

/// evaluator_cfg over a model it borrows.
pub struct EvaluatorCfg<'a> {
    model: &'a mut ProtoModel,
    state: &'a mut EvaluatorState,
}

impl RewriterConfig for EvaluatorCfg<'_> {
    const IS_EXPANDING_MACROS: bool = true;

    fn reduce_app(
        &mut self,
        m: &mut AstManager,
        last_result: &mut LastResult,
        decl: Decl,
        args: &[Expr],
        sort: Sort,
    ) -> Result<Reduced, SmtError> {
        let outer = m.begin_temporaries();
        let result = self.reduce_app_core(m, last_result, decl, args, sort)?;
        match result {
            Reduced::Done(expr) | Reduced::Rewrite(Rewrite { expr, .. }) => m.inc_ref(expr),
            Reduced::Failed => {}
        }
        m.end_temporaries(outer)?;
        Ok(result)
    }

    /// get_macro: the interpretation of an uninterpreted function. With model completion, a
    /// partial interpretation gets an else value, and a function without one gets a constant
    /// interpretation.
    fn get_macro(&mut self, m: &mut AstManager, decl: Decl) -> Result<Expr, SmtError> {
        let range = m.func_decls[decl as usize].range;
        let family = m.func_decls[decl as usize].family;
        let arity = m.func_decls[decl as usize].domain.len();
        if let Some(is_partial) = self
            .model
            .get_func_interp(m, decl)
            .map(FuncInterp::is_partial)
        {
            if is_partial {
                if !self.state.is_model_completion {
                    return Ok(-1);
                }
                let some = self.model.get_some_value(m, range);
                if let Some(interp) = self.model.get_func_interp_mut(m, decl) {
                    interp.set_else(m, some)?;
                }
            }
            return match self.model.get_func_interp_mut(m, decl) {
                Some(interp) => Ok(interp.get_interp(m)?.unwrap_or(-1)),
                None => Ok(-1),
            };
        }
        if !self.state.is_model_completion || family != FAMILY_USER {
            return Ok(-1);
        }
        let some = self.model.get_some_value(m, range);
        let mut created = FuncInterp::new(arity);
        created.set_else(m, some)?;
        self.model.register_func(m, decl, created)?;
        Ok(some)
    }

    fn is_reducing_macro(&self) -> bool {
        true
    }

    /// evaluator_cfg::reduce_quantifier: a th_rewriter of its own reduces the quantifier.
    fn reduce_quantifier(
        &mut self,
        m: &mut AstManager,
        expr: Expr,
        body: Expr,
        patterns: &[Expr],
    ) -> Result<Expr, SmtError> {
        let mut rewriter = Rewriter::new(m, TACTIC_REWRITER_OPTIONS, false);
        let result = rewriter.reduce_quantifier(m, expr, body, patterns)?;
        rewriter.release(m)?;
        Ok(result)
    }

    /// mkNested: an evaluator of the same model, with the same model completion flag.
    fn rewrite_nested(
        &mut self,
        m: &mut AstManager,
        blocked: &OrderedSet<Expr>,
        expr: Expr,
        target: Expr,
    ) -> Result<Expr, SmtError> {
        let mut state = EvaluatorState::new(m, self.state.is_model_completion);
        let nested = EvaluatorCfg {
            model: &mut *self.model,
            state: &mut state,
        };
        rewrite_nested_with(m, nested, blocked, expr, target)
    }

    /// ~imp: evaluator_cfg goes before the caches of rewriter_tpl.
    fn release(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.state.rewriter.release(m)
    }
}

impl EvaluatorCfg<'_> {
    // evaluator_cfg::reduce_app_core.
    fn reduce_app_core(
        &mut self,
        m: &mut AstManager,
        last_result: &mut LastResult,
        decl: Decl,
        args: &[Expr],
        sort: Sort,
    ) -> Result<Reduced, SmtError> {
        let family = m.func_decls[decl as usize].family;
        if family == FAMILY_USER {
            if !args.is_empty() {
                return Ok(match self.evaluate(m, decl, args) {
                    None => Reduced::Failed,
                    Some(result) => Reduced::Rewrite(Rewrite {
                        expr: result,
                        depth: 1,
                    }),
                });
            }
            if let Some(value) = self.model.get_const_interp(m, decl) {
                return Ok(if contains_redex(m, value)? {
                    Reduced::Rewrite(Rewrite {
                        expr: value,
                        depth: UNBOUNDED_DEPTH,
                    })
                } else {
                    Reduced::Done(value)
                });
            }
            if !self.state.is_model_completion {
                return Ok(Reduced::Failed);
            }
            let some = self.model.get_some_value(m, sort);
            self.model.register_const(m, decl, some)?;
            return Ok(Reduced::Done(some));
        }
        if m.func_decls[decl as usize].op == OP_AND
            && let Some(reduced) = self.mk_arith_and_core(m, args)?
        {
            return Ok(Reduced::Rewrite(reduced));
        }
        let rewritten = self
            .state
            .rewriter
            .reduce_app_core(m, last_result, decl, args)?;
        let reduced = if rewritten == Reduced::Failed && family == FAMILY_ARITH {
            self.evaluate_partial_theory_func(m, decl, args, sort)?
        } else {
            rewritten
        };
        if family != FAMILY_ARITH {
            return Ok(reduced);
        }
        let Reduced::Done(reduced_expr) = reduced else {
            return Ok(reduced);
        };
        if m.kinds[reduced_expr as usize] != KIND_APP {
            return Ok(reduced);
        }
        self.state.reduced_args.clear();
        m.push_args(reduced_expr, &mut self.state.reduced_args);
        let reduced_args = std::mem::take(&mut self.state.reduced_args);
        let result = self.evaluate(m, m.decls[reduced_expr as usize], &reduced_args);
        self.state.reduced_args = reduced_args;
        Ok(match result {
            None => reduced,
            Some(result) => Reduced::Rewrite(Rewrite {
                expr: result,
                depth: 1,
            }),
        })
    }

    // evaluate and eval_fi: the result of the entry for the arguments when they are values.
    // Otherwise get_macro expands the interpretation.
    fn evaluate(&self, m: &AstManager, decl: Decl, args: &[Expr]) -> Option<Expr> {
        let interp = self.model.get_func_interp(m, decl)?;
        if interp.get_entries().is_empty() || !args.iter().all(|arg| m.is_unique_value(*arg)) {
            return None;
        }
        interp.get_entry(args).map(|entry| entry.result)
    }

    // evaluate_partial_theory_func: div0, idiv0 and mod0 take their interpretations, or 0 without
    // one, and so does a division by zero. A division by a term is its interpretation when the
    // term is zero.
    fn evaluate_partial_theory_func(
        &mut self,
        m: &mut AstManager,
        decl: Decl,
        args: &[Expr],
        sort: Sort,
    ) -> Result<Reduced, SmtError> {
        let op = m.func_decls[decl as usize].op;
        let by_zero = get_by_zero_op(op);
        let has_interp = self.model.get_func_interp(m, decl).is_some();
        if !has_interp
            && let Some(by_zero) = by_zero
            && !m.is_numeral(args[1])
        {
            let definition = match self.model.get_func_interp_mut(m, by_zero) {
                Some(interp) => interp.get_interp(m)?,
                None => None,
            };
            let Some(definition) = definition else {
                return Ok(Reduced::Failed);
            };
            let result = substitute(m, definition, args)?;
            let zero = m.mk_numeral_of_sort(&Rational::zero(), m.sorts[args[1] as usize]);
            let eq = m.mk_eq(zero, args[1])?;
            let app = m.mk_app(decl, args, sort)?;
            return Ok(Reduced::Done(m.mk_app(OP_ITE, &[eq, result, app], sort)?));
        }
        let target = if has_interp {
            decl
        } else {
            let is_by_zero = by_zero.is_some() && m.get_rational_value(args[1]).is_zero();
            if !is_by_zero && op != OP_DIV0 && op != OP_IDIV0 && op != OP_MOD0 {
                return Ok(Reduced::Failed);
            }
            match by_zero {
                Some(by_zero) if is_by_zero && self.model.get_func_interp(m, by_zero).is_some() => {
                    by_zero
                }
                _ => {
                    return Ok(Reduced::Done(m.mk_numeral_of_sort(&Rational::zero(), sort)));
                }
            }
        };
        let is_partial = self
            .model
            .get_func_interp(m, target)
            .is_some_and(FuncInterp::is_partial);
        if is_partial {
            let some = self.model.get_some_value(m, sort);
            if let Some(interp) = self.model.get_func_interp_mut(m, target) {
                interp.set_else(m, some)?;
            }
        }
        let definition = match self.model.get_func_interp_mut(m, target) {
            Some(interp) => interp.get_interp(m)?,
            None => None,
        };
        let definition = definition.ok_or_else(|| {
            SmtError::Invariant("a completed interpretation has no definition".into())
        })?;
        Ok(Reduced::Rewrite(Rewrite {
            expr: substitute(m, definition, args)?,
            depth: UNBOUNDED_DEPTH,
        }))
    }

    // arith_rewriter::mk_and_core: of lower bounds (<= a y) and (<= b y) on the same term, the
    // conjunction keeps the greatest. Z3 compares each bound with the first rather than with the
    // greatest so far, which drops the greatest when a smaller one follows it. This port keeps the
    // greatest.
    fn mk_arith_and_core(
        &mut self,
        m: &mut AstManager,
        args: &[Expr],
    ) -> Result<Option<Rewrite>, SmtError> {
        if args.len() <= 1 || m.get_op(args[0]) != OP_LE {
            return Ok(None);
        }
        let lower = m.get_arg(args[0], 0);
        let term = m.get_arg(args[0], 1);
        if !m.is_numeral(lower) {
            return Ok(None);
        }
        let mut bound = args[0];
        let mut rest: Vec<Expr> = Vec::new();
        for arg in &args[1..] {
            let is_bound = m.get_op(*arg) == OP_LE
                && m.get_arg(*arg, 1) == term
                && m.is_numeral(m.get_arg(*arg, 0));
            if !is_bound {
                rest.push(*arg);
            } else if m.get_rational_value(m.get_arg(*arg, 0))
                > m.get_rational_value(m.get_arg(bound, 0))
            {
                bound = *arg;
            }
        }
        if rest.len() == args.len() - 1 {
            return Ok(None);
        }
        rest.push(bound);
        Ok(Some(Rewrite {
            expr: m.mk_app(OP_AND, &rest, SORT_BOOL)?,
            depth: 1,
        }))
    }
}

// var_subst without the standard order, whose result the temporaries hold.
fn substitute(m: &mut AstManager, expr: Expr, args: &[Expr]) -> Result<Expr, SmtError> {
    let mut subst = VarSubst::new(m, false);
    let result = subst.apply(m, expr, args)?;
    subst.release(m)?;
    m.release_later(result)?;
    Ok(result)
}

// contains_redex: whether a constant's value has an equality to evaluate.
fn contains_redex(m: &AstManager, expr: Expr) -> Result<bool, SmtError> {
    if m.kinds[expr as usize] != KIND_APP || m.get_num_args(expr) == 0 {
        return Ok(false);
    }
    // Only looked up, never iterated.
    let mut visited = HashSet::new();
    let mut todo = vec![expr];
    while let Some(current) = todo.pop() {
        if !visited.insert(current) {
            continue;
        }
        if m.get_op(current) == OP_EQ {
            return Ok(true);
        }
        if m.kinds[current as usize] == KIND_APP {
            m.push_args(current, &mut todo);
        } else if m.kinds[current as usize] == KIND_QUANTIFIER {
            let data = m.get_quantifier(current)?;
            todo.push(data.body);
            todo.extend_from_slice(&data.patterns);
        }
    }
    Ok(false)
}
