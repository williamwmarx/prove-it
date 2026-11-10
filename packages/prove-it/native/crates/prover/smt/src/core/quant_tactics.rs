//! Ported from Z3 (src/tactic/smtlogics/quant_tactics.cpp, src/tactic/core/simplify_tactic.cpp),
//! MIT license, through `quant-tactics.ts`. With (set-logic UFNIA), Z3's strategic solver runs the
//! ufnia tactic: a preprocessor, then qe-lite, then the SMT kernel. Of the preprocessor,
//! elim-uncnstr's elimination and the simplifier's local_ctx option are not ported, as they change
//! almost none of tlapm's obligations.

use std::collections::HashSet;

use crate::core::ast::{AstManager, Expr, KIND_APP, KIND_QUANTIFIER};
use crate::core::ctx_simplify::ctx_simplify;
use crate::core::goal::Goal;
use crate::core::propagate_values::propagate_values;
use crate::core::qe_lite::apply_qe_lite;
use crate::core::rewriter::{Rewriter, RewriterOptions, TACTIC_REWRITER_OPTIONS};
use crate::core::rewriter_tpl::{DefaultRewriterConfig, RewriterTpl};
use crate::util::error::SmtError;

// The simplify tactic, with pull_cheap_ite where the preprocessor sets it.
fn simplify(
    m: &mut AstManager,
    goal: &mut Goal,
    is_pulling_cheap_ite: bool,
) -> Result<(), SmtError> {
    if goal.is_inconsistent {
        return Ok(());
    }
    let mut rewriter = Rewriter::new(
        m,
        RewriterOptions {
            is_pulling_cheap_ite,
            ..TACTIC_REWRITER_OPTIONS
        },
        false,
    );
    let size = goal.forms.len();
    let mut rewritten = -1;
    let mut index = 0;
    while index < size && !goal.is_inconsistent {
        let result = rewriter.rewrite(m, goal.forms.items[index])?;
        if rewritten != -1 {
            m.dec_ref(rewritten)?;
        }
        rewritten = result;
        goal.update(m, index, rewritten)?;
        index += 1;
    }
    if rewritten != -1 {
        m.dec_ref(rewritten)?;
    }
    goal.elim_redundancies(m)?;
    rewriter.release(m)
}

// collect_occs: whether an uninterpreted constant occurs only once, where a term is visited once
// and a quantifier's patterns are not visited.
fn has_unconstrained_const(m: &AstManager, goal: &Goal) -> Result<bool, SmtError> {
    let mut visited = HashSet::new();
    let mut consts: Vec<Expr> = Vec::new();
    let mut repeated = HashSet::new();
    let mut todo = goal.forms.items.clone();
    while let Some(expr) = todo.pop() {
        let is_const = m.is_uninterpreted_const(expr);
        if visited.contains(&expr) {
            if is_const {
                repeated.insert(expr);
            }
            continue;
        }
        visited.insert(expr);
        if is_const {
            consts.push(expr);
        } else if m.kinds[expr as usize] == KIND_APP {
            m.push_args(expr, &mut todo);
        } else if m.kinds[expr as usize] == KIND_QUANTIFIER {
            todo.push(m.get_quantifier(expr)?.body);
        }
    }
    Ok(consts.iter().any(|expr| !repeated.contains(expr)))
}

// elim_uncnstr_tactic::run without the elimination. Its rewriter still runs over the formulas when
// some constant is unconstrained, and counts its steps. The rewriter starts as if the formulas had
// changed, so it makes a second round.
fn elim_uncnstr(m: &mut AstManager, goal: &Goal) -> Result<(), SmtError> {
    let is_rewriting = has_unconstrained_const(m, goal)?;
    pin_quantifier_bodies(m, goal)?;
    if !is_rewriting {
        return Ok(());
    }
    let mut rewriter = RewriterTpl::new(m, DefaultRewriterConfig);
    for _ in 0..2 {
        for form in goal.forms.items.iter().copied() {
            let result = rewriter.rewrite(m, form)?;
            m.dec_ref(result)?;
        }
        rewriter.reset(m)?;
    }
    rewriter.release(m)
}

// elim_uncnstr_tactic::disable_quantified: the tactic holds the body of each quantifier until it
// is destroyed after the search.
fn pin_quantifier_bodies(m: &mut AstManager, goal: &Goal) -> Result<(), SmtError> {
    let mut visited = HashSet::new();
    let mut disabled = HashSet::new();
    let mut todo = goal.forms.items.clone();
    while let Some(expr) = todo.pop() {
        if visited.contains(&expr) {
            continue;
        }
        visited.insert(expr);
        if m.kinds[expr as usize] == KIND_QUANTIFIER {
            let body = m.get_quantifier(expr)?.body;
            // disable: the body is held, and its subterms marked.
            if !disabled.contains(&body) {
                m.inc_ref(body);
                let mut body_todo = vec![body];
                while let Some(current) = body_todo.pop() {
                    if disabled.contains(&current) {
                        continue;
                    }
                    disabled.insert(current);
                    if m.kinds[current as usize] == KIND_APP {
                        m.push_args(current, &mut body_todo);
                    }
                }
            }
            todo.push(body);
        } else if m.kinds[expr as usize] == KIND_APP {
            m.push_args(expr, &mut todo);
        }
    }
    Ok(())
}

/// mk_ufnia_tactic, up to the SMT kernel: mk_quant_preprocessor without solve-eqs, then qe-lite.
/// The goal holds its formulas; its owner releases them.
pub fn apply_ufnia_tactic(m: &mut AstManager, assertions: &[Expr]) -> Result<Goal, SmtError> {
    let mut goal = Goal::new();
    for assertion in assertions.iter().copied() {
        goal.assert(m, assertion)?;
    }
    simplify(m, &mut goal, false)?;
    // and_then runs the next tactic only on a goal that is not decided: one that is consistent and
    // has formulas left.
    for step in 0..6 {
        if goal.is_inconsistent || goal.forms.is_empty() {
            break;
        }
        match step {
            0 => propagate_values(m, &mut goal)?,
            1 => ctx_simplify(m, &mut goal)?,
            2 => simplify(m, &mut goal, true)?,
            3 => elim_uncnstr(m, &goal)?,
            4 => simplify(m, &mut goal, false)?,
            _ => apply_qe_lite(m, &mut goal)?,
        }
    }
    Ok(goal)
}
