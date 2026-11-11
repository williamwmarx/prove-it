//! Ported from Z3 (src/tactic/core/propagate_values_tactic.cpp, src/ast/shared_occs.cpp), MIT
//! license, through `propagate-values.ts`. The propagate-values tactic: a formula that is an atom, a
//! negated atom or an equality with a value rewrites the other formulas, when its atom or term
//! occurs more than once in the goal.
//!
//! The TypeScript passes the rewriter a map that it keeps extending; here the rewriter owns the
//! map, which `get_substitution_mut` extends.

use std::collections::HashSet;

use crate::core::ast::{AstManager, Expr, KIND_APP, KIND_QUANTIFIER, OP_EQ};
use crate::core::goal::Goal;
use crate::core::rewriter::{Rewriter, TACTIC_REWRITER_OPTIONS};
use crate::util::error::SmtError;
use crate::util::ordered_map::OrderedMap;

// The max_rounds parameter's default.
const MAX_ROUNDS: usize = 4;

// goal_shared_occs with atoms tracked: the terms that the goal's formulas reach more than once,
// quantifier bodies included and patterns excluded.
fn get_shared_occs(m: &AstManager, forms: &[Expr]) -> Result<HashSet<Expr>, SmtError> {
    let mut visited = HashSet::new();
    let mut shared = HashSet::new();
    let mut todo = forms.to_vec();
    while let Some(expr) = todo.pop() {
        if visited.contains(&expr) {
            shared.insert(expr);
            continue;
        }
        visited.insert(expr);
        if m.kinds[expr as usize] == KIND_APP {
            m.push_args(expr, &mut todo);
        } else if m.kinds[expr as usize] == KIND_QUANTIFIER {
            todo.push(m.get_quantifier(expr)?.body);
        }
    }
    Ok(shared)
}

// The state of the tactic's passes.
struct PropagateValues {
    rewriter: Rewriter,
    occs: HashSet<Expr>,
    is_modified: bool,
}

impl PropagateValues {
    // process_current and push_result.
    fn process(
        &mut self,
        m: &mut AstManager,
        goal: &mut Goal,
        index: usize,
    ) -> Result<(), SmtError> {
        let current = goal.forms.items[index];
        let is_rewriting = !self.rewriter.get_substitution_mut().is_empty();
        let rewritten = if is_rewriting {
            self.rewriter.rewrite(m, current)?
        } else {
            current
        };
        if rewritten != current {
            self.is_modified = true;
        }
        goal.update(m, index, rewritten)?;
        if is_rewriting {
            m.dec_ref(rewritten)?;
        }
        let substitution = self.rewriter.get_substitution_mut();
        if self.occs.contains(&rewritten) {
            substitution.insert(rewritten, m.true_expr);
        }
        if m.is_not(rewritten) && self.occs.contains(&m.get_arg(rewritten, 0)) {
            substitution.insert(m.get_arg(rewritten, 0), m.false_expr);
        }
        if m.get_op(rewritten) != OP_EQ {
            return Ok(());
        }
        let left = m.get_arg(rewritten, 0);
        let right = m.get_arg(rewritten, 1);
        if m.is_unique_value(left) && self.occs.contains(&right) {
            substitution.insert(right, left);
        } else if m.is_unique_value(right) && self.occs.contains(&left) {
            substitution.insert(left, right);
        }
        Ok(())
    }
}

/// The propagate-values tactic on the goal. Like the TypeScript, its rewriter is not released.
pub fn propagate_values(m: &mut AstManager, goal: &mut Goal) -> Result<(), SmtError> {
    if goal.is_inconsistent {
        return Ok(());
    }
    let mut rewriter = Rewriter::new(m, TACTIC_REWRITER_OPTIONS, false);
    rewriter.set_substitution(m, OrderedMap::new())?;
    let occs = get_shared_occs(m, &goal.forms.items)?;
    let mut state = PropagateValues {
        rewriter,
        occs,
        is_modified: false,
    };
    // Each pass is a round: a forward pass, which stops when it found nothing, then a backward
    // pass, which stops when it changed nothing.
    let mut round = 0;
    while round < MAX_ROUNDS {
        let size = goal.forms.len();
        for index in 0..size {
            state.process(m, goal, index)?;
            if goal.is_inconsistent {
                return Ok(());
            }
        }
        if state.rewriter.get_substitution_mut().is_empty() && !state.is_modified {
            break;
        }
        state.occs = get_shared_occs(m, &goal.forms.items)?;
        state.rewriter.set_substitution(m, OrderedMap::new())?;
        for index in (0..goal.forms.len()).rev() {
            state.process(m, goal, index)?;
            if goal.is_inconsistent {
                return Ok(());
            }
        }
        if !state.is_modified {
            break;
        }
        state.rewriter.set_substitution(m, OrderedMap::new())?;
        state.is_modified = false;
        state.occs = get_shared_occs(m, &goal.forms.items)?;
        round += 2;
    }
    goal.elim_redundancies(m)
}
