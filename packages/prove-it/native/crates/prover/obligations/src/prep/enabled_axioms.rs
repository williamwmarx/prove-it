//! Expr.Action.implication_to_enabled, the ENABLEDaxioms frontend: it proves a rule about ENABLED
//! from facts of the form the rule needs. A port of `src/prover/prep/enabled-axioms.ts`.

use std::collections::BTreeSet;

use crate::equality::is_equal_expr;
use crate::errors::{ObligationError, Result};
use crate::expression::{
    Builtin, Expr, ExprCore, HypCore, Hyps, ScopeRef, Sequent, Visibility, adjoin, adjoin_all,
    expr, get_scope_at, map_scoped, to_index,
};
use crate::levels::get_level_info;
use crate::substitution::shift_expr;

struct Rule {
    name: &'static str,
    left: Expr,
    right: Expr,
}

fn get_operands(expression: &Expr, builtin: Builtin) -> Option<(&Expr, &Expr)> {
    match &expression.core {
        ExprCore::Apply { operator, args } => match (&operator.core, args.as_slice()) {
            (ExprCore::Internal { builtin: applied }, [left, right]) if *applied == builtin => {
                Some((left, right))
            }
            _ => None,
        },
        _ => None,
    }
}

fn get_enabled(expression: &Expr) -> Option<&Expr> {
    match &expression.core {
        ExprCore::Apply { operator, args } => match (&operator.core, args.as_slice()) {
            (
                ExprCore::Internal {
                    builtin: Builtin::ENABLED,
                },
                [operand],
            ) => Some(operand),
            _ => None,
        },
        _ => None,
    }
}

// Both operands of the connective, when each is an ENABLED.
fn get_enabled_operands(expression: &Expr, builtin: Builtin) -> Option<(&Expr, &Expr)> {
    let operands = get_operands(expression, builtin)?;
    Some((get_enabled(operands.0)?, get_enabled(operands.1)?))
}

#[derive(Clone)]
struct PrimedState {
    scope: ScopeRef,
    is_primed: bool,
}

// E_visit.collect_primed_vars: the variables under a prime, an UNCHANGED, or a subscript.
fn visit_primed(names: &mut BTreeSet<String>, state: &PrimedState, inner: &Expr) -> Result<Expr> {
    let primed = PrimedState {
        is_primed: true,
        ..state.clone()
    };
    let (builtin, args) = match &inner.core {
        ExprCore::Apply { operator, args } => match operator.core {
            ExprCore::Internal { builtin } => (Some(builtin), args.as_slice()),
            _ => (None, args.as_slice()),
        },
        _ => (None, &[][..]),
    };
    let is_sub = matches!(inner.core, ExprCore::Sub { .. });
    let is_scoped = (builtin == Some(Builtin::Prime) && args.len() == 1)
        || builtin == Some(Builtin::ENABLED)
        || (builtin == Some(Builtin::Cdot) && args.len() == 2)
        || (builtin == Some(Builtin::UNCHANGED) && args.len() == 1)
        || is_sub;
    if is_scoped && state.is_primed {
        return Err(ObligationError::assert_failure());
    }
    match (builtin, args, &inner.core) {
        (Some(Builtin::Prime), [operand], _) | (Some(Builtin::UNCHANGED), [operand], _) => {
            visit_primed(names, &primed, operand)?;
        }
        (Some(Builtin::Cdot), [_, second], _) => {
            visit_primed(names, state, second)?;
        }
        (
            _,
            _,
            ExprCore::Sub {
                action, subscript, ..
            },
        ) => {
            visit_primed(names, state, action)?;
            visit_primed(names, &primed, subscript)?;
        }
        (_, _, ExprCore::Ix { index }) => {
            let hyp_scope = get_scope_at(&state.scope, index - 1)
                .ok_or_else(ObligationError::assert_failure)?;
            if let HypCore::Flex { name } = &hyp_scope.hyp.core
                && state.is_primed
            {
                names.insert(name.clone());
            }
        }
        (Some(Builtin::ENABLED), _, _) => {}
        _ => {
            map_scoped(
                state,
                inner,
                &mut |current, child| visit_primed(names, current, child),
                &mut |current, hyp| PrimedState {
                    scope: adjoin(&current.scope, hyp),
                    is_primed: current.is_primed,
                },
                Hyps::Visible,
            )?;
        }
    }
    Ok(inner.clone())
}

fn get_primed_variables(scope: &ScopeRef, expression: &Expr) -> Result<BTreeSet<String>> {
    let mut names = BTreeSet::new();
    visit_primed(
        &mut names,
        &PrimedState {
            scope: scope.clone(),
            is_primed: false,
        },
        expression,
    )?;
    Ok(names)
}

fn is_disjoint(scope: &ScopeRef, left: &Expr, right: &Expr) -> Result<bool> {
    let left_names = get_primed_variables(scope, left)?;
    Ok(get_primed_variables(scope, right)?
        .iter()
        .all(|name| !left_names.contains(name)))
}

fn get_rule_of(name: &'static str, operands: (&Expr, &Expr)) -> Rule {
    Rule {
        name,
        left: operands.0.clone(),
        right: operands.1.clone(),
    }
}

// check_active: the rule the goal's form calls for, with the operands the facts must mention.
fn get_rule(scope: &ScopeRef, goal: &Expr) -> Result<Option<Rule>> {
    let get_level_of =
        |expression: &Expr| -> Result<usize> { Ok(get_level_info(scope, expression)?.level) };
    let assert_actions = |left: &Expr, right: &Expr| -> Result<()> {
        if get_level_of(left)? > 2 || get_level_of(right)? > 2 {
            return Err(ObligationError::assert_failure());
        }
        Ok(())
    };
    let enabled = get_enabled(goal);
    if let Some(operands) = enabled.and_then(|inner| get_operands(inner, Builtin::Disj)) {
        assert_actions(operands.0, operands.1)?;
        return Ok(Some(get_rule_of("abdisj_inverse", operands)));
    }
    if let Some(operands) = get_enabled_operands(goal, Builtin::Disj) {
        assert_actions(operands.0, operands.1)?;
        return Ok(Some(get_rule_of("abdisj", operands)));
    }
    if let Some(operands) = enabled.and_then(|inner| get_operands(inner, Builtin::Conj)) {
        let is_apart = is_disjoint(scope, operands.0, operands.1)?;
        assert_actions(operands.0, operands.1)?;
        if !is_apart {
            return Ok(None);
        }
        let name = if get_level_of(operands.0)? == 2 {
            "abconj_inverse"
        } else {
            "pconj_inverse"
        };
        return Ok(Some(get_rule_of(name, operands)));
    }
    if let Some(operands) = get_enabled_operands(goal, Builtin::Conj) {
        return Ok(if is_disjoint(scope, operands.0, operands.1)? {
            Some(get_rule_of("abconj", operands))
        } else {
            None
        });
    }
    let operands = get_operands(goal, Builtin::Conj);
    if let Some(operands) = operands
        && let Some(action) = get_enabled(operands.1)
    {
        return Ok(
            if get_level_of(operands.0)? <= 1 && get_level_of(action)? <= 2 {
                Some(get_rule_of("pconj", (operands.0, action)))
            } else {
                None
            },
        );
    }
    let equivalence = get_enabled_operands(goal, Builtin::Equiv)
        .or_else(|| get_enabled_operands(goal, Builtin::Eq));
    if let Some(operands) = equivalence {
        return Ok(Some(get_rule_of("equiv", operands)));
    }
    Ok(get_enabled_operands(goal, Builtin::Implies)
        .map(|operands| get_rule_of("implies", operands)))
}

/// implication_to_enabled: the goal follows by the rule its form calls for when a visible fact is
/// the rule's premise and others say that both operands are in BOOLEAN, or the premise is an
/// equivalence. The goal then becomes TRUE; otherwise tlapm records the obligation as not tried.
pub fn implication_to_enabled(sequent: &Sequent) -> Result<Sequent> {
    let goal_scope = adjoin_all(&None, &sequent.context);
    let rule = get_rule(&goal_scope, &sequent.active)?;
    let mut is_premise = false;
    let mut is_left_boolean = false;
    let mut is_right_boolean = false;
    for (index, hyp) in sequent.context.iter().enumerate() {
        let Some(rule) = &rule else {
            continue;
        };
        let HypCore::Fact {
            expression: fact,
            visibility: Visibility::Visible,
            ..
        } = &hyp.core
        else {
            continue;
        };
        let amount = to_index(sequent.context.len() - index);
        let is_left = |expression: &Expr| -> Result<bool> {
            Ok(is_equal_expr(&*shift_expr(amount, expression)?, &rule.left))
        };
        let is_right = |expression: &Expr| -> Result<bool> {
            Ok(is_equal_expr(
                &*shift_expr(amount, expression)?,
                &rule.right,
            ))
        };
        let is_pair = |operands: Option<(&Expr, &Expr)>, names: &[&str]| -> Result<bool> {
            let Some(operands) = operands else {
                return Ok(false);
            };
            Ok(is_left(operands.0)? && is_right(operands.1)? && names.contains(&rule.name))
        };
        let enabled = get_enabled(fact);
        let enabled_conjunction = enabled.and_then(|inner| get_operands(inner, Builtin::Conj));
        let conjunction = get_operands(fact, Builtin::Conj);
        let action = conjunction.and_then(|operands| get_enabled(operands.1));
        let membership = get_operands(fact, Builtin::Mem);
        let is_boolean = membership.is_some_and(|operands| {
            matches!(
                operands.1.core,
                ExprCore::Internal {
                    builtin: Builtin::BOOLEAN
                }
            )
        });
        if is_pair(enabled_conjunction, &["pconj"])?
            || is_pair(
                enabled.and_then(|inner| get_operands(inner, Builtin::Disj)),
                &["abdisj"],
            )?
            || is_pair(
                get_enabled_operands(fact, Builtin::Disj),
                &["abdisj_inverse"],
            )?
            || is_pair(enabled_conjunction, &["abconj"])?
            || is_pair(
                get_enabled_operands(fact, Builtin::Conj),
                &["abconj_inverse", "pconj_inverse"],
            )?
            || is_pair(
                conjunction.zip(action).map(|pair| (pair.0.0, pair.1)),
                &["pconj_inverse"],
            )?
        {
            is_premise = true;
        } else if is_pair(get_operands(fact, Builtin::Equiv), &["equiv"])? {
            is_premise = true;
            is_left_boolean = true;
            is_right_boolean = true;
        } else if is_pair(get_operands(fact, Builtin::Eq), &["equiv"])? {
            is_premise = true;
        } else if let Some(operands) = membership
            && is_boolean
            && is_left(operands.0)?
        {
            is_left_boolean = true;
        } else if let Some(operands) = membership
            && is_boolean
            && is_right(operands.0)?
        {
            is_right_boolean = true;
        } else if is_pair(get_operands(fact, Builtin::Implies), &["implies"])? {
            is_premise = true;
        }
    }
    if !is_premise || !is_left_boolean || !is_right_boolean {
        return Err(ObligationError::prover(
            "ENABLEDaxioms proof directive did not succeed.\n",
        ));
    }
    Ok(Sequent {
        context: sequent.context.clone(),
        active: expr(ExprCore::Internal {
            builtin: Builtin::TRUE,
        }),
    })
}

#[cfg(test)]
mod tests {
    use crate::prep::fingerprint::tests::check_cases;

    /// Each case: the outcomes `enabled-axioms.ts` (and the other Prep modules) give, then the
    /// sequent, as the TypeScript prints them under Bun.
    const CASES: &str = r##"
{"fp":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure","lc":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Flex","name":"x"},{"kind":"Flex","name":"y"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]}]}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]}]}]}}
{"fp":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure","lc":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Flex","name":"x"},{"kind":"Flex","name":"y"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Equiv"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]}]}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Equiv"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]}]}]}}
{"fp":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure","lc":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Flex","name":"x"},{"kind":"Flex","name":"y"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]}]}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]}]}]}}
{"fp":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure"}
{"context":[{"kind":"Flex","name":"x"},{"kind":"Flex","name":"y"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]}]}]}}
{"fp":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure"}
{"context":[{"kind":"Flex","name":"x"},{"kind":"Flex","name":"y"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]}]}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]}]}]}}
{"fp":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure"}
{"context":[{"kind":"Flex","name":"x"},{"kind":"Flex","name":"y"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]}]}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]}]}]}}
{"fp":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Flex","name":"x"},{"kind":"Flex","name":"y"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]}]}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]}]}]}}
{"fp":"01fb31d3b8946148f36d0adb12f13f92","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Flex","name":"x"},{"kind":"Flex","name":"y"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]}]}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]}]}}
{"fp":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure"}
{"context":[{"kind":"Flex","name":"x"},{"kind":"Flex","name":"y"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]}]}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]}]}]}}
{"fp":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure"}
{"context":[{"kind":"Flex","name":"x"},{"kind":"Flex","name":"y"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":2},{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]}]}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":1},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]}]}]}}
{"fp":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure"}
{"context":[{"kind":"Flex","name":"x"},{"kind":"Flex","name":"y"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":2},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]}]}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":1},{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]}]}]}}
{"fp":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure"}
{"context":[{"kind":"Flex","name":"x"},{"kind":"Flex","name":"y"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":2},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]}]}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]}]}]}}
{"fp":"89ec82f29ad782d2241e636c3c36e9a1","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure"}
{"context":[{"kind":"Flex","name":"x"},{"kind":"Flex","name":"y"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Tsub","modal":"Box","action":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},"subscript":{"kind":"Ix","index":1}},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]}]}]}}
{"fp":"b9e708423c7035484b95989b5e3f9091","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure"}
{"context":[{"kind":"Flex","name":"x"},{"kind":"Flex","name":"y"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Tsub","modal":"Box","action":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},"subscript":{"kind":"Ix","index":1}}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]}]}]}}
{"fp":"76c276b90ce41e587187848894fbb57d","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure"}
{"context":[{"kind":"Flex","name":"x"},{"kind":"Flex","name":"y"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]}]}]}}
{"fp":"0bfdf7003886a31b6f96beeda1813b32","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Flex","name":"x"},{"kind":"Flex","name":"y"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Sub","modal":"Box","action":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},"subscript":{"kind":"Ix","index":2}},{"kind":"Apply","operator":{"kind":"Internal","builtin":"UNCHANGED"},"args":[{"kind":"Ix","index":2}]}]}]}}
{"fp":"7612a25c475cabb1ad53f805d3a2641b","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Flex","name":"x"},{"kind":"Flex","name":"y"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Cdot"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]}]}]}]}}
{"fp":"8b0aeb26a2e49de6c5645555423bead8","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Flex","name":"x"},{"kind":"Flex","name":"y"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Quant","quantifier":"Exists","bounds":[{"name":"z","level":"Constant","domain":{"kind":"NoDomain"}}],"body":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]}},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]}]}}
{"fp":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure"}
{"context":[{"kind":"Flex","name":"x"},{"kind":"Flex","name":"y"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Ix","index":5},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]}]}}
{"fp":"a6d0cd0296670772114f40aa37dfdcf4","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Flex","name":"x"},{"kind":"Flex","name":"y"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]},{"kind":"Internal","builtin":"TRUE"}]}}
{"fp":"03bf1ef9075de2433035dde744d14b39","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Flex","name":"x"},{"kind":"Flex","name":"y"},{"kind":"Fact","expression":{"kind":"Opaque","name":"unrelated"},"visibility":"Visible","time":"Now"}],"active":{"kind":"Opaque","name":"goal"}}
{"fp":"02ee9359c84d3a5860bb958bd71181a3","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Flex","name":"x"},{"kind":"Flex","name":"y"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]}]}]},"visibility":"Hidden","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]}]}]}}
{"fp":"5e42c857466f64e6a853428af51cda29","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Flex","name":"x"},{"kind":"Flex","name":"y"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]},{"kind":"Internal","builtin":"BOOLEAN"}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]}]}]}}
{"fp":"3978541ad6ba10f99197aa4613a92ac0","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"ok"}
{"context":[{"kind":"Flex","name":"x"},{"kind":"Flex","name":"y"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Equiv"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Equiv"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]}]}]}}
{"fp":"8c89a2a8b1e5a90c5517cc5304edcb67","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"ok"}
{"context":[{"kind":"Flex","name":"x"},{"kind":"Flex","name":"y"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Equiv"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]}]}]}}
{"fp":"1468a48f87b3107dcd1e44eaf9258d74","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"ok"}
{"context":[{"kind":"Flex","name":"x"},{"kind":"Flex","name":"y"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]}]},"visibility":"Visible","time":"Now"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]},{"kind":"Internal","builtin":"BOOLEAN"}]},"visibility":"Visible","time":"Now"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]},{"kind":"Internal","builtin":"BOOLEAN"}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":5}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":4}]}]}]}}
{"fp":"f6d46b00f64560fadd409f9855edbb99","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"ok"}
{"context":[{"kind":"Flex","name":"x"},{"kind":"Flex","name":"y"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]}]},"visibility":"Visible","time":"Now"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]},{"kind":"Internal","builtin":"BOOLEAN"}]},"visibility":"Visible","time":"Now"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]},{"kind":"Internal","builtin":"BOOLEAN"}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Disj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":5}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":4}]}]}]}}
{"fp":"4f104d9d68755cd427195adc284dbc33","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"ok"}
{"context":[{"kind":"Flex","name":"x"},{"kind":"Flex","name":"y"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]}]},"visibility":"Visible","time":"Now"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]},{"kind":"Internal","builtin":"BOOLEAN"}]},"visibility":"Visible","time":"Now"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]},{"kind":"Internal","builtin":"BOOLEAN"}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":5}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":4}]}]}]}}
{"fp":"53b5ae82796a03d37429e1a98b70c315","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"ok"}
{"context":[{"kind":"Flex","name":"x"},{"kind":"Flex","name":"y"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]}]},"visibility":"Visible","time":"Now"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]},{"kind":"Internal","builtin":"BOOLEAN"}]},"visibility":"Visible","time":"Now"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]},{"kind":"Internal","builtin":"BOOLEAN"}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":5}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":4}]}]}]}}
{"fp":"14224bc50c98acb0df8b35e0b367d4a3","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"ok"}
{"context":[{"kind":"Flex","name":"x"},{"kind":"Flex","name":"y"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]},"visibility":"Visible","time":"Now"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]},{"kind":"Internal","builtin":"BOOLEAN"}]},"visibility":"Visible","time":"Now"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]},{"kind":"Internal","builtin":"BOOLEAN"}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":5}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":4}]}]}]}}
{"fp":"05ae999dc1f9cb2eee58a03178d9258d","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"ok"}
{"context":[{"kind":"Flex","name":"x"},{"kind":"Flex","name":"y"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Equiv"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]},"visibility":"Visible","time":"Now"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]},{"kind":"Internal","builtin":"BOOLEAN"}]},"visibility":"Visible","time":"Now"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]},{"kind":"Internal","builtin":"BOOLEAN"}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Equiv"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":5}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":4}]}]}]}}
{"fp":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"ok"}
{"context":[{"kind":"Flex","name":"x"},{"kind":"Flex","name":"y"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Equiv"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":4}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":5}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":4}]}]}]}}
{"fp":"99fe59bd8878da958e6be62681d0a3f8","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"ok"}
{"context":[{"kind":"Flex","name":"x"},{"kind":"Flex","name":"y"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]},"visibility":"Visible","time":"Now"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]},{"kind":"Internal","builtin":"BOOLEAN"}]},"visibility":"Visible","time":"Now"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]},{"kind":"Internal","builtin":"BOOLEAN"}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Equiv"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":5}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":4}]}]}]}}
{"fp":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure","lc":"TlaProofError|Oops, this seems to be a bug in TLAPM.|Assert_failure","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Flex","name":"x"},{"kind":"Flex","name":"y"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]}]}]},"visibility":"Visible","time":"Now"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]},{"kind":"Internal","builtin":"BOOLEAN"}]},"visibility":"Visible","time":"Now"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]},{"kind":"Internal","builtin":"BOOLEAN"}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]}]}]}}
{"fp":"ba99afe83a0b47bca6ad2048a2f5b841","lc":"ok","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Flex","name":"x"},{"kind":"Flex","name":"y"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Equiv"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Equiv"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]}]}]}}
{"fp":"3a045360d9adedca3d9ff2e46601eedc","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Flex","name":"x"},{"kind":"Flex","name":"y"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]}]}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Conj"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]}]}]}}
{"fp":"1597dcd38372db8c7f63794f1cd77481","lc":"ok","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Flex","name":"x"},{"kind":"Flex","name":"y"},{"kind":"Fresh","name":"pad","shape":0,"level":"Constant","domainVisibility":"Visible"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]}]}]}}
{"fp":"67b1f6bdbbce73a779a0fe95dc7cb531","lc":"ok","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Flex","name":"x"},{"kind":"Flex","name":"y"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]}]},"visibility":"Visible","time":"Now"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]},{"kind":"Internal","builtin":"BOOLEAN"}]},"visibility":"Visible","time":"Now"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]},{"kind":"Internal","builtin":"BOOLEAN"}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Eq"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":5}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":4}]}]}]}}
{"fp":"5964c70ee8e16b4a841f65f98c22232f","lc":"TlaProverError|LevelComparison proof directive did not succeed.\n|","ea":"TlaProverError|ENABLEDaxioms proof directive did not succeed.\n|"}
{"context":[{"kind":"Flex","name":"x"},{"kind":"Flex","name":"y"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":1}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":2}]}]}]},"visibility":"Visible","time":"Now"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]},{"kind":"Internal","builtin":"BOOLEAN"}]},"visibility":"Visible","time":"Now"},{"kind":"Fact","expression":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Mem"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":3}]},{"kind":"Internal","builtin":"BOOLEAN"}]},"visibility":"Visible","time":"Now"}],"active":{"kind":"Apply","operator":{"kind":"Internal","builtin":"Implies"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":5}]}]},{"kind":"Apply","operator":{"kind":"Internal","builtin":"ENABLED"},"args":[{"kind":"Apply","operator":{"kind":"Internal","builtin":"Prime"},"args":[{"kind":"Ix","index":4}]}]}]}}
"##;

    #[test]
    fn matches_the_typescript() {
        assert_eq!(check_cases(CASES), 39);
    }
}
