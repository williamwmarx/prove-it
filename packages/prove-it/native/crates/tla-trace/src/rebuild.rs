//! TLC's recovery of a trace (`TLCTrace.getTrace`, `Tool.getState`): the first state is the first
//! initial state, in TLC's order, that is the search's first state; each next state is the first
//! successor of the previous one, by the step's action, that is the search's next state. TLC
//! fingerprints each state it recovers, which sorts its records, and so does the search with each
//! state it keeps, so every state but the last prints sorted. The last state of a violation is
//! one the search didn't keep, and TLC fingerprinted it only if it satisfies the constraints.

use tla_ir::{Ir, NodeId};
use tla_values::{Id, Store};

use crate::eval::{Context, Evaluator};
use std::rc::Rc;

use crate::value::{Evaluated, Text, Value, equals, from_store, matches, permute, settle};
use crate::{Trace, TraceState, Unsupported};

/// Rebuilds traces of one model.
pub struct Rebuilder<'ir> {
    evaluator: Evaluator<'ir>,
    key: Key,
}

/// How TLC tells a candidate is the state it looks for: by its fingerprint, which is of the state,
/// of its VIEW, or of the least state in its orbit under SYMMETRY.
enum Key {
    State,
    /// The body of the VIEW's definition.
    View(NodeId),
    /// The permutations of the symmetry group, as the model values each one renames.
    Symmetry(Vec<Vec<(Rc<Text>, Rc<Text>)>>),
}

fn unsupported<T>(reason: impl Into<String>) -> Result<T, Unsupported> {
    Err(Unsupported(reason.into()))
}

impl<'ir> Rebuilder<'ir> {
    pub fn new(ir: &'ir Ir) -> Result<Rebuilder<'ir>, Unsupported> {
        let model = &ir.model;
        let mut evaluator = Evaluator::new(ir);
        let key = match (&model.view, &model.symmetry) {
            (Some(_), Some(_)) => return unsupported("rebuilding a trace under VIEW and SYMMETRY"),
            (Some(view), None) => match view.definition {
                Some(index) => Key::View(evaluator.definition(ir.definitions[index as usize]).body),
                None => return unsupported("a VIEW without a definition"),
            },
            (None, Some(group)) => Key::Symmetry(
                group
                    .iter()
                    .map(|permutation| {
                        permutation
                            .iter()
                            .map(|&(from, to)| (evaluator.text(from), evaluator.text(to)))
                            .collect()
                    })
                    .collect(),
            ),
            (None, None) => Key::State,
        };
        Ok(Rebuilder { evaluator, key })
    }

    /// The states of a path the search found, as TLC prints them. `states` holds each state's
    /// values as ids of `store`, in the IR's order of the variables; `actions[i]` is the position
    /// in the model's actions of the step from `states[i]` to `states[i + 1]` (`label_path`), or
    /// `None` to try each action in turn, as `Tool.getState` does. A step to the same state is a
    /// stuttering step.
    pub fn rebuild(
        &mut self,
        store: &Store,
        states: &[&[Id]],
        actions: &[Option<u32>],
    ) -> Result<Trace, Unsupported> {
        let evaluator = &mut self.evaluator;
        let ir = evaluator.ir;
        let width = ir.variables.len();
        if states.iter().any(|state| state.len() != width) {
            return unsupported("a state of another width than the model's");
        }
        let Some(&first) = states.first() else {
            return Ok(Trace { states: Vec::new() });
        };
        let printed = evaluator.printed.len();
        let mut rebuilt: Vec<Vec<Value>> = Vec::with_capacity(states.len());
        let context = run(evaluator.scope_context(ir.model.scope))?;
        evaluator.level = 0;
        evaluator.current = vec![None; width];
        let initial = find(evaluator, &self.key, ir.model.init, &context, true, store, first)?;
        let Some(initial) = initial else {
            return unsupported("no initial state is the trace's first");
        };
        rebuilt.push(initial);
        for (position, pair) in states.windows(2).enumerate() {
            // TLC recovers a state, and so fingerprints it, before it takes its step.
            rebuilt[position].iter().for_each(settle);
            let previous = rebuilt[position].clone();
            if pair[0] == pair[1] {
                rebuilt.push(previous);
                continue;
            }
            evaluator.current = previous.into_iter().map(Some).collect();
            evaluator.next = vec![None; width];
            evaluator.level = position as i32 + 1;
            let candidates: Vec<(NodeId, Option<u32>)> = match actions.get(position).copied() {
                Some(Some(action)) => match ir.model.actions.get(action as usize) {
                    Some(action) => vec![(action.expression, action.scope)],
                    None => return unsupported("an action the model doesn't have"),
                },
                _ if ir.model.actions.is_empty() => vec![(ir.model.next, ir.model.scope)],
                _ => ir
                    .model
                    .actions
                    .iter()
                    .map(|action| (action.expression, action.scope))
                    .collect(),
            };
            let mut found = None;
            for (expression, scope) in candidates {
                let context = run(evaluator.scope_context(scope))?;
                found = find(evaluator, &self.key, expression, &context, false, store, pair[1])?;
                if found.is_some() {
                    break;
                }
            }
            let Some(state) = found else {
                return unsupported(format!(
                    "no step from state {} is the trace's next",
                    position + 1
                ));
            };
            rebuilt.push(state);
        }
        if is_in_model(evaluator, &rebuilt)? {
            rebuilt[rebuilt.len() - 1].iter().for_each(settle);
        }
        if evaluator.printed.len() > printed {
            evaluator.printed.truncate(printed);
            return unsupported("printing while TLC rebuilds a trace");
        }
        Ok(Trace {
            states: rebuilt
                .into_iter()
                .map(|values| TraceState { values })
                .collect(),
        })
    }
}

fn run<T>(evaluated: Evaluated<T>) -> Result<T, Unsupported> {
    evaluated.map_err(|error| Unsupported(format!("rebuilding a trace: {}", error.0)))
}

// The first state the walk of an action completes that TLC takes for the search's state.
fn find(
    evaluator: &mut Evaluator<'_>,
    key: &Key,
    expression: NodeId,
    context: &Context,
    is_init: bool,
    store: &Store,
    target: &[Id],
) -> Result<Option<Vec<Value>>, Unsupported> {
    let target_view = match key {
        Key::View(view) => {
            let saved = std::mem::take(&mut evaluator.current);
            evaluator.current = target.iter().map(|&id| Some(from_store(store, id))).collect();
            let value = evaluator.evaluate(*view, &Context::default());
            evaluator.current = saved;
            Some(run(value)?)
        }
        _ => None,
    };
    let mut found = None;
    run(evaluator.walk_action(expression, context, is_init, &mut |evaluator| {
        let state: Vec<Value> = if is_init {
            evaluator.current.iter().flatten().cloned().collect()
        } else {
            evaluator.next.iter().flatten().cloned().collect()
        };
        let is_match = match key {
            Key::State => is_same(store, target, &state),
            Key::View(view) => {
                let saved = std::mem::replace(
                    &mut evaluator.current,
                    state.iter().cloned().map(Some).collect(),
                );
                let value = evaluator.evaluate(*view, &Context::default());
                evaluator.current = saved;
                equals(&value?, target_view.as_ref().expect("the target's view"))?
            }
            Key::Symmetry(group) => {
                is_same(store, target, &state) || {
                    let mut is_found = false;
                    for permutation in group {
                        let permuted = state
                            .iter()
                            .map(|value| permute(value, permutation))
                            .collect::<Evaluated<Vec<_>>>()?;
                        if is_same(store, target, &permuted) {
                            is_found = true;
                            break;
                        }
                    }
                    is_found
                }
            }
        };
        if is_match {
            found = Some(state);
        }
        Ok(!is_match)
    }))?;
    Ok(found)
}

fn is_same(store: &Store, target: &[Id], state: &[Value]) -> bool {
    state
        .iter()
        .zip(target)
        .all(|(value, &id)| matches(store, id, value))
}

// Whether the last state satisfies the model's constraints and, if a step reached it, its action
// constraints, as TLC's `isInModel` and `isInActions` find before it fingerprints a state.
fn is_in_model(evaluator: &mut Evaluator<'_>, rebuilt: &[Vec<Value>]) -> Result<bool, Unsupported> {
    let ir = evaluator.ir;
    let state = |values: &[Value]| values.iter().cloned().map(Some).collect();
    let last = rebuilt.len() - 1;
    let constraints = ir.model.constraints.iter().map(|name| (name, false));
    let action_constraints = ir.model.action_constraints.iter().map(|name| (name, true));
    for (name, is_action) in constraints.chain(action_constraints) {
        if is_action && last == 0 {
            continue;
        }
        let Some(index) = name.definition else {
            return unsupported("a constraint without a definition");
        };
        if is_action {
            evaluator.current = state(&rebuilt[last - 1]);
            evaluator.next = state(&rebuilt[last]);
        } else {
            evaluator.current = state(&rebuilt[last]);
        }
        let body = evaluator.definition(ir.definitions[index as usize]).body;
        if !run(evaluator.boolean(body, &Context::default()))? {
            return Ok(false);
        }
    }
    Ok(true)
}
