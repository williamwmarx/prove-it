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

use crate::value::{Evaluated, Text, Value, compare, equals, from_store, matches, permute, settle};
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
    /// The VIEW of the least state of the orbit.
    ViewOfSymmetry(NodeId, Vec<Vec<(Rc<Text>, Rc<Text>)>>),
}

fn unsupported<T>(reason: impl Into<String>) -> Result<T, Unsupported> {
    Err(Unsupported(reason.into()))
}

impl<'ir> Rebuilder<'ir> {
    pub fn new(ir: &'ir Ir) -> Result<Rebuilder<'ir>, Unsupported> {
        let model = &ir.model;
        let mut evaluator = Evaluator::new(ir);
        let view = match &model.view {
            Some(view) => match view.definition {
                Some(index) => Some(evaluator.definition(ir.definitions[index as usize]).body),
                None => return unsupported("a VIEW without a definition"),
            },
            None => None,
        };
        let group = model.symmetry.as_ref().map(|group| {
            group
                .iter()
                .map(|permutation| {
                    permutation
                        .iter()
                        .map(|&(from, to)| (evaluator.text(from), evaluator.text(to)))
                        .collect()
                })
                .collect()
        });
        let key = match (view, group) {
            (Some(view), Some(group)) => Key::ViewOfSymmetry(view, group),
            (Some(view), None) => Key::View(view),
            (None, Some(group)) => Key::Symmetry(group),
            (None, None) => Key::State,
        };
        Ok(Rebuilder { evaluator, key })
    }

    /// The states of a path the search found, as TLC prints them. `states` holds each state's
    /// values as ids of `store`, in the IR's order of the variables; `actions[i]` is the position
    /// in the model's actions of the step from `states[i]` to `states[i + 1]` (`label_path`), or
    /// `None` to try each action in turn, as `Tool.getState` does. A step to the same state is a
    /// stuttering step. `loop_start` marks a liveness counterexample, which TLC rebuilds once.
    pub fn rebuild(
        &mut self,
        store: &Store,
        states: &[&[Id]],
        actions: &[Option<u32>],
        loop_start: Option<usize>,
    ) -> Result<Trace, Unsupported> {
        let evaluator = &mut self.evaluator;
        let ir = evaluator.ir;
        let width = ir.variables.len();
        if states.iter().any(|state| state.len() != width) {
            return unsupported("a state of another width than the model's");
        }
        let Some(&first) = states.first() else {
            return Ok(Trace {
                states: Vec::new(),
                trace_output: Vec::new(),
            });
        };
        // What the spec prints depends on every state TLC enumerates, so where it prints, each
        // walk runs to its end, and each step tries TLC's actions in order, as `findStepAction`
        // does; elsewhere a walk stops at the state it looks for.
        let is_printing = ir
            .builtins
            .iter()
            .any(|builtin| matches!(&*ir.texts[builtin.name as usize], "Print" | "PrintT"));
        evaluator.printed.clear();
        let mut rebuilt: Vec<Vec<Value>> = Vec::with_capacity(states.len());
        let context = run(evaluator.scope_context(ir.model.scope))?;
        evaluator.level = 0;
        evaluator.current = vec![None; width];
        let initial = find(
            evaluator,
            &self.key,
            (ir.model.init, &context, true),
            is_printing,
            store,
            first,
        )?;
        let Some(initial) = initial else {
            return unsupported("no initial state is the trace's first");
        };
        let initial_output = std::mem::take(&mut evaluator.printed);
        let mut outputs: Vec<Vec<Vec<String>>> = vec![Vec::new()];
        rebuilt.push(initial);
        let all_actions: Vec<(NodeId, Option<u32>)> = if ir.model.actions.is_empty() {
            vec![(ir.model.next, ir.model.scope)]
        } else {
            ir.model
                .actions
                .iter()
                .map(|action| (action.expression, action.scope))
                .collect()
        };
        for (position, pair) in states.windows(2).enumerate() {
            // TLC recovers a state, and so fingerprints it, before it takes its step.
            rebuilt[position].iter().for_each(settle);
            let previous = rebuilt[position].clone();
            if pair[0] == pair[1] {
                rebuilt.push(previous);
                outputs.push(Vec::new());
                continue;
            }
            evaluator.current = previous.into_iter().map(Some).collect();
            evaluator.level = position as i32 + 1;
            let candidates = match actions.get(position).copied().flatten() {
                Some(action) if !is_printing => match ir.model.actions.get(action as usize) {
                    Some(action) => vec![(action.expression, action.scope)],
                    None => return unsupported("an action the model doesn't have"),
                },
                _ => all_actions.clone(),
            };
            let mut found = None;
            for (expression, scope) in candidates {
                let context = run(evaluator.scope_context(scope))?;
                evaluator.next = vec![None; width];
                found = find(
                    evaluator,
                    &self.key,
                    (expression, &context, false),
                    is_printing,
                    store,
                    pair[1],
                )?;
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
            outputs.push(std::mem::take(&mut evaluator.printed));
        }
        if is_in_model(evaluator, &rebuilt)? {
            rebuilt[rebuilt.len() - 1].iter().for_each(settle);
        }
        evaluator.printed.clear();
        Ok(compose(rebuilt, initial_output, outputs, loop_start))
    }
}

// What TLC prints with each state, as `toTrace` gives it. TLC rebuilds the states it doesn't keep
// before it prints the trace, all but the last of a violation's and all of a lasso's, and then
// prints each later state with what finding its step printed. A trace of one state prints only
// what the initial predicate printed, after it. A violation's trace is rebuilt once more after it
// is printed.
fn compose(
    rebuilt: Vec<Vec<Value>>,
    initial_output: Vec<Vec<String>>,
    outputs: Vec<Vec<Vec<String>>>,
    loop_start: Option<usize>,
) -> Trace {
    let count = rebuilt.len();
    if count == 1 {
        return Trace {
            states: rebuilt
                .into_iter()
                .map(|values| TraceState {
                    values,
                    printed: Vec::new(),
                })
                .collect(),
            trace_output: initial_output,
        };
    }
    let known = usize::from(loop_start.is_none());
    let recovered = count - known;
    let trace_output = if known > 0 {
        initial_output
            .iter()
            .chain(outputs.iter().flatten())
            .cloned()
            .collect()
    } else {
        Vec::new()
    };
    let mut prefix = Some(
        initial_output
            .into_iter()
            .chain(outputs[1..recovered].iter().flatten().cloned())
            .collect::<Vec<_>>(),
    );
    let states = rebuilt
        .into_iter()
        .zip(outputs)
        .enumerate()
        .map(|(position, (values, output))| TraceState {
            values,
            printed: match position {
                0 => prefix.take().unwrap_or_default(),
                _ if position < recovered => Vec::new(),
                _ => output,
            },
        })
        .collect();
    Trace {
        states,
        trace_output,
    }
}

fn run<T>(evaluated: Evaluated<T>) -> Result<T, Unsupported> {
    evaluated.map_err(|error| Unsupported(format!("rebuilding a trace: {}", error.0)))
}

// The first state the walk of an action completes that TLC takes for the search's state.
// With `is_exhaustive`, the walk runs to its end, for what it prints.
fn find(
    evaluator: &mut Evaluator<'_>,
    key: &Key,
    (expression, context, is_init): (NodeId, &Context, bool),
    is_exhaustive: bool,
    store: &Store,
    target: &[Id],
) -> Result<Option<Vec<Value>>, Unsupported> {
    let target_view = match key {
        Key::View(view) => {
            let state: Vec<Value> = target.iter().map(|&id| from_store(store, id)).collect();
            Some(run(view_of(evaluator, *view, &state))?)
        }
        Key::ViewOfSymmetry(view, group) => {
            let state: Vec<Value> = target.iter().map(|&id| from_store(store, id)).collect();
            let least = run(least_in_orbit(evaluator.ir, group, &state))?;
            Some(run(view_of(evaluator, *view, &least))?)
        }
        _ => None,
    };
    let mut found = None;
    run(
        evaluator.walk_action(expression, context, is_init, &mut |evaluator| {
            let state: Vec<Value> = if is_init {
                evaluator.current.iter().flatten().cloned().collect()
            } else {
                evaluator.next.iter().flatten().cloned().collect()
            };
            let is_match = match key {
                Key::State => is_same(store, target, &state),
                Key::View(view) => equals(
                    &view_of(evaluator, *view, &state)?,
                    target_view.as_ref().expect("the target's view"),
                )?,
                Key::ViewOfSymmetry(view, group) => {
                    let least = least_in_orbit(evaluator.ir, group, &state)?;
                    equals(
                        &view_of(evaluator, *view, &least)?,
                        target_view.as_ref().expect("the target's view"),
                    )?
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
            if is_match && found.is_none() {
                found = Some(state);
            }
            Ok(is_exhaustive || !is_match)
        }),
    )?;
    Ok(found)
}

// The VIEW of a state, evaluated with the state as the current one.
fn view_of(evaluator: &mut Evaluator<'_>, view: NodeId, state: &[Value]) -> Evaluated<Value> {
    let saved = std::mem::replace(
        &mut evaluator.current,
        state.iter().cloned().map(Some).collect(),
    );
    let value = evaluator.evaluate(view, &Context::default());
    evaluator.current = saved;
    value
}

// The least state of a state's orbit, as `TLCStateMut.fingerPrint` finds it: each permutation's
// values compared with the least so far in TLC's order of the variables.
fn least_in_orbit(
    ir: &Ir,
    group: &[Vec<(Rc<Text>, Rc<Text>)>],
    state: &[Value],
) -> Evaluated<Vec<Value>> {
    let mut least = state.to_vec();
    for permutation in group {
        let permuted = state
            .iter()
            .map(|value| permute(value, permutation))
            .collect::<Evaluated<Vec<_>>>()?;
        for &position in &ir.tlc_order {
            let position = position as usize;
            match compare(&permuted[position], &least[position])? {
                std::cmp::Ordering::Less => {
                    least = permuted;
                    break;
                }
                std::cmp::Ordering::Greater => break,
                std::cmp::Ordering::Equal => {}
            }
        }
    }
    Ok(least)
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
