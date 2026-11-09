//! Where the search stopped on an error, evaluated again as TLC's `CallStackTool` evaluates it:
//! TLC's message for the error, and the nested expressions it was in, as `tlc/replay.ts` and the
//! tracing evaluator of `evaluate.ts` record them and `getFailureMessage` and `formatCallStack` in
//! TypeScript print them.

use tla_ir::{NodeId, NodeKind, SourceRange};
use tla_values::{Id, Store};

use crate::eval::{CallStack, Context, Evaluator, StackFrame};
use crate::fingerprint::fingerprint_failure;
use crate::print::format_value;
use crate::rebuild::{Rebuilder, is_same, run};
use crate::value::{Evaluated, TlcMessage, Value, fail, fail_with};
use crate::{Ending, Trace, Unsupported};

/// Where the search failed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Site {
    /// Computing the initial states.
    Init,
    /// Computing the successors of the path's last state.
    Next,
    /// Evaluating the invariant at this position of the model's invariants on the path's last
    /// state, a successor that failed it, past the initial states.
    Invariant(u32),
    /// Evaluating the constraint at this position of the model's constraints on the initial state
    /// the path holds.
    InitialConstraint(u32),
    /// Evaluating the invariant at this position of the model's invariants on the initial state
    /// the path holds.
    InitialInvariant(u32),
}

/// Where TLC fails to fingerprint a state: the ranges of the expressions that built the values it
/// fails in, outermost first, and the reason, with and without -tool.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FingerprintFailure {
    pub sources: Vec<SourceRange>,
    pub reason: String,
    pub tool_reason: String,
}

/// TLC's report of an error: the code of the message, its text and its text in -tool output, and
/// the nested expressions it was evaluating, which TLC prints as message 2103 where there are any.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Failure {
    pub code: u32,
    pub message: String,
    pub tool_message: String,
    pub call_stack: Vec<SourceRange>,
    /// The status TLC exits with (`EC.ExitStatus.errorConstantToExitStatus`).
    pub exit_code: i32,
    /// What the spec printed as TLC replayed the failure, each print's values as `Trace` holds
    /// them.
    pub printed: Vec<Vec<String>>,
    /// Where a state the replay found fails to fingerprint, which TLC reports in place of the
    /// call stack: the ranges of the expressions that built the values it fails in, outermost
    /// first.
    pub fingerprint: Option<FingerprintFailure>,
    /// The initial state TLC was working on, where it failed to fingerprint one: each variable's
    /// value as TLC prints it, in the IR's order of the variables.
    pub state: Option<Vec<String>>,
}

const GENERAL: u32 = 1000;
const INVARIANT_EVALUATION_FAILED: u32 = 2111;
const ASSERT_FAILED: u32 = 2132;
const EXPECTED_VALUE: u32 = 2215;
/// `EC.TLC_INITIAL_STATE`: an error and the initial state TLC was working on.
const INITIAL_STATE: u32 = 2102;

const VIOLATION_ASSERT: i32 = 14;
const FAILURE_SPEC_EVAL: i32 = 75;
const FAILURE_SAFETY_EVAL: i32 = 76;

const UNEXPECTED_EXCEPTION: &str = "TLC threw an unexpected exception.\nThis was probably caused by an error in the spec or model.\nSee the User Output or TLC Console for clues to what happened.\nThe exception was a java.lang.RuntimeException\n: ";

// A coded message in -tool output, which TLC marks inside the message that holds it.
fn nested(message: &TlcMessage) -> String {
    match message.code {
        Some(code) => format!(
            "@!@!@STARTMSG {code}:0 @!@!@\n{}\n@!@!@ENDMSG {code} @!@!@",
            message.text
        ),
        None => message.text.clone(),
    }
}

// `getFailureMessage`: an EvalException that escapes the computation of the next states keeps its
// own code; any other error there is an unexpected exception.
fn report(message: &TlcMessage, is_next_state: bool) -> (u32, String, String) {
    if is_next_state && message.is_eval_exception {
        let code = message.code.unwrap_or(GENERAL);
        return (code, message.text.clone(), message.text.clone());
    }
    let prefix = if is_next_state {
        UNEXPECTED_EXCEPTION
    } else {
        ""
    };
    (
        GENERAL,
        format!("{prefix}{}", message.text),
        format!("{prefix}{}", nested(message)),
    )
}

impl<'ir> Rebuilder<'ir> {
    /// Evaluates again where the search failed, at `site`, after the path `states` (as for
    /// `rebuild`; none for the initial predicate), and returns TLC's report of the error.
    /// `Unsupported` where the evaluator doesn't give TLC's message for the error, or where the
    /// evaluation doesn't fail again.
    pub fn evaluate_failure(
        &mut self,
        store: &Store,
        states: &[&[Id]],
        actions: &[Option<u32>],
        site: Site,
    ) -> Result<Failure, Unsupported> {
        // TLC 1.7.4 streams the lazy bounds of a quantifier rather than enumerating them in order,
        // and words some messages apart, neither of which is ported.
        if self.evaluator().is_174() {
            return Err(Unsupported(
                "evaluating the failure again: TLC 1.7.4".into(),
            ));
        }
        // TLC reports an invariant that fails on an initial state otherwise, which isn't ported.
        if matches!(site, Site::Invariant(_)) && states.len() < 2 {
            return Err(Unsupported(
                "evaluating the failure again: an invariant of an initial state".into(),
            ));
        }
        // A successor that fails an invariant is held as TLC found it, as a violating one is.
        let ending = match site {
            Site::Invariant(_) => Ending::Violation,
            _ => Ending::Kept,
        };
        let is_initial = matches!(site, Site::InitialConstraint(_) | Site::InitialInvariant(_));
        if is_initial && states.len() != 1 {
            return Err(Unsupported(
                "evaluating the failure again: an initial state's check past the initial states"
                    .into(),
            ));
        }
        let last = match states {
            _ if is_initial => None,
            [] => None,
            _ => Some(
                self.rebuild_checked(store, states, actions, ending, false)?
                    .states,
            ),
        };
        let evaluator = self.evaluator();
        let ir = evaluator.ir;
        evaluator.printed.clear();
        evaluator.call_stack = Some(CallStack::default());
        let width = ir.variables.len();
        let level = states.len() as i32;
        let current: Vec<Option<_>> = last
            .and_then(|states| states.last().map(|state| state.values.clone()))
            .map(|values| values.into_iter().map(Some).collect())
            .unwrap_or_else(|| vec![None; width]);
        // The initial state TLC failed to check, as the replay found it.
        let mut checked: Option<Vec<Value>> = None;
        let result = match site {
            Site::InitialConstraint(position) | Site::InitialInvariant(position) => {
                let body = |name: &tla_ir::ConfigName| {
                    name.definition
                        .map(|index| evaluator.definition(ir.definitions[index as usize]).body)
                };
                // TLC checks the constraints, then the invariants (`DoInitFunctor`), up to the one
                // that failed.
                let (constraint_count, invariant_count) = match site {
                    Site::InitialConstraint(_) => (position as usize + 1, 0),
                    _ => (ir.model.constraints.len(), position as usize + 1),
                };
                let checks: Option<Vec<NodeId>> = ir
                    .model
                    .constraints
                    .iter()
                    .take(constraint_count)
                    .map(body)
                    .chain(
                        ir.model
                            .invariants
                            .iter()
                            .take(invariant_count)
                            .map(|invariant| body(&invariant.root)),
                    )
                    .collect();
                let Some(checks) = checks else {
                    return Err(Unsupported(
                        "evaluating the failure again: a check the model doesn't define".into(),
                    ));
                };
                // TLC evaluates a failing invariant with its call stack, on the frames of the
                // initial predicate that found the state, and the constraints without it.
                let is_traced = matches!(site, Site::InitialInvariant(_));
                let target = states[0];
                evaluator.current = vec![None; width];
                evaluator.level = 0;
                let context = evaluator.scope_context(ir.model.scope);
                context.and_then(|context| {
                    evaluator.walk_action(ir.model.init, &context, true, &mut |evaluator| {
                        let values: Option<Vec<Value>> =
                            evaluator.current.iter().cloned().collect();
                        let Some(values) = values.filter(|values| is_same(store, target, values))
                        else {
                            return Ok(true);
                        };
                        checked = Some(values);
                        evaluator.level = 1;
                        let call_stack = evaluator.call_stack.take();
                        let (failed, earlier) = checks.split_last().expect("a check");
                        for (position, &body) in earlier.iter().enumerate() {
                            let holds = if position < constraint_count {
                                constraint_holds(evaluator, body)
                            } else {
                                evaluator.boolean(body, &Context::default())
                            };
                            if !matches!(holds, Ok(true)) {
                                evaluator.call_stack = call_stack;
                                return holds;
                            }
                        }
                        if is_traced {
                            evaluator.call_stack = call_stack;
                            return evaluator.boolean(*failed, &Context::default());
                        }
                        let holds = constraint_holds(evaluator, *failed);
                        evaluator.call_stack = call_stack;
                        holds
                    })
                })
            }
            Site::Init => {
                evaluator.current = vec![None; width];
                evaluator.level = 0;
                let context = evaluator.scope_context(ir.model.scope);
                context.and_then(|context| {
                    evaluator.walk_action(ir.model.init, &context, true, &mut |evaluator| {
                        evaluator.fingerprint_found(true)
                    })
                })
            }
            Site::Next => {
                // TLC's actions: the IR's, or, where it has none, the next-state relation split
                // as TLC splits it.
                let actions = if ir.model.actions.is_empty() {
                    // TLC splits the relation at startup, without a state and outside the call
                    // stack, as `getActions` does.
                    evaluator.current = vec![None; width];
                    evaluator.next = vec![None; width];
                    let call_stack = evaluator.call_stack.take();
                    let mut actions = Vec::new();
                    let split = evaluator
                        .scope_context(ir.model.scope)
                        .and_then(|context| {
                            evaluator.split_actions(ir.model.next, &context, &mut actions)
                        })
                        .map(|()| actions);
                    evaluator.call_stack = call_stack;
                    split
                } else {
                    ir.model
                        .actions
                        .iter()
                        .map(|action| {
                            evaluator
                                .scope_context(action.scope)
                                .map(|context| (action.expression, context))
                        })
                        .collect()
                };
                evaluator.current = current;
                evaluator.level = level;
                actions.and_then(|actions| {
                    actions
                        .into_iter()
                        .try_for_each(|(expression, context)| {
                            evaluator.next = vec![None; width];
                            evaluator
                                .walk_action(expression, &context, false, &mut |evaluator| {
                                    evaluator.fingerprint_found(false)
                                })
                                .map(|_| ())
                        })
                        .map(|()| true)
                })
            }
            Site::Invariant(position) => {
                evaluator.current = current;
                evaluator.level = level;
                let mut bodies = Vec::new();
                for invariant in ir.model.invariants.iter().take(position as usize + 1) {
                    let Some(index) = invariant.root.definition else {
                        return Err(Unsupported("an invariant the model doesn't define".into()));
                    };
                    bodies.push(evaluator.definition(ir.definitions[index as usize]).body);
                }
                let Some(failed) = bodies.pop().filter(|_| bodies.len() == position as usize)
                else {
                    return Err(Unsupported("an invariant the model doesn't have".into()));
                };
                // TLC checks the invariants before it in order, outside the call stack, and their
                // comparisons sort what they reach of the state.
                let call_stack = evaluator.call_stack.take();
                for body in bodies {
                    if !run(evaluator.boolean(body, &Context::default()))? {
                        return Err(Unsupported(
                            "evaluating the failure again: an earlier invariant is violated".into(),
                        ));
                    }
                }
                evaluator.call_stack = call_stack;
                evaluator.boolean(failed, &Context::default())
            }
        };
        let call_stack = evaluator.call_stack.take().unwrap_or_default();
        let printed = std::mem::take(&mut evaluator.printed);
        let Err(error) = result else {
            return Err(Unsupported(
                "evaluating the failure again: it didn't fail".into(),
            ));
        };
        if let Some(reason) = call_stack.unfollowed {
            return Err(Unsupported(format!(
                "evaluating the failure again: {reason}"
            )));
        }
        if let Some((sources, state)) = call_stack.fingerprint {
            let Some(message) = error.message else {
                return Err(Unsupported(format!(
                    "evaluating the failure again: {}",
                    error.reason
                )));
            };
            let fingerprint = FingerprintFailure {
                sources: sources
                    .into_iter()
                    .filter_map(|node| ir.nodes.arena[node as usize].range)
                    .collect(),
                reason: message.text.clone(),
                tool_reason: nested(&message),
            };
            // TLC reports a state it fails to fingerprint as it works on an initial state, or as
            // an exception it didn't expect in the next states, and exits as for the replay.
            let (code, text, tool_text, state) = match site {
                Site::Init => (
                    INITIAL_STATE,
                    message.text.clone(),
                    nested(&message),
                    Some(state),
                ),
                _ => {
                    let (code, text, tool_text) = report(&message, true);
                    (code, text, tool_text, None)
                }
            };
            return Ok(Failure {
                code,
                message: text,
                tool_message: tool_text,
                call_stack: Vec::new(),
                exit_code: FAILURE_SPEC_EVAL,
                printed,
                fingerprint: Some(fingerprint),
                state,
            });
        }
        if call_stack.is_fingerprinted {
            return Err(Unsupported(
                "evaluating the failure again: a failure TLC reports as a FingerprintException"
                    .into(),
            ));
        }
        let Some(message) = error.message else {
            return Err(Unsupported(format!(
                "evaluating the failure again: {}",
                error.reason
            )));
        };
        // TLC reports a check of an initial state that fails with the state, where the failure
        // reaches it as a TLCRuntimeException, but an EvalException escapes `doInit` without it.
        if is_initial {
            let Some(values) = checked else {
                return Err(Unsupported(
                    "evaluating the failure again: an initial state the replay didn't find".into(),
                ));
            };
            let state = (!message.is_eval_exception)
                .then(|| values.iter().map(format_value).collect::<Vec<_>>());
            return Ok(Failure {
                code: if state.is_some() {
                    INITIAL_STATE
                } else {
                    GENERAL
                },
                message: message.text.clone(),
                tool_message: nested(&message),
                call_stack: ranges(evaluator, &call_stack),
                exit_code: FAILURE_SPEC_EVAL,
                printed,
                fingerprint: None,
                state,
            });
        }
        // TLC reports an invariant that fails to evaluate with a headline of its own, and no call
        // stack (`doNextEvalFailed`).
        if let Site::Invariant(position) = site {
            let name = &ir.texts[ir.model.invariants[position as usize].root.name as usize];
            let headline = format!("Evaluating invariant {name} failed.");
            return Ok(Failure {
                code: INVARIANT_EVALUATION_FAILED,
                message: format!("{headline}\n{}", message.text),
                tool_message: format!("{headline}\n{}", nested(&message)),
                call_stack: Vec::new(),
                exit_code: FAILURE_SAFETY_EVAL,
                printed,
                fingerprint: None,
                state: None,
            });
        }
        let (code, text, tool_text) = report(&message, site == Site::Next);
        Ok(Failure {
            code,
            message: text,
            tool_message: tool_text,
            call_stack: ranges(evaluator, &call_stack),
            // A failed assertion in the next states exits as one, and any other error, or any
            // in the initial predicate, as the failure of the replay (`getFailureExitCode`).
            exit_code: match (site, message.code) {
                (Site::Next, Some(ASSERT_FAILED)) => VIOLATION_ASSERT,
                _ => FAILURE_SPEC_EVAL,
            },
            printed,
            fingerprint: None,
            state: None,
        })
    }
}

// The ranges of the call stack's nodes, as `CallStack.toString` prints them: a node TLC evaluates
// again right inside itself once, and nothing for a node without a range.
fn ranges(evaluator: &Evaluator<'_>, call_stack: &CallStack) -> Vec<SourceRange> {
    let mut ranges = Vec::new();
    let mut previous = None;
    for &frame in &call_stack.frames {
        if previous == Some(frame) {
            continue;
        }
        previous = Some(frame);
        let range = match frame {
            StackFrame::Node(node) => evaluator.ir.nodes.arena[node as usize].range,
            StackFrame::Prefix(node, count) => prefix_range(evaluator, node, count),
        };
        ranges.extend(range);
    }
    ranges
}

// The range of SANY's node of the first `count` operands of an infix chain: from the chain's
// start to the end of its last operand there, as `getPrefix` in `tlc/replay.ts` takes it.
fn prefix_range(evaluator: &Evaluator<'_>, node: NodeId, count: usize) -> Option<SourceRange> {
    let range = evaluator.ir.nodes.arena[node as usize].range?;
    let junction = evaluator.ir.nodes.junctions.get(&node)?;
    let &(end_line, end_column) = junction.prefix_ends.get(count.checked_sub(2)?)?;
    debug_assert!(matches!(
        evaluator.ir.nodes.arena[node as usize].kind,
        NodeKind::And(_) | NodeKind::Or(_)
    ));
    Some(SourceRange {
        end_line,
        end_column,
        ..range
    })
}

/// TLC's `CallStack.toString`, with the line it ends with.
pub fn format_call_stack(ir: &tla_ir::Ir, call_stack: &[SourceRange]) -> String {
    if call_stack.is_empty() {
        return "    The error call stack is empty.\n".to_string();
    }
    let mut text = String::new();
    for (position, range) in call_stack.iter().enumerate() {
        text.push_str(&format!(
            "{position}. Line {}, column {} to line {}, column {} in {}\n",
            range.start_line,
            range.start_column,
            range.end_line,
            range.end_column,
            ir.texts[range.module as usize]
        ));
    }
    text.push('\n');
    text
}

/// The successor TLC finds incomplete as it expands the last state of a trace: the action that
/// left it so (its position in the model's actions, `None` where the IR carries none), the
/// variables it leaves undefined in the order declared, and its values.
pub struct Incomplete {
    pub action: Option<u32>,
    pub missing: Vec<usize>,
    pub partial: Vec<Option<Value>>,
}

impl Rebuilder<'_> {
    /// The first successor of the last of `states` that the next-state relation leaves
    /// incomplete, walking TLC's actions in order, as `forEachSuccessor` finds it.
    pub fn incomplete_successor(&mut self, trace: &Trace) -> Result<Incomplete, Unsupported> {
        let evaluator = self.evaluator();
        let ir = evaluator.ir;
        let width = ir.variables.len();
        let Some(last) = trace.states.last() else {
            return Err(Unsupported("an incomplete successor of no state".into()));
        };
        evaluator.current = last.values.iter().cloned().map(Some).collect();
        evaluator.level = trace.states.len() as i32;
        evaluator.printed.clear();
        let candidates: Vec<(NodeId, Option<u32>, Option<u32>)> = if ir.model.actions.is_empty() {
            vec![(ir.model.next, ir.model.scope, None)]
        } else {
            ir.model
                .actions
                .iter()
                .enumerate()
                .map(|(index, action)| (action.expression, action.scope, Some(index as u32)))
                .collect()
        };
        for (expression, scope, action) in candidates {
            let context = run(evaluator.scope_context(scope))?;
            evaluator.next = vec![None; width];
            let mut found = None;
            run(
                evaluator.walk(expression, &context, false, &mut |evaluator| {
                    if evaluator.next.iter().all(Option::is_some) {
                        return Ok(true);
                    }
                    found = Some(evaluator.next.clone());
                    Ok(false)
                }),
            )?;
            // What the spec prints as TLC finds the successor comes before the report.
            if !evaluator.printed.is_empty() {
                evaluator.printed.clear();
                return Err(Unsupported(
                    "an incomplete successor of a spec that prints".into(),
                ));
            }
            if let Some(partial) = found {
                let missing = (0..width)
                    .filter(|&index| partial[index].is_none())
                    .collect();
                return Ok(Incomplete {
                    action,
                    missing,
                    partial,
                });
            }
        }
        Err(Unsupported("no successor is incomplete".into()))
    }
}

impl Evaluator<'_> {
    // TLC fingerprints each state its replay finds (`fingerprintReplayed`), outside any
    // evaluation: where that fails, the failure is the FingerprintException of the values it
    // fails in. A state whose fingerprint the evaluator can't tell stops the replay.
    fn fingerprint_found(&mut self, is_init: bool) -> Evaluated<bool> {
        let ir = self.ir;
        let state = if is_init { &self.current } else { &self.next };
        for &position in &ir.tlc_order {
            let Some(value) = &state[position as usize] else {
                continue;
            };
            let failure = fingerprint_failure(value);
            let Some(stack) = &mut self.call_stack else {
                return Ok(true);
            };
            match failure {
                Ok(None) => {}
                Ok(Some((chain, message))) => {
                    let sources: Vec<_> = chain
                        .iter()
                        .filter_map(|value| stack.source(value))
                        .collect();
                    if sources.is_empty() {
                        stack
                            .unfollowed
                            .get_or_insert("a fingerprint of values without sources");
                    } else {
                        let texts = state
                            .iter()
                            .map(|value| value.as_ref().map(format_value).unwrap_or_default())
                            .collect();
                        stack.frames.clear();
                        stack.is_frozen = true;
                        stack.fingerprint = Some((sources, texts));
                    }
                    return fail_with("a state TLC fails to fingerprint", message);
                }
                Err(()) => {
                    stack
                        .unfollowed
                        .get_or_insert("a state whose fingerprint the replay doesn't follow");
                    return fail("a state whose fingerprint the replay doesn't follow");
                }
            }
        }
        Ok(true)
    }
}

// Whether a state satisfies a constraint, which TLC fails where it isn't a boolean (`isInModel`).
fn constraint_holds(evaluator: &mut Evaluator<'_>, body: NodeId) -> Evaluated<bool> {
    match evaluator.evaluate(body, &Context::default())? {
        Value::Bool(holds) => Ok(holds),
        _ if evaluator.ir.nodes.arena[body as usize].range.is_some() => fail_with(
            "a constraint that isn't a boolean",
            TlcMessage {
                text: format!(
                    "TLC expected a boolean value, but did not find one. {}",
                    evaluator.describe_range(body)
                ),
                code: Some(EXPECTED_VALUE),
                is_eval_exception: false,
            },
        ),
        _ => fail("a constraint that isn't a boolean, without a range"),
    }
}
