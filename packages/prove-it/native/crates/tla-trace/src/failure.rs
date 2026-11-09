//! Where the search stopped on an error, evaluated again as TLC's `CallStackTool` evaluates it:
//! TLC's message for the error, and the nested expressions it was in, as `tlc/replay.ts` and the
//! tracing evaluator of `evaluate.ts` record them and `getFailureMessage` and `formatCallStack` in
//! TypeScript print them.

use tla_ir::{AtomKind, NodeId, NodeKind, SourceRange};
use tla_values::{Id, Store};

use crate::eval::{CallStack, Context, Evaluator, StackFrame, UNFOLLOWED_FRAMES};
use crate::fingerprint::fingerprint_failure;
use crate::print::format_value;
use crate::rebuild::{Rebuilder, is_same, run};
use crate::value::{Evaluated, TlcMessage, Value, fail, fail_with, normalize_failure};
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
    /// Evaluating the implied init, a property's initial predicate, at this position of the
    /// model's initial predicates on the initial state the path holds.
    InitialPredicate(u32),
    /// Evaluating the atom at this position of the model's atoms as TLC adds the path's last state
    /// to the behavior graphs: on that state, or, `is_extra`, on a state past the path, the
    /// states' last: a successor's state predicate, or an action on a step to it.
    Atom { atom: u32, is_extra: bool },
    /// Evaluating the atom at this position of the model's atoms as TLC adds the initial state
    /// the path holds to the behavior graphs, before it checks the state.
    InitialAtom(u32),
}

/// Where TLC fails to fingerprint a state: the ranges of the expressions that built the values it
/// fails in, outermost first, and the reason, with and without -tool.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FingerprintFailure {
    pub sources: Vec<SourceRange>,
    pub reason: String,
    pub tool_reason: String,
    /// Whether the ranges are the call stack of TLC's replay with its `CallStackTool`, which
    /// throws the FingerprintException after the run reported the error as it is.
    pub is_replayed: bool,
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
const ASSUMPTION_EVALUATION_FAILED: u32 = 2105;
const INVARIANT_EVALUATION_FAILED: u32 = 2111;
const ASSERT_FAILED: u32 = 2132;
const EXPECTED_VALUE: u32 = 2215;
/// `EC.TLC_INITIAL_STATE`: an error and the initial state TLC was working on.
const INITIAL_STATE: u32 = 2102;

const VIOLATION_ASSUMPTION: i32 = 10;
const VIOLATION_ASSERT: i32 = 14;
const FAILURE_SPEC_EVAL: i32 = 75;
const FAILURE_SAFETY_EVAL: i32 = 76;
const FAILURE_ERROR: i32 = 255;
const ERROR_CONFIG_PARSE: i32 = 151;
/// `EC.TLC_CONFIG_UNDEFINED_OR_NO_OPERATOR`.
const UNDEFINED_IDENTIFIER: u32 = 2280;

const UNEXPECTED_EXCEPTION: &str = "TLC threw an unexpected exception.\nThis was probably caused by an error in the spec or model.\nSee the User Output or TLC Console for clues to what happened.\nThe exception was a java.lang.RuntimeException\n: ";

/// A coded message in -tool output, which TLC marks inside the message that holds it, as it marks
/// the failure of a Java method that one reports (`formatNestedMessage`).
pub(crate) fn nested(message: &TlcMessage) -> String {
    match message.code {
        Some(code) => format!(
            "@!@!@STARTMSG {code}:0 @!@!@\n{}\n@!@!@ENDMSG {code} @!@!@",
            nested_java_failure(&message.text)
        ),
        None => message.text.clone(),
    }
}

const JAVA_METHOD_FAILED: u32 = 2154;
const JAVA_FAILURE: &str = "Attempted to apply the operator overridden by the Java method\n";
const JAVA_FAILURE_INNER: &str = "but it produced the following error:\n";

// The text of a Java method's failure with the failure it reports marked, where that is another
// Java method's.
fn nested_java_failure(text: &str) -> String {
    let inner = text
        .starts_with(JAVA_FAILURE)
        .then(|| text.find(JAVA_FAILURE_INNER))
        .flatten()
        .map(|at| at + JAVA_FAILURE_INNER.len());
    match inner {
        Some(at) if text[at..].starts_with(JAVA_FAILURE) => format!(
            "{}{}",
            &text[..at],
            nested(&TlcMessage {
                text: text[at..].to_owned(),
                code: Some(JAVA_METHOD_FAILED),
                is_eval_exception: false,
            })
        ),
        _ => text.to_owned(),
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
    /// Evaluates again the assumption at `position` of the model's assumptions, which failed to
    /// evaluate as TLC started, after the startup's definitions, and returns TLC's report of it
    /// (`checkAssumptions`), with what it printed before it failed.
    pub fn evaluate_assumption(&mut self, position: u32) -> Result<Failure, Unsupported> {
        let evaluator = self.evaluator();
        let ir = evaluator.ir;
        let Some(&(node, name)) = ir.model.startup.assumptions.get(position as usize) else {
            return Err(Unsupported("an assumption the model doesn't have".into()));
        };
        let width = ir.variables.len();
        evaluator.current = vec![None; width];
        evaluator.next = vec![None; width];
        evaluator.level = 0;
        // The startup printed its definitions and the assumptions before this one already.
        run(evaluator.compute_startup())?;
        evaluator.printed.clear();
        evaluator.call_stack = Some(CallStack::default());
        let result = evaluator.evaluate(node, &Context::default());
        let call_stack = evaluator.call_stack.take().unwrap_or_default();
        let printed = std::mem::take(&mut evaluator.printed);
        let Err(error) = result else {
            return Err(Unsupported(
                "evaluating the assumption again: it didn't fail".into(),
            ));
        };
        if let Some(reason) = call_stack
            .unfollowed
            .filter(|reason| !UNFOLLOWED_FRAMES.contains(reason))
        {
            return Err(Unsupported(format!(
                "evaluating the assumption again: {reason}"
            )));
        }
        let Some(message) = error.message else {
            return Err(Unsupported(format!(
                "evaluating the assumption again: {}",
                error.reason
            )));
        };
        let headline = format!("Evaluating assumption {} failed.", ir.texts[name as usize]);
        Ok(Failure {
            code: ASSUMPTION_EVALUATION_FAILED,
            message: format!("{headline}\n{}", message.text),
            tool_message: format!("{headline}\n{}", nested(&message)),
            call_stack: Vec::new(),
            exit_code: VIOLATION_ASSUMPTION,
            printed,
            fingerprint: None,
            state: None,
        })
    }

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
        // The state an atom reads past the path, which TLC rebuilds no trace to.
        let (states, actions, extra) = match site {
            Site::Atom { is_extra: true, .. } => {
                let (extra, path) = states.split_last().ok_or_else(|| {
                    Unsupported("evaluating the failure again: an atom without a state".into())
                })?;
                let extra: Vec<Option<Value>> = extra
                    .iter()
                    .map(|&id| Some(crate::value::from_store(store, id)))
                    .collect();
                (path, &actions[..path.len().saturating_sub(1)], Some(extra))
            }
            _ => (states, actions, None),
        };
        // A successor that fails an invariant is held as TLC found it, as a violating one is.
        let ending = match site {
            Site::Invariant(_) => Ending::Violation,
            _ => Ending::Kept,
        };
        let is_initial = matches!(
            site,
            Site::InitialConstraint(_) | Site::InitialInvariant(_) | Site::InitialPredicate(_)
        );
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
            Site::InitialConstraint(position)
            | Site::InitialInvariant(position)
            | Site::InitialPredicate(position) => {
                let body = |name: &tla_ir::ConfigName| {
                    name.definition
                        .map(|index| evaluator.definition(ir.definitions[index as usize]).body)
                };
                // TLC checks the constraints, then the invariants, then the implied inits
                // (`DoInitFunctor`), up to the one that failed.
                let (constraint_count, invariant_count, predicate_count) = match site {
                    Site::InitialConstraint(_) => (position as usize + 1, 0, 0),
                    Site::InitialInvariant(_) => {
                        (ir.model.constraints.len(), position as usize + 1, 0)
                    }
                    _ => (
                        ir.model.constraints.len(),
                        ir.model.invariants.len(),
                        position as usize + 1,
                    ),
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
                    .chain(
                        ir.model
                            .initial_predicates
                            .iter()
                            .take(predicate_count)
                            .map(|&predicate| Some(predicate)),
                    )
                    .collect();
                if ir
                    .model
                    .initial_predicate_scopes
                    .iter()
                    .take(predicate_count)
                    .any(Option::is_some)
                {
                    return Err(Unsupported(
                        "evaluating the failure again: an implied init in an instance's scope"
                            .into(),
                    ));
                }
                if predicate_count > ir.model.initial_predicates.len() {
                    return Err(Unsupported(
                        "evaluating the failure again: an implied init the model doesn't have"
                            .into(),
                    ));
                }
                let Some(checks) = checks else {
                    return Err(Unsupported(
                        "evaluating the failure again: a check the model doesn't define".into(),
                    ));
                };
                // TLC evaluates a failing invariant or implied init with its call stack, on the
                // frames of the initial predicate that found the state, and the constraints
                // without it.
                let is_traced = !matches!(site, Site::InitialConstraint(_));
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
                            // A failure computing successors comes from a next-state relation.
                            let next = ir.model.next.expect("a next-state relation");
                            evaluator.split_actions(next, &context, &mut actions)
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
            // TLC evaluates the atom as it adds the state, on the state, the successor whose
            // state predicate it checks, or the step to it.
            Site::Atom { atom, .. } | Site::InitialAtom(atom) => {
                let Some(atom) = ir.model.atoms.get(atom as usize) else {
                    return Err(Unsupported("an atom the model doesn't have".into()));
                };
                evaluator.level = level;
                evaluator.next = vec![None; width];
                evaluator.current = current;
                let context = evaluator.scope_context(atom.scope);
                context.and_then(|context| match &atom.kind {
                    AtomKind::State => {
                        if let Some(extra) = extra {
                            evaluator.current = extra;
                        }
                        evaluator.boolean(atom.expression, &context)
                    }
                    AtomKind::Enabled { .. } => evaluator
                        .enabled(atom.expression, &context)
                        .map(|value| matches!(value, Value::Bool(true))),
                    AtomKind::Action { unchanged, .. } => {
                        if let Some(extra) = extra {
                            evaluator.next = extra;
                        }
                        match unchanged {
                            Some(unchanged) if evaluator.boolean(*unchanged, &context)? => {
                                Ok(false)
                            }
                            _ => evaluator.boolean(atom.expression, &context),
                        }
                    }
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
        // The front writes <<A>>_v of WF_v(A) and SF_v(A) at A, where TLC records no node.
        let mut call_stack = call_stack;
        if let Site::Atom { atom, .. } = site
            && let Some(atom) = ir.model.atoms.get(atom as usize)
            && let NodeKind::AngleAction { action, .. } =
                &ir.nodes.arena[atom.expression as usize].kind
            && ir.nodes.arena[atom.expression as usize].range
                == ir.nodes.arena[*action as usize].range
            && call_stack.frames.first() == Some(&StackFrame::Node(atom.expression))
        {
            call_stack.frames.remove(0);
        }
        let printed = std::mem::take(&mut evaluator.printed);
        let Err(error) = result else {
            return Err(Unsupported(
                "evaluating the failure again: it didn't fail".into(),
            ));
        };
        // TLC fails to fingerprint an initial state that holds a set it can't normalize, then to
        // print the state as it reports that, which escapes as an exception it didn't expect.
        if call_stack.is_unsorted {
            return match call_stack.unprintable {
                Some(message)
                    if site == Site::Init
                        && call_stack.unfollowed.is_none()
                        && printed.is_empty() =>
                {
                    Ok(Failure {
                        code: GENERAL,
                        message: format!("{UNEXPECTED_EXCEPTION}{}", message.text),
                        tool_message: format!("{UNEXPECTED_EXCEPTION}{}", nested(&message)),
                        call_stack: Vec::new(),
                        exit_code: FAILURE_ERROR,
                        printed,
                        fingerprint: None,
                        state: None,
                    })
                }
                _ => Err(Unsupported(
                    "evaluating the failure again: a set TLC leaves unnormalized".into(),
                )),
            };
        }
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
                is_replayed: false,
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
        // A failure in the next states whose receiver the replay gave a source TLC reports as it
        // is, then fails again as a FingerprintException as it replays the expansion with its
        // `CallStackTool`, which gives values their sources, and prints that call stack.
        if call_stack.is_fingerprinted
            && site == Site::Next
            && let Some(message) = &error.message
            && let Some(source) = call_stack.fingerprinted_source
        {
            let (code, text, tool_text) = report(message, true);
            let mut sources = ranges(evaluator, &call_stack);
            if let Some(range) = node_range(evaluator, source)
                && sources.last() != Some(&range)
            {
                sources.push(range);
            }
            return Ok(Failure {
                code,
                message: text,
                tool_message: tool_text,
                call_stack: Vec::new(),
                exit_code: FAILURE_SPEC_EVAL,
                printed,
                fingerprint: Some(FingerprintFailure {
                    sources,
                    reason: message.text.clone(),
                    tool_reason: nested(message),
                    is_replayed: true,
                }),
                state: None,
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
        // TLC reports an error adding an initial state to the behavior graphs with the state, and
        // exits with the error's own status, since its replay of the initial states, which have
        // the state already, doesn't fail again (`ModelChecker#doInit`). An EvalException escapes
        // `doInit` without the state, which isn't ported.
        if let Site::InitialAtom(_) = site {
            if message.is_eval_exception {
                return Err(Unsupported(
                    "evaluating the failure again: an EvalException adding an initial state".into(),
                ));
            }
            let Some(values) = evaluator
                .current
                .iter()
                .cloned()
                .collect::<Option<Vec<Value>>>()
            else {
                return Err(Unsupported(
                    "evaluating the failure again: an initial state the path lacks".into(),
                ));
            };
            return Ok(Failure {
                code: INITIAL_STATE,
                message: message.text.clone(),
                tool_message: nested(&message),
                call_stack: Vec::new(),
                // `EC.ExitStatus.errorConstantToExitStatus` of the error's code: an identifier
                // that is undefined is among the configuration's errors, and the other errors an
                // evaluation raises are general ones.
                exit_code: match message.code {
                    Some(UNDEFINED_IDENTIFIER) => ERROR_CONFIG_PARSE,
                    _ => FAILURE_ERROR,
                },
                printed,
                fingerprint: None,
                state: Some(values.iter().map(format_value).collect()),
            });
        }
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
        // TLC reports an error adding a state to the behavior graphs as one in the next states
        // (`Worker#doNextCheckLiveness`), and exits on an exception it didn't expect as for any.
        let is_atom = matches!(site, Site::Atom { .. });
        let (code, text, tool_text) = report(&message, site == Site::Next || is_atom);
        Ok(Failure {
            code,
            message: text,
            tool_message: tool_text,
            call_stack: ranges(evaluator, &call_stack),
            // A failed assertion in the next states exits as one, and any other error, or any
            // in the initial predicate, as the failure of the replay (`getFailureExitCode`).
            exit_code: match (site, message.code) {
                (Site::Next, Some(ASSERT_FAILED)) => VIOLATION_ASSERT,
                _ if is_atom && !message.is_eval_exception => FAILURE_ERROR,
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
            StackFrame::Node(node) => node_range(evaluator, node),
            StackFrame::Prefix(node, count) => prefix_range(evaluator, node, count),
        };
        ranges.extend(range);
    }
    ranges
}

// A node's range, or for an infix junction the IR keeps none of, SANY's: from its first operand's
// start to its last's end.
fn node_range(evaluator: &Evaluator<'_>, node: NodeId) -> Option<SourceRange> {
    let arena = &evaluator.ir.nodes.arena;
    if let Some(range) = arena[node as usize].range {
        return Some(range);
    }
    let (NodeKind::And(operands) | NodeKind::Or(operands)) = &arena[node as usize].kind else {
        return None;
    };
    // An infix junction has two operands or more; a lone one wraps an expression SANY has no
    // node for.
    if operands.len() < 2 {
        return None;
    }
    // A bulleted list starts at its first bullet, which the IR doesn't hold apart; the IR keeps a
    // junction for each, and for an infix chain of more than two operands.
    if evaluator
        .ir
        .nodes
        .junctions
        .get(&node)
        .is_some_and(|junction| junction.is_bulleted)
    {
        return None;
    }
    let first = node_range(evaluator, *operands.first()?)?;
    let last = node_range(evaluator, *operands.last()?)?;
    Some(SourceRange {
        end_line: last.end_line,
        end_column: last.end_column,
        ..first
    })
}

// The range of SANY's node of the first `count` operands of an infix chain: from the chain's
// start to the end of its last operand there, as `getPrefix` in `tlc/replay.ts` takes it.
fn prefix_range(evaluator: &Evaluator<'_>, node: NodeId, count: usize) -> Option<SourceRange> {
    let range = node_range(evaluator, node)?;
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
        let Some(next) = ir.model.next else {
            return Err(Unsupported(
                "a successor of a model without a next-state relation".into(),
            ));
        };
        let candidates: Vec<(NodeId, Option<u32>, Option<u32>)> = if ir.model.actions.is_empty() {
            vec![(next, ir.model.scope, None)]
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
        if let Some(stack) = &mut self.call_stack
            && stack.is_unsorted
            && state.iter().flatten().any(contains_unsorted)
        {
            // TLC prints the state's variables in order, and a set it can't normalize fails as it
            // prints it; the replay doesn't follow one inside another value.
            let is_followed = is_init
                && state
                    .iter()
                    .flatten()
                    .all(|value| matches!(value, Value::Unsorted(_)) || !contains_unsorted(value));
            stack.unprintable = state
                .iter()
                .flatten()
                .find_map(|value| match value {
                    Value::Unsorted(elements) if is_followed => normalize_failure(elements),
                    _ => None,
                })
                .and_then(|error| error.message);
            return fail("a state TLC fails to fingerprint and print");
        }
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

// Whether a value holds a set TLC can't normalize, or may: the replay doesn't look into a lazy set.
fn contains_unsorted(value: &Value) -> bool {
    match value {
        Value::Unsorted(_) | Value::Lazy(_) => true,
        Value::Set(elements) => elements.iter().any(contains_unsorted),
        Value::Function(function) => function
            .domain
            .iter()
            .chain(&function.range)
            .any(contains_unsorted),
        _ => false,
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn marks_each_java_failure_that_one_reports_under_tool() {
        let method = "public static tlc2.value.impl.Value tlc2.module.TLCEval.tlcEval()";
        let inner =
            format!("{JAVA_FAILURE}{method},\n{JAVA_FAILURE_INNER}Attempted to enumerate STRING.");
        let outer = TlcMessage {
            text: format!("{JAVA_FAILURE}{method},\n{JAVA_FAILURE_INNER}{inner}"),
            code: Some(JAVA_METHOD_FAILED),
            is_eval_exception: false,
        };
        assert_eq!(
            nested(&outer),
            format!(
                "@!@!@STARTMSG 2154:0 @!@!@\n{JAVA_FAILURE}{method},\n{JAVA_FAILURE_INNER}@!@!@STARTMSG 2154:0 @!@!@\n{inner}\n@!@!@ENDMSG 2154 @!@!@\n@!@!@ENDMSG 2154 @!@!@"
            )
        );
    }
}
