//! Where the search stopped on an error, evaluated again as TLC's `CallStackTool` evaluates it:
//! TLC's message for the error, and the nested expressions it was in, as `tlc/replay.ts` and the
//! tracing evaluator of `evaluate.ts` record them and `getFailureMessage` and `formatCallStack` in
//! TypeScript print them.

use tla_ir::{AtomKind, DefinitionForm, NodeId, NodeKind, SourceRange, TextId};
use tla_values::fingerprint::{Fingerprints, Polynomial};
use tla_values::{Id, Store};

use crate::eval::{
    CallStack, Context, Demand, Evaluator, SUBSTITUTED_FRAMES, StackFrame, UNFOLLOWED_FRAMES,
};
use crate::fingerprint::{fingerprint_failure, state_fingerprint};
use crate::print::format_value;
use crate::rebuild::{Rebuilder, is_in_model, is_same, run};
use crate::value::{
    EvalError, Evaluated, Lazy, RuntimeException, TlcMessage, Value, clear_unnormalized, fail,
    fail_with, normalize_failure, settle,
};
use crate::{Ending, Trace, Unsupported};

/// `EC.TLC_LIVE_STATE_PREDICATE_NON_BOOL` and `EC.TLC_LIVE_ENCOUNTERED_NONBOOL_PREDICATE`.
const LIVE_STATE_PREDICATE_NON_BOOL: u32 = 2250;
const LIVE_ACTION_PREDICATE_NON_BOOL: u32 = 2252;

// `Assert.fail` of a liveness atom's value that isn't a boolean, after its evaluation is over, so
// with no call stack: a TLCRuntimeException.
fn live_non_boolean<T>(code: u32) -> Evaluated<T> {
    let text = if code == LIVE_STATE_PREDICATE_NON_BOOL {
        "A state predicate was evaluated to a non-boolean value."
    } else {
        "Encountered an action predicate that's not a boolean."
    };
    fail_with(
        "a liveness atom that isn't a boolean",
        TlcMessage {
            text: text.to_owned(),
            code: Some(code),
            is_eval_exception: false,
            inner: None,
        },
    )
}

// `LNStateAST.eval`: the state predicate's value, which fails where it isn't a boolean.
fn live_state_predicate(
    evaluator: &mut Evaluator<'_>,
    node: NodeId,
    context: &Context,
) -> Evaluated<bool> {
    match evaluator.evaluate(node, context)? {
        Value::Bool(boolean) => Ok(boolean),
        _ => live_non_boolean(LIVE_STATE_PREDICATE_NON_BOOL),
    }
}

// `LNAction.eval`: the action's value, which fails where it isn't a boolean. Of `<<A>>_v`, whose
// action the evaluator asks first, TLC asks the subscript first, and holds a step that leaves it
// unchanged false whatever A's value.
fn live_action(evaluator: &mut Evaluator<'_>, node: NodeId, context: &Context) -> Evaluated<bool> {
    let NodeKind::AngleAction { action, subscript } = evaluator.ir.nodes.arena[node as usize].kind
    else {
        return match evaluator.evaluate(node, context)? {
            Value::Bool(boolean) => Ok(boolean),
            _ => live_non_boolean(LIVE_ACTION_PREDICATE_NON_BOOL),
        };
    };
    match evaluator.evaluate(action, context)? {
        Value::Bool(false) => Ok(false),
        Value::Bool(true) => Ok(!matches!(
            evaluator.unchanged(subscript, context)?,
            Value::Bool(true)
        )),
        _ => match evaluator.unchanged(subscript, context)? {
            Value::Bool(true) => Ok(false),
            _ => live_non_boolean(LIVE_ACTION_PREDICATE_NON_BOOL),
        },
    }
}

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
    /// Evaluating the action constraint at this position of the model's action constraints on the
    /// path's last step, to a successor that failed it, which the path holds as TLC found it.
    ActionConstraint(u32),
    /// Evaluating the constraint at this position of the model's constraints on the path's last
    /// state, a successor that failed it, which the path holds as TLC found it.
    Constraint(u32),
    /// Evaluating the action property at this position of the model's action properties on the
    /// path's last step, to a successor that failed it, which the path holds as TLC found it.
    ActionProperty(u32),
    /// Evaluating the constraint at this position of the model's constraints on the initial state
    /// the path holds.
    InitialConstraint(u32),
    /// Evaluating the VIEW as TLC fingerprints the initial state the path holds, once the
    /// constraints held of it.
    InitialView,
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
    /// the path holds first to the behavior graphs, before it checks the state. `replayed` is the
    /// atom that fails as TLC's replay of the initial states adds the path's second state.
    InitialAtom { atom: u32, replayed: Option<u32> },
    /// Computing the successors of the path's last state, after which TLC fails evaluating the
    /// atom at this position of the model's atoms as it adds the state to the behavior graphs,
    /// on the states `Atom` says: TLC reports the next-state relation's error and the trace, then
    /// the atom's call stack.
    NextAtom { atom: u32, is_extra: bool },
    /// Evaluating the atom at this position of the model's atoms as TLC adds the path's last
    /// state, deadlocked, to the behavior graphs, on the states `Atom` says, the stuttering step's
    /// second the state again: TLC has reported the deadlock and the trace, and prints the call
    /// stack of its rerun with its `CallStackTool`, or nothing where that rerun throws a
    /// FingerprintException, which its worker doesn't catch there.
    DeadlockAtom { atom: u32, is_extra: bool },
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
    /// Whether TLC skips the successor as it looks for it again to print the trace
    /// (`Tool.getState(TLCState, TLCState)` catches a `TLCRuntimeException` that `Assert.fail`
    /// raised with a text alone and goes on), so that it has no state to print it with.
    pub is_skipped_again: bool,
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
    /// them: of an assumption, from the first assumption on.
    pub printed: Vec<crate::OutputEvent>,
    /// Where a state the replay found fails to fingerprint, which TLC reports in place of the
    /// call stack: the ranges of the expressions that built the values it fails in, outermost
    /// first.
    pub fingerprint: Option<FingerprintFailure>,
    /// The initial state TLC was working on, where it failed to fingerprint one: each variable's
    /// value as TLC prints it, in the IR's order of the variables.
    pub state: Option<Vec<String>>,
    /// What TLC's replay of the expansion did after an invariant failed to evaluate.
    pub replay: Replay,
}

/// TLC's replay of an expansion after an invariant failed to evaluate
/// (`doNext(cTool, predErrState)`), which goes on past the successor that failed, and what its
/// worker generated before the next-state relation failed.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Replay {
    /// Whether TLC's worker generated a successor of the state it was expanding before the
    /// next-state relation failed: it then doesn't check the state for deadlock, nor the
    /// postconditions on the trace it rebuilds for them (`Worker.run`).
    pub is_successor_generated: bool,
    /// The successors the replay found that TLC's set of fingerprints lacked, which it adds to
    /// the count of distinct states.
    pub found: u64,
    /// Those of them that passed TLC's checks, which it adds to its queue.
    pub queued: u64,
    /// Whether the replay failed in turn, with the call stack or the FingerprintException the
    /// failure holds: TLC then leaves the state graph's out-degrees out.
    pub is_failed: bool,
    /// The initial states TLC's replay of the initial states generated, where it went on past
    /// one it failed to fingerprint as a FingerprintException, which it counts as generated.
    pub initial_states: Option<u64>,
}

/// The error TLC's simulator meets evaluating the model (`Simulator.simulate`,
/// `SimulationWorker`), which it reports otherwise than the model checker: as the exception it
/// is, without a call stack, since it evaluates with `Tool` and replays nothing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SimulatedFailure {
    /// The code of TLC's message, where it is one of `tlc2.output.MP`'s.
    pub code: Option<u32>,
    /// The message as the exception's `getMessage` gives it, and in -tool output, where TLC marks
    /// a coded message.
    pub text: String,
    pub tool_text: String,
    /// The text of a coded message with the messages it holds marked, which TLC prints at its own
    /// code: in -tool output, `tool_text` without its own marks.
    pub body_tool_text: String,
    /// The class `MP.ECGeneralMsg` names, which shows a TLCRuntimeException as its parent class.
    pub class_name: &'static str,
    /// Whether TLC throws it as a TLCRuntimeException (`Assert.fail`), which the simulator reports
    /// as it is (`MP.printTLCRuntimeException`): at its code where it has one, and otherwise as an
    /// exception TLC didn't expect, without the summary either way.
    pub is_tlc_runtime: bool,
}

/// `EC.TLC_INVARIANT_EVALUATION_FAILED` and `EC.TLC_ACTION_PROPERTY_EVALUATION_FAILED`, which
/// the simulator reports a failing invariant or action property with, as the model checker does.
pub const SIMULATED_INVARIANT_FAILED: u32 = 2111;
pub const SIMULATED_ACTION_PROPERTY_FAILED: u32 = 2113;

const GENERAL: u32 = 1000;
const ASSUMPTION_EVALUATION_FAILED: u32 = 2105;
/// `EC.TLC_ASSUMPTION_FALSE`.
const ASSUMPTION_FALSE: u32 = 2104;
const INVARIANT_EVALUATION_FAILED: u32 = 2111;
const ACTION_PROPERTY_EVALUATION_FAILED: u32 = 2113;
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

fn unexpected_exception(exception: RuntimeException) -> String {
    format!(
        "TLC threw an unexpected exception.\nThis was probably caused by an error in the spec or model.\nSee the User Output or TLC Console for clues to what happened.\nThe exception was a {}\n: ",
        exception.class_name()
    )
}

/// A coded message in -tool output, which TLC marks inside the message that holds it, as it marks
/// the failure of a Java method that one reports (`formatNestedMessage`).
pub(crate) fn nested(message: &TlcMessage) -> String {
    let Some(code) = message.code else {
        return message.text.clone();
    };
    let text = nested_body(message);
    format!("@!@!@STARTMSG {code}:0 @!@!@\n{text}\n@!@!@ENDMSG {code} @!@!@")
}

// The text of a coded message, with the messages it holds marked as -tool output marks them.
fn nested_body(message: &TlcMessage) -> String {
    match &message.inner {
        Some(inner) if message.text.ends_with(&inner.text) => format!(
            "{}{}",
            &message.text[..message.text.len() - inner.text.len()],
            nested(inner)
        ),
        _ => nested_java_failure(&message.text),
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
                inner: None,
            })
        ),
        _ => text.to_owned(),
    }
}

// `getFailureMessage`: an EvalException that escapes the computation of the next states keeps its
// own code; any other error there is an unexpected exception.
fn report(
    message: &TlcMessage,
    is_next_state: bool,
    runtime_exception: RuntimeException,
) -> (u32, String, String) {
    if is_next_state && message.is_eval_exception {
        let code = message.code.unwrap_or(GENERAL);
        return (code, message.text.clone(), message.text.clone());
    }
    let prefix = if is_next_state {
        unexpected_exception(runtime_exception)
    } else {
        String::new()
    };
    (
        GENERAL,
        format!("{prefix}{}", message.text),
        format!("{prefix}{}", nested(message)),
    )
}

/// What TLC has made as it computed the startup's first definitions
/// (`Rebuilder::compute_startup_until`).
pub struct StartupUntil {
    /// Its prints.
    pub prints: usize,
    /// Its warnings.
    pub warnings: usize,
    /// Its writes of a register.
    pub writes: usize,
    /// The state it leaves TLC's generator in.
    pub random: u64,
    /// Whether it computed the last of them, which it keeps, rather than failed on it.
    pub is_last_computed: bool,
}

/// An assumption as TLC checks it, where the engine checked those before it.
pub struct Assumption {
    /// Whether it holds, or `None` where it fails to evaluate with a message of TLC's, which
    /// `evaluate_assumption` reports.
    pub holds: Option<bool>,
    /// What the assumptions before it printed, each print's values as `Trace` holds them.
    pub printed_before: Vec<crate::OutputEvent>,
    /// What it printed.
    pub printed: Vec<crate::OutputEvent>,
    /// The state it leaves TLC's generator in.
    pub random: u64,
}

impl<'ir> Rebuilder<'ir> {
    /// Replays a DFID implied action that failed, retaining the expression stack.
    pub fn dfid_action_failure(
        &mut self,
        store: &Store,
        states: &[&[Id]],
        actions: &[Option<u32>],
        position: usize,
    ) -> Result<Vec<SourceRange>, Unsupported> {
        if states.len() < 2 {
            return Err(Unsupported("DFID action failure without a step".into()));
        }
        let trace = self.rebuild_checked(store, states, actions, Ending::Violation, false)?;
        let evaluator = self.evaluator();
        let property = evaluator
            .ir
            .model
            .action_properties
            .get(position)
            .ok_or_else(|| Unsupported("DFID action property is missing".into()))?
            .clone();
        let predecessor = &trace.states[trace.states.len() - 2].values;
        let successor = &trace.states[trace.states.len() - 1].values;
        evaluator.current = predecessor.iter().cloned().map(Some).collect();
        evaluator.next = successor.iter().cloned().map(Some).collect();
        evaluator.level = states.len() as i32 - 1;
        evaluator.printed.clear();
        evaluator.call_stack = Some(CallStack::default());
        let result = evaluator
            .scope_context(property.scope)
            .and_then(|context| evaluator.boolean(property.action, &context));
        let stack = evaluator.call_stack.take().unwrap_or_default();
        if result.is_ok()
            || !evaluator.printed.is_empty()
            || stack.unfollowed.is_some()
            || stack.is_substituted
        {
            return Err(Unsupported(
                "DFID action failure replay did not fail without effects".into(),
            ));
        }
        let nodes = &evaluator.ir.nodes.arena;
        let action_range = nodes[property.action as usize].range;
        let subscript_range = nodes[property.subscript as usize].range;
        let mut wrappers = nodes.iter().filter_map(|node| match node.kind {
            NodeKind::BoxAction { action, subscript }
                if nodes[action as usize].range == action_range
                    && nodes[subscript as usize].range == subscript_range =>
            {
                node.range
            }
            _ => None,
        });
        let wrapper = wrappers
            .next()
            .ok_or_else(|| Unsupported("DFID action wrapper range is missing".into()))?;
        if wrappers.any(|range| range != wrapper) {
            return Err(Unsupported("DFID action wrapper range is ambiguous".into()));
        }
        let mut frames = vec![wrapper];
        frames.extend(ranges(evaluator, &stack));
        Ok(frames)
    }
    /// Checks the assumption at `position` as TLC checks it (`checkAssumptions`): after the
    /// startup's definitions and the assumptions before it, which hold, with or without -tool,
    /// which AssertError's messages depend on. `Unsupported` where it fails to evaluate, where it
    /// sets a register, which the search would read, and where the startup evaluates what the
    /// evaluator doesn't follow: the configuration's predicates or the symmetry.
    pub fn check_assumption(
        &mut self,
        position: u32,
        is_tool: bool,
    ) -> Result<Assumption, Unsupported> {
        self.ranking_made_texts(|rebuilder| rebuilder.check_ranked_assumption(position, is_tool))
    }

    /// Computes the AssertError application at `node`, which reads no state and has no effect,
    /// after the startup's definitions, with or without -tool, which its messages depend on.
    /// `Err` where it fails, isn't a boolean, or prints, draws or sets a register after all.
    pub fn check_constant(&mut self, node: u32, is_tool: bool) -> Result<bool, Unsupported> {
        self.ranking_made_texts(|rebuilder| {
            let evaluator = rebuilder.evaluator();
            let width = evaluator.ir.variables.len();
            evaluator.current = vec![None; width];
            evaluator.next = vec![None; width];
            evaluator.level = 0;
            evaluator.is_tool = Some(is_tool);
            run(evaluator.compute_startup_drawing())?;
            evaluator.printed.clear();
            let writes = evaluator.register_writes;
            let random = evaluator.random.as_ref().map(|random| random.state());
            let value = evaluator.evaluate(node, &Context::default());
            if !evaluator.printed.is_empty()
                || evaluator.register_writes != writes
                || evaluator.random.as_ref().map(|random| random.state()) != random
            {
                return Err(Unsupported("an AssertError with effects".into()));
            }
            match value {
                Ok(Value::Bool(holds)) => Ok(holds),
                Ok(_) => Err(Unsupported("an AssertError that isn't a boolean".into())),
                Err(error) => Err(Unsupported(format!(
                    "an AssertError that fails: {}",
                    error.reason
                ))),
            }
        })
    }

    /// Computes the constant definition at `index` of the IR's definitions as TLC does as it
    /// starts (`processConstantDefns`), after the startup's definitions before it, with or without
    /// -tool, which AssertEq's messages depend on: its value, a boolean, where it computes it
    /// without an effect or a warning, which TLC keeps and every use reads. `Err` where it fails,
    /// isn't a boolean, or prints, warns, draws or sets a register.
    pub fn compute_constant_definition(
        &mut self,
        index: u32,
        is_tool: bool,
    ) -> Result<bool, Unsupported> {
        self.ranking_made_texts(|rebuilder| {
            let evaluator = rebuilder.evaluator();
            let ir = evaluator.ir;
            let Some(&node) = ir.definitions.get(index as usize) else {
                return Err(Unsupported("a definition the IR doesn't have".into()));
            };
            let width = ir.variables.len();
            evaluator.current = vec![None; width];
            evaluator.next = vec![None; width];
            evaluator.level = 0;
            evaluator.is_tool = Some(is_tool);
            run(evaluator.compute_startup_drawing())?;
            evaluator.printed.clear();
            let writes = evaluator.register_writes;
            let random = evaluator.random.as_ref().map(|random| random.state());
            let definition = evaluator.definition(node).clone();
            if !matches!(&definition.form, DefinitionForm::Operator(params) if params.is_empty()) {
                return Err(Unsupported("a constant definition with parameters".into()));
            }
            let is_starting = std::mem::replace(&mut evaluator.is_starting, true);
            let is_processing = std::mem::replace(&mut evaluator.is_processing_constants, true);
            let value = evaluator.evaluate(definition.body, &Context::default());
            evaluator.is_processing_constants = is_processing;
            evaluator.is_starting = is_starting;
            if !evaluator.printed.is_empty()
                || evaluator.register_writes != writes
                || evaluator.random.as_ref().map(|random| random.state()) != random
            {
                return Err(Unsupported(
                    "a constant definition with effects or warnings".into(),
                ));
            }
            match value {
                Ok(Value::Bool(holds)) => Ok(holds),
                Ok(_) => Err(Unsupported(
                    "a constant definition that isn't a boolean".into(),
                )),
                Err(error) => Err(Unsupported(format!(
                    "a constant definition that fails: {}",
                    error.reason
                ))),
            }
        })
    }

    /// Confirms that TLC, computing the register probe at `position` of the model's
    /// (`register_probes`) as it starts (`processConstantDefns`), after the startup's definitions,
    /// fails on it before any effect, with an error of its own: no print, warning, draw or
    /// register's write before, and no effect the startup doesn't see run. TLC swallows that
    /// failure and computes the definition again at each use. `Err` where it computes it, fails
    /// otherwise, or the evaluator can't follow the failure.
    pub fn confirm_failing_probe(
        &mut self,
        position: usize,
        is_tool: bool,
    ) -> Result<(), Unsupported> {
        self.ranking_made_texts(|rebuilder| {
            let evaluator = rebuilder.evaluator();
            let ir = evaluator.ir;
            let Some(&index) = ir.model.startup.register_probes.get(position) else {
                return Err(Unsupported("a register probe the IR doesn't have".into()));
            };
            let node = ir.definitions[index as usize];
            let width = ir.variables.len();
            evaluator.current = vec![None; width];
            evaluator.next = vec![None; width];
            evaluator.level = 0;
            evaluator.is_tool = Some(is_tool);
            run(evaluator.compute_startup_drawing())?;
            evaluator.printed.clear();
            let writes = evaluator.register_writes;
            let random = evaluator.random.as_ref().map(|random| random.state());
            let definition = evaluator.definition(node).clone();
            if !matches!(&definition.form, DefinitionForm::Operator(params) if params.is_empty()) {
                return Err(Unsupported("a register probe with parameters".into()));
            }
            if evaluator.may_reach_unseen_effects(definition.body) {
                return Err(Unsupported(
                    "a register probe with effects the startup doesn't see".into(),
                ));
            }
            let is_starting = std::mem::replace(&mut evaluator.is_starting, true);
            let is_processing = std::mem::replace(&mut evaluator.is_processing_constants, true);
            let value = evaluator.evaluate(definition.body, &Context::default());
            evaluator.is_processing_constants = is_processing;
            evaluator.is_starting = is_starting;
            if !evaluator.printed.is_empty()
                || evaluator.register_writes != writes
                || evaluator.random.as_ref().map(|random| random.state()) != random
            {
                return Err(Unsupported("a register probe with effects".into()));
            }
            match value {
                Err(EvalError {
                    message: Some(_), ..
                }) => Ok(()),
                Err(error) => Err(Unsupported(format!(
                    "a register probe that fails otherwise: {}",
                    error.reason
                ))),
                Ok(_) => Err(Unsupported("a register probe that computes".into())),
            }
        })
    }

    // TLC interns what the startup and the assumptions make as it makes them, which the
    // evaluator follows in TLC's order there, unlike in the search.
    fn ranking_made_texts<T>(&mut self, check: impl FnOnce(&mut Self) -> T) -> T {
        self.evaluator().start_ranking();
        let result = check(self);
        self.evaluator().stop_ranking();
        result
    }

    fn check_ranked_assumption(
        &mut self,
        position: u32,
        is_tool: bool,
    ) -> Result<Assumption, Unsupported> {
        let evaluator = self.evaluator();
        let ir = evaluator.ir;
        let startup = &ir.model.startup;
        if !startup.predicates.is_empty() || startup.symmetry.is_some() {
            return Err(Unsupported(
                "an assumption after the configuration's predicates or a symmetry".into(),
            ));
        }
        let width = ir.variables.len();
        evaluator.current = vec![None; width];
        evaluator.next = vec![None; width];
        evaluator.level = 0;
        evaluator.is_tool = Some(is_tool);
        run(evaluator.compute_startup_drawing())?;
        evaluator.printed.clear();
        evaluator.is_in_assumptions = true;
        let assumed = Self::check_assumption_after(evaluator, position);
        evaluator.is_in_assumptions = false;
        assumed
    }

    // The assumption at `position` as TLC checks it, after those before it.
    fn check_assumption_after(
        evaluator: &mut Evaluator<'_>,
        position: u32,
    ) -> Result<Assumption, Unsupported> {
        let startup = &evaluator.ir.model.startup;
        for &(node, _) in &startup.assumptions[..position as usize] {
            if !matches!(
                evaluator.evaluate(node, &Context::default()),
                Ok(Value::Bool(true))
            ) {
                return Err(Unsupported(
                    "an assumption the engine found to hold that doesn't again".into(),
                ));
            }
        }
        let Some(&(node, _)) = startup.assumptions.get(position as usize) else {
            return Err(Unsupported("an assumption the model doesn't have".into()));
        };
        let writes = evaluator.register_writes;
        let printed_before = std::mem::take(&mut evaluator.printed);
        evaluator.is_checking_assumption = true;
        let result = evaluator.evaluate(node, &Context::default());
        evaluator.is_checking_assumption = false;
        let holds = match result {
            Ok(Value::Bool(holds)) => Some(holds),
            Ok(_) => return Err(Unsupported("an assumption that isn't a boolean".into())),
            Err(EvalError {
                message: Some(_), ..
            }) => None,
            Err(error) => {
                return Err(Unsupported(format!(
                    "an assumption the engine doesn't evaluate that fails to: {}",
                    error.reason
                )));
            }
        };
        if evaluator.register_writes != writes {
            return Err(Unsupported("an assumption that sets a register".into()));
        }
        let random = evaluator
            .random
            .as_ref()
            .ok_or_else(|| Unsupported("the startup's generator".into()))?
            .state();
        Ok(Assumption {
            holds,
            printed_before,
            printed: std::mem::take(&mut evaluator.printed),
            random,
        })
    }

    /// What the substitutes, the constant definitions and the definitions the configuration names
    /// print as TLC starts (`processConstantDefns`, `getConstantValue`), each print's values as
    /// `Trace` holds them, as TLC built them. A configured definition that fails prints what it
    /// printed before it failed, as TLC keeps it as an operator.
    pub fn startup_prints(&mut self) -> Result<Vec<crate::OutputEvent>, Unsupported> {
        let evaluator = self.evaluator();
        let ir = evaluator.ir;
        evaluator.level = 0;
        run(evaluator.compute_startup_drawing())?;
        // A constant definition TLC evaluated already keeps its value.
        let startup = &ir.model.startup;
        for predicate in &startup.predicates {
            if startup.definitions.contains(&predicate.definition) {
                continue;
            }
            let node = ir.definitions[predicate.definition as usize];
            let _ = evaluator.evaluate(evaluator.definition(node).body, &Context::default());
        }
        evaluator.random = None;
        Ok(std::mem::take(&mut evaluator.printed))
    }

    /// Computes the substitutes and the first `count` of the startup's definitions as TLC does as
    /// it starts (`processConstantDefns`), and gives what it made there. `Err` where the evaluator
    /// doesn't follow TLC there.
    pub fn compute_startup_until(&mut self, count: usize) -> Result<StartupUntil, Unsupported> {
        self.ranking_made_texts(|rebuilder| {
            let evaluator = rebuilder.evaluator();
            let ir = evaluator.ir;
            let width = ir.variables.len();
            evaluator.current = vec![None; width];
            evaluator.next = vec![None; width];
            evaluator.level = 0;
            evaluator.startup_limit = Some(count);
            let computed = run(evaluator.compute_startup_drawing());
            evaluator.startup_limit = None;
            computed?;
            let random = evaluator
                .random
                .as_ref()
                .ok_or_else(|| Unsupported("the startup's generator".into()))?
                .state();
            let is_last_computed = count
                .checked_sub(1)
                .and_then(|last| ir.model.startup.definitions.get(last))
                .is_some_and(|&index| {
                    evaluator.is_startup_computed(ir.definitions[index as usize])
                });
            let warnings = evaluator
                .printed
                .iter()
                .filter(|output| matches!(output, crate::OutputEvent::Warning(_)))
                .count();
            Ok(StartupUntil {
                prints: evaluator.printed.len() - warnings,
                warnings,
                writes: evaluator.register_writes,
                random,
                is_last_computed,
            })
        })
    }

    /// Evaluates the startup's definitions as TLC does, to confirm each the search found failing
    /// fails here too before any effect (`set_searched_failing`): the search swallows such a
    /// failure, as TLC does, whether or not anything reads the definition, and may fail where TLC
    /// doesn't. `Err` where the evaluator computes one, or fails only after an effect.
    pub fn confirm_startup(&mut self) -> Result<(), Unsupported> {
        let evaluator = self.evaluator();
        evaluator.level = 0;
        let confirmed = run(evaluator.compute_startup_drawing());
        evaluator.random = None;
        confirmed
    }

    /// Whether the startup definition at `position` of the model's, a PrintT of an expression
    /// without effects, computes TRUE, as it does as TLC starts: the definitions it names
    /// compute, or fail, as they do there. It gives the warnings TLC prints as it computes the
    /// argument, before the print, where it does.
    pub fn computes_startup_print(
        &mut self,
        position: usize,
    ) -> Option<Vec<tla_ir::RuntimeWarning>> {
        let evaluator = self.evaluator();
        let ir = evaluator.ir;
        let &index = ir.model.startup.definitions.get(position)?;
        evaluator.level = 0;
        let body = evaluator.definition(ir.definitions[index as usize]).body;
        let printed = evaluator.printed.len();
        let unfollowed = evaluator.unfollowed_print_normalizations;
        // TLC evaluates it as it starts (`processConstantDefns`).
        let is_starting = std::mem::replace(&mut evaluator.is_starting, true);
        let computed = evaluator.evaluate(body, &Context::default());
        evaluator.is_starting = is_starting;
        // A print whose deep normalization the evaluator didn't follow may fail in TLC there.
        if evaluator.unfollowed_print_normalizations != unfollowed
            || !matches!(computed, Ok(Value::Bool(true)))
        {
            return None;
        }
        // Its print, last, after the warnings TLC prints as it computes the argument.
        let [warned @ .., crate::OutputEvent::Print(_)] = &evaluator.printed[printed..] else {
            return None;
        };
        warned
            .iter()
            .map(|output| match output {
                crate::OutputEvent::Warning(warning) => Some(warning.clone()),
                crate::OutputEvent::Print(_) => None,
            })
            .collect()
    }

    /// Evaluates again the assumption at `position` of the model's assumptions, which failed to
    /// evaluate as TLC started, after the startup's definitions, and returns TLC's report of it
    /// (`checkAssumptions`), with what the assumptions before it printed and what it printed
    /// before it failed, with or without -tool, which AssertError's messages depend on.
    pub fn evaluate_assumption(
        &mut self,
        position: u32,
        is_tool: bool,
    ) -> Result<Failure, Unsupported> {
        without_null_prints("evaluating the assumption again", || {
            self.ranking_made_texts(|rebuilder| {
                rebuilder.evaluate_ranked_assumption(position, is_tool)
            })
        })
    }

    fn evaluate_ranked_assumption(
        &mut self,
        position: u32,
        is_tool: bool,
    ) -> Result<Failure, Unsupported> {
        let evaluator = self.evaluator();
        let ir = evaluator.ir;
        let Some(&(node, name)) = ir.model.startup.assumptions.get(position as usize) else {
            return Err(Unsupported("an assumption the model doesn't have".into()));
        };
        let width = ir.variables.len();
        evaluator.current = vec![None; width];
        evaluator.next = vec![None; width];
        evaluator.level = 0;
        evaluator.is_tool = Some(is_tool);
        // The startup printed its definitions and the assumptions before this one already, and
        // those set what the registers hold when TLC evaluates this one.
        run(evaluator.compute_startup_drawing())?;
        evaluator.printed.clear();
        evaluator.is_starting = true;
        evaluator.is_in_assumptions = true;
        let failure = Self::evaluate_assumption_after(evaluator, position, node, name);
        evaluator.is_in_assumptions = false;
        failure
    }

    // TLC's report of the assumption at `position` that failed, after those before it.
    fn evaluate_assumption_after(
        evaluator: &mut Evaluator<'_>,
        position: u32,
        node: NodeId,
        name: TextId,
    ) -> Result<Failure, Unsupported> {
        let ir = evaluator.ir;
        for &(earlier, _) in &ir.model.startup.assumptions[..position as usize] {
            if !matches!(
                evaluator.evaluate(earlier, &Context::default()),
                Ok(Value::Bool(true))
            ) {
                evaluator.is_starting = false;
                return Err(Unsupported(
                    "an assumption the engine found to hold that doesn't again".into(),
                ));
            }
        }
        clear_unnormalized();
        // `checkAssumptions` evaluates with `Tool`, whose values have no source.
        let mut call_stack = CallStack::default();
        call_stack.is_unsourced = true;
        evaluator.call_stack = Some(call_stack);
        evaluator.is_assumption = true;
        crate::print::clear_unsorted_prints();
        let result = evaluator.evaluate(node, &Context::default());
        evaluator.is_assumption = false;
        evaluator.is_starting = false;
        let call_stack = evaluator.call_stack.take().unwrap_or_default();
        let printed = std::mem::take(&mut evaluator.printed);
        let message = match result {
            // The search failed on a value TLC keeps lazy, or on a set it streams without sorting,
            // where TLC computes the assumption, as the evaluator, which holds and streams those
            // as TLC does, followed: TLC reports it false (`checkAssumptions`).
            Ok(Value::Bool(false)) if call_stack.unfollowed.is_none() => {
                let message = format!("Assumption {} is false.", ir.texts[name as usize]);
                return Ok(Failure {
                    code: ASSUMPTION_FALSE,
                    message: message.clone(),
                    tool_message: message,
                    call_stack: Vec::new(),
                    exit_code: VIOLATION_ASSUMPTION,
                    printed,
                    fingerprint: None,
                    state: None,
                    replay: Replay::default(),
                });
            }
            Ok(Value::Bool(_)) => {
                return Err(Unsupported(
                    "evaluating the assumption again: it didn't fail".into(),
                ));
            }
            // `Tool.isValid` fails on an assumption that is no boolean, naming it as SANY's
            // `toString` does.
            Ok(_) if ir.nodes.arena[node as usize].range.is_some() => TlcMessage {
                text: format!(
                    "TLC expected a boolean value, but did not find one. {}",
                    ir.texts[name as usize]
                ),
                code: Some(EXPECTED_VALUE),
                is_eval_exception: false,
                inner: None,
            },
            Ok(_) => {
                return Err(Unsupported(
                    "an assumption that is no boolean, without a range".into(),
                ));
            }
            Err(error) => {
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
                message
            }
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
            replay: Replay::default(),
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
        without_null_prints("evaluating the failure again", || {
            self.evaluate_failure_unprinted(store, states, actions, site)
        })
    }

    fn evaluate_failure_unprinted(
        &mut self,
        store: &Store,
        states: &[&[Id]],
        actions: &[Option<u32>],
        site: Site,
    ) -> Result<Failure, Unsupported> {
        if let Site::NextAtom { atom, is_extra } = site {
            return self.evaluate_next_atom(store, states, actions, atom, is_extra);
        }
        let mut is_successor_generated = false;
        let reads = self.evaluator().register_reads;
        let conversions = crate::eval::filter_conversions();
        let fingerprints = self.fingerprints.clone();
        let mut failure =
            self.evaluate_failure_at(store, states, actions, site, &mut is_successor_generated)?;
        // The search sets the registers in the order it explores the states, which the path
        // TLC's report replays doesn't follow. A model that sets none (no TLCSet, TLCGetAndSet
        // or Java class of the user's) reads each register unset wherever TLC reads it.
        let ir = self.evaluator().ir;
        let may_set_register = ir.builtins.iter().any(|builtin| {
            builtin.flags & tla_ir::Builtin::EXTERNAL_CLASS != 0
                || matches!(
                    &*ir.texts[builtin.name as usize],
                    "TLCSet" | "TLCGetAndSet" | "_Track"
                )
        });
        if self.evaluator().register_reads != reads && may_set_register {
            return Err(Unsupported(
                "evaluating the failure again: a failure that reads a register".into(),
            ));
        }
        // TLC words the error as its `Tool` met it, which shares the filter a definition holds
        // wherever it is read, so that one read's `convertAndCache` serves the next. Its replay
        // with the `CallStackTool` reads a copy of it each time (`CallStackTool.eval`), which
        // converts anew, so that the reason of a FingerprintException it throws may be the
        // unconverted filter's. Where the evaluation converted a filter, the replay runs again
        // with copies and gives the reason; it must otherwise report what the first did.
        if crate::eval::filter_conversions() != conversions && !may_set_register {
            self.fingerprints = fingerprints;
            self.evaluator().copies_filters = true;
            let mut is_generated = false;
            let replayed =
                self.evaluate_failure_at(store, states, actions, site, &mut is_generated);
            self.evaluator().copies_filters = false;
            let reason = match replayed {
                Ok(mut replayed) if is_generated == is_successor_generated => {
                    let reason = replayed.fingerprint.as_mut().map(|fingerprint| {
                        (
                            std::mem::take(&mut fingerprint.reason),
                            std::mem::take(&mut fingerprint.tool_reason),
                        )
                    });
                    // The message is the first evaluation's (`ModelChecker.doInit` and
                    // `Worker.run` print it before the replay).
                    replayed.message.clone_from(&failure.message);
                    replayed.tool_message.clone_from(&failure.tool_message);
                    let mut first = failure.clone();
                    if let Some(fingerprint) = &mut first.fingerprint {
                        fingerprint.reason.clear();
                        fingerprint.tool_reason.clear();
                    }
                    (first == replayed).then_some(reason)
                }
                _ => None,
            };
            match (reason, &mut failure.fingerprint) {
                (Some(Some((reason, tool_reason))), Some(fingerprint))
                    if fingerprint.is_replayed || fingerprint.reason == reason =>
                {
                    fingerprint.reason = reason;
                    fingerprint.tool_reason = tool_reason;
                }
                (Some(None), None) => {}
                _ => {
                    return Err(Unsupported(
                        "evaluating the failure again: a replay whose copies of a filter fail otherwise"
                            .into(),
                    ));
                }
            }
        }
        failure.replay.is_successor_generated = is_successor_generated;
        Ok(failure)
    }

    // TLC's worker reports the failure of the next-state relation, then adds the state to the
    // behavior graphs, where the atom fails: TLC prints the call stack of its rerun with its
    // `CallStackTool` and no longer replays the expansion for Next's (`keepCallStack`), so it
    // exits by the error's code (`Worker#doNextCheckLiveness`). Where the rerun has no call
    // stack, TLC replays the expansion as for any failure of Next.
    fn evaluate_next_atom(
        &mut self,
        store: &Store,
        states: &[&[Id]],
        actions: &[Option<u32>],
        atom: u32,
        is_extra: bool,
    ) -> Result<Failure, Unsupported> {
        let path = &states[..states.len().saturating_sub(usize::from(is_extra))];
        let next = self.evaluate_failure(
            store,
            path,
            actions
                .get(..path.len().saturating_sub(1))
                .unwrap_or(actions),
            Site::Next,
        )?;
        let failed =
            self.evaluate_failure(store, states, actions, Site::Atom { atom, is_extra })?;
        if next.fingerprint.is_some() || failed.fingerprint.is_some() {
            return Err(Unsupported(
                "evaluating the failure again: a state TLC fails to fingerprint before an atom fails"
                    .into(),
            ));
        }
        if !next.printed.is_empty() || !failed.printed.is_empty() {
            return Err(Unsupported(
                "evaluating the failure again: an atom that fails after a failure that prints"
                    .into(),
            ));
        }
        if failed.call_stack.is_empty() {
            return Ok(next);
        }
        Ok(Failure {
            call_stack: failed.call_stack,
            exit_code: match next.exit_code {
                FAILURE_SPEC_EVAL => FAILURE_ERROR,
                exit_code => exit_code,
            },
            ..next
        })
    }

    fn evaluate_failure_at(
        &mut self,
        store: &Store,
        states: &[&[Id]],
        actions: &[Option<u32>],
        site: Site,
        is_successor_generated: &mut bool,
    ) -> Result<Failure, Unsupported> {
        // TLC 1.7.4 streams the lazy bounds of a quantifier rather than enumerating them in order,
        // and words some messages apart, neither of which is ported.
        if self.evaluator().is_174() {
            return Err(Unsupported(
                "evaluating the failure again: TLC 1.7.4".into(),
            ));
        }
        // TLC reports an invariant that fails on an initial state otherwise, which isn't ported.
        if matches!(
            site,
            Site::Invariant(_)
                | Site::ActionConstraint(_)
                | Site::Constraint(_)
                | Site::ActionProperty(_)
        ) && states.len() < 2
        {
            return Err(Unsupported(
                "evaluating the failure again: an invariant of an initial state".into(),
            ));
        }
        // The state an atom reads past the path, which TLC rebuilds no trace to.
        let (states, actions, extra) = match site {
            Site::Atom { is_extra: true, .. } | Site::DeadlockAtom { is_extra: true, .. } => {
                let (extra, path) = states.split_last().ok_or_else(|| {
                    Unsupported("evaluating the failure again: an atom without a state".into())
                })?;
                let extra: Vec<Option<Value>> = extra
                    .iter()
                    .map(|&id| crate::value::from_store(store, id).map(Some))
                    .collect::<Result<_, _>>()?;
                (path, &actions[..path.len().saturating_sub(1)], Some(extra))
            }
            _ => (states, actions, None),
        };
        // The initial state TLC's replay fails at again isn't on the path.
        let (states, replayed) = match site {
            Site::InitialAtom {
                replayed: Some(atom),
                ..
            } => match states {
                [_, replayed] => (&states[..1], Some((*replayed, atom))),
                _ => {
                    return Err(Unsupported(
                        "evaluating the failure again: the initial state TLC's replay fails at"
                            .into(),
                    ));
                }
            },
            _ => (states, None),
        };
        // A successor that fails an invariant or an action constraint is held as TLC found it, as
        // a violating one is.
        let ending = match site {
            Site::Invariant(_) | Site::ActionProperty(_) => Ending::Violation,
            Site::ActionConstraint(_) | Site::Constraint(_) => Ending::Failed,
            _ => Ending::Kept,
        };
        let is_initial = matches!(
            site,
            Site::InitialConstraint(_)
                | Site::InitialView
                | Site::InitialInvariant(_)
                | Site::InitialPredicate(_)
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
        let known = self.fingerprints.take();
        let is_keyed_by_state = self.is_keyed_by_state();
        let evaluator = self.evaluator();
        let ir = evaluator.ir;
        evaluator.printed.clear();
        clear_unnormalized();
        evaluator.call_stack = Some(CallStack::default());
        let width = ir.variables.len();
        let level = states.len() as i32;
        let path: Vec<Vec<Value>> = last
            .iter()
            .flatten()
            .map(|state| state.values.clone())
            .collect();
        let current: Vec<Option<_>> = path
            .last()
            .cloned()
            .map(|values| values.into_iter().map(Some).collect())
            .unwrap_or_else(|| vec![None; width]);
        // The initial state TLC failed to check, as the replay found it.
        let mut checked: Option<Vec<Value>> = None;
        // The initial states the replay of the initial predicate found.
        let mut initial_states = 0;
        // Whether TLC's replay of the initial predicate went on past the check that failed.
        let mut is_initial_check_continued = false;
        // What of TLC's replay of the initial states, outside the failure, isn't followed.
        let mut unfollowed: Option<&'static str> = None;
        let result = match site {
            Site::NextAtom { .. } => {
                return Err(Unsupported(
                    "evaluating the failure again: Next's and an atom's at once".into(),
                ));
            }
            Site::InitialConstraint(_)
            | Site::InitialView
            | Site::InitialInvariant(_)
            | Site::InitialPredicate(_) => {
                let body = |name: &tla_ir::ConfigName| {
                    name.definition
                        .map(|index| evaluator.definition(ir.definitions[index as usize]).body)
                };
                // TLC checks the constraints, fingerprints the state, which evaluates the VIEW,
                // then checks the invariants, then the implied inits (`DoInitFunctor`), up to the
                // one that failed.
                let (constraint_count, invariant_count, predicate_count) = match site {
                    Site::InitialConstraint(position) => (position as usize + 1, 0, 0),
                    Site::InitialView => (ir.model.constraints.len(), 0, 0),
                    Site::InitialInvariant(position) => {
                        (ir.model.constraints.len(), position as usize + 1, 0)
                    }
                    Site::InitialPredicate(position) => (
                        ir.model.constraints.len(),
                        ir.model.invariants.len(),
                        position as usize + 1,
                    ),
                    _ => unreachable!("an initial check"),
                };
                // The VIEW TLC's state evaluates as it fingerprints itself (`TLCStateMut.fingerPrint`).
                let view = match site {
                    Site::InitialView => match ir.model.view.as_ref().and_then(body) {
                        Some(view) => Some(view),
                        None => {
                            return Err(Unsupported(
                                "evaluating the failure again: a VIEW the model doesn't define"
                                    .into(),
                            ));
                        }
                    },
                    _ => None,
                };
                // The invariants as TLC checks them: the model's, then its properties checked as
                // invariants, which the engine counts past them.
                let mut invariants = evaluator.tlc_invariants()?;
                invariants.truncate(invariant_count);
                if invariants.iter().any(|&(_, scope, _)| scope.is_some()) {
                    return Err(Unsupported(
                        "evaluating the failure again: an invariant in an instance's scope".into(),
                    ));
                }
                if invariant_count > invariants.len() {
                    return Err(Unsupported(
                        "evaluating the failure again: an invariant the model doesn't have".into(),
                    ));
                }
                let checks: Option<Vec<NodeId>> = ir
                    .model
                    .constraints
                    .iter()
                    .take(constraint_count)
                    .map(body)
                    .chain(invariants.iter().map(|&(invariant, _, _)| Some(invariant)))
                    .chain(
                        ir.model
                            .initial_predicates
                            .iter()
                            .take(predicate_count)
                            .map(|&predicate| Some(predicate)),
                    )
                    .chain(view.map(Some))
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
                let check_initial = |evaluator: &mut Evaluator<'_>,
                                     checked: &mut Option<Vec<Value>>,
                                     unfollowed: &mut Option<&'static str>|
                 -> Evaluated<bool> {
                    let values: Option<Vec<Value>> = evaluator.current.iter().cloned().collect();
                    let Some(values) = values.filter(|values| is_same(store, target, values))
                    else {
                        // The replay forces the checks of each initial state before the target.
                        if evaluator.current.iter().all(Option::is_some)
                            && let Err(reason) =
                                evaluator.check_replayed_initial(true, is_keyed_by_state)
                        {
                            unfollowed.get_or_insert(reason);
                        }
                        return Ok(true);
                    };
                    *checked = Some(values);
                    evaluator.level = 1;
                    let call_stack = evaluator.call_stack.take();
                    let (failed, earlier) = checks.split_last().expect("a check");
                    for (position, &body) in earlier.iter().enumerate() {
                        // TLC fingerprints the state once the constraints hold, before it
                        // checks the invariants (`DoInitFunctor`).
                        if position == constraint_count && is_keyed_by_state {
                            evaluator.current.iter().flatten().for_each(settle);
                        }
                        let holds = if position < constraint_count {
                            constraint_holds(evaluator, body)
                        } else {
                            evaluator.check_holds(body, &Context::default())
                        };
                        if !matches!(holds, Ok(true)) {
                            evaluator.call_stack = call_stack;
                            return holds;
                        }
                    }
                    // `TLCStateMut.fingerPrint` normalizes the state's values and evaluates the
                    // VIEW with the tool the state holds, TLC's own rather than the replay's
                    // `CallStackTool`: the VIEW pushes no frame, and a failure freezes the call
                    // stack at the initial predicate's frames that found the state. A failure in
                    // a method of a value with a source, which TLC throws as a
                    // FingerprintException, isn't followed: TLC's tool gives the values the VIEW
                    // builds none.
                    if view.is_some() {
                        evaluator.current.iter().flatten().for_each(settle);
                        evaluator.call_stack = call_stack;
                        let depth = evaluator
                            .call_stack
                            .as_ref()
                            .map(|stack| (stack.frames.len(), stack.is_frozen));
                        let viewed = evaluator.evaluate(*failed, &Context::default());
                        if let (Some(stack), Some((depth, is_frozen))) =
                            (&mut evaluator.call_stack, depth)
                            && viewed.is_err()
                        {
                            if stack.is_fingerprinted {
                                stack.unfollowed.get_or_insert(
                                    "a VIEW that fails in a method of a value with a source",
                                );
                            }
                            stack.frames.truncate(depth);
                            stack.is_frozen = is_frozen;
                        }
                        return viewed.map(|_| true);
                    }
                    if is_traced {
                        if earlier.len() <= constraint_count && is_keyed_by_state {
                            evaluator.current.iter().flatten().for_each(settle);
                        }
                        evaluator.call_stack = call_stack;
                        return evaluator.boolean_as(
                            *failed,
                            &Context::default(),
                            Demand::Invariant,
                        );
                    }
                    // TLC's replay of the initial states evaluates the constraint with its
                    // `CallStackTool`, so a failure as it evaluates the constraint has the
                    // constraint's frames after the initial predicate's. A constraint that
                    // isn't a boolean fails once evaluated (`Tool.isInModel`), without them.
                    evaluator.call_stack = call_stack;
                    traced_constraint_holds(evaluator, *failed)
                };
                // `DoInitFunctor.addElement` catches a FingerprintException of a check as a
                // `Throwable` and keeps it, and the replay of the initial predicate goes on, on
                // the call stack the exception froze, which keeps every frame it pushes after,
                // counting the states left without checking them; then `doInit` throws it.
                let mut failure = None;
                let mut printed = 0;
                let walked = context.and_then(|context| {
                    evaluator.walk_action(ir.model.init, &context, true, &mut |evaluator| {
                        initial_states += 1;
                        if failure.is_some() {
                            return Ok(true);
                        }
                        let checked_at = checked.is_some();
                        let result = check_initial(evaluator, &mut checked, &mut unfollowed);
                        match result {
                            Err(error)
                                if !checked_at
                                    && checked.is_some()
                                    && evaluator.call_stack.as_ref().is_some_and(|stack| {
                                        stack.is_fingerprinted && stack.is_frozen
                                    }) =>
                            {
                                failure = Some(error);
                                printed = evaluator.printed.len();
                                Ok(true)
                            }
                            result => result,
                        }
                    })
                });
                match failure {
                    Some(error) => {
                        if (walked.is_err() || evaluator.printed.len() != printed)
                            && let Some(stack) = &mut evaluator.call_stack
                        {
                            stack.unfollowed.get_or_insert(
                                "initial states that fail or print after a check TLC fails as a FingerprintException",
                            );
                        }
                        is_initial_check_continued = true;
                        Err(error)
                    }
                    None => walked,
                }
            }
            Site::Init => {
                evaluator.current = vec![None; width];
                evaluator.level = 0;
                let context = evaluator.scope_context(ir.model.scope);
                // `DoInitFunctor` keeps a FingerprintException, which `addElement` catches as a
                // `Throwable`, and only counts the states left, then `doInit` throws it.
                let mut failure = None;
                let mut printed = 0;
                let walked = context.and_then(|context| {
                    evaluator.walk_action(ir.model.init, &context, true, &mut |evaluator| {
                        initial_states += 1;
                        if failure.is_some() {
                            return Ok(true);
                        }
                        let found = evaluator.fingerprint_found(true);
                        // The replay forces the checks of each initial state the initial
                        // predicate gives before it fails.
                        if found.is_ok()
                            && let Err(reason) =
                                evaluator.check_replayed_initial(false, is_keyed_by_state)
                        {
                            unfollowed.get_or_insert(reason);
                        }
                        match found {
                            Err(error)
                                if evaluator.call_stack.as_ref().is_some_and(|stack| {
                                    stack.unfollowed.is_none()
                                        && stack
                                            .fingerprint
                                            .as_ref()
                                            .is_some_and(|(sources, _)| !sources.is_empty())
                                }) =>
                            {
                                failure = Some((error, evaluator.call_stack.take()));
                                printed = evaluator.printed.len();
                                Ok(true)
                            }
                            found => found,
                        }
                    })
                });
                match failure {
                    Some((error, call_stack)) => {
                        evaluator.call_stack = call_stack;
                        if (walked.is_err() || evaluator.printed.len() != printed)
                            && let Some(stack) = &mut evaluator.call_stack
                        {
                            stack.unfollowed.get_or_insert(
                                "initial states that fail or print after one TLC can't fingerprint",
                            );
                        }
                        Err(error)
                    }
                    None => walked,
                }
            }
            Site::Next => {
                let actions = evaluator.tlc_actions();
                evaluator.current = current;
                evaluator.level = level;
                actions.and_then(|actions| {
                    actions
                        .into_iter()
                        .try_for_each(|(expression, context)| {
                            evaluator.next = vec![None; width];
                            // TLC's worker fingerprints each successor as the action gives it,
                            // but its replay takes all of the action's successors first, so
                            // the replay follows a successor that fails to fingerprint only
                            // where the rest of the action evaluates, and prints nothing.
                            let mut failure = None;
                            let printed = evaluator.printed.len();
                            let walked = evaluator.walk_action(
                                expression,
                                &context,
                                false,
                                &mut |evaluator| {
                                    if failure.is_some() {
                                        return Ok(true);
                                    }
                                    *is_successor_generated = true;
                                    let found = evaluator.fingerprint_found(false);
                                    match found {
                                        Err(error) => {
                                            failure = Some((error, evaluator.call_stack.take()));
                                            Ok(true)
                                        }
                                        found => found,
                                    }
                                },
                            );
                            let Some((error, call_stack)) = failure else {
                                return walked.map(|_| ());
                            };
                            evaluator.call_stack = call_stack;
                            if (walked.is_err() || evaluator.printed.len() != printed)
                                && let Some(stack) = &mut evaluator.call_stack
                            {
                                stack.unfollowed.get_or_insert(
                                    "an action that fails or prints after a successor TLC can't fingerprint",
                                );
                            }
                            Err(error)
                        })
                        .map(|()| true)
                })
            }
            // TLC evaluates the atom as it adds the state, on the state, the successor whose
            // state predicate it checks, or the step to it.
            Site::Atom { atom, .. }
            | Site::DeadlockAtom { atom, .. }
            | Site::InitialAtom { atom, .. } => {
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
                        live_state_predicate(evaluator, atom.expression, &context)
                    }
                    AtomKind::Enabled { .. } => evaluator
                        .enabled(atom.expression, &context)
                        .map(|value| matches!(value, Value::Bool(true))),
                    AtomKind::Action { unchanged, .. } => {
                        // `LNAction.eval` evaluates the subscript in each state, then compares the
                        // two values outside any evaluation, so a failing comparison has no call
                        // stack, and TLC prints none; where it fails in the method of a value the
                        // subscript built, it is a FingerprintException (`subscript_equals`).
                        if let Some(unchanged) = unchanged {
                            let NodeKind::Unchanged(subscript) =
                                &ir.nodes.arena[*unchanged as usize].kind
                            else {
                                return fail("a subscript the replay doesn't read");
                            };
                            let before = evaluator.evaluate(*subscript, &context);
                            let current = evaluator.current.clone();
                            if let Some(extra) = &extra {
                                evaluator.current = extra.clone();
                            }
                            let after = before.and_then(|before| {
                                Ok((before, evaluator.evaluate(*subscript, &context)?))
                            });
                            evaluator.current = current;
                            if let Some(extra) = extra {
                                evaluator.next = extra;
                            }
                            match after.and_then(|(before, after)| {
                                evaluator.subscript_equals(&before, &after)
                            }) {
                                Ok(true) => Ok(false),
                                Ok(false) => live_action(evaluator, atom.expression, &context),
                                Err(error) => Err(error),
                            }
                        } else {
                            if let Some(extra) = extra {
                                evaluator.next = extra;
                            }
                            live_action(evaluator, atom.expression, &context)
                        }
                    }
                })
            }
            Site::ActionConstraint(position) => {
                *is_successor_generated = true;
                replay_successor_check(evaluator, &path, SuccessorCheck::Action(position))?
            }
            Site::Constraint(position) => {
                *is_successor_generated = true;
                replay_successor_check(evaluator, &path, SuccessorCheck::State(position))?
            }
            Site::Invariant(position) => {
                evaluator.current = current;
                evaluator.level = level;
                let mut checks = evaluator.tlc_invariants()?;
                checks.truncate(position as usize + 1);
                let Some((failed, scope, _)) =
                    checks.pop().filter(|_| checks.len() == position as usize)
                else {
                    return Err(Unsupported("an invariant the model doesn't have".into()));
                };
                // TLC checks the invariants before it in order, outside the call stack, and their
                // comparisons sort what they reach of the state.
                let call_stack = evaluator.call_stack.take();
                for (body, scope, _) in checks {
                    let context = run(evaluator.scope_context(scope))?;
                    if !run(evaluator.check_holds(body, &context))? {
                        return Err(Unsupported(
                            "evaluating the failure again: an earlier invariant is violated".into(),
                        ));
                    }
                }
                evaluator.call_stack = call_stack;
                evaluator
                    .scope_context(scope)
                    .and_then(|context| evaluator.boolean_as(failed, &context, Demand::Invariant))
            }
            Site::ActionProperty(position) => {
                // TLC's worker checked the invariants of the successor, where it was new, and the
                // action properties before this one, which held (`Worker.addElement`).
                let call_stack = evaluator.call_stack.take();
                evaluator.current = current.clone();
                evaluator.next = vec![None; width];
                evaluator.level = level;
                for (body, scope, _) in evaluator.tlc_invariants()? {
                    let context = run(evaluator.scope_context(scope))?;
                    if !run(evaluator.check_holds(body, &context))? {
                        return Err(Unsupported(
                            "evaluating the failure again: an invariant is violated".into(),
                        ));
                    }
                }
                let [.., predecessor, _] = path.as_slice() else {
                    return Err(Unsupported(
                        "evaluating the failure again: an action property without a step".into(),
                    ));
                };
                evaluator.current = predecessor.iter().cloned().map(Some).collect();
                evaluator.next = current;
                evaluator.level = level - 1;
                for earlier in 0..position {
                    if !run(action_property_holds(evaluator, earlier)?)? {
                        return Err(Unsupported(
                            "evaluating the failure again: an earlier action property is violated"
                                .into(),
                        ));
                    }
                }
                if !evaluator.printed.is_empty() {
                    return Err(Unsupported(
                        "evaluating the failure again: a check before the action property prints"
                            .into(),
                    ));
                }
                evaluator.call_stack = call_stack;
                action_property_holds(evaluator, position)?
            }
        };
        let call_stack = evaluator.call_stack.take().unwrap_or_default();
        if let Some(reason) = unfollowed {
            return Err(Unsupported(format!(
                "evaluating the failure again: {reason}"
            )));
        }
        // TLC evaluates the action of <<A>>_v, and records no node for the brackets, whether
        // the property writes them or the front does for WF_v(A) and SF_v(A).
        let mut call_stack = call_stack;
        if let Site::Atom { atom, .. } | Site::DeadlockAtom { atom, .. } = site
            && let Some(atom) = ir.model.atoms.get(atom as usize)
            && matches!(
                ir.nodes.arena[atom.expression as usize].kind,
                NodeKind::AngleAction { .. }
            )
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
        if matches!(
            error.runtime_exception,
            crate::value::RuntimeException::ClassCast
                | crate::value::RuntimeException::IndexOutOfBounds
        ) && !call_stack.is_fingerprinted
        {
            call_stack.frames.clear();
        }
        // A set TLC fails to normalize as it words another failure with the set's `toString`
        // adds the set's source to a fingerprint stack (`SetEnumValue`'s `getNewHead`), which the
        // evaluator, holding no source of the set, can't place.
        if error.is_named_normalization && call_stack.is_fingerprinted {
            return Err(Unsupported(
                "evaluating the failure again: a set TLC fails to normalize as it words a failure, in a fingerprint stack"
                    .into(),
            ));
        }
        // TLC evaluates a startup definition that failed as it started again where it is used,
        // with the sources of that use's values, which the evaluator doesn't follow into the
        // definition: a failure TLC reports as a FingerprintException there has frames it lacks.
        // One in a method of an interval may be such a failure.
        if (call_stack.is_fingerprinted || call_stack.is_interval_unplaced)
            && evaluator.failed_startup_uses > 0
        {
            return Err(Unsupported(
                "evaluating the failure again: a FingerprintException in a startup definition that failed"
                    .into(),
            ));
        }
        // TLC fails to fingerprint an initial state that holds a set it can't normalize, then to
        // print the state as it reports that, which escapes as an exception it didn't expect. A
        // next-state relation that fails in a method of a value with a source fails before TLC
        // fingerprints any successor of the expansion that holds such a set; elsewhere such a
        // failure is TLC's where the replay found no state it fails to fingerprint or print.
        let local_normalization = error.is_set_normalization
            && error.message.as_ref().is_some_and(|message| {
                (message.code == Some(JAVA_METHOD_FAILED)
                    && error.runtime_exception == RuntimeException::Runtime)
                    || (message.is_eval_exception
                        && error.runtime_exception == RuntimeException::Runtime)
            })
            && call_stack.scalar_state_at_value_failure == Some(true)
            && call_stack.unfollowed.is_none()
            && call_stack.unprintable.is_none()
            && call_stack.fingerprint.is_none()
            && !call_stack.frames.iter().any(|frame| {
                matches!(frame, StackFrame::Node(node)
                    if matches!(ir.nodes.arena[*node as usize].kind, NodeKind::FunctionConstruction { .. }))
            });
        // Outside a step, the replay follows such a failure only where its frames end at the set
        // enumeration TLC fails to sort, or at the element of it whose own method failed as TLC
        // sorted it (`{("a" :> 1), <<2>>}`, `<<2>>`). Where they end at a value holding it (a
        // function set, a record set, a product, SUBSET of it, a function a constructor built
        // over it, a filter or a union of those), whose method fails, TLC traces on into that
        // set, and the sets between, from their sources (`FingerprintException.getNewHead`),
        // which the values the replay captured don't keep. In a step, where it follows the
        // others as main does (`({} \cup {1, "a"}) = {}`, whose stack ends at the union TLC
        // returns the set from), it declines such a sort of a set those holders hold.
        let sources: Vec<NodeId> = call_stack
            .frames
            .iter()
            .filter_map(|frame| match frame {
                StackFrame::Node(node) => Some(*node),
                _ => None,
            })
            .chain(call_stack.fingerprinted_sources.iter().copied())
            .collect();
        let ends_in_node = !call_stack.fingerprinted_sources.is_empty()
            || matches!(call_stack.frames.last(), Some(StackFrame::Node(_)));
        // A tuple or a record TLC builds as it evaluates the set enumeration's element, and the
        // tuples and records it holds, compare their components in turn (`TupleValue.equals`,
        // `RecordValue.equals`), so frames that go on from the element through those
        // constructors alone end in the element whose method failed
        // (`{<<<<1>>, 2>>, <<[a |-> 1], 3>>}`, ending at `[a |-> 1]`).
        let ends_in_element = sources.iter().enumerate().any(|(at, set)| {
            let NodeKind::SetEnumeration(elements) = &ir.nodes.arena[*set as usize].kind else {
                return false;
            };
            let Some((element, inner)) = sources[at + 1..].split_first() else {
                return false;
            };
            let is_constructor = |node: NodeId| {
                matches!(
                    ir.nodes.arena[node as usize].kind,
                    NodeKind::Tuple(_) | NodeKind::Record(_)
                )
            };
            elements.contains(element)
                && !inner.is_empty()
                && is_constructor(*element)
                && inner.iter().all(|&node| is_constructor(node))
                && std::iter::once(element).chain(inner).zip(inner).all(
                    |(&holder, &node)| match &ir.nodes.arena[holder as usize].kind {
                        NodeKind::Tuple(parts) => parts.contains(&node),
                        NodeKind::Record(fields) => fields.iter().any(|&(_, field)| field == node),
                        _ => false,
                    },
                )
        });
        let ends_at_holder = ends_in_node
            && !ends_in_element
            && match sources.as_slice() {
                [.., set, element]
                    if matches!(&ir.nodes.arena[*set as usize].kind,
                        NodeKind::SetEnumeration(elements) if elements.contains(element)) =>
                {
                    false
                }
                [.., last] => match &ir.nodes.arena[*last as usize].kind {
                    NodeKind::SetEnumeration(_) => false,
                    NodeKind::FunctionConstruction { .. }
                    | NodeKind::FunctionSet { .. }
                    | NodeKind::RecordSet(_)
                    | NodeKind::Product(_)
                    | NodeKind::SetFilter { .. }
                    | NodeKind::SetMap { .. } => true,
                    NodeKind::Apply { name, .. } if !name.is_local => {
                        site != Site::Next
                            || matches!(ir.texts[name.text as usize].as_ref(), "SUBSET" | "UNION")
                    }
                    _ => site != Site::Next,
                },
                [] => false,
            };
        if call_stack.is_unsorted
            && !local_normalization
            && !(call_stack.is_fingerprinted
                && !call_stack.is_unsorted_union_member
                && !(ends_at_holder && (site != Site::Next || error.is_set_normalization))
                && (site == Site::Next
                    || call_stack.fingerprint.is_none() && call_stack.unprintable.is_none()))
        {
            return match call_stack.unprintable {
                Some(message)
                    if site == Site::Init
                        && call_stack.unfollowed.is_none()
                        && printed.is_empty() =>
                {
                    Ok(Failure {
                        code: GENERAL,
                        message: format!(
                            "{}{}",
                            unexpected_exception(error.runtime_exception),
                            message.text
                        ),
                        tool_message: format!(
                            "{}{}",
                            unexpected_exception(error.runtime_exception),
                            nested(&message)
                        ),
                        call_stack: Vec::new(),
                        exit_code: FAILURE_ERROR,
                        printed,
                        fingerprint: None,
                        state: None,
                        replay: Replay::default(),
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
        // TLC prints no frames of the evaluation where an invariant or an action property of a
        // successor fails to evaluate (`doNextEvalFailed`), only those of its replay of the
        // expansion, which `replay_failed` follows: the frames of a substitution don't matter
        // there.
        if call_stack.is_substituted
            && !matches!(site, Site::Invariant(_) | Site::ActionProperty(_))
        {
            return Err(Unsupported(format!(
                "evaluating the failure again: {SUBSTITUTED_FRAMES}"
            )));
        }
        // `DoInitFunctor` reports an initial state that isn't a legal state, one some variable
        // lacks a value in, outside any evaluation.
        if site == Site::Init
            && let Some(state) = call_stack.incomplete
        {
            let message = "current state is not a legal state".to_string();
            return Ok(Failure {
                code: INITIAL_STATE,
                message: message.clone(),
                tool_message: message,
                call_stack: Vec::new(),
                exit_code: FAILURE_ERROR,
                printed,
                fingerprint: None,
                state: Some(state),
                replay: Replay::default(),
            });
        }
        if let Some((sources, state)) = call_stack.fingerprint.take() {
            let Some(message) = error.message else {
                return Err(Unsupported(format!(
                    "evaluating the failure again: {}",
                    error.reason
                )));
            };
            // A value without a source fails as it is: `DoInitFunctor` reports it with the
            // state, and TLC's replay prints the frames it froze in.
            if sources.is_empty() {
                return Ok(Failure {
                    code: INITIAL_STATE,
                    message: message.text.clone(),
                    tool_message: nested(&message),
                    call_stack: ranges(evaluator, &call_stack),
                    exit_code: FAILURE_SPEC_EVAL,
                    printed,
                    fingerprint: None,
                    state: Some(state),
                    replay: Replay {
                        initial_states: (site == Site::Init).then_some(initial_states),
                        ..Replay::default()
                    },
                });
            }
            // TLC prints the trace to a successor it failed to fingerprint by finding it again
            // among the successors of the state before it (`Tool.getState(TLCState, TLCState)`),
            // whose comparison with the successor may fail anew. A failure with a code, as the
            // overflow of a count, escapes, and TLC reports it again; one of `Assert.fail` with a
            // text alone, as a union's `elements` of a set it can't enumerate, TLC skips the
            // successor for, which leaves it without the state (`is_skipped_again`): the printing
            // of the trace words that (`TLCTrace.printTrace`).
            let is_skipped_again =
                site != Site::Init && message.code.is_none() && !message.is_eval_exception;

            // Only a union's own failure (`SetCupValue.elements`) is placed by its source alone; a
            // failure inside a set the union holds, as `[a : Nat]` or `SUBSET Nat` in `{1} \cup
            // [a : Nat]`, is traced by the sources of the values it came from too, which the
            // replay doesn't follow.
            if is_skipped_again
                && !message
                    .text
                    .starts_with("Attempted to enumerate S \\cup T when S:")
            {
                return Err(Unsupported(
                    "evaluating the failure again: a successor TLC fails to fingerprint with an error it skips finding it again"
                        .into(),
                ));
            }
            let fingerprint = FingerprintFailure {
                sources: sources
                    .into_iter()
                    .filter_map(|node| ir.nodes.arena[node as usize].range)
                    .collect(),
                reason: message.text.clone(),
                tool_reason: nested(&message),
                is_replayed: false,
                is_skipped_again,
            };
            // TLC reports a state it fails to fingerprint as it works on an initial state, or as
            // an exception it didn't expect in the next states, and exits as for the replay.
            let (code, text, tool_text, state, initial_states) = match site {
                Site::Init => (
                    INITIAL_STATE,
                    message.text.clone(),
                    nested(&message),
                    Some(state),
                    Some(initial_states),
                ),
                _ => {
                    let (code, text, tool_text) = report(&message, true, error.runtime_exception);
                    (code, text, tool_text, None, None)
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
                replay: Replay {
                    initial_states,
                    ..Replay::default()
                },
            });
        }
        // A constraint or an invariant that fails on an initial state in a value's method, or the
        // initial predicate itself: TLC reports the error, with the state where `DoInitFunctor`
        // kept it, then its replay of the initial states throws the FingerprintException, whose
        // call stack it prints.
        if call_stack.is_fingerprinted
            && let Some(message) = &error.message
            && (site == Site::Init && call_stack.is_frozen && !call_stack.frames.is_empty()
                || !call_stack.fingerprinted_sources.is_empty()
                    && matches!(site, Site::InitialConstraint(_) | Site::InitialInvariant(_))
                    && checked.is_some()
                // A check of an initial state that fails in a method of a value its own
                // evaluation built: the frames the failure froze in its replay, where the value
                // gave its source, are those of the stack TLC prints (`CallStack.freeze`).
                || call_stack.is_frozen
                    && !call_stack.frames.is_empty()
                    && matches!(site, Site::InitialInvariant(_) | Site::InitialPredicate(_))
                    && checked.is_some())
        {
            // An EvalException escapes `doInit` without the state, and the initial predicate
            // fails before `DoInitFunctor` has one, so TLC prints a general error around the
            // nested message.
            let (code, text, tool_text, state) = match &checked {
                Some(values) if !message.is_eval_exception => (
                    INITIAL_STATE,
                    message.text.clone(),
                    nested(message),
                    Some(state_texts(values)?),
                ),
                _ => (GENERAL, message.text.clone(), nested(message), None),
            };
            return Ok(Failure {
                code,
                message: text,
                tool_message: tool_text,
                call_stack: Vec::new(),
                exit_code: FAILURE_SPEC_EVAL,
                printed,
                fingerprint: Some(FingerprintFailure {
                    sources: fingerprint_ranges(evaluator, &call_stack),
                    reason: message.text.clone(),
                    tool_reason: nested(message),
                    is_replayed: true,
                    is_skipped_again: false,
                }),
                state,
                replay: Replay {
                    initial_states: is_initial_check_continued.then_some(initial_states),
                    ..Replay::default()
                },
            });
        }
        // A failure in the initial or next states whose receiver the replay gave a source TLC
        // reports as it is, then fails again as a FingerprintException as it replays the
        // computation with its `CallStackTool`, which gives values their sources, and prints that
        // call stack (`ModelChecker.modelCheckImpl`).
        let is_next_state = matches!(
            site,
            Site::Next | Site::ActionConstraint(_) | Site::Constraint(_)
        );
        if call_stack.is_fingerprinted
            && (site == Site::Init || is_next_state)
            && let Some(message) = &error.message
            && (!call_stack.fingerprinted_sources.is_empty()
                || call_stack.is_frozen_before_fingerprint)
        {
            // In a step, a failure through a union, an intersection, a difference or UNION over a
            // function set, a record set or a product holding a set enumeration TLC holds
            // unnormalized: TLC's trace goes on into that set enumeration, whose source the
            // holder's enumeration reads (`getNewHead`), which the replay doesn't follow.
            if site == Site::Next
                && (call_stack.is_unsorted_held_member
                    || ends_at_operator_over_holder(ir, &sources))
            {
                return Err(Unsupported(
                    "evaluating the failure again: a FingerprintException through a set a union's operand holds"
                        .into(),
                ));
            }
            let (code, text, tool_text) = report(message, is_next_state, error.runtime_exception);
            let sources = fingerprint_ranges(evaluator, &call_stack);
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
                    is_skipped_again: false,
                }),
                state: None,
                replay: Replay::default(),
            });
        }
        // TLC's rerun of an atom on a deadlocked state with its `CallStackTool` throws the
        // FingerprintException, which escapes `Worker#doNextCheckLiveness` to a report of the
        // error that finds the deadlock's already set: TLC prints nothing of it.
        if call_stack.is_fingerprinted
            && matches!(site, Site::DeadlockAtom { .. })
            && let Some(message) = &error.message
        {
            let (code, text, tool_text) = report(message, true, error.runtime_exception);
            return Ok(Failure {
                code,
                message: text,
                tool_message: tool_text,
                call_stack: Vec::new(),
                exit_code: FAILURE_ERROR,
                printed,
                fingerprint: Some(FingerprintFailure {
                    sources: fingerprint_ranges(evaluator, &call_stack),
                    reason: message.text.clone(),
                    tool_reason: nested(message),
                    is_replayed: true,
                    is_skipped_again: false,
                }),
                state: None,
                replay: Replay::default(),
            });
        }
        // TLC's rerun of an atom with its `CallStackTool` as it adds a state to the behavior graphs
        // throws the FingerprintException, which `Worker#doNextCheckLiveness` doesn't catch: it
        // prints no call stack, and leaves `keepCallStack` set, and `ModelChecker#doNextFailed`
        // reports it as a general error without a message (`getMessage` is null), then the trace,
        // and TLC replays the expansion as for any failure of an atom without a call stack.
        if call_stack.is_fingerprinted
            && call_stack.is_subscript_fingerprinted
            && !call_stack.fingerprinted_sources.is_empty()
            && matches!(site, Site::Atom { .. })
            && call_stack.unfollowed.is_none()
            && let Some(message) = &error.message
        {
            let (code, text, tool_text) = report(message, true, error.runtime_exception);
            return Ok(Failure {
                code,
                message: text,
                tool_message: tool_text,
                call_stack: Vec::new(),
                exit_code: FAILURE_ERROR,
                printed,
                fingerprint: Some(FingerprintFailure {
                    sources: fingerprint_ranges(evaluator, &call_stack),
                    reason: message.text.clone(),
                    tool_reason: nested(message),
                    is_replayed: true,
                    is_skipped_again: false,
                }),
                state: None,
                replay: Replay::default(),
            });
        }
        // TLC's search evaluates an invariant without the `CallStackTool`, whose values have no
        // source, so the failure is the one the evaluator gives where it follows it.
        if call_stack.is_fingerprinted
            && !(matches!(site, Site::Invariant(_)) && call_stack.is_member_followed)
        {
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
        // `doInit` without the state, so TLC prints it as a general error, whose status it exits
        // with.
        if let Site::InitialAtom { .. } = site {
            if message.is_eval_exception {
                return Ok(Failure {
                    code: GENERAL,
                    message: message.text.clone(),
                    tool_message: nested(&message),
                    call_stack: Vec::new(),
                    exit_code: FAILURE_ERROR,
                    printed,
                    fingerprint: None,
                    state: None,
                    replay: Replay::default(),
                });
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
            let state = state_texts(&values)?;
            // Where the replay fails again, TLC prints its call stack and exits as for it.
            let (call_stack, exit_code) = match replayed {
                Some((target, atom)) => (
                    replay_initial_atom(evaluator, store, target, atom, is_keyed_by_state)?,
                    FAILURE_SPEC_EVAL,
                ),
                // `EC.ExitStatus.errorConstantToExitStatus` of the error's code: an identifier
                // that is undefined is among the configuration's errors, and the other errors an
                // evaluation raises are general ones.
                None => (
                    Vec::new(),
                    match message.code {
                        Some(UNDEFINED_IDENTIFIER) => ERROR_CONFIG_PARSE,
                        _ => FAILURE_ERROR,
                    },
                ),
            };
            return Ok(Failure {
                code: INITIAL_STATE,
                message: message.text.clone(),
                tool_message: nested(&message),
                call_stack,
                exit_code,
                printed,
                fingerprint: None,
                state: Some(state),
                replay: Replay::default(),
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
            let state = match message.is_eval_exception {
                true => None,
                false => Some(state_texts(&values)?),
            };
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
                replay: Replay::default(),
            });
        }
        // TLC reports an invariant or an action property that fails to evaluate with a headline
        // of its own, and no call stack (`doNextEvalFailed`).
        if let Site::Invariant(_) | Site::ActionProperty(_) = site {
            let (code, headline) = match site {
                Site::ActionProperty(position) => {
                    let Some(property) = ir.model.action_properties.get(position as usize) else {
                        return Err(Unsupported(
                            "an action property the model doesn't have".into(),
                        ));
                    };
                    (
                        ACTION_PROPERTY_EVALUATION_FAILED,
                        format!(
                            "Evaluating action property {} failed.",
                            ir.texts[property.name as usize]
                        ),
                    )
                }
                Site::Invariant(position) => {
                    let Some(&(_, _, name)) = evaluator.tlc_invariants()?.get(position as usize)
                    else {
                        return Err(Unsupported("an invariant the model doesn't have".into()));
                    };
                    (
                        INVARIANT_EVALUATION_FAILED,
                        format!("Evaluating invariant {} failed.", ir.texts[name as usize]),
                    )
                }
                _ => unreachable!("an invariant or an action property"),
            };
            if !is_keyed_by_state {
                return Err(Unsupported(
                    "replaying the expansion under a VIEW or SYMMETRY".into(),
                ));
            }
            let Some(known) = known else {
                return Err(Unsupported(
                    "replaying the expansion without the fingerprints the search found".into(),
                ));
            };
            // TLC reports the message of the evaluation that failed, so what evaluating it again
            // printed isn't printed again; its replay skips the failing state, which it had
            // added to its set (`Worker#isSeenState`), and checks no invariant there.
            let replayed = replay_expansion(evaluator, path, &known)?;
            // The replay checks the action properties of the step again, which fails again
            // there, but where it stops before.
            if matches!(site, Site::ActionProperty(_)) && replayed.failure.is_none() {
                return Err(Unsupported(
                    "replaying the expansion: an action property that doesn't fail again".into(),
                ));
            }
            let printed = std::mem::take(&mut evaluator.printed);
            let (call_stack, fingerprint, exit_code) = match replayed.failure {
                None => (Vec::new(), None, FAILURE_SAFETY_EVAL),
                Some(ReplayFailure::Fingerprint(fingerprint)) => {
                    (Vec::new(), Some(fingerprint), FAILURE_SPEC_EVAL)
                }
                Some(ReplayFailure::Nested(call_stack, exit_code)) => (call_stack, None, exit_code),
            };
            return Ok(Failure {
                code,
                message: format!("{headline}\n{}", message.text),
                tool_message: format!("{headline}\n{}", nested(&message)),
                call_stack,
                exit_code,
                printed,
                fingerprint,
                state: None,
                replay: replayed.replay,
            });
        }
        // TLC reports an error adding a state to the behavior graphs as one in the next states
        // (`Worker#doNextCheckLiveness`), and exits on an exception it didn't expect as for any.
        let is_atom = matches!(site, Site::Atom { .. } | Site::DeadlockAtom { .. });
        let (code, text, tool_text) =
            report(&message, is_next_state || is_atom, error.runtime_exception);
        Ok(Failure {
            code,
            message: text,
            tool_message: tool_text,
            call_stack: ranges(evaluator, &call_stack),
            // A failed assertion in the next states exits as one, and any other error, or any
            // in the initial predicate, as the failure of the replay (`getFailureExitCode`).
            exit_code: match (site, message.code) {
                (
                    Site::Next
                    | Site::ActionConstraint(_)
                    | Site::Constraint(_)
                    | Site::Atom { .. }
                    | Site::DeadlockAtom { .. },
                    Some(ASSERT_FAILED),
                ) => VIOLATION_ASSERT,
                // TLC's replay of the expansion, and an error adding a state to the behavior
                // graphs, exit by an EvalException's code (`errorConstantToExitStatus`): an
                // undefined identifier is among the configuration's errors, and the others are
                // general ones.
                (
                    Site::Next
                    | Site::ActionConstraint(_)
                    | Site::Constraint(_)
                    | Site::Atom { .. }
                    | Site::DeadlockAtom { .. },
                    Some(UNDEFINED_IDENTIFIER),
                ) if message.is_eval_exception => ERROR_CONFIG_PARSE,
                (Site::Next | Site::ActionConstraint(_) | Site::Constraint(_), _)
                    if local_normalization =>
                {
                    FAILURE_SPEC_EVAL
                }
                (Site::Next | Site::ActionConstraint(_) | Site::Constraint(_), _)
                    if message.is_eval_exception =>
                {
                    FAILURE_ERROR
                }
                _ if is_atom => FAILURE_ERROR,
                _ => FAILURE_SPEC_EVAL,
            },
            printed,
            fingerprint: None,
            state: None,
            replay: Replay::default(),
        })
    }
}

// The call stack TLC prints with a FingerprintException its replay threw: the nodes it was in,
// then the sources of the values whose methods the failure passed through, outermost first
// (`CallStack.freeze`), a node that repeats the one before it once.
// TLC's replay of the initial states with its `CallStackTool` adds the initial states its first
// pass didn't find to the behavior graphs, and fails again evaluating `position` of the model's
// atoms on `target`, within the frames of the initial predicate that found it
// (`ModelChecker#doInit`): the call stack it prints.
fn replay_initial_atom(
    evaluator: &mut Evaluator<'_>,
    store: &Store,
    target: &[Id],
    position: u32,
    is_keyed_by_state: bool,
) -> Result<Vec<SourceRange>, Unsupported> {
    let ir = evaluator.ir;
    let Some(atom) = ir.model.atoms.get(position as usize) else {
        return Err(Unsupported("an atom the model doesn't have".into()));
    };
    let width = ir.variables.len();
    evaluator.printed.clear();
    evaluator.call_stack = Some(CallStack::default());
    evaluator.current = vec![None; width];
    evaluator.next = vec![None; width];
    evaluator.level = 0;
    let context = evaluator.scope_context(ir.model.scope);
    // What of the replay outside the atom isn't followed.
    let mut unfollowed: Option<&'static str> = None;
    let result = context.and_then(|context| {
        evaluator.walk_action(ir.model.init, &context, true, &mut |evaluator| {
            let values: Option<Vec<Value>> = evaluator.current.iter().cloned().collect();
            if !values.is_some_and(|values| is_same(store, target, &values)) {
                // The replay forces the checks of each initial state before the target, which
                // print again what they printed.
                if let Err(reason) = evaluator.check_replayed_initial(true, is_keyed_by_state) {
                    unfollowed.get_or_insert(reason);
                }
                return Ok(true);
            }
            // `DoInitFunctor` evaluates the constraints of the target before it adds the state
            // to the behavior graphs, which it adds only where they hold.
            let call_stack = evaluator.call_stack.take();
            evaluator.level = 1;
            for constraint in &ir.model.constraints {
                let holds = match constraint.definition {
                    Some(index) => {
                        let body = evaluator.definition(ir.definitions[index as usize]).body;
                        constraint_holds(evaluator, body)
                    }
                    None => fail("a constraint the model doesn't define"),
                };
                if !matches!(holds, Ok(true)) {
                    unfollowed.get_or_insert("a target the constraints exclude or fail on");
                }
            }
            evaluator.call_stack = call_stack;
            let context = evaluator.scope_context(atom.scope)?;
            match atom.kind {
                AtomKind::State => evaluator.boolean(atom.expression, &context),
                AtomKind::Enabled { .. } => evaluator
                    .enabled(atom.expression, &context)
                    .map(|value| matches!(value, Value::Bool(true))),
                AtomKind::Action { .. } => fail("an action TLC evaluates of an initial state"),
            }
        })
    });
    let call_stack = evaluator.call_stack.take().unwrap_or_default();
    if let Some(reason) = unfollowed {
        return Err(Unsupported(format!(
            "evaluating the failure again: {reason}"
        )));
    }
    if result.is_ok() {
        return Err(Unsupported(
            "evaluating the failure again: TLC's replay of the initial states doesn't fail".into(),
        ));
    }
    if let Some(reason) = call_stack
        .unfollowed
        .or(call_stack.is_substituted.then_some(SUBSTITUTED_FRAMES))
    {
        return Err(Unsupported(format!(
            "evaluating the failure again: {reason}"
        )));
    }
    if !evaluator.printed.is_empty()
        || call_stack.is_unsorted
        || call_stack.is_fingerprinted
        || call_stack.fingerprint.is_some()
    {
        return Err(Unsupported(
            "evaluating the failure again: TLC's replay of the initial states prints or fingerprints"
                .into(),
        ));
    }
    Ok(ranges(evaluator, &call_stack))
}

// TLC's report of a failure, which declines where the evaluator wrote the text of a null as it
// found it (`print::null_prints`), or the operation of a lazy set that fails to expand
// (`print::unexpanded_prints`): TLC fails printing it otherwise.
fn without_null_prints<T>(
    what: &str,
    report: impl FnOnce() -> Result<T, Unsupported>,
) -> Result<T, Unsupported> {
    let null_prints = crate::print::null_prints();
    let unexpanded_prints = crate::print::unexpanded_prints();
    let failure = report()?;
    if crate::print::null_prints() != null_prints {
        return Err(Unsupported(format!(
            "{what}: a message that prints a value TLC never initialized"
        )));
    }
    // A lazy set whose `toString` throws, where TLC may print it.
    if crate::print::unexpanded_prints() != unexpanded_prints {
        return Err(Unsupported(format!(
            "{what}: a message that prints a lazy set TLC fails to expand"
        )));
    }
    Ok(failure)
}

// A state TLC fails to print, normalizing a set it can't sort as it writes it.
const UNPRINTABLE_STATE: &str = "a state that holds a set TLC fails to sort as it prints it";

// The texts of a state's values as TLC prints them, where it prints them without normalizing a set
// it can't sort (`SetEnumValue.toString`), which fails there.
fn state_texts(values: &[Value]) -> Result<Vec<String>, Unsupported> {
    let printed_unsorted = crate::print::unsorted_prints();
    let texts = values.iter().map(format_value).collect();
    if crate::print::unsorted_prints() != printed_unsorted {
        return Err(Unsupported(format!(
            "evaluating the failure again: {UNPRINTABLE_STATE}"
        )));
    }
    Ok(texts)
}

fn fingerprint_ranges(evaluator: &Evaluator<'_>, call_stack: &CallStack) -> Vec<SourceRange> {
    let mut sources = ranges(evaluator, call_stack);
    for &source in &call_stack.fingerprinted_sources {
        if let Some(range) = node_range(evaluator, source)
            && sources.last() != Some(&range)
        {
            sources.push(range);
        }
    }
    sources
}

// What TLC's replay of an expansion found, and how it failed where it did: as a
// FingerprintException, or with the nested expressions and the status TLC exits with.
struct Replayed {
    replay: Replay,
    failure: Option<ReplayFailure>,
}

enum ReplayFailure {
    Fingerprint(FingerprintFailure),
    Nested(Vec<SourceRange>, i32),
}

// What TLC's replay of the expansion reports where a check fails again within its call stack.
fn replay_failed(
    evaluator: &mut Evaluator<'_>,
    error: EvalError,
    mut replay: Replay,
) -> Result<Replayed, Unsupported> {
    let unsupported = |reason: &str| Err(Unsupported(format!("replaying the expansion: {reason}")));
    let call_stack = evaluator.call_stack.take().unwrap_or_default();
    if let Some(reason) = call_stack
        .unfollowed
        .or(call_stack.is_substituted.then_some(SUBSTITUTED_FRAMES))
    {
        return unsupported(reason);
    }
    if call_stack.is_unsorted || call_stack.fingerprint.is_some() {
        return unsupported("a set TLC leaves unnormalized");
    }
    let Some(message) = error.message else {
        return unsupported(&error.reason);
    };
    replay.is_failed = true;
    let failure = if call_stack.is_fingerprinted {
        if !call_stack.is_member_followed {
            return unsupported("a FingerprintException the replay throws");
        }
        ReplayFailure::Fingerprint(FingerprintFailure {
            sources: fingerprint_ranges(evaluator, &call_stack),
            reason: message.text.clone(),
            tool_reason: nested(&message),
            is_replayed: true,
            is_skipped_again: false,
        })
    } else {
        // TLC exits by the code of an EvalException, and by that of the nested expressions it
        // prints for any other error.
        ReplayFailure::Nested(
            ranges(evaluator, &call_stack),
            match message.code {
                Some(ASSERT_FAILED) => VIOLATION_ASSERT,
                _ if message.is_eval_exception => FAILURE_ERROR,
                _ => FAILURE_SPEC_EVAL,
            },
        )
    };
    Ok(Replayed {
        replay,
        failure: Some(failure),
    })
}

// Whether the action property at `position` holds of the evaluator's step, as TLC's
// `Tool.isValid` evaluates its `[A]_v` (`OPCODE_sa`): the box action's node is the call stack's
// first frame. `Unsupported` where the IR doesn't place that node.
fn action_property_holds(
    evaluator: &mut Evaluator<'_>,
    position: u32,
) -> Result<Evaluated<bool>, Unsupported> {
    let ir = evaluator.ir;
    let Some(property) = ir.model.action_properties.get(position as usize) else {
        return Err(Unsupported(
            "an action property the model doesn't have".into(),
        ));
    };
    let nodes = &ir.nodes.arena;
    let (action_range, subscript_range) = (
        nodes[property.action as usize].range,
        nodes[property.subscript as usize].range,
    );
    // The front keeps the box action's node, of the same source as the property's action and
    // subscript, for its range alone.
    let mut wrappers = nodes
        .iter()
        .enumerate()
        .filter_map(|(id, node)| match node.kind {
            NodeKind::BoxAction { action, subscript }
                if action_range.is_some()
                    && nodes[action as usize].range == action_range
                    && nodes[subscript as usize].range == subscript_range =>
            {
                node.range.map(|range| (id as NodeId, range))
            }
            _ => None,
        });
    let Some((wrapper, range)) = wrappers.next() else {
        return Err(Unsupported(
            "an action property whose box action has no place".into(),
        ));
    };
    if wrappers.any(|(_, other)| other != range) {
        return Err(Unsupported(
            "an action property whose box action has two places".into(),
        ));
    }
    let context = match evaluator.scope_context(property.scope) {
        Ok(context) => context,
        Err(error) => return Ok(Err(error)),
    };
    let (action, subscript) = (property.action, property.subscript);
    Ok(
        evaluator.in_frame(StackFrame::Node(wrapper), &mut |evaluator| {
            if evaluator.boolean_as(action, &context, Demand::SquareAction(wrapper))? {
                return Ok(true);
            }
            match evaluator.unchanged(subscript, &context)? {
                Value::Bool(holds) => Ok(holds),
                _ => unreachable!("UNCHANGED is a boolean"),
            }
        }),
    )
}

// TLC's replay of the expansion of the state before the path's last, after an invariant failed to
// evaluate on the last (`ModelChecker.doNext` with the `CallStackTool`): each action's successors
// in turn, each in the model fingerprinted and skipped where TLC's set of fingerprints has it,
// and the invariants checked of each it lacks. TLC's error is already set, so a violation ends
// the replay quietly, and only an evaluation that fails is reported.
fn replay_expansion(
    evaluator: &mut Evaluator<'_>,
    mut path: Vec<Vec<Value>>,
    known: &[u64],
) -> Result<Replayed, Unsupported> {
    let ir = evaluator.ir;
    let unsupported = |reason: &str| Err(Unsupported(format!("replaying the expansion: {reason}")));
    path.pop();
    let Some(predecessor) = path.last() else {
        return unsupported("no state to expand");
    };
    let predecessor: Vec<Option<Value>> = predecessor.iter().cloned().map(Some).collect();
    let level = path.len() as i32;
    let invariants = evaluator.tlc_invariants()?;
    evaluator.call_stack = Some(CallStack::default());
    let Ok(actions) = evaluator.tlc_actions() else {
        return unsupported("the next-state relation doesn't split");
    };
    let width = ir.variables.len();
    let mut fingerprints = Fingerprints::new(Polynomial::get(ir.model.fingerprint_index));
    let mut found: Vec<u64> = Vec::new();
    let mut replay = Replay::default();
    for (expression, context) in actions {
        // TLC computes every successor by the action before it checks the first.
        evaluator.current = predecessor.clone();
        evaluator.next = vec![None; width];
        evaluator.level = level;
        let mut successors = Vec::new();
        let walked = evaluator.walk_action(expression, &context, false, &mut |evaluator| {
            successors.push(evaluator.next.clone());
            Ok(true)
        });
        if walked.is_err() {
            return unsupported("the next states fail");
        }
        for successor in successors {
            let Some(successor) = successor.into_iter().collect::<Option<Vec<Value>>>() else {
                return unsupported("a successor that isn't complete");
            };
            path.push(successor);
            let is_in_model = is_in_model(evaluator, &path)?;
            let successor = path.pop().expect("the successor");
            let is_unseen = if is_in_model {
                if successor
                    .iter()
                    .any(|value| !matches!(fingerprint_failure(value), Ok(None)))
                {
                    return unsupported("a successor TLC fails to fingerprint");
                }
                let ordered: Vec<&Value> = ir
                    .tlc_order
                    .iter()
                    .map(|&position| &successor[position as usize])
                    .collect();
                let Some(fingerprint) = state_fingerprint(&mut fingerprints, &ordered) else {
                    return unsupported("a successor whose fingerprint the evaluator can't tell");
                };
                let is_unseen =
                    known.binary_search(&fingerprint).is_err() && !found.contains(&fingerprint);
                if is_unseen {
                    found.push(fingerprint);
                    replay.found += 1;
                }
                is_unseen
            } else {
                true
            };
            let successor: Vec<Option<Value>> = successor.into_iter().map(Some).collect();
            evaluator.current = successor.clone();
            evaluator.next = vec![None; width];
            evaluator.level = level + 1;
            // TLC checks the invariants of a successor it hadn't seen, then the action properties
            // of every step (`ModelChecker.doNext`).
            let invariants = if is_unseen { &invariants[..] } else { &[] };
            for &(invariant, scope, _) in invariants {
                let Ok(context) = evaluator.scope_context(scope) else {
                    return unsupported("an invariant's scope");
                };
                // One TLC computed as it started it doesn't check (`startup_check`).
                match evaluator.startup_check(invariant) {
                    Ok(None) => {}
                    Ok(Some(Value::Bool(true))) => continue,
                    _ => return unsupported("an invariant TLC computed as it started"),
                }
                match evaluator.boolean_as(invariant, &context, Demand::Invariant) {
                    Ok(true) => {}
                    Ok(false) => {
                        return Ok(Replayed {
                            replay,
                            failure: None,
                        });
                    }
                    Err(error) => return replay_failed(evaluator, error, replay),
                }
            }
            if !ir.model.action_properties.is_empty() {
                evaluator.current = predecessor.clone();
                evaluator.next = successor;
                evaluator.level = level;
            }
            for position in 0..ir.model.action_properties.len() {
                match action_property_holds(evaluator, position as u32)? {
                    Ok(true) => {}
                    // TLC's replay stops at a violated action property, or under -continue
                    // prints it and goes on, which isn't followed.
                    Ok(false) => {
                        return unsupported("an action property the replay finds violated");
                    }
                    Err(error) => return replay_failed(evaluator, error, replay),
                }
            }
            if is_in_model && is_unseen {
                replay.queued += 1;
            }
        }
    }
    Ok(Replayed {
        replay,
        failure: None,
    })
}

// TLC's replay of the expansion of the state before the path's last, after an action constraint
// failed to evaluate on the step to the last (`ModelChecker.doNext` with the `CallStackTool`):
// each action's successors in turn, checked as `doNext` checks them, until the step to the last,
// where the action constraint at `position` fails again within the call stack. Each successor in
// the model before it is one TLC's worker added to its set of fingerprints, so it checks nothing
// more of it, and the invariants hold of each outside the model, or TLC's worker would have
// stopped there.
/// The check of a successor that failed to evaluate: a constraint or an action constraint, by
/// its position among the model's.
#[derive(Clone, Copy, PartialEq, Eq)]
enum SuccessorCheck {
    State(u32),
    Action(u32),
}

fn replay_successor_check(
    evaluator: &mut Evaluator<'_>,
    path: &[Vec<Value>],
    check: SuccessorCheck,
) -> Result<Evaluated<bool>, Unsupported> {
    let ir = evaluator.ir;
    let unsupported = |reason: &str| Err(Unsupported(format!("replaying the expansion: {reason}")));
    if !ir.model.action_properties.is_empty() {
        return unsupported("a property TLC checks of each step");
    }
    let [.., predecessor, target] = path else {
        return unsupported("no state to expand");
    };
    let bodies = |evaluator: &Evaluator<'_>, names: &[tla_ir::ConfigName]| {
        names
            .iter()
            .map(|name| {
                name.definition
                    .map(|index| evaluator.definition(ir.definitions[index as usize]).body)
            })
            .collect::<Option<Vec<NodeId>>>()
    };
    let (Some(constraints), Some(action_constraints)) = (
        bodies(evaluator, &ir.model.constraints),
        bodies(evaluator, &ir.model.action_constraints),
    ) else {
        return unsupported("a constraint without a definition");
    };
    let is_present = match check {
        SuccessorCheck::State(position) => (position as usize) < constraints.len(),
        SuccessorCheck::Action(position) => (position as usize) < action_constraints.len(),
    };
    if !is_present {
        return unsupported("a constraint the model doesn't have");
    }
    let invariants = evaluator.tlc_invariants()?;
    let Ok(actions) = evaluator.tlc_actions() else {
        return unsupported("the next-state relation doesn't split");
    };
    let width = ir.variables.len();
    let level = path.len() as i32 - 1;
    let mut fingerprints = Fingerprints::new(Polynomial::get(ir.model.fingerprint_index));
    let mut fingerprint = |state: &[Value]| {
        let ordered: Vec<&Value> = ir
            .tlc_order
            .iter()
            .map(|&position| &state[position as usize])
            .collect();
        state_fingerprint(&mut fingerprints, &ordered)
    };
    let Some(target) = fingerprint(target) else {
        return unsupported("a successor whose fingerprint the evaluator can't tell");
    };
    let state = |values: &[Value]| values.iter().cloned().map(Some).collect::<Vec<_>>();
    let predecessor = state(predecessor);
    for (expression, context) in actions {
        // TLC computes every successor by the action before it checks the first.
        evaluator.current = predecessor.clone();
        evaluator.next = vec![None; width];
        evaluator.level = level;
        let mut successors = Vec::new();
        let walked = evaluator.walk_action(expression, &context, false, &mut |evaluator| {
            successors.push(evaluator.next.clone());
            Ok(true)
        });
        if walked.is_err() {
            return unsupported("the next states fail");
        }
        for successor in successors {
            let Some(successor) = successor.into_iter().collect::<Option<Vec<Value>>>() else {
                return unsupported("a successor that isn't complete");
            };
            let is_target = fingerprint(&successor) == Some(target);
            // TLCGet("level") reads the successor's level in a constraint, and its
            // predecessor's in an action constraint.
            evaluator.current = state(&successor);
            evaluator.next = vec![None; width];
            evaluator.level = level + 1;
            let mut is_in_model = true;
            for (index, &constraint) in constraints.iter().enumerate() {
                if is_target && check == SuccessorCheck::State(index as u32) {
                    return Ok(traced_constraint_holds(evaluator, constraint));
                }
                if !run(constraint_holds(evaluator, constraint))? {
                    is_in_model = false;
                    break;
                }
            }
            if is_in_model {
                evaluator.current = predecessor.clone();
                evaluator.next = state(&successor);
                evaluator.level = level;
                for (index, &constraint) in action_constraints.iter().enumerate() {
                    if is_target && check == SuccessorCheck::Action(index as u32) {
                        return Ok(traced_constraint_holds(evaluator, constraint));
                    }
                    if !run(constraint_holds(evaluator, constraint))? {
                        is_in_model = false;
                        break;
                    }
                }
            }
            if is_target {
                return unsupported("the step to the successor that failed holds");
            }
            if is_in_model {
                if successor
                    .iter()
                    .any(|value| !matches!(fingerprint_failure(value), Ok(None)))
                {
                    return unsupported("a successor TLC fails to fingerprint");
                }
                continue;
            }
            evaluator.current = state(&successor);
            evaluator.next = vec![None; width];
            evaluator.level = level + 1;
            for &(invariant, scope, _) in &invariants {
                let context = run(evaluator.scope_context(scope))?;
                if !run(evaluator.check_holds(invariant, &context))? {
                    return unsupported("a successor outside the model that violates an invariant");
                }
            }
        }
    }
    unsupported("no step to the successor that failed")
}

// The ranges of the call stack's nodes, as `CallStack.toString` prints them: a node TLC evaluates
// again right inside itself once, and nothing for a node without a range.
fn ranges(evaluator: &Evaluator<'_>, call_stack: &CallStack) -> Vec<SourceRange> {
    let mut ranges = Vec::new();
    let mut previous = None;
    for (position, &frame) in call_stack.frames.iter().enumerate() {
        if previous == Some(frame) {
            continue;
        }
        previous = Some(frame);
        let range = match frame {
            StackFrame::Node(node) => node_range(evaluator, node),
            StackFrame::Prefix(node, count) => prefix_range(evaluator, node, count),
        };
        ranges.extend(range);
        // The frame of a copy's `SubstInNode`, after the one that names the copy.
        ranges.extend(
            (call_stack.substitution_frames.iter())
                .filter(|(after, _)| *after == position)
                .map(|(_, range)| *range),
        );
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
    // The conjunction of the specification's initial predicates is the IR's own, written
    // nowhere: TLC evaluates each predicate by itself (`SpecProcessor.processConfigSpec`).
    if arena[node as usize].line == 0 {
        return None;
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

impl<'ir> Evaluator<'ir> {
    // TLC's invariants, in the order it checks them: the model's, then its properties checked as
    // invariants, each with the scope it is read in and the name TLC reports it by.
    fn tlc_invariants(&self) -> Result<Vec<(NodeId, Option<tla_ir::Index>, TextId)>, Unsupported> {
        let ir = self.ir;
        let mut invariants = Vec::new();
        for invariant in &ir.model.invariants {
            let Some(index) = invariant.root.definition else {
                return Err(Unsupported("an invariant the model doesn't define".into()));
            };
            invariants.push((
                self.definition(ir.definitions[index as usize]).body,
                None,
                invariant.root.name,
            ));
        }
        let properties = ir
            .model
            .property_invariants
            .iter()
            .zip(&ir.model.property_invariant_scopes)
            .zip(&ir.model.property_invariant_names);
        invariants
            .extend(properties.map(|((invariant, &scope), &name)| (invariant.root, scope, name)));
        Ok(invariants)
    }

    // The value TLC computed as it started of a check whose body is that of a constant
    // definition it computed then (`processConstantDefns`): TLC holds the value in place of the
    // definition, so `processConfigInvariants` and `processModelConstraints` drop a TRUE one
    // (warning 2149 of an invariant), reject any other before the search, and no state checks it
    // again, nor prints what it printed. None for any other check, and for a definition that
    // failed there, which TLC keeps as an operator and evaluates again in each state. Where the
    // evaluator wasn't told which failed, a startup definition it holds no value of declines.
    pub(crate) fn startup_check(&mut self, body: NodeId) -> Evaluated<Option<Value>> {
        let ir = self.ir;
        let node = ir
            .model
            .startup
            .definitions
            .iter()
            .map(|&index| ir.definitions[index as usize])
            .find(|&node| self.definition(node).body == body);
        let Some(node) = node else {
            return Ok(None);
        };
        if let Some(value) = self.cache.get(&(node, false)) {
            return Ok(Some(value.clone()));
        }
        if !self.is_startup_known || self.uncomputed_warning_startup.contains(&node) {
            return fail("a check TLC may have computed as it started");
        }
        if self.failed_startup.contains(&node) {
            return Ok(None);
        }
        match &self.definition(node).form {
            DefinitionForm::Operator(params) if params.is_empty() => Ok(Some(Value::Bool(true))),
            _ => fail("a check TLC may have computed as it started"),
        }
    }

    // Whether a check holds of the state, which TLC doesn't evaluate where it computed it as it
    // started (`startup_check`).
    pub(crate) fn check_holds(&mut self, body: NodeId, context: &Context) -> Evaluated<bool> {
        match self.startup_check(body)? {
            Some(Value::Bool(holds)) => Ok(holds),
            Some(_) => fail("a check TLC computed as it started that isn't a boolean"),
            None => self.boolean(body, context),
        }
    }

    // TLC's actions, which the IR holds.
    fn tlc_actions(&mut self) -> Evaluated<Vec<(NodeId, Context)>> {
        let actions = &self.ir.model.actions;
        // `add_actions` splits the relation as TLC does; a model it couldn't split has none.
        if actions.is_empty() {
            return fail("a next-state relation the IR holds no actions of");
        }
        actions
            .iter()
            .map(|action| {
                self.scope_context(action.scope)
                    .map(|context| (action.expression, context))
            })
            .collect()
    }

    // TLC fingerprints each state its replay finds (`fingerprintReplayed`), outside any
    // evaluation: where that fails, the failure is the FingerprintException of the values it
    // fails in. A state whose fingerprint the evaluator can't tell stops the replay.
    fn fingerprint_found(&mut self, is_init: bool) -> Evaluated<bool> {
        let model = &self.ir.model;
        // `DoInitFunctor` fingerprints an initial state only where the constraints hold of it
        // (`isInModel`), as its replay finds the state.
        if is_init && !model.constraints.is_empty() {
            let level = std::mem::replace(&mut self.level, 1);
            let call_stack = self.call_stack.take();
            let printed = self.printed.len();
            let mut holds = Ok(true);
            for constraint in &model.constraints {
                holds = match constraint.definition {
                    Some(index) => {
                        let body = self.definition(self.ir.definitions[index as usize]).body;
                        constraint_holds(self, body)
                    }
                    None => fail("a constraint the model doesn't define"),
                };
                if !matches!(holds, Ok(true)) {
                    break;
                }
            }
            self.call_stack = call_stack;
            self.level = level;
            // TLC evaluated the constraints of the state as it found it before the replay, where
            // the search stopped first.
            if self.printed.len() != printed
                && let Some(stack) = &mut self.call_stack
            {
                stack
                    .unfollowed
                    .get_or_insert("a constraint that prints as TLC replays the initial states");
            }
            match holds {
                Ok(true) => {}
                Ok(false) => return Ok(true),
                Err(error) => {
                    if let Some(stack) = &mut self.call_stack {
                        stack.unfollowed.get_or_insert(
                            "a constraint that fails as TLC replays the initial states",
                        );
                    }
                    return Err(error);
                }
            }
        }
        let found = self.fingerprint_state(is_init);
        // TLC's worker fingerprints a successor only where the constraints hold of it, which
        // the replay doesn't evaluate here.
        if found.is_err()
            && !is_init
            && (!model.constraints.is_empty() || !model.action_constraints.is_empty())
            && let Some(stack) = &mut self.call_stack
        {
            stack
                .unfollowed
                .get_or_insert("a state TLC fingerprints only where its constraints hold");
        }
        found
    }

    // TLC's replay of the initial states for the call stack (`ModelChecker.doInit(cTool, true)`)
    // forces the checks of `DoInitFunctor.addElement`: of each initial state it finds before the
    // one that fails again, the duplicates the first pass skipped among them, it evaluates the
    // constraints (`isInModel`), fingerprints the state where they hold, then checks every
    // invariant and every implied init, which print again what they printed in the first pass.
    // `with_constraints` is false where `fingerprint_found` evaluated the constraints and
    // fingerprinted the state already. Each check held of the state in the first pass; one that
    // doesn't hold or fails here, or a VIEW that prints, isn't followed.
    fn check_replayed_initial(
        &mut self,
        with_constraints: bool,
        is_keyed_by_state: bool,
    ) -> Result<(), &'static str> {
        let ir = self.ir;
        let model = &ir.model;
        let level = std::mem::replace(&mut self.level, 1);
        let call_stack = self.call_stack.take();
        let checked = (|| -> Result<(), &'static str> {
            const FAILED: &str = "a check that fails as TLC replays the initial states";
            const VIOLATED: &str = "a check that doesn't hold as TLC replays the initial states";
            if with_constraints {
                let mut is_in_model = true;
                for constraint in &model.constraints {
                    let Some(index) = constraint.definition else {
                        return Err(FAILED);
                    };
                    let body = self.definition(ir.definitions[index as usize]).body;
                    match constraint_holds(self, body) {
                        Ok(true) => {}
                        Ok(false) => {
                            is_in_model = false;
                            break;
                        }
                        Err(_) => return Err(FAILED),
                    }
                }
                if is_in_model {
                    if is_keyed_by_state {
                        self.current.iter().flatten().for_each(settle);
                    }
                    if let Some(view) = &model.view {
                        let Some(index) = view.definition else {
                            return Err(FAILED);
                        };
                        let body = self.definition(ir.definitions[index as usize]).body;
                        let printed = self.printed.len();
                        if self.evaluate(body, &Context::default()).is_err() {
                            return Err(FAILED);
                        }
                        if self.printed.len() != printed {
                            return Err("a VIEW that prints as TLC replays the initial states");
                        }
                    }
                }
            }
            let invariants = self.tlc_invariants().map_err(|_| FAILED)?;
            for (body, scope, _) in invariants {
                let context = self.scope_context(scope).map_err(|_| FAILED)?;
                match self.check_holds(body, &context) {
                    Ok(true) => {}
                    Ok(false) => return Err(VIOLATED),
                    Err(_) => return Err(FAILED),
                }
            }
            for (&predicate, &scope) in model
                .initial_predicates
                .iter()
                .zip(&model.initial_predicate_scopes)
            {
                let context = self.scope_context(scope).map_err(|_| FAILED)?;
                match self.check_holds(predicate, &context) {
                    Ok(true) => {}
                    Ok(false) => return Err(VIOLATED),
                    Err(_) => return Err(FAILED),
                }
            }
            Ok(())
        })();
        self.call_stack = call_stack;
        self.level = level;
        checked
    }

    fn fingerprint_state(&mut self, is_init: bool) -> Evaluated<bool> {
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
                    // `CallStackTool.eval` copies a `SetPredValue` without its source.
                    let sources: Vec<_> = chain
                        .iter()
                        .filter(|value| !is_filter(value))
                        .filter_map(|value| stack.source(value))
                        .collect();
                    let printed_unsorted = crate::print::unsorted_prints();
                    let texts = state
                        .iter()
                        .map(|value| value.as_ref().map(format_value).unwrap_or_default())
                        .collect();
                    // TLC prints the state it fails to fingerprint, which fails again where it
                    // normalizes a set it can't sort (`SetEnumValue.toString`), within a lazy
                    // set's text too: TLC then reports an exception it didn't expect.
                    if crate::print::unsorted_prints() != printed_unsorted {
                        stack.unfollowed.get_or_insert(UNPRINTABLE_STATE);
                        return fail(UNPRINTABLE_STATE);
                    }
                    if chain.iter().all(is_filter)
                        || sources.is_empty()
                            && chain.iter().any(|value| {
                                matches!(value,
                            Value::Lazy(lazy) if matches!(***lazy, Lazy::Any))
                            })
                    {
                        // A filter fails as a plain exception, in the frames the replay is in,
                        // which TLC's worker reports otherwise than `DoInitFunctor` does.
                        if !is_init {
                            stack
                                .unfollowed
                                .get_or_insert("a successor that fails to fingerprint a filter");
                        }
                        stack.fingerprint = Some((Vec::new(), texts));
                    } else if sources.is_empty() {
                        stack
                            .unfollowed
                            .get_or_insert("a fingerprint of values without sources");
                    } else {
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

fn is_filter(value: &Value) -> bool {
    matches!(value, Value::Lazy(lazy) if matches!(***lazy, Lazy::Filter(..)))
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
// Whether a constraint holds, evaluated within the call stack TLC's `CallStackTool` keeps. A
// constraint that isn't a boolean fails once evaluated (`Tool.isInModel`, `Tool.isInActions`),
// outside the frames of its evaluation.
fn traced_constraint_holds(evaluator: &mut Evaluator<'_>, body: NodeId) -> Evaluated<bool> {
    let depth = evaluator
        .call_stack
        .as_ref()
        .map(|stack| (stack.frames.len(), stack.is_frozen));
    if let Some(value) = evaluator.startup_check(body)? {
        return constraint_value_holds(evaluator, body, value);
    }
    let value = evaluator.evaluate(body, &Context::default())?;
    if let (Some(stack), Some((depth, is_frozen))) = (&mut evaluator.call_stack, depth)
        && !stack.is_fingerprinted
    {
        stack.frames.truncate(depth);
        stack.is_frozen = is_frozen;
    }
    constraint_value_holds(evaluator, body, value)
}

fn constraint_holds(evaluator: &mut Evaluator<'_>, body: NodeId) -> Evaluated<bool> {
    let value = match evaluator.startup_check(body)? {
        Some(value) => value,
        None => evaluator.evaluate(body, &Context::default())?,
    };
    constraint_value_holds(evaluator, body, value)
}

// Whether a constraint's value says it holds, or TLC's failure where it isn't a boolean.
fn constraint_value_holds(
    evaluator: &mut Evaluator<'_>,
    body: NodeId,
    value: Value,
) -> Evaluated<bool> {
    let node = &evaluator.ir.nodes.arena[body as usize];
    match value {
        Value::Bool(holds) => Ok(holds),
        // `Tool.eval` gives a literal the value its tool object holds, which
        // `processModelConstraints` replaced with the constraint's `OpDefNode`: TLC fails with a
        // ClassCastException, whose message names the JVM's classes.
        _ if matches!(
            node.kind,
            NodeKind::Number(_)
                | NodeKind::WideNumber(_)
                | NodeKind::Decimal(_)
                | NodeKind::String(_)
        ) =>
        {
            fail("a constraint that is a literal, which TLC fails to cast")
        }
        _ if node.range.is_some() => fail_with(
            "a constraint that isn't a boolean",
            TlcMessage {
                text: format!(
                    "TLC expected a boolean value, but did not find one. {}",
                    evaluator.describe_range(body)
                ),
                code: Some(EXPECTED_VALUE),
                is_eval_exception: false,
                inner: None,
            },
        ),
        _ => fail("a constraint that isn't a boolean, without a range"),
    }
}

impl<'ir> Rebuilder<'ir> {
    /// Takes that TLC simulates the model, whose run TLCGet reads otherwise.
    pub fn set_simulation(&mut self) {
        self.evaluator().is_simulation = true;
    }

    /// Evaluates again where TLC's simulator failed, at `site`, after the path `states` (as for
    /// `rebuild`; none for the initial predicate), and returns TLC's error: `Init`, an initial
    /// state's `InitialInvariant` or `InitialConstraint`, `Next` in the model's action at
    /// `action`, or a successor's `Invariant` or `ActionProperty`. The simulator evaluates with
    /// `Tool`, whose values have no source, in the order `Simulator.simulate` and
    /// `SimulationWorker.addElement` check a state. `Unsupported` where the evaluator doesn't give
    /// TLC's message, where the evaluation doesn't fail again, and where it prints as it fails.
    pub fn evaluate_simulated_failure(
        &mut self,
        store: &Store,
        states: &[&[Id]],
        actions: &[Option<u32>],
        site: Site,
        action: Option<u32>,
    ) -> Result<SimulatedFailure, Unsupported> {
        without_null_prints("evaluating the simulation's failure again", || {
            self.evaluate_simulated(store, states, actions, site, action)
        })
    }

    fn evaluate_simulated(
        &mut self,
        store: &Store,
        states: &[&[Id]],
        actions: &[Option<u32>],
        site: Site,
        action: Option<u32>,
    ) -> Result<SimulatedFailure, Unsupported> {
        let unsupported = |reason: &str| {
            Err(Unsupported(format!(
                "evaluating the simulation's failure again: {reason}"
            )))
        };
        if self.evaluator().is_174() {
            return unsupported("TLC 1.7.4");
        }
        let is_initial = matches!(site, Site::InitialInvariant(_) | Site::InitialConstraint(_));
        let is_successor = matches!(site, Site::Invariant(_) | Site::ActionProperty(_));
        match site {
            Site::Init if states.is_empty() => {}
            _ if is_initial && states.len() == 1 => {}
            Site::Next if !states.is_empty() && action.is_some() => {}
            _ if is_successor && states.len() > 1 => {}
            _ => return unsupported("a site the simulator doesn't fail at"),
        }
        // The path's states as TLC built them, the last as the action gave it.
        let path: Vec<Vec<Value>> = if matches!(site, Site::Init) || is_initial {
            Vec::new()
        } else {
            let ending = if is_successor {
                Ending::Violation
            } else {
                Ending::Kept
            };
            self.rebuild_checked(store, states, actions, ending, false)?
                .states
                .into_iter()
                .map(|state| state.values)
                .collect()
        };
        let evaluator = self.evaluator();
        let ir = evaluator.ir;
        let width = ir.variables.len();
        let level = states.len() as i32;
        evaluator.printed.clear();
        clear_unnormalized();
        crate::print::clear_unsorted_prints();
        // The checks before the one that failed, which held: they may sort what they reach of the
        // state, as TLC's do.
        let invariants = evaluator.tlc_invariants()?;
        let checked = match site {
            Site::InitialInvariant(position) | Site::Invariant(position) => position as usize,
            _ => invariants.len(),
        };
        if checked > invariants.len()
            || matches!(site, Site::Invariant(p) | Site::InitialInvariant(p) if p as usize >= invariants.len())
        {
            return unsupported("an invariant the model doesn't have");
        }
        let failing = {
            let mut call_stack = CallStack::default();
            call_stack.is_unsourced = true;
            Some(call_stack)
        };
        let result = match site {
            Site::Init => {
                evaluator.current = vec![None; width];
                evaluator.next = vec![None; width];
                evaluator.level = 0;
                let context = run(evaluator.scope_context(ir.model.scope))?;
                evaluator.call_stack = failing;
                evaluator.walk_action(ir.model.init, &context, true, &mut |_| Ok(true))
            }
            Site::InitialInvariant(_) | Site::InitialConstraint(_) => {
                // `Simulator.simulate` checks each initial state once it has them all: the
                // invariants, then the constraints (`isInModel`).
                evaluator.current = vec![None; width];
                evaluator.next = vec![None; width];
                evaluator.level = 0;
                let context = run(evaluator.scope_context(ir.model.scope))?;
                let target = states[0];
                let mut found: Option<Vec<Value>> = None;
                run(
                    evaluator.walk_action(ir.model.init, &context, true, &mut |evaluator| {
                        if found.is_none()
                            && let Some(values) = evaluator
                                .current
                                .iter()
                                .cloned()
                                .collect::<Option<Vec<Value>>>()
                                .filter(|values| is_same(store, target, values))
                        {
                            found = Some(values);
                        }
                        Ok(true)
                    }),
                )?;
                let Some(found) = found else {
                    return unsupported("an initial state the initial predicate doesn't give");
                };
                evaluator.printed.clear();
                evaluator.current = found.into_iter().map(Some).collect();
                evaluator.level = 1;
                for &(body, scope, _) in &invariants[..checked] {
                    let context = run(evaluator.scope_context(scope))?;
                    if !run(evaluator.check_holds(body, &context))? {
                        return unsupported("an earlier invariant is violated");
                    }
                }
                match site {
                    Site::InitialInvariant(position) => {
                        let (body, scope, _) = invariants[position as usize];
                        let context = run(evaluator.scope_context(scope))?;
                        evaluator.call_stack = failing;
                        evaluator.boolean_as(body, &context, Demand::Invariant)
                    }
                    Site::InitialConstraint(position) => {
                        let mut result = fail("a constraint the model doesn't have");
                        for (index, constraint) in ir.model.constraints.iter().enumerate() {
                            let Some(definition) = constraint.definition else {
                                return unsupported("a constraint the model doesn't define");
                            };
                            let body = evaluator
                                .definition(ir.definitions[definition as usize])
                                .body;
                            if index == position as usize {
                                evaluator.call_stack = failing;
                                result = constraint_holds(evaluator, body);
                                break;
                            }
                            if !run(constraint_holds(evaluator, body))? {
                                return unsupported("an earlier constraint doesn't hold");
                            }
                        }
                        result
                    }
                    _ => unreachable!("an initial state's check"),
                }
            }
            Site::Next => {
                // `SimulationWorker.simulateRandomTrace` takes the successors of the one action
                // it tried, which failed.
                let Some((expression, context)) = run(evaluator.tlc_actions())?
                    .into_iter()
                    .nth(action.unwrap_or(u32::MAX) as usize)
                else {
                    return unsupported("an action the model doesn't have");
                };
                evaluator.current = path
                    .last()
                    .cloned()
                    .map(|values| values.into_iter().map(Some).collect())
                    .unwrap_or_else(|| vec![None; width]);
                evaluator.next = vec![None; width];
                evaluator.level = level;
                evaluator.call_stack = failing;
                evaluator.walk_action(expression, &context, false, &mut |_| Ok(true))
            }
            Site::Invariant(_) | Site::ActionProperty(_) => {
                let [.., predecessor, successor] = path.as_slice() else {
                    return unsupported("a successor without a step");
                };
                let successor: Vec<Option<Value>> = successor.iter().cloned().map(Some).collect();
                evaluator.current = successor.clone();
                evaluator.next = vec![None; width];
                evaluator.level = level;
                for &(body, scope, _) in &invariants[..checked] {
                    let context = run(evaluator.scope_context(scope))?;
                    if !run(evaluator.check_holds(body, &context))? {
                        return unsupported("an earlier invariant is violated");
                    }
                }
                match site {
                    Site::Invariant(position) => {
                        let (body, scope, _) = invariants[position as usize];
                        let context = run(evaluator.scope_context(scope))?;
                        evaluator.call_stack = failing;
                        evaluator.boolean_as(body, &context, Demand::Invariant)
                    }
                    Site::ActionProperty(position) => {
                        evaluator.current = predecessor.iter().cloned().map(Some).collect();
                        evaluator.next = successor;
                        evaluator.level = level - 1;
                        for earlier in 0..position {
                            if !run(action_property_holds(evaluator, earlier)?)? {
                                return unsupported("an earlier action property is violated");
                            }
                        }
                        evaluator.call_stack = failing;
                        action_property_holds(evaluator, position)?
                    }
                    _ => unreachable!("a successor's check"),
                }
            }
            _ => return unsupported("a site the simulator doesn't fail at"),
        };
        let call_stack = evaluator.call_stack.take().unwrap_or_default();
        let printed = std::mem::take(&mut evaluator.printed);
        let Err(error) = result else {
            return unsupported("it didn't fail");
        };
        if !printed.is_empty() {
            return unsupported("a failure that prints");
        }
        if let Some(reason) = call_stack.unfollowed {
            return unsupported(reason);
        }
        if call_stack.is_unsorted
            || call_stack.fingerprint.is_some()
            || call_stack.incomplete.is_some()
        {
            return unsupported("a set TLC leaves unnormalized, or a state it can't complete");
        }
        if error.is_set_normalization || error.is_named_normalization {
            return unsupported("a set TLC fails to normalize");
        }
        let Some(message) = error.message else {
            return unsupported(&error.reason);
        };
        let class_name = if message.is_eval_exception {
            "tlc2.tool.EvalException"
        } else {
            error.runtime_exception.class_name()
        };
        let is_tlc_runtime =
            !message.is_eval_exception && error.runtime_exception == RuntimeException::Runtime;
        Ok(SimulatedFailure {
            code: message.code,
            text: message.text.clone(),
            tool_text: nested(&message),
            body_tool_text: match message.code {
                Some(_) => nested_body(&message),
                None => message.text.clone(),
            },
            class_name,
            is_tlc_runtime,
        })
    }
}

// Whether frames end at a union, an intersection, a difference or UNION one of whose operands
// holds a function set, a record set or a product, as written or through the definitions it
// names: in a step, a failure sorting a set enumeration TLC holds unnormalized there goes on
// into that holder's set, whose source TLC's FingerprintException adds (`getNewHead`), which
// the replay doesn't follow (`1 \in ({2} \cup [{1} -> {1, "a"}])`).
fn ends_at_operator_over_holder(ir: &tla_ir::Ir, sources: &[NodeId]) -> bool {
    let Some(&last) = sources.last() else {
        return false;
    };
    let NodeKind::Apply { name, args } = &ir.nodes.arena[last as usize].kind else {
        return false;
    };
    if name.is_local
        || !matches!(
            ir.texts[name.text as usize].as_ref(),
            "\\cup" | "\\cap" | "\\" | "UNION"
        )
    {
        return false;
    }
    fn holds(ir: &tla_ir::Ir, node: NodeId, seen: &mut std::collections::HashSet<NodeId>) -> bool {
        if !seen.insert(node) || seen.len() > 4096 {
            return seen.len() > 4096;
        }
        let kind = &ir.nodes.arena[node as usize].kind;
        match kind {
            NodeKind::FunctionSet { .. } | NodeKind::RecordSet(_) | NodeKind::Product(_) => {
                return true;
            }
            NodeKind::Reference(target) => return holds(ir, *target, seen),
            NodeKind::Identifier(name) | NodeKind::Apply { name, .. } if !name.is_local => {
                if let tla_ir::Resolution::Definition(index) = name.resolution
                    && let Some(&definition) = ir.definitions.get(index as usize)
                    && let NodeKind::Definition(written) = &ir.nodes.arena[definition as usize].kind
                    && holds(ir, written.body, seen)
                {
                    return true;
                }
            }
            _ => {}
        }
        kind.children()
            .into_iter()
            .any(|child| holds(ir, child, seen))
    }
    let mut seen = std::collections::HashSet::new();
    args.iter().any(|&arg| holds(ir, arg, &mut seen))
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
            inner: None,
        };
        assert_eq!(
            nested(&outer),
            format!(
                "@!@!@STARTMSG 2154:0 @!@!@\n{JAVA_FAILURE}{method},\n{JAVA_FAILURE_INNER}@!@!@STARTMSG 2154:0 @!@!@\n{inner}\n@!@!@ENDMSG 2154 @!@!@\n@!@!@ENDMSG 2154 @!@!@"
            )
        );
    }

    #[test]
    fn marks_the_coded_error_a_java_failure_reports_under_tool() {
        let method = "public static tlc2.value.impl.IntValue tlc2.module.FiniteSets.Cardinality(tlc2.value.impl.Value)";
        let inner = TlcMessage {
            text: "Overflow when computing the number of elements in:\nSUBSET (1..31)".into(),
            code: Some(2178),
            is_eval_exception: false,
            inner: None,
        };
        let outer = TlcMessage {
            text: format!(
                "{JAVA_FAILURE}{method},\n{JAVA_FAILURE_INNER}{}",
                inner.text
            ),
            code: Some(JAVA_METHOD_FAILED),
            is_eval_exception: false,
            inner: Some(Box::new(inner.clone())),
        };
        assert_eq!(
            nested(&outer),
            format!(
                "@!@!@STARTMSG 2154:0 @!@!@\n{JAVA_FAILURE}{method},\n{JAVA_FAILURE_INNER}@!@!@STARTMSG 2178:0 @!@!@\n{}\n@!@!@ENDMSG 2178 @!@!@\n@!@!@ENDMSG 2154 @!@!@",
                inner.text
            )
        );
    }
}
