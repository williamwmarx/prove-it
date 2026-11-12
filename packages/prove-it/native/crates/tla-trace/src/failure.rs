//! Where the search stopped on an error, evaluated again as TLC's `CallStackTool` evaluates it:
//! TLC's message for the error, and the nested expressions it was in, as `tlc/replay.ts` and the
//! tracing evaluator of `evaluate.ts` record them and `getFailureMessage` and `formatCallStack` in
//! TypeScript print them.

use tla_ir::{AtomKind, NodeId, NodeKind, SourceRange, TextId};
use tla_values::fingerprint::{Fingerprints, Polynomial};
use tla_values::{Id, Store};

use crate::eval::{CallStack, Context, Demand, Evaluator, StackFrame, UNFOLLOWED_FRAMES};
use crate::fingerprint::{fingerprint_failure, state_fingerprint};
use crate::print::format_value;
use crate::rebuild::{Rebuilder, is_in_model, is_same, run};
use crate::value::{
    EvalError, Evaluated, Lazy, TlcMessage, Value, clear_unnormalized, equals, fail, fail_with,
    normalize_failure, settle,
};
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
    /// the path holds first to the behavior graphs, before it checks the state. `replayed` is the
    /// atom that fails as TLC's replay of the initial states adds the path's second state.
    InitialAtom { atom: u32, replayed: Option<u32> },
    /// Computing the successors of the path's last state, after which TLC fails evaluating the
    /// atom at this position of the model's atoms as it adds the state to the behavior graphs,
    /// on the states `Atom` says: TLC reports the next-state relation's error and the trace, then
    /// the atom's call stack.
    NextAtom { atom: u32, is_extra: bool },
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
    /// them: of an assumption, from the first assumption on.
    pub printed: Vec<Vec<String>>,
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

/// An assumption as TLC checks it, where the engine checked those before it.
pub struct Assumption {
    /// Whether it holds, or `None` where it fails to evaluate with a message of TLC's, which
    /// `evaluate_assumption` reports.
    pub holds: Option<bool>,
    /// What the assumptions before it printed, each print's values as `Trace` holds them.
    pub printed_before: Vec<Vec<String>>,
    /// What it printed.
    pub printed: Vec<Vec<String>>,
    /// The state it leaves TLC's generator in.
    pub random: u64,
}

impl<'ir> Rebuilder<'ir> {
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
        let holds = match evaluator.evaluate(node, &Context::default()) {
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
    pub fn startup_prints(&mut self) -> Result<Vec<Vec<String>>, Unsupported> {
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

    /// Evaluates again the assumption at `position` of the model's assumptions, which failed to
    /// evaluate as TLC started, after the startup's definitions, and returns TLC's report of it
    /// (`checkAssumptions`), with what the assumptions before it printed and what it printed
    /// before it failed, with or without -tool, which AssertError's messages depend on.
    pub fn evaluate_assumption(
        &mut self,
        position: u32,
        is_tool: bool,
    ) -> Result<Failure, Unsupported> {
        self.ranking_made_texts(|rebuilder| rebuilder.evaluate_ranked_assumption(position, is_tool))
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
        run(evaluator.compute_startup())?;
        evaluator.printed.clear();
        for &(earlier, _) in &ir.model.startup.assumptions[..position as usize] {
            if !matches!(
                evaluator.evaluate(earlier, &Context::default()),
                Ok(Value::Bool(true))
            ) {
                return Err(Unsupported(
                    "an assumption the engine found to hold that doesn't again".into(),
                ));
            }
        }
        clear_unnormalized();
        evaluator.call_stack = Some(CallStack::default());
        let result = evaluator.evaluate(node, &Context::default());
        let call_stack = evaluator.call_stack.take().unwrap_or_default();
        let printed = std::mem::take(&mut evaluator.printed);
        let message = match result {
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
        if let Site::NextAtom { atom, is_extra } = site {
            return self.evaluate_next_atom(store, states, actions, atom, is_extra);
        }
        let mut is_successor_generated = false;
        let reads = self.evaluator().register_reads;
        let mut failure =
            self.evaluate_failure_at(store, states, actions, site, &mut is_successor_generated)?;
        // The search sets the registers in the order it explores the states, which the path
        // TLC's report replays doesn't follow.
        if self.evaluator().register_reads != reads {
            return Err(Unsupported(
                "evaluating the failure again: a failure that reads a register".into(),
            ));
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
        let result = match site {
            Site::NextAtom { .. } => {
                return Err(Unsupported(
                    "evaluating the failure again: Next's and an atom's at once".into(),
                ));
            }
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
                            // TLC fingerprints the state once the constraints hold, before it
                            // checks the invariants (`DoInitFunctor`).
                            if position == constraint_count && is_keyed_by_state {
                                evaluator.current.iter().flatten().for_each(settle);
                            }
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
                        let depth = evaluator
                            .call_stack
                            .as_ref()
                            .map(|stack| (stack.frames.len(), stack.is_frozen));
                        let value = evaluator.evaluate(*failed, &Context::default())?;
                        if let (Some(stack), Some((depth, is_frozen))) =
                            (&mut evaluator.call_stack, depth)
                            && !stack.is_fingerprinted
                        {
                            stack.frames.truncate(depth);
                            stack.is_frozen = is_frozen;
                        }
                        constraint_value_holds(evaluator, *failed, value)
                    })
                })
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
            Site::Atom { atom, .. } | Site::InitialAtom { atom, .. } => {
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
                        // `LNAction.eval` evaluates the subscript in each state, then compares the
                        // two values outside any evaluation, so a failing comparison has no call
                        // stack, and TLC prints none.
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
                            match after.and_then(|(before, after)| equals(&before, &after)) {
                                Ok(true) => Ok(false),
                                Ok(false) => evaluator.boolean(atom.expression, &context),
                                Err(error) => Err(error),
                            }
                        } else {
                            if let Some(extra) = extra {
                                evaluator.next = extra;
                            }
                            evaluator.boolean(atom.expression, &context)
                        }
                    }
                })
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
                    if !run(evaluator.boolean(body, &context))? {
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
        };
        let call_stack = evaluator.call_stack.take().unwrap_or_default();
        // TLC evaluates the action of <<A>>_v, and records no node for the brackets, whether
        // the property writes them or the front does for WF_v(A) and SF_v(A).
        let mut call_stack = call_stack;
        if let Site::Atom { atom, .. } = site
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
        // TLC fails to fingerprint an initial state that holds a set it can't normalize, then to
        // print the state as it reports that, which escapes as an exception it didn't expect. A
        // next-state relation that fails in a method of a value with a source fails before TLC
        // fingerprints any successor of the expansion that holds such a set.
        if call_stack.is_unsorted && !(call_stack.is_fingerprinted && site == Site::Next) {
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
                    replay: Replay::default(),
                });
            }
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
            let (code, text, tool_text, state, initial_states) = match site {
                Site::Init => (
                    INITIAL_STATE,
                    message.text.clone(),
                    nested(&message),
                    Some(state),
                    Some(initial_states),
                ),
                _ => {
                    let (code, text, tool_text) = report(&message, true);
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
                    Some(values.iter().map(format_value).collect()),
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
                }),
                state,
                replay: Replay::default(),
            });
        }
        // A failure in the initial or next states whose receiver the replay gave a source TLC
        // reports as it is, then fails again as a FingerprintException as it replays the
        // computation with its `CallStackTool`, which gives values their sources, and prints that
        // call stack (`ModelChecker.modelCheckImpl`).
        if call_stack.is_fingerprinted
            && matches!(site, Site::Init | Site::Next)
            && let Some(message) = &error.message
            && (!call_stack.fingerprinted_sources.is_empty()
                || call_stack.is_frozen_before_fingerprint)
        {
            let (code, text, tool_text) = report(message, site == Site::Next);
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
            let state = values.iter().map(format_value).collect();
            // Where the replay fails again, TLC prints its call stack and exits as for it.
            let (call_stack, exit_code) = match replayed {
                Some((target, atom)) => (
                    replay_initial_atom(evaluator, store, target, atom)?,
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
                replay: Replay::default(),
            });
        }
        // TLC reports an invariant that fails to evaluate with a headline of its own, and no call
        // stack (`doNextEvalFailed`).
        if let Site::Invariant(position) = site {
            let Some(&(_, _, name)) = evaluator.tlc_invariants()?.get(position as usize) else {
                return Err(Unsupported("an invariant the model doesn't have".into()));
            };
            let headline = format!("Evaluating invariant {} failed.", ir.texts[name as usize]);
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
            let replayed = replay_expansion(evaluator, path, &known)?;
            let mut printed = printed;
            printed.append(&mut evaluator.printed);
            let (call_stack, fingerprint, exit_code) = match replayed.failure {
                None => (Vec::new(), None, FAILURE_SAFETY_EVAL),
                Some(ReplayFailure::Fingerprint(fingerprint)) => {
                    (Vec::new(), Some(fingerprint), FAILURE_SPEC_EVAL)
                }
                Some(ReplayFailure::Nested(call_stack, exit_code)) => (call_stack, None, exit_code),
            };
            return Ok(Failure {
                code: INVARIANT_EVALUATION_FAILED,
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
                (Site::Next | Site::Atom { .. }, Some(ASSERT_FAILED)) => VIOLATION_ASSERT,
                // TLC's replay of the expansion, and an error adding a state to the behavior
                // graphs, exit by an EvalException's code (`errorConstantToExitStatus`): an
                // undefined identifier is among the configuration's errors, and the others are
                // general ones.
                (Site::Next | Site::Atom { .. }, Some(UNDEFINED_IDENTIFIER))
                    if message.is_eval_exception =>
                {
                    ERROR_CONFIG_PARSE
                }
                (Site::Next, _) if message.is_eval_exception => FAILURE_ERROR,
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
    let result = context.and_then(|context| {
        evaluator.walk_action(ir.model.init, &context, true, &mut |evaluator| {
            let values: Option<Vec<Value>> = evaluator.current.iter().cloned().collect();
            if !values.is_some_and(|values| is_same(store, target, &values)) {
                return Ok(true);
            }
            evaluator.level = 1;
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
    if result.is_ok() {
        return Err(Unsupported(
            "evaluating the failure again: TLC's replay of the initial states doesn't fail".into(),
        ));
    }
    if let Some(reason) = call_stack.unfollowed {
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
    if !ir.model.action_properties.is_empty() {
        return unsupported("a property TLC checks of each step");
    }
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
            if !is_unseen {
                continue;
            }
            evaluator.current = successor.into_iter().map(Some).collect();
            evaluator.next = vec![None; width];
            evaluator.level = level + 1;
            for &(invariant, scope, _) in &invariants {
                let Ok(context) = evaluator.scope_context(scope) else {
                    return unsupported("an invariant's scope");
                };
                match evaluator.boolean_as(invariant, &context, Demand::Invariant) {
                    Ok(true) => {}
                    Ok(false) => {
                        return Ok(Replayed {
                            replay,
                            failure: None,
                        });
                    }
                    Err(error) => {
                        let call_stack = evaluator.call_stack.take().unwrap_or_default();
                        if let Some(reason) = call_stack.unfollowed {
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
                            })
                        } else {
                            // TLC exits by the code of an EvalException, and by that of the
                            // nested expressions it prints for any other error.
                            ReplayFailure::Nested(
                                ranges(evaluator, &call_stack),
                                match message.code {
                                    Some(ASSERT_FAILED) => VIOLATION_ASSERT,
                                    _ if message.is_eval_exception => FAILURE_ERROR,
                                    _ => FAILURE_SPEC_EVAL,
                                },
                            )
                        };
                        return Ok(Replayed {
                            replay,
                            failure: Some(failure),
                        });
                    }
                }
            }
            if is_in_model {
                replay.queued += 1;
            }
        }
    }
    Ok(Replayed {
        replay,
        failure: None,
    })
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
                    let texts = state
                        .iter()
                        .map(|value| value.as_ref().map(format_value).unwrap_or_default())
                        .collect();
                    if chain.iter().all(is_filter) {
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
    matches!(value, Value::Lazy(lazy) if matches!(**lazy, Lazy::Filter(..)))
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
    let value = evaluator.evaluate(body, &Context::default())?;
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
