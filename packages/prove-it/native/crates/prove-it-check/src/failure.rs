//! TLC's report of an error the search stopped at, as `printResult` in `src/cli/tlc.ts` prints a
//! failure: `tla-trace` evaluates again where the search failed, as TLC replays it with its call
//! stack, and rebuilds the trace to the state TLC was expanding.

use tla_engine::clock::Instant;

use tla_engine::search::Violation;
use tla_ir::{Ir, NodeId, NodeKind, SourceRange};
use tla_trace::{
    Alias, CounterExample, Ending, Failure, Rebuilder, Registers, Site, Trace, Unsupported,
    format_call_stack,
};
use tla_values::{Id, Store};

use crate::check::{Statistics, print_finished, print_postcondition_failure, print_statistics};
use crate::messages::{self as code, Level, Printer};
use crate::stack::on_search_stack;
use crate::summary::out_degree_summary;

// The status TLC exits with after a failure evaluating the spec, and after an exception it didn't
// expect (`EC.ExitStatus`).
pub(crate) const FAILURE_SPEC_EVAL: i32 = 75;
pub(crate) const ERROR: i32 = 255;
use crate::trace::{
    PostconditionRun, Postconditions, check, format_fields, format_partial_state, format_print,
    format_state, format_texts,
};

/// Where the search stopped on an error: the path to the state it was expanding, as ids of
/// `store` (none in the initial predicate), the position in the model's actions of each step's
/// action, where it failed, and the counts TLC reports with the error.
pub struct ErrorStop<'a> {
    /// The engine's reason for the stop, which names an incomplete successor.
    pub reason: &'a str,
    pub store: &'a Store,
    pub states: Vec<&'a [Id]>,
    pub actions: Vec<Option<u32>>,
    pub site: Site,
    pub statistics: Statistics,
    /// The outdegree buckets of the state graph TLC reports after an invariant that fails to
    /// evaluate.
    pub out_degrees: &'a [u64],
    /// TLC's set of fingerprints when the search stopped at such an invariant, sorted.
    pub fingerprints: &'a [u64],
    /// With an ALIAS or postconditions, the violation the search stopped at, for the startup
    /// values and registers they may read.
    pub replayed: Option<&'a Violation>,
    /// Whether TLC prints the trace's states through an ALIAS.
    pub is_aliased: bool,
    /// What TLCGet reads as TLC checks the postconditions after the failure, where it does.
    pub postconditions: Option<PostconditionRun>,
}

// The failure and the trace's states as TLC prints them, each with its label and what the spec
// printed before it, then what it printed after the trace: as TLC rebuilt the trace once more,
// and as it replayed the failure.
struct Report {
    failure: Failure,
    states: Vec<PrintedStep>,
    after: Vec<String>,
    postconditions: Option<Postconditions>,
}

struct PrintedStep {
    label: String,
    text: String,
    output: Vec<String>,
}

/// Prints TLC's report of the error and returns the status TLC exits with, or why the run isn't
/// native yet.
pub fn print_failure(
    printer: &mut Printer,
    ir: &Ir,
    stop: &ErrorStop<'_>,
    start: Instant,
) -> Result<i32, String> {
    // TLC's worker adds the state to the behavior graph before it replays a failure in its next
    // states, which can fail or print in turn.
    let is_atom = matches!(stop.site, Site::Atom { .. });
    let is_initial_atom = matches!(stop.site, Site::InitialAtom { .. });
    // A failure among the initial states comes before TLC has taken a step, and the search
    // hands one over only where the atoms TLC evaluated of the initial states before it
    // evaluate.
    let is_initial = matches!(
        stop.site,
        Site::Init
            | Site::InitialConstraint(_)
            | Site::InitialInvariant(_)
            | Site::InitialPredicate(_)
            | Site::InitialAtom { .. }
    );
    // An invariant that fails to evaluate stops TLC's worker before it adds the state it was
    // expanding to the behavior graphs, and TLC's replay of the expansion adds nothing to them
    // (`ModelChecker.doNext`), so the temporal properties show only in what their atoms print as
    // TLC adds the states before it.
    let is_followed =
        is_atom || is_initial || matches!(stop.site, Site::Invariant(_)) && !atoms_print(ir);
    if !ir.model.live_properties.is_empty() && !is_followed {
        return Err("a failure in a model with temporal properties".into());
    }
    if stop.site == Site::Next && stop.reason == "a successor that isn't complete" {
        return print_incomplete(printer, ir, stop, start);
    }
    let report = evaluate(ir, stop, printer.is_tool)?;
    let failure = &report.failure;
    if stop.replayed.is_some() && failure.fingerprint.is_some() {
        return Err("a state TLC fails to fingerprint with an ALIAS or a POSTCONDITION".into());
    }
    // TLC rebuilds the trace again for the postconditions, between what it prints after the
    // trace and what the replay prints, which the printing doesn't order.
    if let Some(checked) = &report.postconditions
        && (!checked.printed.is_empty() || !report.after.is_empty())
    {
        return Err("a failure with a POSTCONDITION in a spec that prints".into());
    }
    if is_atom && failure.fingerprint.is_some() {
        return Err("a state TLC fails to fingerprint as it adds it to the behavior graphs".into());
    }
    // TLC prints the call stack of an error adding a state to the behavior graphs before the
    // error (`Worker#doNextCheckLiveness`), where its rerun has one (`hasCallStack`): a failing
    // comparison of a subscript's two values (`LNAction.eval`) is in no evaluation.
    if is_atom && !failure.call_stack.is_empty() {
        print_call_stack(printer, ir, &failure.call_stack);
    }
    let message = if printer.is_tool {
        &failure.tool_message
    } else {
        &failure.message
    };
    // TLC names the initial state it failed to fingerprint in the message.
    match &failure.state {
        Some(state) => printer.print(
            failure.code,
            Level::Error,
            &format!(
                "{message}\nWhile working on the initial state:\n{}",
                format_texts(ir, state)
            ),
        ),
        None => printer.print(failure.code, Level::Error, message),
    }
    // TLC reports an exception it didn't expect without the call stack or statistics, but for one
    // adding a state to the behavior graphs, an initial one too, or one its replay of an
    // expansion threw.
    if failure.exit_code == ERROR
        && !is_atom
        && !is_initial_atom
        && !failure.replay.is_failed
        && !matches!(stop.site, Site::Next)
    {
        print_finished(printer, start);
        return Ok(ERROR);
    }
    // TLC prints the trace to the state it was expanding, and none for the initial predicate:
    // what the spec printed as it rebuilt the first state after the error, and each later state's
    // before the state (`printTrace`).
    if let Some(first) = report.states.first() {
        for line in &first.output {
            printer.line(line);
        }
        printer.print(
            code::BEHAVIOR_UP_TO_THIS_POINT,
            Level::Error,
            "The behavior up to this point is:",
        );
        for (position, step) in report.states.iter().enumerate() {
            if position > 0 {
                for line in &step.output {
                    printer.line(line);
                }
            }
            printer.print(
                code::STATE_PRINT_2,
                Level::State,
                &format!("{}: <{}>\n{}", position + 1, step.label, step.text),
            );
        }
    }
    // A successor TLC can't fingerprint fails again as TLC prints it with the trace.
    let is_replayed = failure
        .fingerprint
        .as_ref()
        .is_some_and(|fingerprint| fingerprint.is_replayed);
    if failure.fingerprint.is_some() && !is_replayed && !report.states.is_empty() {
        printer.print(failure.code, Level::Error, message);
    }
    // TLC computes the initial states again for the call stack, from a count of none, and
    // reports its progress at each power of two before the state that fails again
    // (`DoInitFunctor.addElement`).
    let is_progress_replayed = matches!(
        stop.site,
        Site::Init
            | Site::InitialAtom { .. }
            | Site::InitialConstraint(_)
            | Site::InitialInvariant(_)
            | Site::InitialPredicate(_)
    );
    let progress = std::iter::successors(Some(2u64), |count| count.checked_mul(2))
        .take_while(|&count| is_progress_replayed && count < stop.statistics.generated);
    if stop.statistics.generated > 2
        && is_progress_replayed
        && (failure.fingerprint.is_some() || !report.after.is_empty())
    {
        return Err("TLC's progress as it computes the initial states again, in a spec that prints or with a state it can't fingerprint".into());
    }
    for count in progress {
        printer.print(
            code::COMPUTING_INIT_PROGRESS,
            Level::None,
            &format!("Computed {count} initial states..."),
        );
    }
    for line in &report.after {
        printer.line(line);
    }
    print_postcondition_failure(printer, ir, report.postconditions.as_ref());
    match &failure.fingerprint {
        // TLC reports where it failed to fingerprint in place of the call stack, innermost first.
        // TLC prints the call stack of its replay where the replay threw the FingerprintException.
        Some(fingerprint) if fingerprint.is_replayed => {
            let reason = if printer.is_tool {
                &fingerprint.tool_reason
            } else {
                &fingerprint.reason
            };
            printer.print(
                code::FINGERPRINT_FAILED,
                Level::Error,
                &format!(
                    "TLC was unable to fingerprint.\n\nFingerprint Stack Trace:\n{}\nReason:\n{reason}",
                    format_call_stack(ir, &fingerprint.sources)
                ),
            );
        }
        Some(fingerprint) => {
            let trace: String = fingerprint
                .sources
                .iter()
                .enumerate()
                .rev()
                .map(|(position, range)| {
                    format!(
                        "{position}) line {}, col {} to line {}, col {} of module {}\n",
                        range.start_line,
                        range.start_column,
                        range.end_line,
                        range.end_column,
                        ir.texts[range.module as usize]
                    )
                })
                .collect();
            let reason = if printer.is_tool {
                &fingerprint.tool_reason
            } else {
                &fingerprint.reason
            };
            printer.print(
                code::FINGERPRINT_FAILED,
                Level::Error,
                &format!(
                    "TLC was unable to fingerprint.\n\nFingerprint Stack Trace:\n{trace}\nReason:\n{reason}"
                ),
            );
        }
        // TLC reports an invariant that fails to evaluate without its call stack, but for the
        // call stack of its replay of the expansion where that fails in turn.
        // Nor one adding an initial state to the behavior graphs, but where its replay of the
        // initial states fails again adding a state it hadn't found.
        None if is_atom
            || is_initial_atom && failure.call_stack.is_empty()
            || matches!(stop.site, Site::Invariant(_)) && !failure.replay.is_failed => {}
        None => print_call_stack(printer, ir, &failure.call_stack),
    }
    // TLC counts the state it failed to fingerprint as generated, which the search stopped before
    // counting, and an initial state as at depth 1.
    let statistics = match (&failure.fingerprint, stop.site) {
        (Some(fingerprint), _) if fingerprint.is_replayed => stop.statistics,
        (Some(_), site) => Statistics {
            generated: stop.statistics.generated + 1,
            depth: match site {
                Site::Init => stop.statistics.depth.max(1),
                _ => stop.statistics.depth,
            },
            ..stop.statistics
        },
        (None, _) => stop.statistics,
    };
    // TLC's replay adds the successors it hadn't seen to its set, and to its queue those that
    // pass its checks.
    let statistics = Statistics {
        distinct: statistics.distinct + failure.replay.found,
        queued: statistics.queued + failure.replay.queued,
        ..statistics
    };
    print_statistics(printer, &statistics, start);
    if (matches!(stop.site, Site::Invariant(_)) || is_atom)
        && !failure.replay.is_failed
        && let Some(summary) = out_degree_summary(stop.out_degrees)
    {
        printer.print(code::STATE_GRAPH_OUTDEGREE, Level::None, &summary);
    }
    print_finished(printer, start);
    Ok(failure.exit_code)
}

// Whether an atom of the temporal properties may print as TLC evaluates it: one read in an
// instance's scope, or one that reaches Print or PrintT, through the definitions it names.
fn atoms_print(ir: &Ir) -> bool {
    let arena = &ir.nodes.arena;
    if ir.model.atoms.iter().any(|atom| atom.scope.is_some()) {
        return true;
    }
    let mut pending: Vec<NodeId> = ir.model.atoms.iter().map(|atom| atom.expression).collect();
    let mut seen = vec![false; arena.len()];
    while let Some(node) = pending.pop() {
        if std::mem::replace(&mut seen[node as usize], true) {
            continue;
        }
        let kind = &arena[node as usize].kind;
        if let NodeKind::Identifier(name)
        | NodeKind::Apply { name, .. }
        | NodeKind::OperatorReference(name) = kind
        {
            if matches!(&*ir.texts[name.text as usize], "Print" | "PrintT") {
                return true;
            }
            if let tla_ir::Resolution::Definition(index) = name.resolution {
                pending.push(ir.definitions[index as usize]);
            }
        }
        if let NodeKind::Reference(target) = kind {
            pending.push(*target);
        }
        pending.extend(kind.children());
    }
    false
}

fn print_call_stack(printer: &mut Printer, ir: &Ir, call_stack: &[SourceRange]) {
    printer.print(
        code::NESTED_EXPRESSION,
        Level::Error,
        &format!(
            "The error occurred when TLC was evaluating the nested\nexpressions at the following positions:\n{}",
            format_call_stack(ir, call_stack)
        ),
    );
}

/// Prints TLC's report of the assumption at `position` that failed to evaluate as TLC started,
/// after what the assumptions printed before it failed that the run hasn't, and returns the
/// status TLC exits with, or why the run isn't native yet. `printed` is what the run printed of
/// the assumptions, which must be what TLC prints first. TLC prints no statistics, since it hasn't
/// searched.
pub fn print_assumption_failure(
    printer: &mut Printer,
    ir: &Ir,
    position: u32,
    printed: &[String],
    workers: usize,
    start: Instant,
) -> Result<i32, String> {
    let failure = evaluate_on_search_stack(|| {
        Rebuilder::new(ir).and_then(|mut rebuilder| {
            rebuilder.set_workers(workers);
            rebuilder.evaluate_assumption(position)
        })
    })?;
    // What TLC prints of the assumptions before this one, which hold, and of this one.
    let mut expected: Vec<String> = failure
        .printed
        .iter()
        .map(|print| format_print(print))
        .collect();
    if !expected.starts_with(printed) {
        return Err("the assumptions printing other than TLC prints".into());
    }
    for text in &expected.split_off(printed.len()) {
        printer.line(text);
    }
    let message = if printer.is_tool {
        &failure.tool_message
    } else {
        &failure.message
    };
    printer.print(failure.code, Level::Error, message);
    print_finished(printer, start);
    Ok(failure.exit_code)
}

// Evaluates the failure again and rebuilds the trace.
fn evaluate(ir: &Ir, stop: &ErrorStop<'_>, is_tool: bool) -> Result<Report, String> {
    evaluate_on_search_stack(|| {
        let mut rebuilder = Rebuilder::new(ir)?;
        rebuilder.set_fingerprints(stop.fingerprints);
        if let Some(violation) = stop.replayed {
            rebuilder.set_startup(
                &violation.store,
                &violation.startup,
                violation.startup_random,
            )?;
            if let Some(group) = &violation.symmetry {
                rebuilder.set_symmetry(group);
            }
            rebuilder.set_registers(Registers::from_store(
                &violation.store,
                &violation.registers.numbered,
                &violation.registers.named,
            )?);
        }
        let failure =
            rebuilder.evaluate_failure(stop.store, &stop.states, &stop.actions, stop.site)?;
        // TLC holds a successor that fails an invariant as it found it.
        let ending = match stop.site {
            Site::Invariant(_) => Ending::Violation,
            _ => Ending::Kept,
        };
        // TLC prints no trace for a check of an initial state that fails.
        let trace = if matches!(
            stop.site,
            Site::InitialConstraint(_)
                | Site::InitialInvariant(_)
                | Site::InitialPredicate(_)
                | Site::InitialAtom { .. }
        ) {
            Trace {
                states: Vec::new(),
                trace_output: Vec::new(),
            }
        } else {
            // An atom's state past the path is no state of the trace.
            let (states, actions) = match stop.site {
                Site::Atom { is_extra: true, .. } => {
                    let states = &stop.states[..stop.states.len().saturating_sub(1)];
                    (states, &stop.actions[..states.len().saturating_sub(1)])
                }
                _ => (&stop.states[..], &stop.actions[..]),
            };
            rebuilder.rebuild(stop.store, states, actions, ending)?
        };
        // TLC rebuilds the trace once more after it prints it, for the postconditions, then
        // replays the failure. Its worker rebuilds it after a failure in the next-state relation
        // only as it goes on to check the state for deadlock, having generated no successor of
        // it, and never after an invariant fails to evaluate, since it generated the successor
        // (`Worker.run`, `Worker.addElement`).
        let is_rebuilt_again = match stop.site {
            Site::Invariant(_) => false,
            Site::Next => ir.model.check_deadlock && !failure.replay.is_successor_generated,
            _ => true,
        };
        let after = trace
            .trace_output
            .iter()
            .filter(|_| is_rebuilt_again)
            .chain(&failure.printed)
            .map(|print| format_print(print))
            .collect();
        // TLC prints a state it was expanding alone, an initial one, as it is, and every other
        // trace through the ALIAS (`TLCTrace.printTrace`).
        let aliases = if stop.is_aliased && trace.states.len() > 1 {
            rebuilder.alias(&trace, None, is_tool)?
        } else {
            None
        };
        // TLC's worker checks the postconditions on the trace to the state it was expanding.
        let postconditions = stop
            .postconditions
            .as_ref()
            .map(|run| {
                let counter_example = CounterExample {
                    trace: &trace,
                    cycle: None,
                };
                check(&mut rebuilder, ir, run, Some(counter_example))
            })
            .transpose()?;
        Ok(Report {
            failure,
            states: labelled(ir, &trace, aliases.as_deref())?,
            after,
            postconditions,
        })
    })
}

// Runs the evaluator with the search's stack, since it recurses with the expressions it evaluates.
fn evaluate_on_search_stack<T: Send>(
    evaluate: impl FnOnce() -> Result<T, Unsupported> + Send,
) -> Result<T, String> {
    on_search_stack(evaluate).map_err(|Unsupported(reason)| reason)
}

// Each state of a rebuilt trace as TLC prints it, with its label and what the spec printed before
// it.
fn labelled(
    ir: &Ir,
    trace: &Trace,
    aliases: Option<&[Alias]>,
) -> Result<Vec<PrintedStep>, Unsupported> {
    let mut states = Vec::with_capacity(trace.states.len());
    for (position, state) in trace.states.iter().enumerate() {
        let label = match (position, state.action) {
            (0, _) => "Initial predicate".to_string(),
            (_, Some(action)) => match ir.model.actions.get(action as usize) {
                Some(action) => ir.texts[action.label as usize].to_string(),
                None => return Err(Unsupported("an action the IR lacks".into())),
            },
            (_, None) => {
                return Err(Unsupported(
                    "a step whose action the rebuilt trace lacks".into(),
                ));
            }
        };
        states.push(PrintedStep {
            label,
            text: match aliases.map(|aliases| &aliases[position]) {
                Some(Alias::Record(fields)) => format_fields(
                    fields
                        .iter()
                        .map(|(name, value)| (name.as_str(), Some(value))),
                ),
                _ => format_state(ir, &state.values),
            },
            output: state
                .printed
                .iter()
                .map(|print| format_print(print))
                .collect(),
        });
    }
    Ok(states)
}

/// TLC's report of a successor the next-state relation leaves incomplete, as
/// `reportIncompleteSuccessor` prints it: the trace to the state TLC was expanding, then the
/// successor, its undefined variables null, and no call stack.
fn print_incomplete(
    printer: &mut Printer,
    ir: &Ir,
    stop: &ErrorStop<'_>,
    start: Instant,
) -> Result<i32, String> {
    // TLC names the action where the next-state relation has several, by the name the IR's label
    // starts with, and TLC 1.7.4 says a variable isn't assigned.
    let actions = &ir.model.actions;
    let is_174 = ir
        .model
        .version
        .is_some_and(|version| &*ir.texts[version as usize] == "1.7.4");
    if actions.is_empty() || is_174 {
        return Err("an incomplete successor of a model whose actions the IR lacks".into());
    }
    if stop.replayed.is_some() {
        return Err("an incomplete successor with an ALIAS or a POSTCONDITION".into());
    }
    let (states, incomplete) = evaluate_on_search_stack(|| {
        let mut rebuilder = Rebuilder::new(ir)?;
        let trace = rebuilder.rebuild(stop.store, &stop.states, &stop.actions, Ending::Kept)?;
        if !trace.trace_output.is_empty()
            || trace.states.iter().any(|state| !state.printed.is_empty())
        {
            return Err(Unsupported(
                "an incomplete successor of a spec that prints".into(),
            ));
        }
        let incomplete = rebuilder.incomplete_successor(&trace)?;
        let partial: Vec<_> = incomplete.partial.iter().map(Option::as_ref).collect();
        Ok((
            labelled(ir, &trace, None)?,
            (
                incomplete.action,
                incomplete.missing,
                format_partial_state(ir, &partial),
            ),
        ))
    })?;
    let (action, missing, partial) = incomplete;
    let Some(action) = action.and_then(|action| actions.get(action as usize)) else {
        return Err("an incomplete successor of an action the IR lacks".into());
    };
    let label = &ir.texts[action.label as usize];
    let subject = if actions.len() == 1 {
        "the next-state action".to_string()
    } else {
        let name = label.split(" line ").next().unwrap_or(label);
        format!("action {name} of the next-state relation")
    };
    let names: Vec<&str> = missing
        .iter()
        .map(|&index| ir.texts[ir.variables[index] as usize].as_ref())
        .collect();
    let (noun, verb) = if names.len() > 1 {
        ("variables", "are")
    } else {
        ("variable", "is")
    };
    printer.print(
        code::INCOMPLETE_SUCCESSOR,
        Level::Error,
        &format!(
            "Successor state is not completely specified by {subject}. The following {noun} {verb} not defined: {}.\n",
            names.join(", ")
        ),
    );
    printer.print(
        code::BEHAVIOR_UP_TO_THIS_POINT,
        Level::Error,
        "The behavior up to this point is:",
    );
    let successor = PrintedStep {
        label: label.to_string(),
        text: partial,
        output: Vec::new(),
    };
    for (position, step) in states.iter().chain([&successor]).enumerate() {
        printer.print(
            code::STATE_PRINT_2,
            Level::State,
            &format!("{}: <{}>\n{}", position + 1, step.label, step.text),
        );
    }
    // TLC counts the incomplete successor as generated, which the search stopped before counting.
    let statistics = Statistics {
        generated: stop.statistics.generated + 1,
        ..stop.statistics
    };
    print_statistics(printer, &statistics, start);
    print_finished(printer, start);
    Ok(FAILURE_SPEC_EVAL)
}
