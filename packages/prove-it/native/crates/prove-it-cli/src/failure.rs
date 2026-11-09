//! TLC's report of an error the search stopped at, as `printResult` in `src/cli/tlc.ts` prints a
//! failure: `tla-trace` evaluates again where the search failed, as TLC replays it with its call
//! stack, and rebuilds the trace to the state TLC was expanding.

use std::time::Instant;

use tla_ir::{Ir, SourceRange};
use tla_trace::{Ending, Failure, Rebuilder, Site, Trace, Unsupported, format_call_stack};
use tla_values::{Id, Store};

use crate::check::{SEARCH_STACK_BYTES, Statistics, print_finished, print_statistics};
use crate::messages::{self as code, Level, Printer};
use crate::summary::out_degree_summary;

// The status TLC exits with after a failure evaluating the spec, and after an exception it didn't
// expect (`EC.ExitStatus`).
const FAILURE_SPEC_EVAL: i32 = 75;
const ERROR: i32 = 255;
use crate::trace::{format_partial_state, format_print, format_state, format_texts};

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
}

// The failure and the trace's states as TLC prints them, each with its label and what the spec
// printed before it, then what it printed after the trace: as TLC rebuilt the trace once more,
// and as it replayed the failure.
struct Report {
    failure: Failure,
    states: Vec<PrintedStep>,
    after: Vec<String>,
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
    if !ir.model.live_properties.is_empty() && !is_atom {
        return Err("a failure in a model with temporal properties".into());
    }
    if stop.site == Site::Next && stop.reason == "a successor that isn't complete" {
        return print_incomplete(printer, ir, stop, start);
    }
    let report = evaluate(ir, stop)?;
    let failure = &report.failure;
    if is_atom && failure.fingerprint.is_some() {
        return Err("a state TLC fails to fingerprint as it adds it to the behavior graphs".into());
    }
    // TLC prints the call stack of an error adding a state to the behavior graphs before the
    // error (`Worker#doNextCheckLiveness`).
    if is_atom {
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
    // adding a state to the behavior graphs.
    if failure.exit_code == ERROR && !is_atom {
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
    if failure.fingerprint.is_some() && !report.states.is_empty() {
        printer.print(failure.code, Level::Error, message);
    }
    for line in &report.after {
        printer.line(line);
    }
    match &failure.fingerprint {
        // TLC reports where it failed to fingerprint in place of the call stack, innermost first.
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
        // TLC reports an invariant that fails to evaluate without its call stack.
        None if matches!(stop.site, Site::Invariant(_)) || is_atom => {}
        None => print_call_stack(printer, ir, &failure.call_stack),
    }
    // TLC counts the state it failed to fingerprint as generated, which the search stopped before
    // counting, and an initial state as at depth 1.
    let statistics = match (&failure.fingerprint, stop.site) {
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
    print_statistics(printer, &statistics, start);
    if (matches!(stop.site, Site::Invariant(_)) || is_atom)
        && let Some(summary) = out_degree_summary(stop.out_degrees)
    {
        printer.print(code::STATE_GRAPH_OUTDEGREE, Level::None, &summary);
    }
    print_finished(printer, start);
    Ok(failure.exit_code)
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
/// after what it printed before it failed, and returns the status TLC exits with, or why the run
/// isn't native yet. TLC prints no statistics, since it hasn't searched.
pub fn print_assumption_failure(
    printer: &mut Printer,
    ir: &Ir,
    position: u32,
    start: Instant,
) -> Result<i32, String> {
    let failure = on_search_stack(|| Rebuilder::new(ir)?.evaluate_assumption(position))?;
    for print in &failure.printed {
        printer.line(&format_print(print));
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
fn evaluate(ir: &Ir, stop: &ErrorStop<'_>) -> Result<Report, String> {
    on_search_stack(|| {
        let mut rebuilder = Rebuilder::new(ir)?;
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
            Site::InitialConstraint(_) | Site::InitialInvariant(_) | Site::InitialPredicate(_)
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
        // TLC rebuilds the trace once more after it prints it, then replays the failure.
        let after = trace
            .trace_output
            .iter()
            .chain(&failure.printed)
            .map(|print| format_print(print))
            .collect();
        Ok(Report {
            failure,
            states: labelled(ir, &trace)?,
            after,
        })
    })
}

// Runs the evaluator on a thread with the search's stack, since it recurses with the expressions it
// evaluates.
fn on_search_stack<T: Send>(
    evaluate: impl FnOnce() -> Result<T, Unsupported> + Send,
) -> Result<T, String> {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(SEARCH_STACK_BYTES)
            .spawn_scoped(scope, evaluate)
            .expect("a thread to evaluate the failure")
            .join()
            .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
            .map_err(|Unsupported(reason)| reason)
    })
}

// Each state of a rebuilt trace as TLC prints it, with its label and what the spec printed before
// it.
fn labelled(ir: &Ir, trace: &Trace) -> Result<Vec<PrintedStep>, Unsupported> {
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
            text: format_state(ir, &state.values),
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
    let (states, incomplete) = on_search_stack(|| {
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
            labelled(ir, &trace)?,
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
