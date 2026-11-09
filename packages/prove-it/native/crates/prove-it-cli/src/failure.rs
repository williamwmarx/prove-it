//! TLC's report of an error the search stopped at, as `printResult` in `src/cli/tlc.ts` prints a
//! failure: `tla-trace` evaluates again where the search failed, as TLC replays it with its call
//! stack, and rebuilds the trace to the state TLC was expanding.

use std::time::Instant;

use tla_ir::Ir;
use tla_trace::{Ending, Failure, Rebuilder, Site, Unsupported, format_call_stack};
use tla_values::{Id, Store};

use crate::check::{SEARCH_STACK_BYTES, Statistics, print_finished, print_statistics};
use crate::messages::{self as code, Level, Printer};
use crate::trace::format_state;

/// Where the search stopped on an error: the path to the state it was expanding, as ids of
/// `store` (none in the initial predicate), the position in the model's actions of each step's
/// action, where it failed, and the counts TLC reports with the error.
pub struct ErrorStop<'a> {
    pub store: &'a Store,
    pub states: Vec<&'a [Id]>,
    pub actions: Vec<Option<u32>>,
    pub site: Site,
    pub statistics: Statistics,
}

// The failure and the trace's states as TLC prints them, each with its label.
struct Report {
    failure: Failure,
    states: Vec<(String, String)>,
}

/// Prints TLC's report of the error and returns the status TLC exits with, or why the run isn't
/// native yet.
pub fn print_failure(
    printer: &mut Printer,
    ir: &Ir,
    stop: &ErrorStop<'_>,
    start: Instant,
) -> Result<i32, String> {
    // TLC prints the outdegree of the state graph after an invariant that fails to evaluate.
    if matches!(stop.site, Site::Invariant(_)) {
        return Err("an invariant that fails to evaluate".into());
    }
    let report = evaluate(ir, stop)?;
    let failure = &report.failure;
    let message = if printer.is_tool {
        &failure.tool_message
    } else {
        &failure.message
    };
    printer.print(failure.code, Level::Error, message);
    // TLC prints the trace to the state it was expanding, and none for the initial predicate.
    if !report.states.is_empty() {
        printer.print(
            code::BEHAVIOR_UP_TO_THIS_POINT,
            Level::Error,
            "The behavior up to this point is:",
        );
        for (position, (label, text)) in report.states.iter().enumerate() {
            printer.print(
                code::STATE_PRINT_2,
                Level::State,
                &format!("{}: <{label}>\n{text}", position + 1),
            );
        }
    }
    printer.print(
        code::NESTED_EXPRESSION,
        Level::Error,
        &format!(
            "The error occurred when TLC was evaluating the nested\nexpressions at the following positions:\n{}",
            format_call_stack(ir, &failure.call_stack)
        ),
    );
    print_statistics(printer, &stop.statistics, start);
    print_finished(printer, start);
    Ok(failure.exit_code)
}

// Evaluates the failure again and rebuilds the trace, on a thread with the search's stack, since
// the evaluator recurses with the expressions it evaluates.
fn evaluate(ir: &Ir, stop: &ErrorStop<'_>) -> Result<Report, String> {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(SEARCH_STACK_BYTES)
            .spawn_scoped(scope, || {
                let mut rebuilder = Rebuilder::new(ir)?;
                let failure = rebuilder.evaluate_failure(
                    stop.store,
                    &stop.states,
                    &stop.actions,
                    stop.site,
                )?;
                let trace =
                    rebuilder.rebuild(stop.store, &stop.states, &stop.actions, Ending::Kept)?;
                // What the spec prints as TLC replays the failure or rebuilds the trace comes
                // with the report, in an order the printing doesn't follow yet.
                if !failure.printed.is_empty()
                    || !trace.trace_output.is_empty()
                    || trace.states.iter().any(|state| !state.printed.is_empty())
                {
                    return Err(Unsupported("a failure in a spec that prints".into()));
                }
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
                    states.push((label, format_state(ir, &state.values)));
                }
                Ok(Report { failure, states })
            })
            .expect("a thread to evaluate the failure")
            .join()
            .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
            .map_err(|Unsupported(reason)| reason)
    })
}
