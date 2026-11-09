//! TLC's states as it prints them in a violation: rebuilt by `tla-trace` from the initial predicate
//! along the engine's path, so each value prints as TLC built it, and written as `TLCState.toString`
//! (`formatState` in `values.ts`) writes them, a line per variable in TLC's order, as a conjunction
//! when there are several. What the spec printed as TLC rebuilt the trace comes with it.

use tla_engine::search::{Violation, ViolationKind};
use tla_ir::Ir;
use tla_trace::{
    Alias, CounterExample, Ending, PostconditionInputs, Rebuilder, Stats, Unsupported, Value,
    Verdict, format_value,
};
use tla_values::Id;

use crate::check::SEARCH_STACK_BYTES;
use tla_trace::pretty_print;

/// A trace's states as TLC prints them, each with what TLC printed before it, and what it prints
/// after the trace.
pub struct PrintedTrace {
    pub states: Vec<PrintedState>,
    pub trace_output: Vec<String>,
    /// What the postconditions found on the trace, when the caller asked for them.
    pub postconditions: Option<Postconditions>,
}

/// What TLCGet reads after the search, for the postconditions.
pub struct PostconditionRun {
    /// Each `_POSSIBLE` predicate's name and count, -1 where TLC evaluated it on none.
    pub possible: Vec<(String, i64)>,
    pub stats: Stats,
}

/// What TLC printed as it evaluated the postconditions, each print as one line, and the first one
/// that doesn't hold, by its position in the model's postconditions, with what TLC found.
pub struct Postconditions {
    pub printed: Vec<String>,
    pub failure: Option<(usize, Verdict)>,
}

pub struct PrintedState {
    pub text: String,
    /// The position in the model's actions of the action that took the step to the state, as
    /// TLC finds it.
    pub action: Option<u32>,
    pub output: Vec<String>,
}

/// The violation's trace, or why `tla-trace` can't rebuild it. The evaluator recurses with the
/// expressions it evaluates, so it runs on a thread with the search's stack.
pub fn rebuild_trace(
    ir: &Ir,
    violation: &Violation,
    postconditions: Option<&PostconditionRun>,
) -> Result<PrintedTrace, String> {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(SEARCH_STACK_BYTES)
            .spawn_scoped(scope, || {
                let states: Vec<&[Id]> = violation.states.iter().map(Vec::as_slice).collect();
                // TLC holds a violating state as it found it, and recovers a deadlocked one.
                let ending = match violation.kind {
                    ViolationKind::Deadlock => Ending::Kept,
                    ViolationKind::Invariant(_) | ViolationKind::InitialInvariant(_) => {
                        Ending::Violation
                    }
                    ViolationKind::Lasso { .. } | ViolationKind::Accepted { .. } => Ending::Lasso,
                    ViolationKind::Error { .. } => {
                        return Err("a failure evaluating the model".into());
                    }
                };
                let cycle_start = match violation.kind {
                    ViolationKind::Lasso { loop_start, .. } => Some(loop_start),
                    _ => None,
                };
                // TLC prints each state through the ALIAS, when there is one.
                let rebuilt = Rebuilder::new(ir).and_then(|mut rebuilder| {
                    rebuilder.set_startup(
                        &violation.store,
                        &violation.startup,
                        violation.startup_random,
                    );
                    if let Some(group) = &violation.symmetry {
                        rebuilder.set_symmetry(group);
                    }
                    let trace =
                        rebuilder.rebuild(&violation.store, &states, &violation.labels, ending)?;
                    let aliases = rebuilder.alias(&trace, cycle_start)?;
                    // CounterExample closes a lasso with its step back into the cycle, which a
                    // stuttering one doesn't take.
                    let cycle = match violation.kind {
                        ViolationKind::Lasso {
                            loop_start,
                            loop_label: Some(label),
                        } => Some((loop_start, label)),
                        _ => None,
                    };
                    let checked = postconditions
                        .map(|run| {
                            check(
                                &mut rebuilder,
                                ir,
                                run,
                                Some(CounterExample {
                                    trace: &trace,
                                    cycle,
                                }),
                            )
                        })
                        .transpose()?;
                    Ok((trace, aliases, checked))
                });
                rebuilt
                    .map(|(trace, aliases, postconditions)| PrintedTrace {
                        postconditions,
                        states: trace
                            .states
                            .iter()
                            .enumerate()
                            .map(|(position, state)| PrintedState {
                                text: match aliases.as_ref().map(|aliases| &aliases[position]) {
                                    Some(Alias::Record(fields)) => format_fields(
                                        fields
                                            .iter()
                                            .map(|(name, value)| (name.as_str(), Some(value))),
                                    ),
                                    _ => format_state(ir, &state.values),
                                },
                                action: state.action,
                                output: state
                                    .printed
                                    .iter()
                                    .map(|print| format_print(print))
                                    .collect(),
                            })
                            .collect(),
                        trace_output: trace
                            .trace_output
                            .iter()
                            .map(|print| format_print(print))
                            .collect(),
                    })
                    .map_err(|Unsupported(reason)| reason)
            })
            .expect("a thread to rebuild the trace")
            .join()
            .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
    })
}

/// The postconditions of a search that completed, as TLC checks them, or why `tla-trace` can't.
pub fn check_postconditions(ir: &Ir, run: &PostconditionRun) -> Result<Postconditions, String> {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(SEARCH_STACK_BYTES)
            .spawn_scoped(scope, || {
                Rebuilder::new(ir)
                    .and_then(|mut rebuilder| check(&mut rebuilder, ir, run, None))
                    .map_err(|Unsupported(reason)| reason)
            })
            .expect("a thread to check the postconditions")
            .join()
            .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
    })
}

// Each postcondition in turn, up to the first that doesn't hold.
fn check(
    rebuilder: &mut Rebuilder<'_>,
    ir: &Ir,
    run: &PostconditionRun,
    counter_example: Option<CounterExample<'_>>,
) -> Result<Postconditions, Unsupported> {
    let mut printed = Vec::new();
    for index in 0..ir.model.postconditions.len() {
        let inputs = PostconditionInputs {
            possible: &run.possible,
            stats: run.stats,
            counter_example: counter_example.as_ref().map(|example| CounterExample {
                trace: example.trace,
                cycle: example.cycle,
            }),
        };
        let checked = rebuilder.postcondition(index, &inputs)?;
        printed.extend(checked.printed.iter().map(|print| format_print(print)));
        if checked.verdict != Verdict::Holds {
            return Ok(Postconditions {
                printed,
                failure: Some((index, checked.verdict)),
            });
        }
    }
    Ok(Postconditions {
        printed,
        failure: None,
    })
}

fn pretty(text: &str) -> String {
    pretty_print(&text.encode_utf16().collect::<Vec<_>>())
}

// What one Print or PrintT printed: each value pretty printed, two spaces apart.
pub(crate) fn format_print(texts: &[String]) -> String {
    texts
        .iter()
        .map(|text| pretty(text))
        .collect::<Vec<_>>()
        .join("  ")
}

/// A state's values, in the engine's order of the variables, as TLC prints the state.
pub(crate) fn format_state(ir: &Ir, values: &[Value]) -> String {
    format_partial_state(ir, &values.iter().map(Some).collect::<Vec<_>>())
}

/// A state some of whose variables are unassigned, which TLC prints as null.
pub(crate) fn format_partial_state(ir: &Ir, values: &[Option<&Value>]) -> String {
    format_fields(ir.tlc_order.iter().map(|&position| {
        (
            ir.texts[ir.variables[position as usize] as usize].as_ref(),
            values[position as usize],
        )
    }))
}

/// A state whose values are the texts TLC prints for them, in the IR's order of the variables.
pub(crate) fn format_texts(ir: &Ir, texts: &[String]) -> String {
    let is_conjunction = ir.tlc_order.len() > 1;
    let mut text = String::new();
    for &position in &ir.tlc_order {
        let conjunct = if is_conjunction { "/\\ " } else { "" };
        let name = &ir.texts[ir.variables[position as usize] as usize];
        text.push_str(&format!(
            "{conjunct}{name} = {}\n",
            pretty(&texts[position as usize])
        ));
    }
    text
}

/// Named values as TLC prints a state (`TLCStateMut.toString`): a line each, as a conjunction when
/// there are several.
fn format_fields<'v>(
    fields: impl ExactSizeIterator<Item = (&'v str, Option<&'v Value>)>,
) -> String {
    let is_conjunction = fields.len() > 1;
    let mut text = String::new();
    for (name, value) in fields {
        let conjunct = if is_conjunction { "/\\ " } else { "" };
        let value = value.map_or_else(|| "null".to_string(), |value| pretty(&format_value(value)));
        text.push_str(&format!("{conjunct}{name} = {value}\n"));
    }
    text
}
