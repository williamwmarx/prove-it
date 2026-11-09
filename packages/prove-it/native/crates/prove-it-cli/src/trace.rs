//! TLC's states as it prints them in a violation: rebuilt by `tla-trace` from the initial predicate
//! along the engine's path, so each value prints as TLC built it, and written as `TLCState.toString`
//! (`formatState` in `values.ts`) writes them, a line per variable in TLC's order, as a conjunction
//! when there are several. What the spec printed as TLC rebuilt the trace comes with it.

use tla_engine::search::{Violation, ViolationKind};
use tla_ir::Ir;
use tla_trace::{Ending, Rebuilder, Unsupported, Value, format_value};
use tla_values::Id;

use crate::check::SEARCH_STACK_BYTES;
use tla_trace::pretty_print;

/// A trace's states as TLC prints them, each with what TLC printed before it, and what it prints
/// after the trace.
pub struct PrintedTrace {
    pub states: Vec<PrintedState>,
    pub trace_output: Vec<String>,
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
pub fn rebuild_trace(ir: &Ir, violation: &Violation) -> Result<PrintedTrace, String> {
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
                    ViolationKind::Lasso { .. } => Ending::Lasso,
                };
                let trace = Rebuilder::new(ir).and_then(|mut rebuilder| {
                    rebuilder.rebuild(&violation.store, &states, &violation.labels, ending)
                });
                trace
                    .map(|trace| PrintedTrace {
                        states: trace
                            .states
                            .iter()
                            .map(|state| PrintedState {
                                text: format_state(ir, &state.values),
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

fn pretty(text: &str) -> String {
    pretty_print(&text.encode_utf16().collect::<Vec<_>>())
}

// What one Print or PrintT printed: each value pretty printed, two spaces apart.
fn format_print(texts: &[String]) -> String {
    texts
        .iter()
        .map(|text| pretty(text))
        .collect::<Vec<_>>()
        .join("  ")
}

/// A state's values, in the engine's order of the variables, as TLC prints the state.
fn format_state(ir: &Ir, values: &[Value]) -> String {
    let is_conjunction = ir.tlc_order.len() > 1;
    let mut text = String::new();
    for &position in &ir.tlc_order {
        let value = pretty(&format_value(&values[position as usize]));
        let name = &ir.texts[ir.variables[position as usize] as usize];
        let conjunct = if is_conjunction { "/\\ " } else { "" };
        text.push_str(&format!("{conjunct}{name} = {value}\n"));
    }
    text
}
