//! The prover's backends, for `src/prover/deciders.ts`: `decide(prover, text, timeLimitMs,
//! stepLimit, cancel)` decides the text tlapm would send `prover` within `timeLimitMs` and, when it
//! is a number, `stepLimit` steps, and returns one of:
//!
//! - `{ kind: "decided", verdict, statistics }`, the backend's answer and its statistics;
//! - `{ kind: "error", message }`, malformed input, which the caller throws as a `TlaProverError`;
//! - `{ kind: "declined", reason }`, where the Rust backend doesn't decide the input, so that the
//!   TypeScript one does.
//!
//! `cancel`, an `Int32Array` over shared memory whose first element another thread sets to cancel
//! the decision, reaches the backend only through the N-API binding, as a `Cancel` that reads it: a
//! WebAssembly decision runs on the thread that would set it.

pub use prove_it_prover::Cancel;
use prove_it_prover::{DecideError, Limits, Statistic};

use crate::hooks::HookResult;
use crate::sources::get_text;
use crate::value::HostValue;

/// The stack of the thread a decision runs on: the backends recurse as deep as the terms they
/// rewrite, which the stack of the thread JavaScript calls on doesn't hold.
#[cfg(not(target_arch = "wasm32"))]
const DECIDE_STACK_BYTES: usize = 256 * 1024 * 1024;

/// `decide(prover, text, timeLimitMs, stepLimit)`, on this thread: wasm's stack is the one it
/// links.
#[cfg(target_arch = "wasm32")]
pub fn decide(arguments: &[HostValue], cancel: Option<Cancel>) -> HookResult {
    decide_here(arguments, cancel)
}

/// `decide(prover, text, timeLimitMs, stepLimit)`, on a thread with a deep stack.
#[cfg(not(target_arch = "wasm32"))]
pub fn decide(arguments: &[HostValue], cancel: Option<Cancel>) -> HookResult {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(DECIDE_STACK_BYTES)
            .spawn_scoped(scope, || decide_here(arguments, cancel))
            .expect("a thread for the decision")
            .join()
            .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
    })
}

fn decide_here(arguments: &[HostValue], cancel: Option<Cancel>) -> HookResult {
    let [prover, text, time_limit, step_limit, ..] = arguments else {
        return Err("decide takes a prover, a text, a time limit and a step limit".into());
    };
    let prover = get_text(prover, "the prover")?;
    let text = get_text(text, "the text")?;
    let HostValue::Number(time_limit) = *time_limit else {
        return Err("the time limit must be a number of milliseconds".into());
    };
    let step_limit = match *step_limit {
        HostValue::Undefined | HostValue::Null => None,
        HostValue::Number(steps) if steps >= 0.0 && steps.fract() == 0.0 => Some(steps as u64),
        _ => return Err("the step limit must be a whole number or undefined".into()),
    };
    let limits = Limits::new(time_limit, step_limit, cancel);
    Ok(match prove_it_prover::decide(&prover, &text, &limits) {
        Ok(decision) => HostValue::Object(vec![
            ("kind", HostValue::text("decided")),
            ("verdict", HostValue::text(decision.verdict.name())),
            (
                "statistics",
                HostValue::Object(
                    decision
                        .statistics
                        .iter()
                        .map(|(name, statistic)| {
                            let value = match statistic {
                                Statistic::Count(count) => HostValue::Number(*count as f64),
                                Statistic::Text(text) => HostValue::text(text),
                            };
                            (*name, value)
                        })
                        .collect(),
                ),
            ),
        ]),
        Err(DecideError::Prover(message)) => HostValue::Object(vec![
            ("kind", HostValue::text("error")),
            ("message", HostValue::text(&message)),
        ]),
        Err(DecideError::Declined(reason)) => HostValue::Object(vec![
            ("kind", HostValue::text("declined")),
            ("reason", HostValue::text(&reason)),
        ]),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn get_kind(result: &HostValue) -> HostValue {
        let HostValue::Object(properties) = result else {
            panic!("decide returns an object");
        };
        properties[0].1.clone()
    }

    #[test]
    fn a_backend_not_ported_yet_declines() {
        let arguments = [
            HostValue::text("zenon"),
            HostValue::text("$goal p"),
            HostValue::Number(1000.0),
            HostValue::Undefined,
        ];
        let result = decide(&arguments, None).expect("a result");
        assert_eq!(get_kind(&result), HostValue::text("declined"));
    }

    #[test]
    fn a_step_limit_must_be_a_whole_number() {
        let arguments = [
            HostValue::text("ls4"),
            HostValue::text("p"),
            HostValue::Number(f64::INFINITY),
            HostValue::Number(1.5),
        ];
        assert!(decide(&arguments, None).is_err());
    }
}
