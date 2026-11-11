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
use prove_it_prover::{DecideError, Decision, Limits, Statistic};

use crate::hooks::HookResult;
use crate::sources::get_text;
use crate::value::HostValue;

/// What `decide` was asked, read from its arguments.
struct Request {
    prover: String,
    text: String,
    time_limit: f64,
    step_limit: Option<u64>,
    cancel: Option<Cancel>,
}

type Answer = Result<Decision, DecideError>;

/// `decide(prover, text, timeLimitMs, stepLimit)`.
pub fn decide(arguments: &[HostValue], cancel: Option<Cancel>) -> HookResult {
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
    let request = Request {
        prover,
        text,
        time_limit,
        step_limit,
        cancel,
    };
    Ok(get_result(decide_request(request)))
}

fn decide_here(request: Request) -> Answer {
    let limits = Limits::new(request.time_limit, request.step_limit, request.cancel);
    prove_it_prover::decide(&request.prover, &request.text, &limits)
}

/// On this thread: wasm's stack is the one it links.
#[cfg(target_arch = "wasm32")]
fn decide_request(request: Request) -> Answer {
    decide_here(request)
}

/// On the calling thread's decide thread, which has a deep stack: the backends recurse as deep as
/// the terms they rewrite, which the stack of the thread JavaScript calls on doesn't hold. Each
/// calling thread keeps its own for as long as it lives, so that what a backend caches per thread,
/// such as Isabelle's decoded logic, serves every decision the thread makes.
#[cfg(not(target_arch = "wasm32"))]
fn decide_request(request: Request) -> Answer {
    use std::cell::RefCell;
    use std::panic::{AssertUnwindSafe, catch_unwind, resume_unwind};
    use std::sync::mpsc::{Receiver, Sender, channel};
    use std::thread::Result;

    const DECIDE_STACK_BYTES: usize = 256 * 1024 * 1024;

    struct DecideThread {
        requests: Sender<Request>,
        answers: Receiver<Result<Answer>>,
    }

    let spawn = || {
        let (requests, received) = channel::<Request>();
        let (answered, answers) = channel();
        std::thread::Builder::new()
            .name("prove-it decide".into())
            .stack_size(DECIDE_STACK_BYTES)
            .spawn(move || {
                // It ends when its calling thread does, which drops the sender.
                for request in received {
                    let answer = catch_unwind(AssertUnwindSafe(|| decide_here(request)));
                    if answered.send(answer).is_err() {
                        break;
                    }
                }
            })
            .expect("a thread for the decisions");
        DecideThread { requests, answers }
    };

    thread_local! {
        static DECIDE_THREAD: RefCell<Option<DecideThread>> = const { RefCell::new(None) };
    }
    let answer = DECIDE_THREAD.with_borrow_mut(|decide_thread| {
        let thread = decide_thread.get_or_insert_with(spawn);
        thread.requests.send(request).expect("the decide thread");
        let answer = thread.answers.recv().expect("the decide thread's answer");
        // A panic may leave the thread's caches half built, so the next decision gets a new one.
        if answer.is_err() {
            *decide_thread = None;
        }
        answer
    });
    answer.unwrap_or_else(|panic| resume_unwind(panic))
}

fn get_result(answer: Answer) -> HostValue {
    match answer {
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
    }
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
    fn a_prover_without_a_backend_declines() {
        let arguments = [
            HostValue::text("cvc4"),
            HostValue::text(""),
            HostValue::Number(1000.0),
            HostValue::Undefined,
        ];
        let result = decide(&arguments, None).expect("a result");
        assert_eq!(get_kind(&result), HostValue::text("declined"));
    }

    // Each decision of a calling thread runs on the same decide thread, after the last.
    #[test]
    fn a_thread_decides_again() {
        let arguments = [
            HostValue::text("ls4"),
            HostValue::text("p"),
            HostValue::Number(f64::INFINITY),
            HostValue::Undefined,
        ];
        for _ in 0..3 {
            let result = decide(&arguments, None).expect("a result");
            assert_eq!(get_kind(&result), HostValue::text("decided"));
        }
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
