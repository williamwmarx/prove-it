//! What every prover backend shares, as `src/prover/verdict.ts` defines it: the verdict on the text
//! tlapm would send the backend's prover, the limits a decision runs within, and the statistics it
//! reports, which are the same in every port of a backend so that two ports can be shown to make
//! the same search.

use std::sync::atomic::{AtomicI32, Ordering};

/// A backend's answer. tlapm frames an obligation as unsat when the backend proves it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Verdict {
    Unsat,
    Sat,
    Unknown,
}

impl Verdict {
    pub fn name(self) -> &'static str {
        match self {
            Verdict::Unsat => "unsat",
            Verdict::Sat => "sat",
            Verdict::Unknown => "unknown",
        }
    }
}

/// One of a backend's statistics, under the name the TypeScript backend gives it.
#[derive(Clone, Debug, PartialEq)]
pub enum Statistic {
    Count(u64),
    Text(String),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Decision {
    pub verdict: Verdict,
    /// In the order the TypeScript backend writes them.
    pub statistics: Vec<(&'static str, Statistic)>,
}

/// Why a backend gives no decision.
#[derive(Clone, Debug, PartialEq)]
pub enum DecideError {
    /// The input is malformed, as a `TlaProverError` reports it: tlapm counts it as a failure.
    Prover(String),
    /// The port doesn't decide this input, so the TypeScript backend does.
    Declined(String),
}

/// The limits a decision runs within: a deadline, a number of steps, and a cell another thread
/// sets to cancel it. Each check of the limits is a step, as in the TypeScript backends; past the
/// step limit a backend gives up as it does at the deadline. Scripts set a step limit and no
/// deadline, so that what a backend answers doesn't depend on the machine; prove sets a deadline.
pub struct Limits<'a> {
    deadline: f64,
    step_limit: u64,
    steps: u64,
    cancel: Option<&'a AtomicI32>,
}

impl<'a> Limits<'a> {
    /// `time_limit` in milliseconds from now, which may be infinite; `cancel` is canceled once it
    /// holds anything but 0.
    pub fn new(time_limit: f64, step_limit: Option<u64>, cancel: Option<&'a AtomicI32>) -> Self {
        Limits {
            deadline: now() + time_limit,
            step_limit: step_limit.unwrap_or(u64::MAX),
            steps: 0,
            cancel,
        }
    }

    /// The steps taken so far.
    pub fn steps(&self) -> u64 {
        self.steps
    }

    /// Counts a step, and returns whether the step limit is reached: `isStepLimitReached`.
    pub fn is_step_limit_reached(&mut self) -> bool {
        self.steps += 1;
        self.steps > self.step_limit
    }

    /// Whether more steps than the limit have been taken, without counting one.
    pub fn is_step_limit_passed(&self) -> bool {
        self.steps > self.step_limit
    }

    pub fn is_past_deadline(&self) -> bool {
        now() > self.deadline
    }

    pub fn is_canceled(&self) -> bool {
        self.cancel
            .is_some_and(|cancel| cancel.load(Ordering::Relaxed) != 0)
    }
}

/// Milliseconds since some fixed point, as `Date.now()` serves the TypeScript backends.
#[cfg(not(target_arch = "wasm32"))]
fn now() -> f64 {
    use std::sync::OnceLock;
    use std::time::Instant;
    static START: OnceLock<Instant> = OnceLock::new();
    START.get_or_init(Instant::now).elapsed().as_secs_f64() * 1000.0
}

/// Milliseconds from the host, which WebAssembly has no clock of its own for: the import
/// `tla-engine`'s clock reads too.
#[cfg(target_arch = "wasm32")]
fn now() -> f64 {
    #[link(wasm_import_module = "env")]
    unsafe extern "C" {
        fn prove_it_now() -> f64;
    }
    // SAFETY: the loader provides the import, which takes nothing and returns a number.
    unsafe { prove_it_now() }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_step_limit_is_reached_on_the_step_past_it() {
        let mut limits = Limits::new(f64::INFINITY, Some(2), None);
        assert!(!limits.is_step_limit_reached());
        assert!(!limits.is_step_limit_reached());
        assert!(!limits.is_step_limit_passed());
        assert!(limits.is_step_limit_reached());
        assert!(limits.is_step_limit_passed());
        assert_eq!(limits.steps(), 3);
    }

    #[test]
    fn a_cell_that_holds_anything_but_zero_cancels() {
        let cell = AtomicI32::new(0);
        let limits = Limits::new(f64::INFINITY, None, Some(&cell));
        assert!(!limits.is_canceled());
        cell.store(1, Ordering::Relaxed);
        assert!(limits.is_canceled());
        assert!(!limits.is_past_deadline());
    }

    #[test]
    fn a_deadline_already_passed_is_past() {
        assert!(Limits::new(-1.0, None, None).is_past_deadline());
    }
}
