//! What every prover backend shares, as `src/prover/verdict.ts` defines it: the verdict on the text
//! tlapm would send the backend's prover, the limits a decision runs within, and the statistics it
//! reports, which are the same in every port of a backend so that two ports can be shown to make
//! the same search.

use std::cell::Cell;
use std::rc::Rc;
use std::sync::Arc;

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

/// Whether another thread has canceled the decision. The N-API binding reads it from a cell of
/// shared memory that JavaScript sets.
pub type Cancel = Arc<dyn Fn() -> bool + Send + Sync>;

/// The limits a decision runs within: a deadline, a number of steps, and whether another thread
/// canceled it. Each check of the limits is a step, as in the TypeScript backends; past the step
/// limit a backend gives up as it does at the deadline. Scripts set a step limit and no deadline,
/// so that what a backend answers doesn't depend on the machine; prove sets a deadline.
///
/// A handle that clones cheaply and has no lifetime, so that what a backend keeps beyond a borrow,
/// such as Isabelle's lazy sequences and tactics, can hold one; every clone counts the same steps.
/// It is not `Send`: a decision runs on one thread. A backend must not keep one once `decide`
/// returns.
#[derive(Clone)]
pub struct Limits(Rc<Inner>);

struct Inner {
    deadline: f64,
    step_limit: u64,
    steps: Cell<u64>,
    cancel: Option<Cancel>,
}

impl Limits {
    /// `time_limit` in milliseconds from now, which may be infinite.
    pub fn new(time_limit: f64, step_limit: Option<u64>, cancel: Option<Cancel>) -> Self {
        Limits(Rc::new(Inner {
            deadline: now() + time_limit,
            step_limit: step_limit.unwrap_or(u64::MAX),
            steps: Cell::new(0),
            cancel,
        }))
    }

    /// The steps taken so far.
    pub fn steps(&self) -> u64 {
        self.0.steps.get()
    }

    /// Counts a step, and returns whether the step limit is reached: `isStepLimitReached`.
    pub fn is_step_limit_reached(&self) -> bool {
        self.0.steps.set(self.0.steps.get() + 1);
        self.is_step_limit_passed()
    }

    /// Whether more steps than the limit have been taken, without counting one, as Zenon's
    /// `getStopReason` asks.
    pub fn is_step_limit_passed(&self) -> bool {
        self.0.steps.get() > self.0.step_limit
    }

    /// Whether more steps than the limit have been taken, without counting one.
    pub fn is_step_limit_passed(&self) -> bool {
        self.steps > self.step_limit
    }

    pub fn is_past_deadline(&self) -> bool {
        now() > self.0.deadline
    }

    pub fn is_canceled(&self) -> bool {
        self.0.cancel.as_ref().is_some_and(|cancel| cancel())
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
        let limits = Limits::new(f64::INFINITY, Some(2), None);
        assert!(!limits.is_step_limit_reached());
        assert!(!limits.is_step_limit_reached());
        assert!(!limits.is_step_limit_passed());
        assert!(limits.is_step_limit_reached());
        assert!(limits.is_step_limit_passed());
        assert_eq!(limits.steps(), 3);
    }

    #[test]
    fn clones_count_the_same_steps() {
        let limits = Limits::new(f64::INFINITY, Some(1), None);
        let clone = limits.clone();
        assert!(!clone.is_step_limit_reached());
        assert!(limits.is_step_limit_reached());
        assert_eq!(clone.steps(), 2);
    }

    #[test]
    fn cancels_once_the_cancel_says_so() {
        use std::sync::atomic::{AtomicBool, Ordering};
        let flag = Arc::new(AtomicBool::new(false));
        let cancel: Cancel = {
            let flag = Arc::clone(&flag);
            Arc::new(move || flag.load(Ordering::Relaxed))
        };
        let limits = Limits::new(f64::INFINITY, None, Some(cancel));
        assert!(!limits.is_canceled());
        flag.store(true, Ordering::Relaxed);
        assert!(limits.is_canceled());
        assert!(!limits.is_past_deadline());
    }

    #[test]
    fn a_deadline_already_passed_is_past() {
        assert!(Limits::new(-1.0, None, None).is_past_deadline());
    }
}
