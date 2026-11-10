//! Ported from Z3 (src/util/rlimit.h, src/util/rlimit.cpp), MIT license, through `rlimit.ts`. The
//! resource limit of an ast_manager, shared by every context and rewriter that uses the manager:
//! `&ResourceLimit` everywhere, since every method takes `&self`. It cancels the work at the
//! deadline, when the cancel cell is set, or past the step limit.
//!
//! V8's heap check is not ported: the core stops at a cap on its own size instead
//! (design/prover.md 3.6), with `stop(StopReason::Heap)`.

use std::cell::Cell;

use prove_decide::Limits;

use crate::util::error::SmtError;

/// The clock and the cancel cell are read on every 256th step, since a step costs less.
const CLOCK_CHECK_MASK: u64 = 255;

/// Why the work was canceled: the statistic `stop`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StopReason {
    Steps,
    Time,
    Signal,
    Heap,
}

impl StopReason {
    pub fn name(self) -> &'static str {
        match self {
            StopReason::Steps => "steps",
            StopReason::Time => "time",
            StopReason::Signal => "signal",
            StopReason::Heap => "heap",
        }
    }
}

/// Holds a clone of the decision's `Limits`, which counts the same steps; nothing keeps it after
/// `decide` returns.
pub struct ResourceLimit {
    limits: Limits,
    stop_reason: Cell<Option<StopReason>>,
}

impl ResourceLimit {
    pub fn new(limits: &Limits) -> ResourceLimit {
        ResourceLimit {
            limits: limits.clone(),
            stop_reason: Cell::new(None),
        }
    }

    /// m_count: the steps taken, which MBQI also uses as a random seed.
    pub fn count(&self) -> u64 {
        self.limits.steps()
    }

    /// Why the work was canceled, once it is.
    pub fn stop_reason(&self) -> Option<StopReason> {
        self.stop_reason.get()
    }

    /// inc: counts a step and returns whether the work may go on.
    pub fn inc(&self) -> bool {
        let is_over_step_limit = self.limits.is_step_limit_reached();
        if self.stop_reason.get().is_some() {
            return false;
        }
        let stop_reason = if is_over_step_limit {
            Some(StopReason::Steps)
        } else if self.limits.steps() & CLOCK_CHECK_MASK != 0 {
            None
        } else if self.limits.is_past_deadline() {
            Some(StopReason::Time)
        } else if self.limits.is_canceled() {
            Some(StopReason::Signal)
        } else {
            None
        };
        if stop_reason.is_none() {
            return true;
        }
        self.stop_reason.set(stop_reason);
        false
    }

    /// tactic::checkpoint: counts a step, and fails once the work is canceled.
    pub fn checkpoint(&self) -> Result<(), SmtError> {
        if self.inc() {
            Ok(())
        } else {
            Err(SmtError::Canceled)
        }
    }

    /// Cancels the work for a reason of the port's own, such as the core's size cap.
    pub fn stop(&self, reason: StopReason) {
        if self.stop_reason.get().is_none() {
            self.stop_reason.set(Some(reason));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_step_limit_stops_the_work_and_says_why() {
        let limits = Limits::new(f64::INFINITY, Some(2), None);
        let limit = ResourceLimit::new(&limits);
        assert!(limit.inc());
        assert_eq!(limit.checkpoint(), Ok(()));
        assert!(!limit.inc());
        assert_eq!(limit.stop_reason(), Some(StopReason::Steps));
        assert_eq!(limit.checkpoint(), Err(SmtError::Canceled));
        assert_eq!(limit.count(), limits.steps());
    }

    #[test]
    fn the_deadline_is_read_on_every_256th_step() {
        let limits = Limits::new(-1.0, None, None);
        let limit = ResourceLimit::new(&limits);
        assert!((1..256).all(|_| limit.inc()));
        assert!(!limit.inc());
        assert_eq!(limit.stop_reason(), Some(StopReason::Time));
    }
}
