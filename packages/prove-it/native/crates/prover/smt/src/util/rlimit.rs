//! Ported from Z3 (src/util/rlimit.h, src/util/rlimit.cpp), MIT license, through `rlimit.ts`. The
//! resource limit of an ast_manager, shared by every context and rewriter that uses the manager:
//! `&ResourceLimit` everywhere, since every method takes `&self`. It cancels the work at the
//! deadline, when the cancel cell is set, or past the step limit.
//!
//! V8's heap check is not ported: the core stops at a cap on its own size instead
//! (design/prover.md 3.6), with `stop(StopReason::Heap)`.

use std::cell::Cell;
use std::rc::Rc;

use prove_decide::Limits;

use crate::util::error::SmtError;

/// The clock and the cancel cell are read on every 256th step, since a step costs less.
const CLOCK_CHECK_MASK: u64 = 255;

/// The cap on what a decision holds, in place of Z3's max_memory: the expressions the manager made,
/// the goal's formulas, the e-graph's nodes and the instances E-matching found, each about 140
/// bytes, so about 9 GB. Counts, so that it stops every run at the same step. The decider corpus
/// holds at most 7.3 million under its step limits.
pub const MAX_SIZE: usize = 1 << 26;

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
/// `decide` returns. Its clones share the stop reason too, so nlsat's managers, which keep one,
/// count and stop as the limit itself.
#[derive(Clone)]
pub struct ResourceLimit {
    limits: Limits,
    stop_reason: Rc<Cell<Option<StopReason>>>,
    time_checks: Rc<Cell<u64>>,
}

impl ResourceLimit {
    pub fn new(limits: &Limits) -> ResourceLimit {
        ResourceLimit {
            limits: limits.clone(),
            stop_reason: Rc::new(Cell::new(None)),
            time_checks: Rc::new(Cell::new(0)),
        }
    }

    /// m_count: the steps taken, which MBQI also uses as a random seed.
    pub fn count(&self) -> u64 {
        self.limits.steps()
    }

    /// memory::allocate past max_memory: fails once what the decision holds passes MAX_SIZE.
    pub fn check_size(&self, size: usize) -> Result<(), SmtError> {
        if size <= MAX_SIZE {
            return Ok(());
        }
        self.stop(StopReason::Heap);
        Err(SmtError::Canceled)
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

    /// Fails at the deadline or once the cancel cell is set, for loops that take no step, such as
    /// building or simplifying a large term. It counts no step, so it moves no step count, and it
    /// leaves a stop already made to the code that made it. It reads the clock on every 256th call.
    pub fn check_time(&self) -> Result<(), SmtError> {
        let calls = self.time_checks.get().wrapping_add(1);
        self.time_checks.set(calls);
        if calls & CLOCK_CHECK_MASK != 0 || self.stop_reason.get().is_some() {
            return Ok(());
        }
        let stop_reason = if self.limits.is_past_deadline() {
            StopReason::Time
        } else if self.limits.is_canceled() {
            StopReason::Signal
        } else {
            return Ok(());
        };
        self.stop_reason.set(Some(stop_reason));
        Err(SmtError::Canceled)
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

    #[test]
    fn a_time_check_stops_at_the_deadline_without_a_step() {
        let limits = Limits::new(-1.0, Some(1), None);
        let limit = ResourceLimit::new(&limits);
        assert!((1..256).all(|_| limit.check_time().is_ok()));
        assert_eq!(limit.check_time(), Err(SmtError::Canceled));
        assert_eq!(limit.stop_reason(), Some(StopReason::Time));
        assert_eq!(limit.count(), 0);
        let stepped = ResourceLimit::new(&limits);
        assert!(!(0..2).all(|_| stepped.inc()));
        assert!((0..512).all(|_| stepped.check_time().is_ok()));
        assert_eq!(stepped.stop_reason(), Some(StopReason::Steps));
    }

    #[test]
    fn a_clone_counts_and_stops_with_the_limit() {
        let limits = Limits::new(f64::INFINITY, Some(2), None);
        let limit = ResourceLimit::new(&limits);
        let clone = limit.clone();
        assert!(clone.inc());
        assert!(limit.inc());
        assert!(!clone.inc());
        assert_eq!(limit.stop_reason(), Some(StopReason::Steps));
        assert!(!limit.inc());
        assert_eq!(limit.count(), 4);
        let other = ResourceLimit::new(&Limits::new(f64::INFINITY, None, None));
        other.clone().stop(StopReason::Heap);
        assert_eq!(other.stop_reason(), Some(StopReason::Heap));
    }
}
