// Ported from Z3 (src/util/rlimit.{h,cpp}, the checkpoints of src/math/polynomial and
// src/nlsat/nlsat_solver.cpp), MIT license, see z3-license.txt. m_limit: the resource limit that
// the nlsat solver shares with its polynomial, upolynomial and algebraic number managers. Every
// step counts against the resource limit and against the budget of the check, which Z3 sets with
// a scoped_rlimit on a child limit. A manager made without a solver has its own limit, which
// never stops.
//
// The TypeScript managers share one object; here a clone shares the state behind an `Rc`, and
// keeps a clone of the resource limit, whose clones share its count and stop reason.

use std::cell::Cell;
use std::fmt;
use std::rc::Rc;

use super::{ResourceLimit, SmtError};

#[derive(Clone, Default)]
pub struct NlsatLimit(Rc<NlsatLimitState>);

#[derive(Default)]
struct NlsatLimitState {
    steps: Cell<u64>,
    limit: Option<ResourceLimit>,
    budget: Option<u64>,
}

impl NlsatLimit {
    pub fn new(limit: Option<&ResourceLimit>, budget: Option<u64>) -> NlsatLimit {
        NlsatLimit(Rc::new(NlsatLimitState {
            steps: Cell::new(0),
            limit: limit.cloned(),
            budget,
        }))
    }

    pub fn steps(&self) -> u64 {
        self.0.steps.get()
    }

    /// inc: counts a step and returns whether the work may go on.
    pub fn inc(&self) -> bool {
        let state = &self.0;
        state.steps.set(state.steps.get() + 1);
        !(state.limit.as_ref().is_some_and(|limit| !limit.inc())
            || state
                .budget
                .is_some_and(|budget| state.steps.get() > budget))
    }

    /// checkpoint: counts a step, and fails once the work is canceled.
    pub fn checkpoint(&self) -> Result<(), SmtError> {
        if self.inc() {
            Ok(())
        } else {
            Err(SmtError::Canceled)
        }
    }
}

impl fmt::Debug for NlsatLimit {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "NlsatLimit({} steps)", self.steps())
    }
}
