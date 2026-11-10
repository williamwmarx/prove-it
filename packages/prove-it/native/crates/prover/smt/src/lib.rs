//! A port of Z3 as tlapm runs it, `z3 -smt2 AUTO_CONFIG=false smt.MBQI=true`, on the SMT-LIB text
//! tlapm writes: `src/prover/smt/solver` in TypeScript (design/prover.md, stages P3a to P3c).

pub mod core;
pub mod lp;
pub mod nlsat;
pub mod util;

use prove_decide::{DecideError, Decision, Limits};

use crate::util::error::SmtError;

/// Z3's verdict on an SMT-LIB script: `decideZ3` of `deciders.ts`. Z3 rejects malformed input with
/// an error, and tlapm counts that as a failure, so a parse error is `DecideError::Prover` with its
/// message. Input that reaches the arithmetic theory, still a stub (`core::solver`'s header), is
/// declined, and so is a broken invariant of the port, where the TypeScript may go on
/// (design/smt-core.md, "Where the port refuses what the TS accepts"), so that the TypeScript
/// decides both.
pub fn decide(text: &str, limits: &Limits) -> Result<Decision, DecideError> {
    core::solver::decide_smt(text, limits).map_err(|error| match error {
        SmtError::Parse(message) => DecideError::Prover(message),
        error => DecideError::Declined(error.to_string()),
    })
}
