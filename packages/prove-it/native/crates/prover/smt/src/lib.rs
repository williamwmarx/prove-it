//! A port of Z3 as tlapm runs it, `z3 -smt2 AUTO_CONFIG=false smt.MBQI=true`, on the SMT-LIB text
//! tlapm writes: `src/prover/smt/solver` in TypeScript (design/prover.md, stages P3a to P3c).

pub mod core;
pub mod lp;
pub mod nlsat;
pub mod util;

use prove_decide::{DecideError, Decision, Limits};

/// Declines every input until the port lands, so that the TypeScript backend decides it.
pub fn decide(_text: &str, _limits: &Limits) -> Result<Decision, DecideError> {
    Err(DecideError::Declined("Z3 isn't ported to Rust yet".into()))
}
