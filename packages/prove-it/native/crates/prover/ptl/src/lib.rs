//! The decider of the propositional temporal logic tlapm sends LS4, on LS4's input text:
//! `src/prover/ptl` in TypeScript (design/prover.md, P1).

use prove_decide::{DecideError, Decision, Limits};

/// Declines every input until the port lands, so that the TypeScript backend decides it.
pub fn decide(_text: &str, _limits: &Limits) -> Result<Decision, DecideError> {
    Err(DecideError::Declined(
        "the PTL decider isn't ported to Rust yet".into(),
    ))
}
