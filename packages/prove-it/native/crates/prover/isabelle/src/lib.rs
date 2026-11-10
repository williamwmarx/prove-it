//! A port of the parts of Isabelle that TLAPS proofs use, deciding the theory tlapm writes:
//! `src/prover/isabelle` in TypeScript (design/prover.md, P4a and P4b). One module per
//! TypeScript file, named after it.

// Tactics, sequences and conversions are closures over closures, as in Isabelle.
#![allow(clippy::type_complexity)]

pub mod error;
pub mod isar;
pub mod pure;
pub mod tla;

use prove_decide::{DecideError, Decision, Limits};

/// Declines every input until the port lands, so that the TypeScript backend decides it.
pub fn decide(_text: &str, _limits: &mut Limits) -> Result<Decision, DecideError> {
    Err(DecideError::Declined(
        "Isabelle isn't ported to Rust yet".into(),
    ))
}
