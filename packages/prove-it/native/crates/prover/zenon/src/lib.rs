//! A port of Zenon as tlapm ships it, with its TLA+ extension and an independent check of each
//! proof, on the .znn text tlapm writes: `src/prover/zenon` in TypeScript (design/prover.md, P2).
//! Zenon is Copyright INRIA, under the licence in `LICENSE` beside this crate; `ocaml` ports parts
//! of OCaml's standard library under the LGPL with OCaml's linking exception.

pub mod eqrel;
pub mod expr;
pub mod index_table;
pub mod limits;
pub mod llproof;
pub mod node;
pub mod ocaml;
pub mod parse;
pub mod phrase;
pub mod proof;
pub mod tla;

use prove_decide::{DecideError, Decision, Limits};

/// A malformed input or a failure that stops Zenon: `TlaZenonError`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ZenonError(pub String);

impl ZenonError {
    pub fn new(message: impl Into<String>) -> ZenonError {
        ZenonError(message.into())
    }
}

/// Declines every input until the port lands, so that the TypeScript backend decides it.
pub fn decide(_text: &str, _limits: &Limits) -> Result<Decision, DecideError> {
    Err(DecideError::Declined(
        "Zenon isn't ported to Rust yet".into(),
    ))
}
