//! A port of the parts of Isabelle that TLAPS proofs use, deciding the theory tlapm writes:
//! `src/prover/isabelle` in TypeScript (design/prover.md, P4a and P4b). One module per
//! TypeScript file, named after it.

// Tactics, sequences and conversions are closures over closures, as in Isabelle.
#![allow(clippy::type_complexity)]

mod decide;
pub mod error;
pub mod isar;
pub mod provers;
pub mod pure;
pub mod tla;
pub mod tools;

pub use decide::decide;
