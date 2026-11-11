//! tlapm's obligations, Prep and the backends' encoders, on tla-front's AST: `src/obligations` and
//! the encoders of `src/prover` in TypeScript. Stages P5b and P5c of design/prover.md port them.

pub mod action;
pub mod anonymize;
pub mod equality;
pub mod errors;
pub mod expression;
pub mod first_order;
pub mod format;
pub mod generate;
pub mod index;
pub mod isabelle;
pub mod levels;
pub mod marshal;
pub mod module;
pub mod normalize;
pub mod ocaml;
pub mod operators;
pub mod pragma;
pub mod prep;
pub mod printer;
pub mod proof;
pub mod ptl;
pub mod regroup;
pub mod ship;
pub mod simplify;
pub mod smt;
pub mod source;
pub mod subexpression;
pub mod substitution;
pub mod temporal;
pub mod tlaps_module;
pub mod tuples;
pub mod zenon;

/// Forgets every cache the crate keeps on this thread, as the TypeScript's modules keep theirs, so
/// that a run after it gives what a fresh process gives.
pub fn reset_caches() {
    levels::reset_caches();
    temporal::reset_caches();
    prep::normalize::reset_caches();
    prep::action::reset_caches();
}
