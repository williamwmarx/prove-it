//! tlapm's obligations, Prep and the backends' encoders, on tla-front's AST: `src/obligations` and
//! the encoders of `src/prover` in TypeScript. Stages P5b and P5c of design/prover.md port them.

pub mod equality;
pub mod errors;
pub mod expression;
pub mod format;
pub mod levels;
pub mod operators;
pub mod pragma;
pub mod proof;
pub mod substitution;
pub mod temporal;
pub mod tuples;
