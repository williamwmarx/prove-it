//! The decider of the propositional temporal logic tlapm sends LS4, on LS4's input text:
//! `src/prover/ptl` in TypeScript (design/prover.md, P1).

mod decide;
mod sat;
mod tableau;

pub use decide::decide;
