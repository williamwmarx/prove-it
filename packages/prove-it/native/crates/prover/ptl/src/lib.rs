//! The decider of the propositional temporal logic tlapm sends LS4, on LS4's input text
//! (design/prover.md, P1), and the only one: the TypeScript decider it ports is deleted.

mod decide;
mod sat;
mod tableau;

pub use decide::decide;
