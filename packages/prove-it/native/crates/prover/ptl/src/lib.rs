//! The decider of the propositional temporal logic tlapm sends LS4 (design/prover.md, P1): a port
//! of ptl_to_trp, which turns tlapm's text into LS4's clause set, and of LS4's reading of that
//! clause set, whose satisfiability a tableau decides in LS4's place.

mod decide;
mod sat;
mod spec;
mod tableau;
mod translate;

pub use decide::decide;
