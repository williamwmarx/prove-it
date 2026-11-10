//! Z3's `math/lp`: `src/prover/smt/solver/lp` (design/prover.md, stage P3b-lp): the LAR solver,
//! the simplex core, bound propagation, the integer solver with cuts and the Diophantine
//! equations, and the NLA solver. `dependency` is stage P3a's, since `nlsat` uses it too.

pub mod constraints;
pub mod dependency;
pub mod explanation;
pub mod lar_term;
pub mod lp_settings;
pub mod numeric_pair;
