//! Z3's `math/lp`: `src/prover/smt/solver/lp` (design/prover.md, stage P3b-lp): the LAR solver,
//! the simplex core, bound propagation, the integer solver with cuts and the Diophantine
//! equations, and the NLA solver. `dependency` is stage P3a's, since `nlsat` uses it too.

pub mod constraints;
pub mod dependency;
pub mod explanation;
pub mod hnf;
pub mod lar_term;
pub mod lp_settings;
pub mod nla_backoff;
pub mod nla_emonics;
pub mod nla_var_eqs;
pub mod numeric_pair;
pub mod union_find;
