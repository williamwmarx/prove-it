//! Z3's `math/lp`: `src/prover/smt/solver/lp` (design/prover.md, stage P3b-lp): the LAR solver,
//! the simplex core, bound propagation, the integer solver with cuts and the Diophantine
//! equations, and the NLA solver. `dependency` is stage P3a's, since `nlsat` uses it too.

pub mod constraints;
pub mod cross_nested;
pub mod dep_intervals;
pub mod dependency;
pub mod explanation;
pub mod hnf;
pub mod lar_term;
pub mod lp_settings;
pub mod nex;
pub mod nex_creator;
pub mod nla_backoff;
pub mod nla_emonics;
pub mod nla_var_eqs;
pub mod numeric_pair;
pub mod pdd;
pub mod pdd_interval;
pub mod pdd_simplifier;
pub mod pdd_solver;
pub mod union_find;

#[cfg(test)]
mod tests_intervals;
