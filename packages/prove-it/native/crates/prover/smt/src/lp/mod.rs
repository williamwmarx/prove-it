//! Z3's `math/lp`: `src/prover/smt/solver/lp` (design/prover.md, stage P3b-lp): the LAR solver,
//! the simplex core, bound propagation, the integer solver with cuts and the Diophantine
//! equations, and the NLA solver. `dependency` is stage P3a's, since `nlsat` uses it too.

pub mod bound_propagator;
pub mod constraints;
pub mod containers;
pub mod core_solver;
pub mod cross_nested;
pub mod dep_intervals;
pub mod dependency;
pub mod dioph_eq;
pub mod explanation;
pub mod gomory;
pub mod hnf;
pub mod hnf_cutter;
pub mod int_cube;
pub mod int_solver;
pub mod json;
pub mod lar_solver;
pub mod lar_term;
pub mod lp_settings;
pub mod maximize_term;
pub mod nex;
pub mod nex_creator;
pub mod nla_backoff;
pub mod nla_basics;
pub mod nla_core;
pub mod nla_divisions;
pub mod nla_emonics;
pub mod nla_factorization;
pub mod nla_grobner;
pub mod nla_horner;
pub mod nla_intervals;
pub mod nla_monomial_bounds;
pub mod nla_monotone;
pub mod nla_order;
pub mod nla_patcher;
pub mod nla_tangents;
pub mod nla_throttle;
pub mod nla_types;
pub mod nla_var_eqs;
pub mod nra_solver;
pub mod numeric_pair;
pub mod pdd;
pub mod pdd_interval;
pub mod pdd_simplifier;
pub mod pdd_solver;
pub mod random_updater;
pub mod static_matrix;
pub mod trace;
pub mod union_find;

#[cfg(test)]
mod tests_int_solver;
#[cfg(test)]
mod tests_intervals;
