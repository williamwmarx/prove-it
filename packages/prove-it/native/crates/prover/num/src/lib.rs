//! Big integers and rationals with the semantics of JavaScript's `bigint` that the TypeScript SMT
//! solver relies on (`src/prover/smt/solver/rational.ts`): `/` truncates toward zero, `%` takes
//! the dividend's sign and `>>` floors. Stage P3a of design/prover.md ports it.

mod int;
mod rational;

pub use int::{Int, ParseIntError};
pub use rational::{Rational, get_euclidean_div, get_euclidean_mod, get_gcd, get_lcm};
