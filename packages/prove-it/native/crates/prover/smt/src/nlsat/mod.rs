//! nlsat, Z3's solver for nonlinear real arithmetic, ported from `src/prover/smt/solver/nlsat`
//! (design/prover.md, track P3b-nlsat): binary rationals, univariate and multivariate integer
//! polynomials with their factorization, real algebraic numbers, and the solver with its levelwise
//! projection and explanations.

pub mod algebraic;
pub mod atoms;
#[cfg(test)]
mod differential_tests;
pub mod evaluator;
pub mod explain;
pub mod interval_set;
pub mod levelwise;
pub mod mpbq;
pub mod polynomial;
pub mod solver;
#[cfg(test)]
mod test_util;
pub mod types;
pub mod upolynomial;
pub mod upolynomial_factorization;

pub use crate::lp::dependency::{Dependency, DependencyNode, linearize, mk_join, mk_leaf};
pub use crate::util::error::SmtError;
pub use crate::util::lbool::LBool;
pub use crate::util::random_gen::RandomGen;
pub use crate::util::rlimit::ResourceLimit;
pub use prove_num::{Int, Rational, get_gcd, get_lcm};

/// `lbool.ts`'s names for the three truth values.
pub const L_TRUE: LBool = LBool::True;
pub const L_FALSE: LBool = LBool::False;
pub const L_UNDEF: LBool = LBool::Undef;
