// Ported from Z3 (src/math/lp/factorization.h), MIT license, see z3-license.txt. A factor of a
// monic is a variable or a monic, with a sign. The core makes the factorizations, see
// get_factorizations in nla_core.rs.
use prove_num::Rational;

use crate::lp::nla_emonics::Emonics;
use crate::lp::nla_types::sign_to_rat;

// `variable` is the factor's lp variable, the monic's variable when `is_mon`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Factor {
    pub variable: usize,
    pub is_mon: bool,
    pub is_negated: bool,
}

pub fn mk_factor(variable: usize, is_mon: bool) -> Factor {
    Factor {
        variable,
        is_mon,
        is_negated: false,
    }
}

pub fn get_factor_sign(factor: &Factor) -> Rational {
    sign_to_rat(factor.is_negated)
}

// A factorization: the factors of a monic, whose monic index is set for the factorization into its
// variables.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Factorization {
    pub factors: Vec<Factor>,
    pub mon: Option<usize>,
}

pub fn mk_mon_factorization(emons: &Emonics, monic: usize) -> Factorization {
    Factorization {
        factors: emons.monics[monic]
            .vars
            .iter()
            .map(|lp_var| mk_factor(*lp_var, false))
            .collect(),
        mon: Some(monic),
    }
}
