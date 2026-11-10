// Ported from Z3 (src/math/lp/nla_monotone_lemmas.h, src/math/lp/nla_monotone_lemmas.cpp), MIT
// license, see z3-license.txt. The monotonicity lemmas of nla: the absolute value of a monomial is
// at most, or at least, the product of its factors' absolute values when they are.
//
// Monics are monic indices (see nla_core.rs). Monotone has no state; its functions take the view.
use std::cmp::Ordering;

use prove_num::Rational;

use crate::lp::constraints::{KIND_GE, KIND_GT, KIND_LE, KIND_LT};
use crate::lp::nla_core::Nla;
use crate::lp::nla_throttle::{NlaThrottle, THROTTLE_MONOTONE_LEMMA};
use crate::lp::nla_types::{LemmaBuilder, mk_ineq};

#[derive(Default)]
pub struct Monotone {}

impl Monotone {
    pub fn monotonicity_lemma(nla: &mut Nla<'_, '_>) {
        let shift = nla.random() as usize;
        let size = nla.to_refine.size();
        for index in 0..size {
            if nla.done() {
                break;
            }
            let monic = nla
                .emons
                .get_index(nla.to_refine.elems[(index + shift) % size]);
            Monotone::monotonicity_lemma_on_monic(nla, monic);
        }
    }

    fn monotonicity_lemma_on_monic(nla: &mut Nla<'_, '_>, monic: usize) {
        if nla.mon_has_zero(&nla.emons.monics[monic].vars) || nla.has_big_num(monic) {
            return;
        }
        let product_value = nla.product_value(monic).abs();
        let monic_value = nla.var_val(monic).abs();
        let is_lt = monic_value.compare(&product_value) == Ordering::Less;
        let variable = nla.emons.monics[monic].variable;
        if NlaThrottle::insert_monotone(nla.lra, THROTTLE_MONOTONE_LEMMA, variable, is_lt) {
            return;
        }
        if is_lt {
            Monotone::monotonicity_lemma_lt(nla, monic);
        } else if monic_value.compare(&product_value) == Ordering::Greater {
            Monotone::monotonicity_lemma_gt(nla, monic);
        }
    }

    // /\_i |m[i]| <= |val(m[i])| => |m| <= |product_i val(m[i])|
    fn monotonicity_lemma_gt(nla: &mut Nla<'_, '_>, monic: usize) {
        let lemma = LemmaBuilder::new(nla);
        let mut product = Rational::one();
        for index in 0..nla.emons.monics[monic].vars.len() {
            let lp_var = nla.emons.monics[monic].vars[index];
            let value = nla.val(lp_var);
            let cmp = if value.is_negative() {
                KIND_LT
            } else {
                KIND_GT
            };
            lemma.add_ineq(nla, mk_ineq(lp_var, cmp, value.clone()));
            let cmp = if value.is_negative() {
                KIND_GT
            } else {
                KIND_LT
            };
            lemma.add_ineq(nla, mk_ineq(lp_var, cmp, Rational::zero()));
            product = product.mul(&value);
        }
        let variable = nla.emons.monics[monic].variable;
        let cmp = if product.is_negative() {
            KIND_GE
        } else {
            KIND_LE
        };
        lemma.add_ineq(nla, mk_ineq(variable, cmp, product));
    }

    // /\_i |m[i]| >= |val(m[i])| => |m| >= |product_i val(m[i])|
    fn monotonicity_lemma_lt(nla: &mut Nla<'_, '_>, monic: usize) {
        let lemma = LemmaBuilder::new(nla);
        let mut product = Rational::one();
        for index in 0..nla.emons.monics[monic].vars.len() {
            let lp_var = nla.emons.monics[monic].vars[index];
            let value = nla.val(lp_var);
            let cmp = if value.is_negative() {
                KIND_GT
            } else {
                KIND_LT
            };
            lemma.add_ineq(nla, mk_ineq(lp_var, cmp, value.clone()));
            product = product.mul(&value);
        }
        let variable = nla.emons.monics[monic].variable;
        let cmp = if product.is_negative() {
            KIND_LE
        } else {
            KIND_GE
        };
        lemma.add_ineq(nla, mk_ineq(variable, cmp, product));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lp::nla_core::tests::{NlaFixture, show_lemmas};

    // The expected states and lemmas are the TS oracle's on the same setups.

    // |x*y| = 1 below |2 * 3|: the bounds explain the lemma away, and the second call is
    // throttled.
    #[test]
    fn bounds_a_monic_below_its_product() {
        let (mut fixture, _) = NlaFixture::mk_scenario(
            3,
            &[(2, &[0, 1])],
            &[
                (0, KIND_GE, 2),
                (1, KIND_GE, 3),
                (2, KIND_GE, 1),
                (2, KIND_LE, 1),
            ],
        );
        fixture.with_nla(|nla| {
            Monotone::monotonicity_lemma(nla);
            Monotone::monotonicity_lemma(nla);
        });
        assert_eq!(fixture.show_state(), "values 2,3,1 toRefine 2");
        assert_eq!(show_lemmas(&fixture.core), ["[] {0,1,3}"]);
    }

    // |x*y| = 10 above |-2 * 3|.
    #[test]
    fn bounds_a_monic_above_its_product() {
        let (mut fixture, _) = NlaFixture::mk_scenario(
            3,
            &[(2, &[0, 1])],
            &[(0, KIND_LE, -2), (1, KIND_GE, 3), (2, KIND_GE, 10)],
        );
        fixture.with_nla(Monotone::monotonicity_lemma);
        assert_eq!(fixture.show_state(), "values -2,3,10 toRefine 2");
        assert_eq!(
            show_lemmas(&fixture.core),
            ["[1*v0 -1 -2 | 1*v1 1 3 | 1*v2 2 -6] {0,1}"]
        );
    }
}
