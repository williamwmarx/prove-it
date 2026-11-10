// Ported from Z3 (src/math/lp/nla_throttle.h, src/math/lp/nla_throttle.cpp), MIT license, see
// z3-license.txt. The signatures of the lemmas nla has generated in the current scope, so that a
// pass does not generate the same lemma twice.
//
// TS's NlaThrottle holds the lar_solver, whose trail undoes its set of signatures, and the stats.
// Here the set is the lar_solver's (`LarSolver::insert_nla_throttle_seen`, keyed by the 8 values
// that TS joins into a string), so NlaThrottle has no state and its functions take the solver.
use prove_num::Rational;

use crate::lp::lar_solver::LarSolver;

pub const THROTTLE_ORDER_LEMMA: u32 = 0;
pub const THROTTLE_BINOMIAL_SIGN_LEMMA: u32 = 1;
pub const THROTTLE_MONOTONE_LEMMA: u32 = 2;
pub const THROTTLE_TANGENT_LEMMA: u32 = 3;

fn pack_rational_sign(value: &Rational) -> u32 {
    if value.is_positive() {
        1
    } else if value.is_negative() {
        255
    } else {
        0
    }
}

fn normalize_sign(sign: i32) -> u32 {
    sign.wrapping_add(127) as u32
}

// An lp variable as a value of a signature: TS's -1 (NULL_LPVAR) becomes u32::MAX, a key no
// variable has, so equal TS keys stay equal keys here.
fn get_var_key(lp_var: usize) -> u32 {
    lp_var as u32
}

pub struct NlaThrottle;

impl NlaThrottle {
    // insert_new: whether the signature, its values padded with zeros to 8, was seen, recording it
    // when not.
    fn insert_new(lra: &mut LarSolver<'_>, values: &[u32]) -> bool {
        let mut key = [0; 8];
        key[..values.len()].copy_from_slice(values);
        if !lra.insert_nla_throttle_seen(key) {
            lra.settings_mut().stats.nla_throttled_lemmas += 1;
            return true;
        }
        false
    }

    pub fn insert_monotone(
        lra: &mut LarSolver<'_>,
        kind: u32,
        monic_var: usize,
        is_lt: bool,
    ) -> bool {
        NlaThrottle::insert_new(lra, &[kind, get_var_key(monic_var), u32::from(is_lt)])
    }

    pub fn insert_binomial_sign(
        lra: &mut LarSolver<'_>,
        kind: u32,
        xy_var: usize,
        x: usize,
        y: usize,
        sign: i32,
        sy: i32,
    ) -> bool {
        NlaThrottle::insert_new(
            lra,
            &[
                kind,
                get_var_key(xy_var),
                get_var_key(x),
                get_var_key(y),
                normalize_sign(sign),
                normalize_sign(sy),
            ],
        )
    }

    #[allow(clippy::too_many_arguments)]
    pub fn insert_order(
        lra: &mut LarSolver<'_>,
        kind: u32,
        ac_var: usize,
        a: usize,
        c_sign: &Rational,
        c: usize,
        bd_var: usize,
        b_var: usize,
        d_sign: &Rational,
        d: usize,
        ab_cmp: i32,
    ) -> bool {
        let last = (pack_rational_sign(d_sign) << 24)
            | ((get_var_key(d) & 0xffff) << 8)
            | ((ab_cmp as u32) & 0xff);
        NlaThrottle::insert_new(
            lra,
            &[
                kind,
                get_var_key(ac_var),
                get_var_key(a),
                pack_rational_sign(c_sign),
                get_var_key(c),
                get_var_key(bd_var),
                get_var_key(b_var),
                last,
            ],
        )
    }

    pub fn insert_tangent(
        lra: &mut LarSolver<'_>,
        kind: u32,
        monic_var: usize,
        x_var: usize,
        y_var: usize,
        is_below: bool,
        plane_type: u32,
    ) -> bool {
        NlaThrottle::insert_new(
            lra,
            &[
                kind,
                get_var_key(monic_var),
                get_var_key(x_var),
                get_var_key(y_var),
                u32::from(is_below),
                plane_type,
            ],
        )
    }

    // The simplified tangent signature, without the plane type.
    pub fn insert_simplified_tangent(
        lra: &mut LarSolver<'_>,
        kind: u32,
        monic_var: usize,
        x_var: usize,
        y_var: usize,
        is_below: bool,
    ) -> bool {
        NlaThrottle::insert_new(
            lra,
            &[
                kind,
                get_var_key(monic_var),
                get_var_key(x_var),
                get_var_key(y_var),
                u32::from(is_below),
            ],
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // As the TS: a signature is new once per scope, and its repeat counts a throttled lemma.
    #[test]
    fn throttles_a_repeated_signature_until_the_scope_is_popped() {
        let mut lra = LarSolver::new(Box::new(|| false));
        assert!(!NlaThrottle::insert_monotone(
            &mut lra,
            THROTTLE_MONOTONE_LEMMA,
            3,
            true
        ));
        lra.push();
        assert!(NlaThrottle::insert_monotone(
            &mut lra,
            THROTTLE_MONOTONE_LEMMA,
            3,
            true
        ));
        assert!(!NlaThrottle::insert_monotone(
            &mut lra,
            THROTTLE_MONOTONE_LEMMA,
            3,
            false
        ));
        assert!(!NlaThrottle::insert_order(
            &mut lra,
            THROTTLE_ORDER_LEMMA,
            1,
            2,
            &Rational::minus_one(),
            3,
            4,
            5,
            &Rational::one(),
            6,
            -1,
        ));
        assert_eq!(lra.settings().stats.nla_throttled_lemmas, 1);
        lra.pop(1);
        assert!(!NlaThrottle::insert_monotone(
            &mut lra,
            THROTTLE_MONOTONE_LEMMA,
            3,
            false
        ));
        assert!(NlaThrottle::insert_monotone(
            &mut lra,
            THROTTLE_MONOTONE_LEMMA,
            3,
            true
        ));
        assert_eq!(lra.settings().stats.nla_throttled_lemmas, 2);
    }
}
