// Ported from Z3 (src/math/lp/nla_order_lemmas.h, src/math/lp/nla_order_lemmas.cpp), MIT
// license, see z3-license.txt. The order lemmas of nla: a > b and c > 0 imply ac > bc, over the
// binary factorizations of the monomials to refine, and the sign lemmas of binomials.
//
// Monics are monic indices (see nla_core.rs). Order has no state; its functions take the view.
use std::cmp::Ordering;

use prove_num::Rational;

use crate::lp::constraints::{
    ConstraintKind, KIND_EQ, KIND_GE, KIND_GT, KIND_LE, KIND_LT, KIND_NE,
};
use crate::lp::lar_term::LarTerm;
use crate::lp::nla_core::{NLA_PARAMS, Nla};
use crate::lp::nla_factorization::{Factor, Factorization, get_factor_sign, mk_factor};
use crate::lp::nla_throttle::{NlaThrottle, THROTTLE_BINOMIAL_SIGN_LEMMA, THROTTLE_ORDER_LEMMA};
use crate::lp::nla_types::{
    LemmaBuilder, get_rat_sign, mk_ineq, mk_term_ineq, negate_kind, sign_to_rat,
};
use crate::lp::nla_var_eqs::get_signed_var_var;

#[derive(Default)]
pub struct Order {}

impl Order {
    pub fn order_lemma(nla: &mut Nla<'_, '_>) {
        if !NLA_PARAMS.order {
            return;
        }
        let offset = nla.random() as usize;
        let size = nla.to_refine.size();
        for index in 0..size {
            if nla.done() {
                break;
            }
            let monic = nla
                .emons
                .get_index(nla.to_refine.elems[(index + offset) % size]);
            Order::order_lemma_on_monic(nla, monic);
        }
    }

    fn order_lemma_on_monic(nla: &mut Nla<'_, '_>, monic: usize) {
        let mut factorizations = nla.get_factorizations(monic);
        while let Some(factorization) = factorizations.next(nla) {
            if factorization.factors.len() != 2 {
                continue;
            }
            match factorization.mon {
                Some(mon) => Order::order_lemma_on_binomial(nla, mon),
                None => Order::order_lemma_on_factorization(nla, monic, &factorization),
            }
            if nla.done() {
                break;
            }
        }
    }

    // Either variable of the binomial plays the role of c.
    fn order_lemma_on_binomial(nla: &mut Nla<'_, '_>, ac: usize) {
        let is_gt = nla.var_val(ac).compare(&nla.mul_val(ac)) == Ordering::Greater;
        for k in [0, 1] {
            let x = nla.emons.monics[ac].vars[k];
            let y = nla.emons.monics[ac].vars[1 - k];
            Order::order_lemma_on_binomial_sign(nla, ac, x, y, if is_gt { 1 } else { -1 });
            Order::order_lemma_on_factor_binomial_explore(nla, ac, k);
        }
    }

    // y <= 0 or x < a or xy >= ay, and the like for the sign of val(xy) - val(x) * val(y).
    fn order_lemma_on_binomial_sign(
        nla: &mut Nla<'_, '_>,
        xy: usize,
        x: usize,
        y: usize,
        sign: i32,
    ) {
        if !NLA_PARAMS.order_binomial_sign {
            return;
        }
        let x_value = nla.val(x);
        if !nla.var_is_int(x) && x_value.is_big() {
            return;
        }
        let y_sign = get_rat_sign(&nla.val(y));
        let xy_var = nla.emons.monics[xy].variable;
        if NlaThrottle::insert_binomial_sign(
            nla.lra,
            THROTTLE_BINOMIAL_SIGN_LEMMA,
            xy_var,
            x,
            y,
            sign,
            y_sign,
        ) {
            return;
        }
        let lemma = LemmaBuilder::new(nla);
        let cmp = if y_sign == 1 { KIND_LE } else { KIND_GE };
        lemma.add_ineq(nla, mk_ineq(y, cmp, Rational::zero()));
        let cmp = if y_sign * sign == 1 { KIND_GT } else { KIND_LT };
        lemma.add_ineq(nla, mk_ineq(x, cmp, x_value.clone()));
        let term = LarTerm::from_entries([(xy_var, &Rational::one()), (y, &x_value.neg())]);
        let cmp = if sign == 1 { KIND_LE } else { KIND_GE };
        lemma.add_ineq(nla, mk_term_ineq(term, cmp, Rational::zero()));
    }

    // The monics bd with d equivalent to ac[k].
    fn order_lemma_on_factor_binomial_explore(nla: &mut Nla<'_, '_>, ac: usize, k: usize) {
        let lp_var = nla.emons.monics[ac].vars[k];
        let mut products = nla.core.emons.get_products_of(lp_var, &nla.core.var_eqs);
        while let Some(bd) = products.next(&mut nla.core.emons) {
            if nla.emons.monics[bd].variable == nla.emons.monics[ac].variable {
                continue;
            }
            Order::order_lemma_on_factor_binomial_rm(nla, ac, k, bd);
            if nla.done() {
                break;
            }
        }
    }

    fn order_lemma_on_factor_binomial_rm(nla: &mut Nla<'_, '_>, ac: usize, k: usize, bd: usize) {
        let d = mk_factor(
            get_signed_var_var(nla.var_eqs.find_var(nla.emons.monics[ac].vars[k])),
            false,
        );
        if let Some(b) = nla.divide(bd, &d) {
            Order::order_lemma_on_binomial_ac_bd(nla, ac, k, bd, &b, d.variable);
        }
    }

    // ac >= bd && |c| = |d| => ac/|c| >= bd/|d|
    fn order_lemma_on_binomial_ac_bd(
        nla: &mut Nla<'_, '_>,
        ac: usize,
        k: usize,
        bd: usize,
        b: &Factor,
        d: usize,
    ) {
        let a = nla.emons.monics[ac].vars[1 - k];
        let c = nla.emons.monics[ac].vars[k];
        let ac_value = nla.var_val(ac);
        let c_sign = Rational::from(i64::from(get_rat_sign(&nla.val(c))));
        let d_sign = Rational::from(i64::from(get_rat_sign(&nla.val(d))));
        let bd_value = nla.var_val(bd);
        let a_times_c_sign = nla.val(a).mul(&c_sign);
        let b_times_d_sign = nla.val_factor(b).mul(&d_sign);
        let comparison = ac_value.compare(&bd_value);
        let factor_comparison = a_times_c_sign.compare(&b_times_d_sign);
        if comparison != Ordering::Less && factor_comparison == Ordering::Less {
            Order::generate_mon_ol(nla, ac, a, &c_sign, c, bd, b, &d_sign, d, KIND_LT);
        } else if comparison != Ordering::Greater && factor_comparison == Ordering::Greater {
            Order::generate_mon_ol(nla, ac, a, &c_sign, c, bd, b, &d_sign, d, KIND_GT);
        }
    }

    // ac > bd => ac/|c| > bd/|d| => a*c_sign > b*d_sign, whose last inequality does not hold.
    #[allow(clippy::too_many_arguments)]
    fn generate_mon_ol(
        nla: &mut Nla<'_, '_>,
        ac: usize,
        a: usize,
        c_sign: &Rational,
        c: usize,
        bd: usize,
        b: &Factor,
        d_sign: &Rational,
        d: usize,
        ab_cmp: ConstraintKind,
    ) {
        let ac_var = nla.emons.monics[ac].variable;
        let bd_var = nla.emons.monics[bd].variable;
        if NlaThrottle::insert_order(
            nla.lra,
            THROTTLE_ORDER_LEMMA,
            ac_var,
            a,
            c_sign,
            c,
            bd_var,
            b.variable,
            d_sign,
            d,
            ab_cmp,
        ) {
            return;
        }
        let lemma = LemmaBuilder::new(nla);
        let term = LarTerm::from_entries([(c, c_sign)]);
        lemma.add_ineq(nla, mk_term_ineq(term, KIND_LE, Rational::zero()));
        lemma.explain_var(nla, c);
        let term = LarTerm::from_entries([
            (a, c_sign),
            (b.variable, &d_sign.mul(&get_factor_sign(b)).neg()),
        ]);
        lemma.add_ineq(
            nla,
            mk_term_ineq(term, negate_kind(ab_cmp), Rational::zero()),
        );
        let term =
            LarTerm::from_entries([(ac_var, &Rational::one()), (bd_var, &Rational::minus_one())]);
        lemma.add_ineq(nla, mk_term_ineq(term, ab_cmp, Rational::zero()));
        lemma.explain_monic(nla, bd);
        lemma.explain_factor(nla, b);
        lemma.explain_var(nla, d);
    }

    // ac_f[k] plays the role of c.
    fn order_lemma_on_ac_and_bc(
        nla: &mut Nla<'_, '_>,
        ac: usize,
        ac_factorization: &Factorization,
        k: usize,
        bd: usize,
    ) -> bool {
        let factors = &ac_factorization.factors;
        match nla.divide(bd, &factors[k]) {
            Some(b) => Order::order_lemma_on_ac_and_bc_and_factors(
                nla,
                ac,
                &factors[1 - k],
                &factors[k],
                bd,
                &b,
            ),
            None => false,
        }
    }

    // m = ab: a monic n = cd with |b| = |d| gives m R n & |b| = |d| => ab/|b| R cd/|d|.
    fn order_lemma_on_factorization(nla: &mut Nla<'_, '_>, monic: usize, ab: &Factorization) {
        let mut is_negated = false;
        for factor in &ab.factors {
            is_negated = is_negated != factor.is_negated;
        }
        let sign = sign_to_rat(is_negated);
        let factors_value = nla
            .val(ab.factors[0].variable)
            .mul(&nla.val(ab.factors[1].variable));
        let monic_value = sign.mul(&nla.var_val(monic));
        if monic_value != factors_value && !nla.has_real(monic) {
            let is_gt = monic_value.compare(&factors_value) == Ordering::Greater;
            for (j, k) in [(0, 1), (1, 0)] {
                let lemma = LemmaBuilder::new(nla);
                Order::order_lemma_on_ab(
                    nla,
                    &lemma,
                    monic,
                    &sign,
                    ab.factors[k].variable,
                    ab.factors[j].variable,
                    is_gt,
                );
                lemma.explain_factorization(nla, ab);
                lemma.explain_monic(nla, monic);
            }
        }
        for k in [0, 1] {
            Order::order_lemma_on_ac_explore(nla, monic, ab, k);
        }
    }

    fn order_lemma_on_ac_explore(
        nla: &mut Nla<'_, '_>,
        rooted: usize,
        ac: &Factorization,
        k: usize,
    ) {
        let c = ac.factors[k];
        if c.is_mon {
            let mut candidates = nla
                .core
                .emons
                .get_products_of(c.variable, &nla.core.var_eqs);
            while let Some(bc) = candidates.next(&mut nla.core.emons) {
                if Order::order_lemma_on_ac_and_bc(nla, rooted, ac, k, bc) {
                    return;
                }
            }
            return;
        }
        let mut candidates = nla.core.emons.get_use_list(c.variable, &nla.core.var_eqs);
        while let Some(bc) = candidates.next(&nla.core.emons) {
            if Order::order_lemma_on_ac_and_bc(nla, rooted, ac, k, bc) {
                return;
            }
        }
    }

    fn generate_ol_eq(
        nla: &mut Nla<'_, '_>,
        ac: usize,
        a: &Factor,
        c: &Factor,
        bc: usize,
        b: &Factor,
    ) {
        let lemma = LemmaBuilder::new(nla);
        lemma.add_ineq(nla, mk_ineq(c.variable, KIND_EQ, Rational::zero()));
        let term = LarTerm::from_entries([
            (nla.emons.monics[ac].variable, &Rational::one()),
            (nla.emons.monics[bc].variable, &Rational::minus_one()),
        ]);
        lemma.add_ineq(nla, mk_term_ineq(term, KIND_NE, Rational::zero()));
        let term = LarTerm::from_entries([
            (a.variable, &get_factor_sign(a)),
            (b.variable, &get_factor_sign(b).neg()),
        ]);
        lemma.add_ineq(nla, mk_term_ineq(term, KIND_EQ, Rational::zero()));
        Order::explain_ol(nla, &lemma, ac, a, bc, b, c);
    }

    // c > 0 and ac >= bc => a >= b, and the like for the other signs and relations.
    fn generate_ol(
        nla: &mut Nla<'_, '_>,
        ac: usize,
        a: &Factor,
        c: &Factor,
        bc: usize,
        b: &Factor,
    ) {
        let lemma = LemmaBuilder::new(nla);
        let cmp = if nla.val(c.variable).is_negative() {
            KIND_GE
        } else {
            KIND_LE
        };
        lemma.add_ineq(nla, mk_ineq(c.variable, cmp, Rational::zero()));
        let term = LarTerm::from_entries([
            (nla.emons.monics[ac].variable, &Rational::one()),
            (nla.emons.monics[bc].variable, &Rational::minus_one()),
        ]);
        let cmp = if nla.var_val(ac).compare(&nla.var_val(bc)) == Ordering::Less {
            KIND_GT
        } else {
            KIND_LT
        };
        lemma.add_ineq(nla, mk_term_ineq(term, cmp, Rational::zero()));
        let term = LarTerm::from_entries([
            (a.variable, &get_factor_sign(a)),
            (b.variable, &get_factor_sign(b).neg()),
        ]);
        let cmp = if nla.val_factor(a).compare(&nla.val_factor(b)) == Ordering::Less {
            KIND_GE
        } else {
            KIND_LE
        };
        lemma.add_ineq(nla, mk_term_ineq(term, cmp, Rational::zero()));
        Order::explain_ol(nla, &lemma, ac, a, bc, b, c);
    }

    fn explain_ol(
        nla: &mut Nla<'_, '_>,
        lemma: &LemmaBuilder,
        ac: usize,
        a: &Factor,
        bc: usize,
        b: &Factor,
        c: &Factor,
    ) {
        lemma.explain_monic(nla, ac);
        lemma.explain_factor(nla, a);
        lemma.explain_monic(nla, bc);
        lemma.explain_factor(nla, b);
        lemma.explain_factor(nla, c);
    }

    // ac = a*c and bc = b*c: ac >= bc implies ac/|c| >= bc/|c|.
    fn order_lemma_on_ac_and_bc_and_factors(
        nla: &mut Nla<'_, '_>,
        ac: usize,
        a: &Factor,
        c: &Factor,
        bc: usize,
        b: &Factor,
    ) -> bool {
        let c_sign = Rational::from(i64::from(get_rat_sign(&nla.val_factor(c))));
        let a_times_c_sign = nla.val_factor(a).mul(&c_sign);
        let b_times_c_sign = nla.val_factor(b).mul(&c_sign);
        let comparison = nla.var_val(ac).compare(&nla.var_val(bc));
        let factor_comparison = a_times_c_sign.compare(&b_times_c_sign);
        if (comparison == Ordering::Greater && factor_comparison == Ordering::Less)
            || (comparison == Ordering::Less && factor_comparison == Ordering::Greater)
        {
            Order::generate_ol(nla, ac, a, c, bc, b);
            return true;
        }
        if comparison == Ordering::Equal && factor_comparison != Ordering::Equal {
            Order::generate_ol_eq(nla, ac, a, c, bc, b);
            return true;
        }
        false
    }

    // sign * m = ab: b != val(b) or sign*m <= a*val(b), or >= when not gt.
    fn order_lemma_on_ab(
        nla: &mut Nla<'_, '_>,
        lemma: &LemmaBuilder,
        monic: usize,
        sign: &Rational,
        a: usize,
        b: usize,
        is_gt: bool,
    ) {
        let b_value = nla.val(b);
        lemma.add_ineq(nla, mk_ineq(b, KIND_NE, b_value.clone()));
        let term = LarTerm::from_entries([
            (nla.emons.monics[monic].variable, sign),
            (a, &b_value.neg()),
        ]);
        let cmp = if is_gt { KIND_LE } else { KIND_GE };
        lemma.add_ineq(nla, mk_term_ineq(term, cmp, Rational::zero()));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lp::nla_core::tests::{NlaFixture, show_lemmas};

    // The expected states and lemmas are the TS oracle's on the same setups.

    // ac = a*c >= 5 and bc = b*c <= 1 with a >= 1, b >= 2 and c >= 1: the bounds explain the
    // binomial sign lemmas away, and ac >= bc with a < b gives ac < bc or a >= b.
    #[test]
    fn orders_the_binomials_with_a_positive_c() {
        let (mut fixture, constraints) = NlaFixture::mk_scenario(
            5,
            &[(3, &[0, 2]), (4, &[1, 2])],
            &[
                (0, KIND_GE, 1),
                (1, KIND_GE, 2),
                (2, KIND_GE, 1),
                (3, KIND_GE, 5),
                (4, KIND_LE, 1),
            ],
        );
        fixture.with_nla(Order::order_lemma);
        assert_eq!(constraints, [0, 1, 2, 3, 4]);
        assert_eq!(fixture.show_state(), "values 1,2,1,5,0 toRefine 3,4");
        assert_eq!(
            show_lemmas(&fixture.core),
            ["[] {1,2,4}", "[] {1,2,4}", "[-1*v0+1*v1 -2 0] {2,3,4}"]
        );
    }

    // The same with c <= -1, ac <= -10 and bc >= 1: ac < bc with -a > -b.
    #[test]
    fn orders_the_binomials_with_a_negative_c() {
        let (mut fixture, _) = NlaFixture::mk_scenario(
            5,
            &[(3, &[0, 2]), (4, &[1, 2])],
            &[
                (0, KIND_GE, 1),
                (1, KIND_GE, 2),
                (2, KIND_LE, -1),
                (3, KIND_LE, -10),
                (4, KIND_GE, 1),
            ],
        );
        fixture.with_nla(Order::order_lemma);
        assert_eq!(fixture.show_state(), "values 1,2,-1,-10,1 toRefine 3,4");
        assert_eq!(
            show_lemmas(&fixture.core),
            ["[] {1,2,4}", "[] {1,2,4}", "[1*v0+-1*v1 2 0] {2,3,4}"]
        );
    }

    // m = x*y*z, n = y*z, p = w*x and q = w*n: the binary factorizations of the monics to refine,
    // the binomials' sign lemmas, and the monics sharing a factor with them.
    #[test]
    fn orders_the_binary_factorizations() {
        let (mut fixture, _) = NlaFixture::mk_scenario(
            8,
            &[(3, &[0, 1, 2]), (4, &[1, 2]), (6, &[5, 0]), (7, &[5, 4])],
            &[
                (0, KIND_GE, 2),
                (1, KIND_GE, 3),
                (2, KIND_GE, 1),
                (3, KIND_LE, 1),
                (4, KIND_GE, 4),
                (5, KIND_GE, 1),
                (6, KIND_GE, 7),
                (7, KIND_LE, 0),
            ],
        );
        fixture.with_nla(Order::order_lemma);
        assert_eq!(
            fixture.show_state(),
            "values 2,3,1,0,4,1,7,0 toRefine 6,7,3,4"
        );
        assert_eq!(
            show_lemmas(&fixture.core),
            [
                "[1*v1 1 3 | -3*v2+1*v4 -2 0] {2}",
                "[1*v2 1 1 | -1*v1+1*v4 -2 0] {1}",
                "[1*v0 1 2 | -2*v5+1*v6 -2 0] {5}",
                "[-1*v4+1*v5 2 0] {0,3,6}",
                "[1*v5 1 1 | -1*v0+1*v6 -2 0] {0}",
                "[1*v0+-1*v4 2 0] {5,6,7}",
                "[] {4,5,7}",
                "[] {4,5,7}",
                "[-1*v0+1*v4 -2 0] {5,6,7}",
            ]
        );
    }

    // m = x*y*z = 6 and q = w*n = 6 with n = y*z = 3: only q is wrong.
    #[test]
    fn orders_a_binomial_over_a_monic() {
        let (mut fixture, _) = NlaFixture::mk_scenario(
            8,
            &[(3, &[0, 1, 2]), (4, &[1, 2]), (6, &[5, 4])],
            &[
                (0, KIND_GE, 2),
                (1, KIND_GE, 3),
                (2, KIND_GE, 1),
                (3, KIND_GE, 6),
                (3, KIND_LE, 6),
                (4, KIND_GE, 3),
                (5, KIND_GE, 1),
                (6, KIND_GE, 6),
                (6, KIND_LE, 6),
            ],
        );
        fixture.with_nla(Order::order_lemma);
        assert_eq!(fixture.show_state(), "values 2,3,1,6,3,1,6,0 toRefine 6");
        assert_eq!(
            show_lemmas(&fixture.core),
            [
                "[1*v4 1 3 | -3*v5+1*v6 -2 0] {6}",
                "[1*v5 1 1 | -1*v4+1*v6 -2 0] {5}"
            ]
        );
    }
}
