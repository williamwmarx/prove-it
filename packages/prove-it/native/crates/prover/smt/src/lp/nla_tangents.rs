// Ported from Z3 (src/math/lp/nla_tangent_lemmas.h, src/math/lp/nla_tangent_lemmas.cpp), MIT
// license, see z3-license.txt. The tangent lemmas of nla: for a binary product whose value is
// wrong, the lines through the point of its factors' values and two planes tangent to z = xy that
// cut the point off.
//
// Monics are monic indices (see nla_core.rs). Tangents has no state; its functions take the view,
// and TangentImp's methods take it too.
use std::cmp::Ordering;

use prove_num::Rational;

use crate::lp::constraints::{KIND_EQ, KIND_GE, KIND_GT, KIND_LE, KIND_LT, KIND_NE};
use crate::lp::lar_term::LarTerm;
use crate::lp::nla_core::{NLA_PARAMS, Nla};
use crate::lp::nla_factorization::{Factor, Factorization, get_factor_sign};
use crate::lp::nla_throttle::{NlaThrottle, THROTTLE_TANGENT_LEMMA};
use crate::lp::nla_types::{LemmaBuilder, mk_ineq, mk_term_ineq};

#[derive(Clone)]
struct Point {
    x: Rational,
    y: Rational,
}

fn mk_point(x: Rational, y: Rational) -> Point {
    Point { x, y }
}

// tangent_imp: the lemmas for one monic and its binary factorization.
struct TangentImp {
    a: Point,
    b: Point,
    xy: Point,
    value: Rational,
    // The monic index.
    monic: usize,
    correct_value: Rational,
    // Whether the wrong value is below the correct one.
    is_below: bool,
    // Whether the tangent points are strictly inside the bound box.
    is_pl_strict_interior: bool,
    monic_var: usize,
    x: Factor,
    y: Factor,
    x_var: usize,
    y_var: usize,
    is_mon: bool,
}

impl TangentImp {
    fn new(
        xy: Point,
        value: Rational,
        monic: usize,
        monic_var: usize,
        factorization: &Factorization,
    ) -> TangentImp {
        let correct_value = xy.x.mul(&xy.y);
        let is_below = value.compare(&correct_value) == Ordering::Less;
        let x = factorization.factors[0];
        let y = factorization.factors[1];
        TangentImp {
            a: mk_point(Rational::zero(), Rational::zero()),
            b: mk_point(Rational::zero(), Rational::zero()),
            xy,
            value,
            monic,
            correct_value,
            is_below,
            is_pl_strict_interior: true,
            monic_var,
            x,
            y,
            x_var: x.variable,
            y_var: y.variable,
            is_mon: factorization.mon.is_some(),
        }
    }

    fn run(&mut self, nla: &mut Nla<'_, '_>) {
        self.get_points(nla);
        self.generate_line1(nla);
        self.generate_line2(nla);
        self.generate_plane(nla, &self.a);
        self.generate_plane(nla, &self.b);
    }

    fn explain(&self, nla: &mut Nla<'_, '_>, lemma: &LemmaBuilder) {
        if self.is_mon {
            return;
        }
        lemma.explain_monic(nla, self.monic);
        lemma.explain_factor(nla, &self.x);
        lemma.explain_factor(nla, &self.y);
    }

    fn generate_plane(&self, nla: &mut Nla<'_, '_>, plane: &Point) {
        if NlaThrottle::insert_simplified_tangent(
            nla.lra,
            THROTTLE_TANGENT_LEMMA,
            self.monic_var,
            self.x_var,
            self.y_var,
            self.is_below,
        ) {
            return;
        }
        let lemma = LemmaBuilder::new(nla);
        nla.negate_relation(&lemma, self.x_var, &get_factor_sign(&self.x).mul(&plane.x));
        nla.negate_relation(&lemma, self.y_var, &get_factor_sign(&self.y).mul(&plane.y));
        let mut term = LarTerm::new();
        term.add_monomial(&get_factor_sign(&self.y).mul(&plane.x).neg(), self.y_var);
        term.add_monomial(&get_factor_sign(&self.x).mul(&plane.y).neg(), self.x_var);
        term.add_monomial(&Rational::one(), self.monic_var);
        let cmp = match (self.is_below, self.is_pl_strict_interior) {
            (true, true) => KIND_GT,
            (true, false) => KIND_GE,
            (false, true) => KIND_LT,
            (false, false) => KIND_LE,
        };
        lemma.add_ineq(nla, mk_term_ineq(term, cmp, plane.x.mul(&plane.y).neg()));
        self.explain(nla, &lemma);
    }

    fn generate_line1(&self, nla: &mut Nla<'_, '_>) {
        if NlaThrottle::insert_tangent(
            nla.lra,
            THROTTLE_TANGENT_LEMMA,
            self.monic_var,
            self.x_var,
            self.y_var,
            self.is_below,
            1,
        ) {
            return;
        }
        let lemma = LemmaBuilder::new(nla);
        let x_value = nla.val(self.x_var);
        lemma.add_ineq(nla, mk_ineq(self.x_var, KIND_NE, x_value));
        let term = LarTerm::from_entries([
            (self.monic_var, &Rational::one()),
            (self.y_var, &get_factor_sign(&self.y).mul(&self.xy.x).neg()),
        ]);
        lemma.add_ineq(nla, mk_term_ineq(term, KIND_EQ, Rational::zero()));
        self.explain(nla, &lemma);
    }

    fn generate_line2(&self, nla: &mut Nla<'_, '_>) {
        if NlaThrottle::insert_tangent(
            nla.lra,
            THROTTLE_TANGENT_LEMMA,
            self.monic_var,
            self.x_var,
            self.y_var,
            self.is_below,
            2,
        ) {
            return;
        }
        let lemma = LemmaBuilder::new(nla);
        let y_value = nla.val(self.y_var);
        lemma.add_ineq(nla, mk_ineq(self.y_var, KIND_NE, y_value));
        let term = LarTerm::from_entries([
            (self.monic_var, &Rational::one()),
            (self.x_var, &get_factor_sign(&self.x).mul(&self.xy.y).neg()),
        ]);
        lemma.add_ineq(nla, mk_term_ineq(term, KIND_EQ, Rational::zero()));
        self.explain(nla, &lemma);
    }

    // get_initial_points: two planes tangent to z = xy, at a and at b, that make a cut.
    fn get_initial_points(&mut self) {
        let x = &self.xy.x;
        let y = &self.xy.y;
        let is_all_ints = self.value.is_int() && x.is_int() && y.is_int();
        let difference = self.correct_value.sub(&self.value).abs();
        let delta = if is_all_ints || Rational::one().compare(&difference) != Ordering::Greater {
            Rational::one()
        } else {
            difference
        };
        if !self.is_below {
            self.a = mk_point(x.sub(&delta), y.add(&delta));
            self.b = mk_point(x.add(&delta), y.sub(&delta));
            return;
        }
        self.a = mk_point(x.sub(&delta), y.sub(&delta));
        self.b = mk_point(x.add(&delta), y.add(&delta));
    }

    // push_point: the point moved away from xy, doubling the distance, while the plane still cuts.
    fn push_point(&self, nla: &Nla<'_, '_>, point: Point) -> Point {
        let two = Rational::from(2);
        let mut difference = mk_point(point.x.sub(&self.xy.x), point.y.sub(&self.xy.y));
        let mut result = point;
        for _ in 0..10 {
            if nla.done() {
                break;
            }
            difference = mk_point(difference.x.mul(&two), difference.y.mul(&two));
            let candidate = mk_point(self.xy.x.add(&difference.x), self.xy.y.add(&difference.y));
            if !self.is_plane_correct_cut(&candidate) {
                return result;
            }
            result = candidate;
        }
        result
    }

    fn get_tang_plane(&self, point: &Point) -> Rational {
        point
            .x
            .mul(&self.xy.y)
            .add(&point.y.mul(&self.xy.x))
            .sub(&point.x.mul(&point.y))
    }

    // set_box_corners: McCormick points at the corners of the factors' bound box.
    fn set_box_corners(&mut self, nla: &Nla<'_, '_>) -> bool {
        let x_var = self.x_var;
        let y_var = self.y_var;
        if !nla.has_lower_bound(x_var) || !nla.has_upper_bound(x_var) {
            return false;
        }
        if !nla.has_lower_bound(y_var) || !nla.has_upper_bound(y_var) {
            return false;
        }
        let x_low = nla.get_lower_bound(x_var);
        let x_high = nla.get_upper_bound(x_var);
        let y_low = nla.get_lower_bound(y_var);
        let y_high = nla.get_upper_bound(y_var);
        if x_low == x_high || y_low == y_high {
            return false;
        }
        let x_value = nla.val(x_var);
        let y_value = nla.val(y_var);
        if x_low == x_value || x_high == x_value {
            return false;
        }
        if y_low == y_value || y_high == y_value {
            return false;
        }
        if self.is_below {
            self.a = mk_point(x_low, y_low);
            self.b = mk_point(x_high, y_high);
        } else {
            self.a = mk_point(x_low, y_high);
            self.b = mk_point(x_high, y_low);
        }
        self.is_pl_strict_interior = false;
        true
    }

    fn get_points(&mut self, nla: &Nla<'_, '_>) {
        if NLA_PARAMS.tangents_box_corners && self.set_box_corners(nla) {
            return;
        }
        self.get_initial_points();
        self.a = self.push_point(nla, self.a.clone());
        self.b = self.push_point(nla, self.b.clone());
    }

    fn is_plane_correct_cut(&self, plane: &Point) -> bool {
        let sign = if self.is_below {
            Rational::one()
        } else {
            Rational::minus_one()
        };
        let tang_plane = self.get_tang_plane(plane);
        self.correct_value.sub(&tang_plane).mul(&sign).is_positive()
            && !tang_plane.sub(&self.value).mul(&sign).is_negative()
    }
}

#[derive(Default)]
pub struct Tangents {}

impl Tangents {
    pub fn tangent_lemma(nla: &mut Nla<'_, '_>) {
        if !NLA_PARAMS.tangents {
            return;
        }
        let Some((monic, factorization)) = nla.find_bfc_to_refine() else {
            return;
        };
        let xy = mk_point(
            nla.val_factor(&factorization.factors[0]),
            nla.val_factor(&factorization.factors[1]),
        );
        let monic_var = nla.emons.monics[monic].variable;
        TangentImp::new(xy, nla.val(monic_var), monic, monic_var, &factorization).run(nla);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lp::nla_core::tests::{NlaFixture, show_lemmas};

    // The expected states and lemmas are the TS oracle's on the same setups.

    // m = x*y = 1 with x >= 2 and y >= 3: below. The second call is throttled.
    #[test]
    fn cuts_a_value_below_the_product() {
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
            Tangents::tangent_lemma(nla);
            Tangents::tangent_lemma(nla);
        });
        assert_eq!(fixture.show_state(), "values 2,3,1 toRefine 2");
        assert_eq!(
            show_lemmas(&fixture.core),
            ["[1*v0 3 2] {1,3}", "[1*v1 3 3] {0,3}", "[] {0,1,3}"]
        );
    }

    // m = x*y >= 10 with x >= 2 and y >= 3: above.
    #[test]
    fn cuts_a_value_above_the_product() {
        let (mut fixture, _) = NlaFixture::mk_scenario(
            3,
            &[(2, &[0, 1])],
            &[(0, KIND_GE, 2), (1, KIND_GE, 3), (2, KIND_GE, 10)],
        );
        fixture.with_nla(Tangents::tangent_lemma);
        assert_eq!(fixture.show_state(), "values 2,3,10 toRefine 2");
        assert_eq!(
            show_lemmas(&fixture.core),
            [
                "[1*v0 3 2 | -2*v1+1*v2 0 0] {}",
                "[1*v1 3 3 | -3*v0+1*v2 0 0] {}",
                "[1*v1 2 5 | -5*v0+1*v2 -1 0] {0}"
            ]
        );
    }

    // m = x*y*z and n = y*z: the monic to refine drawn first is the binomial n.
    #[test]
    fn cuts_the_monic_drawn_to_refine() {
        let (mut fixture, _) = NlaFixture::mk_scenario(
            5,
            &[(3, &[0, 1, 2]), (4, &[1, 2])],
            &[
                (0, KIND_GE, 2),
                (1, KIND_GE, 3),
                (2, KIND_GE, 1),
                (3, KIND_GE, 1),
                (3, KIND_LE, 1),
                (4, KIND_GE, 1),
            ],
        );
        fixture.with_nla(Tangents::tangent_lemma);
        assert_eq!(fixture.show_state(), "values 2,3,1,1,1 toRefine 3,4");
        assert_eq!(
            show_lemmas(&fixture.core),
            [
                "[1*v1 3 3 | -3*v2+1*v4 0 0] {}",
                "[1*v2 3 1 | -1*v1+1*v4 0 0] {}",
                "[-2*v2+1*v4 1 0] {1,2}"
            ]
        );
    }
}
