// Ported from Z3 (src/math/lp/nla_divisions.h, src/math/lp/nla_divisions.cpp), MIT license, see
// z3-license.txt. The lemmas of nla on div, mod and /: monotonicity in the dividend and the
// divisor, bounded divisions by numerals, and divisibility closures over a shared divisor. The
// check is skipped while nla uses nlsat's model.
//
// TS pushes `() => divisions.pop()` on the emonics trail; here `CoreUndo::PopIdivision`,
// `PopBoundedDivision` and `PopDivisibility`, which `Nla::pop` applies.
use prove_num::{Rational, get_euclidean_div};

use crate::lp::constraints::{KIND_EQ, KIND_GE, KIND_GT, KIND_LE, KIND_LT, KIND_NE};
use crate::lp::lar_solver::NULL_LPVAR;
use crate::lp::lar_term::LarTerm;
use crate::lp::nla_core::Nla;
use crate::lp::nla_emonics::CoreUndo;
use crate::lp::nla_types::{LemmaBuilder, mk_ineq, mk_term_ineq};

// A division q = x / y with r its remainder, or a divisibility fact r = mod(x, y), q = div(x, y).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Division {
    pub quotient: usize,
    pub dividend: usize,
    pub divisor: usize,
    pub remainder: usize,
}

struct DivisionValues {
    dividend: usize,
    dividend_value: Rational,
    divisor: usize,
    divisor_value: Rational,
    quotient: usize,
    quotient_value: Rational,
}

// div on integers: Euclidean division, as mpz_manager::div.
fn get_int_div(dividend: &Rational, divisor: &Rational) -> Rational {
    Rational::from(get_euclidean_div(dividend.num(), divisor.num()))
}

fn has_null_column(division: &Division) -> bool {
    division.quotient == NULL_LPVAR
        || division.dividend == NULL_LPVAR
        || division.divisor == NULL_LPVAR
        || division.remainder == NULL_LPVAR
}

fn mk_difference(first: usize, second: usize) -> LarTerm {
    LarTerm::from_entries([(first, &Rational::one()), (second, &Rational::minus_one())])
}

#[derive(Default)]
pub struct Divisions {
    pub(crate) idivisions: Vec<Division>,
    pub(crate) bounded_divisions: Vec<Division>,
    // Divisibility facts, whose quotient is div(x, y) and remainder mod(x, y).
    pub(crate) divisibility: Vec<Division>,
}

impl Divisions {
    // The theory calls the three add functions: each is an entry point of nla, so it drains the
    // changed bounds first (see nla_core.rs).
    pub fn add_idivision(nla: &mut Nla<'_, '_>, division: Division) {
        nla.drain_changed_bounds();
        if has_null_column(&division) {
            return;
        }
        nla.divisions.idivisions.push(division);
        nla.emons.push_core_undo(CoreUndo::PopIdivision);
    }

    pub fn add_bounded_division(nla: &mut Nla<'_, '_>, division: Division) {
        nla.drain_changed_bounds();
        if has_null_column(&division) {
            return;
        }
        let lra = &nla.lra;
        if lra.has_term(division.dividend) || lra.has_term(division.divisor) {
            return;
        }
        if lra.has_term(division.quotient) {
            return;
        }
        nla.divisions.bounded_divisions.push(division);
        nla.emons.push_core_undo(CoreUndo::PopBoundedDivision);
    }

    pub fn add_divisibility(nla: &mut Nla<'_, '_>, division: Division) {
        nla.drain_changed_bounds();
        if has_null_column(&division) {
            return;
        }
        nla.divisions.divisibility.push(division);
        nla.emons.push_core_undo(CoreUndo::PopDivisibility);
    }

    // y1 >= y2 > 0 & 0 <= x1 <= x2 => x1/y1 <= x2/y2
    fn monotonicity1(
        nla: &mut Nla<'_, '_>,
        first: &DivisionValues,
        second: &DivisionValues,
    ) -> bool {
        if !(first.divisor_value >= second.divisor_value
            && second.divisor_value.is_positive()
            && !first.dividend_value.is_negative()
            && first.dividend_value <= second.dividend_value
            && first.quotient_value > second.quotient_value)
        {
            return false;
        }
        let lemma = LemmaBuilder::new(nla);
        let zero = Rational::zero();
        lemma.add_ineq(
            nla,
            mk_term_ineq(
                mk_difference(first.divisor, second.divisor),
                KIND_LT,
                zero.clone(),
            ),
        );
        lemma.add_ineq(nla, mk_ineq(second.divisor, KIND_LE, zero.clone()));
        lemma.add_ineq(nla, mk_ineq(first.dividend, KIND_LT, zero.clone()));
        lemma.add_ineq(
            nla,
            mk_term_ineq(
                mk_difference(first.dividend, second.dividend),
                KIND_GT,
                zero.clone(),
            ),
        );
        lemma.add_ineq(
            nla,
            mk_term_ineq(
                mk_difference(first.quotient, second.quotient),
                KIND_LE,
                zero,
            ),
        );
        true
    }

    // y2 <= y1 < 0 & x1 >= x2 >= 0 => x1/y1 <= x2/y2
    fn monotonicity2(
        nla: &mut Nla<'_, '_>,
        first: &DivisionValues,
        second: &DivisionValues,
    ) -> bool {
        if !(second.divisor_value <= first.divisor_value
            && first.divisor_value.is_negative()
            && first.dividend_value >= second.dividend_value
            && !second.dividend_value.is_negative()
            && first.quotient_value > second.quotient_value)
        {
            return false;
        }
        let lemma = LemmaBuilder::new(nla);
        let zero = Rational::zero();
        lemma.add_ineq(
            nla,
            mk_term_ineq(
                mk_difference(first.divisor, second.divisor),
                KIND_LT,
                zero.clone(),
            ),
        );
        lemma.add_ineq(nla, mk_ineq(first.divisor, KIND_GE, zero.clone()));
        lemma.add_ineq(
            nla,
            mk_term_ineq(
                mk_difference(first.dividend, second.dividend),
                KIND_LT,
                zero.clone(),
            ),
        );
        lemma.add_ineq(nla, mk_ineq(second.dividend, KIND_LT, zero.clone()));
        lemma.add_ineq(
            nla,
            mk_term_ineq(
                mk_difference(first.quotient, second.quotient),
                KIND_LE,
                zero,
            ),
        );
        true
    }

    // y2 <= y1 < 0 & x1 <= x2 <= 0 => x1/y1 >= x2/y2
    fn monotonicity3(
        nla: &mut Nla<'_, '_>,
        first: &DivisionValues,
        second: &DivisionValues,
    ) -> bool {
        if !(second.divisor_value <= first.divisor_value
            && first.divisor_value.is_negative()
            && first.dividend_value <= second.dividend_value
            && !second.dividend_value.is_positive()
            && first.quotient_value < second.quotient_value)
        {
            return false;
        }
        let lemma = LemmaBuilder::new(nla);
        let zero = Rational::zero();
        lemma.add_ineq(
            nla,
            mk_term_ineq(
                mk_difference(first.divisor, second.divisor),
                KIND_LT,
                zero.clone(),
            ),
        );
        lemma.add_ineq(nla, mk_ineq(first.divisor, KIND_GE, zero.clone()));
        lemma.add_ineq(
            nla,
            mk_term_ineq(
                mk_difference(first.dividend, second.dividend),
                KIND_GT,
                zero.clone(),
            ),
        );
        lemma.add_ineq(nla, mk_ineq(second.dividend, KIND_GT, zero.clone()));
        lemma.add_ineq(
            nla,
            mk_term_ineq(
                mk_difference(first.quotient, second.quotient),
                KIND_GE,
                zero,
            ),
        );
        true
    }

    fn monotonicity(
        nla: &mut Nla<'_, '_>,
        first: &DivisionValues,
        second: &DivisionValues,
    ) -> bool {
        Divisions::monotonicity1(nla, first, second)
            || Divisions::monotonicity1(nla, second, first)
            || Divisions::monotonicity2(nla, first, second)
            || Divisions::monotonicity2(nla, second, first)
            || Divisions::monotonicity3(nla, first, second)
            || Divisions::monotonicity3(nla, second, first)
    }

    fn get_values(nla: &Nla<'_, '_>, division: &Division) -> DivisionValues {
        DivisionValues {
            dividend: division.dividend,
            dividend_value: nla.val(division.dividend),
            divisor: division.divisor,
            divisor_value: nla.val(division.divisor),
            quotient: division.quotient,
            quotient_value: nla.val(division.quotient),
        }
    }

    // The monotonicity lemmas of the integer divisions whose quotients are wrong, against the
    // others. Z3's theory_lra registers no real divisions, so the rdivisions it would also check
    // stay empty.
    fn check_monotonicity(nla: &mut Nla<'_, '_>) -> bool {
        for index in 0..nla.divisions.idivisions.len() {
            let division = nla.divisions.idivisions[index];
            if !(nla.is_relevant)(division.quotient) {
                continue;
            }
            let values = Divisions::get_values(nla, &division);
            if values.divisor_value.is_zero() {
                continue;
            }
            if !values.dividend_value.is_int() || !values.divisor_value.is_int() {
                continue;
            }
            if values.quotient_value == get_int_div(&values.dividend_value, &values.divisor_value) {
                continue;
            }
            for other_index in 0..nla.divisions.idivisions.len() {
                let other = nla.divisions.idivisions[other_index];
                if other.quotient == division.quotient || !(nla.is_relevant)(other.quotient) {
                    continue;
                }
                let other_values = Divisions::get_values(nla, &other);
                if Divisions::monotonicity(nla, &values, &other_values) {
                    return true;
                }
            }
        }
        false
    }

    pub fn check(nla: &mut Nla<'_, '_>) {
        if nla.is_using_nra_model {
            return;
        }
        if Divisions::check_monotonicity(nla) {
            return;
        }
        Divisions::check_mod_mult(nla);
        Divisions::check_linear_divisibility(nla);
        Divisions::check_mod_congruence(nla);
    }

    // p <= q * div(r, q) + q - 1 => div(p, q) <= div(r, q), and p >= q * div(r, q) =>
    // div(r, q) <= div(p, q), for a bounded p, a value q and r = eval(p).
    pub fn check_bounded_divisions(nla: &mut Nla<'_, '_>) {
        let offset = nla.random() as usize;
        let size = nla.divisions.bounded_divisions.len();
        for index in 0..size {
            let division = nla.divisions.bounded_divisions[(offset + index) % size];
            let quotient = division.quotient;
            if !(nla.is_relevant)(quotient) {
                continue;
            }
            let dividend_value = nla.val(division.dividend);
            let divisor_value = nla.val(division.divisor);
            if dividend_value.is_negative() || !dividend_value.is_int() {
                continue;
            }
            if !divisor_value.is_positive() || !divisor_value.is_int() {
                continue;
            }
            let div_value = get_int_div(&dividend_value, &divisor_value);
            if nla.val(quotient) == div_value {
                continue;
            }
            let high = divisor_value
                .mul(&div_value)
                .add(&divisor_value)
                .sub(&Rational::one());
            let low = divisor_value.mul(&div_value);
            if dividend_value > high {
                let lemma = LemmaBuilder::new(nla);
                lemma.add_ineq(nla, mk_ineq(division.divisor, KIND_NE, divisor_value));
                lemma.add_ineq(nla, mk_ineq(division.dividend, KIND_GT, high));
                lemma.add_ineq(nla, mk_ineq(quotient, KIND_LE, div_value));
                return;
            }
            if dividend_value < low {
                let lemma = LemmaBuilder::new(nla);
                lemma.add_ineq(nla, mk_ineq(division.divisor, KIND_NE, divisor_value));
                lemma.add_ineq(nla, mk_ineq(division.dividend, KIND_LT, low));
                lemma.add_ineq(nla, mk_ineq(quotient, KIND_GE, div_value));
                return;
            }
        }
    }

    // mod(factor, p) = 0 => mod(factor * k, p) = 0
    fn check_mod_mult(nla: &mut Nla<'_, '_>) {
        let offset = nla.random() as usize;
        let size = nla.divisions.bounded_divisions.len();
        for index in 0..size {
            let division = nla.divisions.bounded_divisions[(offset + index) % size];
            let remainder = division.remainder;
            if !(nla.is_relevant)(division.quotient) {
                continue;
            }
            if nla.var_is_fixed_to_zero(remainder) || nla.val(remainder).is_zero() {
                continue;
            }
            if !nla.is_monic_var(division.dividend) {
                continue;
            }
            let divisor_value = nla.val(division.divisor);
            if !divisor_value.is_positive() || !divisor_value.is_int() {
                continue;
            }
            let factors = nla.emons.get(division.dividend).vars.clone();
            for factor in factors {
                for other_index in 0..nla.divisions.bounded_divisions.len() {
                    let other = nla.divisions.bounded_divisions[other_index];
                    if other.dividend != factor {
                        continue;
                    }
                    if nla.val(other.divisor) != divisor_value {
                        continue;
                    }
                    if !nla.var_is_fixed_to_zero(other.remainder) {
                        continue;
                    }
                    let lemma = LemmaBuilder::new(nla);
                    lemma.add_ineq(nla, mk_ineq(other.remainder, KIND_NE, Rational::zero()));
                    lemma.add_ineq(nla, mk_ineq(remainder, KIND_EQ, Rational::zero()));
                    return;
                }
            }
        }
    }

    // y != 0 & mod(a, y) = 0 & x = c * a, for an integer constant c, => mod(x, y) = 0
    fn check_linear_divisibility(nla: &mut Nla<'_, '_>) {
        let size = nla.divisions.divisibility.len();
        for index in 0..size {
            let fact = nla.divisions.divisibility[index];
            let x = fact.dividend;
            let y = fact.divisor;
            if !(nla.is_relevant)(fact.remainder) {
                continue;
            }
            if nla.val(fact.remainder).is_zero() {
                continue;
            }
            let x_value = nla.val(x);
            let y_value = nla.val(y);
            if y_value.is_zero() || x_value.is_zero() {
                continue;
            }
            for other_index in 0..size {
                if index == other_index {
                    continue;
                }
                let other = nla.divisions.divisibility[other_index];
                let a = other.dividend;
                let y2 = other.divisor;
                if y2 != y && nla.val(y2) != y_value {
                    continue;
                }
                if !(nla.is_relevant)(other.remainder) {
                    continue;
                }
                if !nla.val(other.remainder).is_zero() {
                    continue;
                }
                let a_value = nla.val(a);
                if a_value.is_zero() {
                    continue;
                }
                let coeff = x_value.div(&a_value);
                if !coeff.is_int() || coeff.is_zero() {
                    continue;
                }
                if x_value != coeff.mul(&a_value) {
                    continue;
                }
                let lemma = LemmaBuilder::new(nla);
                lemma.add_ineq(nla, mk_ineq(y, KIND_EQ, Rational::zero()));
                if y2 != y {
                    lemma.add_ineq(
                        nla,
                        mk_term_ineq(mk_difference(y, y2), KIND_NE, Rational::zero()),
                    );
                }
                lemma.add_ineq(
                    nla,
                    mk_term_ineq(
                        LarTerm::from_entries([(x, &Rational::one()), (a, &coeff.neg())]),
                        KIND_NE,
                        Rational::zero(),
                    ),
                );
                lemma.add_ineq(nla, mk_ineq(other.remainder, KIND_NE, Rational::zero()));
                lemma.add_ineq(nla, mk_ineq(fact.remainder, KIND_EQ, Rational::zero()));
                return;
            }
        }
    }

    // div(x,y) - div(s,y) = delta => mod(x,y) - mod(s,y) = (x - s) - delta*y, for y != 0
    fn check_mod_congruence(nla: &mut Nla<'_, '_>) {
        let size = nla.divisions.divisibility.len();
        for index in 0..size {
            let fact = nla.divisions.divisibility[index];
            let y = fact.divisor;
            if !(nla.is_relevant)(fact.remainder) {
                continue;
            }
            let y_value = nla.val(y);
            if y_value.is_zero() {
                continue;
            }
            for other_index in index + 1..size {
                let other = nla.divisions.divisibility[other_index];
                let y2 = other.divisor;
                if !(nla.is_relevant)(other.remainder) {
                    continue;
                }
                if y2 != y && nla.val(y2) != y_value {
                    continue;
                }
                let delta = nla.val(fact.quotient).sub(&nla.val(other.quotient));
                let left = nla.val(fact.remainder).sub(&nla.val(other.remainder));
                let right = nla
                    .val(fact.dividend)
                    .sub(&nla.val(other.dividend))
                    .sub(&delta.mul(&y_value));
                if left == right {
                    continue;
                }
                let lemma = LemmaBuilder::new(nla);
                lemma.add_ineq(nla, mk_ineq(y, KIND_EQ, Rational::zero()));
                if y2 != y {
                    lemma.add_ineq(
                        nla,
                        mk_term_ineq(mk_difference(y, y2), KIND_NE, Rational::zero()),
                    );
                }
                lemma.add_ineq(
                    nla,
                    mk_term_ineq(
                        mk_difference(fact.quotient, other.quotient),
                        KIND_NE,
                        delta.clone(),
                    ),
                );
                let mut term = LarTerm::new();
                term.add_monomial(&Rational::one(), fact.remainder);
                term.add_monomial(&Rational::minus_one(), other.remainder);
                term.add_monomial(&Rational::minus_one(), fact.dividend);
                term.add_monomial(&Rational::one(), other.dividend);
                term.add_monomial(&delta, y);
                lemma.add_ineq(nla, mk_term_ineq(term, KIND_EQ, Rational::zero()));
                return;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lp::nla_core::tests::{NlaFixture, show_lemmas};

    fn mk_division(quotient: usize, dividend: usize, divisor: usize, remainder: usize) -> Division {
        Division {
            quotient,
            dividend,
            divisor,
            remainder,
        }
    }

    // The expected lemmas here and below are the TS oracle's on the same setups.
    #[test]
    fn makes_a_monotonicity_lemma_of_integer_divisions() {
        let (mut fixture, _) = NlaFixture::mk_scenario(
            8,
            &[],
            &[
                (1, KIND_GE, 1),
                (2, KIND_GE, 2),
                (0, KIND_GE, 5),
                (5, KIND_GE, 4),
                (6, KIND_GE, 2),
                (4, KIND_GE, 2),
            ],
        );
        fixture.with_nla(|nla| {
            Divisions::add_idivision(nla, mk_division(0, 1, 2, 3));
            Divisions::add_idivision(nla, mk_division(4, 5, 6, 7));
            Divisions::check(nla);
        });
        assert_eq!(fixture.show_state(), "values 5,1,2,0,2,4,2,0 toRefine ");
        assert_eq!(
            show_lemmas(&fixture.core),
            ["[1*v2+-1*v6 -1 0 | 1*v1+-1*v5 1 0 | 1*v0+-1*v4 -2 0] {0,4}"]
        );
    }

    // The values of a bounded division always lie between its low and high, as in Z3, so the
    // check makes no lemma; it draws one random number.
    #[test]
    fn checks_a_bounded_division() {
        let (mut fixture, _) = NlaFixture::mk_scenario(
            4,
            &[],
            &[
                (1, KIND_GE, 7),
                (2, KIND_GE, 2),
                (2, KIND_LE, 2),
                (0, KIND_GE, 5),
            ],
        );
        let next = fixture.with_nla(|nla| {
            Divisions::add_bounded_division(nla, mk_division(0, 1, 2, 3));
            nla.check_bounded_divisions();
            nla.random()
        });
        assert_eq!(next, 21238);
        assert_eq!(fixture.show_state(), "values 5,7,2,0 toRefine ");
        assert!(show_lemmas(&fixture.core).is_empty());
    }

    #[test]
    fn makes_the_mod_mult_lemma_of_bounded_divisions() {
        let (mut fixture, _) = NlaFixture::mk_scenario(
            9,
            &[(2, &[0, 1])],
            &[
                (4, KIND_GE, 3),
                (4, KIND_LE, 3),
                (5, KIND_GE, 1),
                (7, KIND_GE, 3),
                (7, KIND_LE, 3),
                (8, KIND_GE, 0),
                (8, KIND_LE, 0),
            ],
        );
        fixture.with_nla(|nla| {
            Divisions::add_bounded_division(nla, mk_division(3, 2, 4, 5));
            Divisions::add_bounded_division(nla, mk_division(6, 0, 7, 8));
            Divisions::check(nla);
        });
        assert_eq!(fixture.show_state(), "values 0,0,0,0,3,1,0,3,0 toRefine ");
        assert_eq!(show_lemmas(&fixture.core), ["[] {2,5,6}"]);
    }

    #[test]
    fn makes_the_divisibility_and_congruence_lemmas() {
        let (mut fixture, _) = NlaFixture::mk_scenario(
            8,
            &[],
            &[
                (0, KIND_GE, 6),
                (1, KIND_GE, 3),
                (3, KIND_GE, 1),
                (4, KIND_GE, 2),
                (5, KIND_GE, 3),
            ],
        );
        fixture.with_nla(|nla| {
            Divisions::add_divisibility(nla, mk_division(2, 0, 1, 3));
            Divisions::add_divisibility(nla, mk_division(6, 4, 5, 7));
            Divisions::check(nla);
        });
        assert_eq!(fixture.show_state(), "values 6,3,0,1,2,3,0,0 toRefine ");
        assert_eq!(
            show_lemmas(&fixture.core),
            [
                "[1*v1+-1*v5 3 0 | 1*v0+-3*v4 3 0 | 1*v7 3 0] {1,2}",
                "[1*v1+-1*v5 3 0 | 1*v2+-1*v6 3 0 | -1*v0+1*v3+1*v4+-1*v7 0 0] {1}",
            ]
        );
    }

    #[test]
    fn makes_the_congruence_lemma() {
        let (mut fixture, _) = NlaFixture::mk_scenario(
            8,
            &[],
            &[
                (0, KIND_GE, 6),
                (1, KIND_GE, 3),
                (3, KIND_GE, 1),
                (4, KIND_GE, 2),
                (5, KIND_GE, 3),
                (7, KIND_GE, 2),
            ],
        );
        fixture.with_nla(|nla| {
            Divisions::add_divisibility(nla, mk_division(2, 0, 1, 3));
            Divisions::add_divisibility(nla, mk_division(6, 4, 5, 7));
            Divisions::check(nla);
        });
        assert_eq!(fixture.show_state(), "values 6,3,0,1,2,3,0,2 toRefine ");
        assert_eq!(
            show_lemmas(&fixture.core),
            ["[1*v1+-1*v5 3 0 | 1*v2+-1*v6 3 0 | -1*v0+1*v3+1*v4+-1*v7 0 0] {1}"]
        );
    }

    #[test]
    fn skips_the_check_on_the_nra_model() {
        let (mut fixture, _) = NlaFixture::mk_scenario(
            8,
            &[],
            &[
                (0, KIND_GE, 6),
                (1, KIND_GE, 3),
                (3, KIND_GE, 1),
                (4, KIND_GE, 2),
                (5, KIND_GE, 3),
                (7, KIND_GE, 2),
            ],
        );
        fixture.with_nla(|nla| {
            Divisions::add_divisibility(nla, mk_division(2, 0, 1, 3));
            Divisions::add_divisibility(nla, mk_division(6, 4, 5, 7));
            nla.set_use_nra_model(true);
            Divisions::check(nla);
        });
        assert!(show_lemmas(&fixture.core).is_empty());
    }
}
