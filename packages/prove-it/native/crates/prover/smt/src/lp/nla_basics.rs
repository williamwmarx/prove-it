// Ported from Z3 (src/math/lp/nla_basics_lemmas.h, src/math/lp/nla_basics_lemmas.cpp), MIT
// license, see z3-license.txt. The basic lemmas of nla on monomials whose values are wrong: signs
// (-ab = (-a)b), zeros (xy = 0 iff x = 0 or y = 0), neutral factors (|xa| = |x| and x != 0 imply
// |a| = 1) and proportions (|xy| >= |y| when x != 0). Only the model-based lemmas are ported: with
// derived = true, basic_lemma returns after the sign lemma, so Z3 never reaches its derived
// zero and neutral lemmas.
//
// Monics are monic indices (see nla_core.rs). Basics has no state; its functions take the view.
use std::cmp::Ordering;
use std::collections::HashSet;

use prove_num::Rational;

use crate::lp::constraints::{KIND_EQ, KIND_GE, KIND_GT, KIND_LE, KIND_LT, KIND_NE};
use crate::lp::lar_solver::NULL_LPVAR;
use crate::lp::lar_term::LarTerm;
use crate::lp::nla_core::Nla;
use crate::lp::nla_factorization::Factorization;
use crate::lp::nla_types::{LemmaBuilder, get_rat_sign, mk_ineq, mk_term_ineq, sign_to_rat};

struct FactorValue {
    variable: usize,
    value: Rational,
}

// can_create_lemma_for_mon_neutral_from_factors_to_monic_model_based's result.
struct Neutral {
    not_one: usize,
    sign: Rational,
}

#[derive(Default)]
pub struct Basics {}

impl Basics {
    pub fn basic_lemma(nla: &mut Nla<'_, '_>, is_derived: bool) {
        if Basics::basic_sign_lemma(nla, is_derived) {
            return;
        }
        if is_derived {
            return;
        }
        let start = nla.random() as usize;
        let size = nla.to_refine.size();
        for index in 0..size {
            let monic = nla
                .emons
                .get_index(nla.to_refine.elems[(index + start) % nla.to_refine.size()]);
            Basics::basic_lemma_for_mon_model_based(nla, monic);
        }
    }

    // Signs.

    fn basic_sign_lemma_on_two_monics(nla: &mut Nla<'_, '_>, first: usize, second: usize) -> bool {
        let sign = sign_to_rat(nla.emons.monics[first].rsign != nla.emons.monics[second].rsign);
        if nla.var_val(first) == nla.var_val(second).mul(&sign) {
            return false;
        }
        Basics::generate_sign_lemma(nla, first, second, &sign);
        true
    }

    fn generate_zero_lemmas(nla: &mut Nla<'_, '_>, monic: usize) {
        let mut sign = get_rat_sign(&nla.var_val(monic));
        let mut fixed_zeros = Vec::new();
        let zero_var = Basics::find_best_zero(nla, monic, &mut fixed_zeros);
        let mut zero_power = 0;
        for lp_var in &nla.emons.monics[monic].vars {
            if *lp_var == zero_var {
                zero_power += 1;
                continue;
            }
            sign = Basics::get_non_strict_sign(nla, *lp_var, sign);
            if sign == 0 {
                break;
            }
        }
        if sign != 0 && zero_power % 2 == 0 {
            sign = 0;
        }
        if sign == 0 {
            Basics::add_trivial_zero_lemma(nla, zero_var, monic);
        } else {
            Basics::generate_strict_case_zero_lemma(nla, monic, zero_var, sign);
        }
        for lp_var in fixed_zeros {
            Basics::add_fixed_zero_lemma(nla, monic, lp_var);
        }
    }

    // try_get_non_strict_sign_from_bounds and get_non_strict_sign: the sign times the sign of the
    // variable, from its value or else its bounds, or 0.
    fn get_non_strict_sign(nla: &Nla<'_, '_>, lp_var: usize, sign: i32) -> i32 {
        let value = nla.val(lp_var);
        if !value.is_zero() {
            return sign * get_rat_sign(&value);
        }
        if nla.has_lower_bound(lp_var) && !nla.get_lower_bound(lp_var).is_negative() {
            return sign;
        }
        if nla.has_upper_bound(lp_var) && !nla.get_upper_bound(lp_var).is_positive() {
            return -sign;
        }
        0
    }

    fn basic_sign_lemma_model_based_one_mon(
        nla: &mut Nla<'_, '_>,
        monic: usize,
        product_sign: i32,
    ) {
        if product_sign == 0 {
            Basics::generate_zero_lemmas(nla, monic);
            return;
        }
        let lemma = LemmaBuilder::new(nla);
        for index in 0..nla.emons.monics[monic].vars.len() {
            let lp_var = nla.emons.monics[monic].vars[index];
            Basics::negate_strict_sign(nla, &lemma, lp_var);
        }
        let cmp = if product_sign == 1 { KIND_GT } else { KIND_LT };
        let variable = nla.emons.monics[monic].variable;
        lemma.add_ineq(nla, mk_ineq(variable, cmp, Rational::zero()));
    }

    fn basic_sign_lemma_model_based(nla: &mut Nla<'_, '_>) -> bool {
        let start = nla.random() as usize;
        let size = nla.to_refine.size();
        for index in (0..size).rev() {
            let monic = nla
                .emons
                .get_index(nla.to_refine.elems[(start + index) % size]);
            let product_sign = nla.get_monic_sign(monic);
            if get_rat_sign(&nla.var_val(monic)) == product_sign {
                continue;
            }
            Basics::basic_sign_lemma_model_based_one_mon(nla, monic, product_sign);
            if nla.done() {
                return true;
            }
        }
        !nla.lemmas.is_empty()
    }

    fn basic_sign_lemma_on_mon(
        nla: &mut Nla<'_, '_>,
        lp_var: usize,
        explored: &mut HashSet<usize>,
    ) -> bool {
        if !explored.insert(lp_var) {
            return false;
        }
        let monic = nla.emons.get_index(lp_var);
        let mut others = nla.emons.get_sign_equiv_monics(monic);
        while let Some(other) = others.next(&nla.emons) {
            if nla.emons.monics[monic].variable != nla.emons.monics[other].variable
                && Basics::basic_sign_lemma_on_two_monics(nla, monic, other)
                && nla.done()
            {
                return true;
            }
        }
        false
    }

    fn basic_sign_lemma(nla: &mut Nla<'_, '_>, is_derived: bool) -> bool {
        if !is_derived {
            return Basics::basic_sign_lemma_model_based(nla);
        }
        let mut explored = HashSet::new();
        for index in 0..nla.to_refine.size() {
            let lp_var = nla.to_refine.elems[index];
            if Basics::basic_sign_lemma_on_mon(nla, lp_var, &mut explored) {
                return true;
            }
        }
        false
    }

    fn generate_sign_lemma(nla: &mut Nla<'_, '_>, first: usize, second: usize, sign: &Rational) {
        let lemma = LemmaBuilder::new(nla);
        let term = LarTerm::from_entries([
            (nla.emons.monics[first].variable, &Rational::one()),
            (nla.emons.monics[second].variable, &sign.neg()),
        ]);
        lemma.add_ineq(nla, mk_term_ineq(term, KIND_EQ, Rational::zero()));
        lemma.explain_monic(nla, first);
        lemma.explain_monic(nla, second);
    }

    // Zeros.

    // find_best_zero: a variable of value 0, preferably with 0 inside its bounds, and the variables
    // fixed to 0.
    fn find_best_zero(nla: &Nla<'_, '_>, monic: usize, fixed_zeros: &mut Vec<usize>) -> usize {
        let mut zero_var = NULL_LPVAR;
        for lp_var in &nla.emons.monics[monic].vars {
            if !nla.val(*lp_var).is_zero() {
                continue;
            }
            if nla.var_is_fixed_to_zero(*lp_var) {
                fixed_zeros.push(*lp_var);
            }
            if zero_var == NULL_LPVAR || nla.zero_is_an_inner_point_of_bounds(*lp_var) {
                zero_var = *lp_var;
            }
        }
        zero_var
    }

    fn add_trivial_zero_lemma(nla: &mut Nla<'_, '_>, zero_var: usize, monic: usize) {
        let lemma = LemmaBuilder::new(nla);
        lemma.add_ineq(nla, mk_ineq(zero_var, KIND_NE, Rational::zero()));
        let variable = nla.emons.monics[monic].variable;
        lemma.add_ineq(nla, mk_ineq(variable, KIND_EQ, Rational::zero()));
    }

    fn generate_strict_case_zero_lemma(
        nla: &mut Nla<'_, '_>,
        monic: usize,
        zero_var: usize,
        zero_sign: i32,
    ) {
        let lemma = LemmaBuilder::new(nla);
        let cmp = if zero_sign == 1 { KIND_GT } else { KIND_LT };
        lemma.add_ineq(nla, mk_ineq(zero_var, cmp, Rational::zero()));
        for index in 0..nla.emons.monics[monic].vars.len() {
            let lp_var = nla.emons.monics[monic].vars[index];
            if lp_var != zero_var {
                Basics::negate_strict_sign(nla, &lemma, lp_var);
            }
        }
        let variable = nla.emons.monics[monic].variable;
        Basics::negate_strict_sign(nla, &lemma, variable);
    }

    fn add_fixed_zero_lemma(nla: &mut Nla<'_, '_>, monic: usize, lp_var: usize) {
        let lemma = LemmaBuilder::new(nla);
        lemma.explain_fixed(nla, lp_var);
        let variable = nla.emons.monics[monic].variable;
        lemma.add_ineq(nla, mk_ineq(variable, KIND_EQ, Rational::zero()));
    }

    fn negate_strict_sign(nla: &mut Nla<'_, '_>, lemma: &LemmaBuilder, lp_var: usize) {
        let value = nla.val(lp_var);
        if !value.is_zero() {
            let cmp = if get_rat_sign(&value) == 1 {
                KIND_LE
            } else {
                KIND_GE
            };
            lemma.add_ineq(nla, mk_ineq(lp_var, cmp, Rational::zero()));
            return;
        }
        if nla.has_lower_bound(lp_var) && !nla.get_lower_bound(lp_var).is_negative() {
            lemma.explain_existing_lower_bound(nla, lp_var);
            lemma.add_ineq(nla, mk_ineq(lp_var, KIND_GT, Rational::zero()));
            return;
        }
        lemma.explain_existing_upper_bound(nla, lp_var);
        lemma.add_ineq(nla, mk_ineq(lp_var, KIND_LT, Rational::zero()));
    }

    // Model-based lemmas on the factorizations of a monic.

    fn basic_lemma_for_mon_model_based(nla: &mut Nla<'_, '_>, rooted: usize) {
        let is_zero = nla.var_val(rooted).is_zero();
        let mut factorizations = nla.get_factorizations(rooted);
        while let Some(factorization) = factorizations.next(nla) {
            if factorization.factors.is_empty() {
                continue;
            }
            if is_zero {
                Basics::basic_lemma_for_mon_zero_model_based(nla, rooted, &factorization);
                Basics::basic_lemma_for_mon_neutral_model_based(nla, rooted, &factorization);
                continue;
            }
            Basics::basic_lemma_for_mon_non_zero_model_based(nla, &factorization);
            Basics::basic_lemma_for_mon_neutral_model_based(nla, rooted, &factorization);
            Basics::proportion_lemma_model_based(nla, rooted, &factorization);
        }
    }

    // x != 0 or y = 0 => |xy| >= |y|
    fn proportion_lemma_model_based(
        nla: &mut Nla<'_, '_>,
        rooted: usize,
        factorization: &Factorization,
    ) {
        if nla.has_real_factorization(factorization) {
            return;
        }
        let rooted_value = nla.var_val(rooted).abs();
        if rooted_value.is_zero() {
            return;
        }
        let factor_index = factorization.factors.iter().position(|factor| {
            nla.val_factor(factor).abs().compare(&rooted_value) == Ordering::Greater
        });
        if let Some(factor_index) = factor_index {
            Basics::generate_pl(nla, rooted, factorization, factor_index);
        }
    }

    // sign_m*m < 0 or \/_{i != k} f_i = 0 or sign_m*m >= sign_k*f_k
    fn generate_pl_on_mon(nla: &mut Nla<'_, '_>, monic: usize, factor_index: usize) {
        let lemma = LemmaBuilder::new(nla);
        let monic_var = nla.emons.monics[monic].variable;
        let monic_sign = Rational::from(i64::from(get_rat_sign(&nla.val(monic_var))));
        let term = LarTerm::from_entries([(monic_var, &monic_sign)]);
        lemma.add_ineq(nla, mk_term_ineq(term, KIND_LT, Rational::zero()));
        for index in 0..nla.emons.monics[monic].vars.len() {
            let lp_var = nla.emons.monics[monic].vars[index];
            if index != factor_index {
                lemma.add_ineq(nla, mk_ineq(lp_var, KIND_EQ, Rational::zero()));
                continue;
            }
            let var_sign = Rational::from(i64::from(get_rat_sign(&nla.val(lp_var))));
            let term = LarTerm::from_entries([(monic_var, &monic_sign), (lp_var, &var_sign.neg())]);
            lemma.add_ineq(nla, mk_term_ineq(term, KIND_GE, Rational::zero()));
        }
    }

    fn generate_pl(
        nla: &mut Nla<'_, '_>,
        monic: usize,
        factorization: &Factorization,
        factor_index: usize,
    ) {
        if factorization.mon.is_some() {
            Basics::generate_pl_on_mon(nla, monic, factor_index);
            return;
        }
        let lemma = LemmaBuilder::new(nla);
        let monic_sign = Rational::from(i64::from(get_rat_sign(&nla.var_val(monic))));
        let monic_var = nla.emons.monics[monic].variable;
        let term = LarTerm::from_entries([(monic_var, &monic_sign)]);
        lemma.add_ineq(nla, mk_term_ineq(term, KIND_LT, Rational::zero()));
        for (index, factor) in factorization.factors.iter().enumerate() {
            if index != factor_index {
                lemma.add_ineq(nla, mk_ineq(factor.variable, KIND_EQ, Rational::zero()));
                continue;
            }
            let var_sign = Rational::from(i64::from(get_rat_sign(&nla.val(factor.variable))));
            let term = LarTerm::from_entries([
                (monic_var, &monic_sign),
                (factor.variable, &var_sign.neg()),
            ]);
            lemma.add_ineq(nla, mk_term_ineq(term, KIND_GE, Rational::zero()));
        }
        lemma.explain_factorization(nla, factorization);
        lemma.explain_monic(nla, monic);
    }

    fn is_separated_from_zero(nla: &Nla<'_, '_>, factorization: &Factorization) -> bool {
        factorization.factors.iter().all(|factor| {
            nla.var_has_positive_lower_bound(factor.variable)
                || nla.var_has_negative_upper_bound(factor.variable)
        })
    }

    // xy = 0 -> x = 0 or y = 0
    fn basic_lemma_for_mon_zero_model_based(
        nla: &mut Nla<'_, '_>,
        rooted: usize,
        factorization: &Factorization,
    ) {
        let lemma = LemmaBuilder::new(nla);
        let variable = nla.emons.monics[rooted].variable;
        lemma.add_ineq(nla, mk_ineq(variable, KIND_NE, Rational::zero()));
        if !Basics::is_separated_from_zero(nla, factorization) {
            for factor in &factorization.factors {
                lemma.add_ineq(nla, mk_ineq(factor.variable, KIND_EQ, Rational::zero()));
            }
        } else {
            for factor in &factorization.factors {
                lemma.explain_var_separated_from_zero(nla, factor.variable);
            }
        }
        lemma.explain_factorization(nla, factorization);
    }

    // /\_{j != i} f_j = val(f_j) => m = sign * f_i, or /\_j f_j = val(f_j) => m = sign, over the
    // variables of a monic.
    fn basic_lemma_for_mon_neutral_from_factors_to_monic_model_based_fm(
        nla: &mut Nla<'_, '_>,
        monic: usize,
    ) {
        let factors: Vec<FactorValue> = nla.emons.monics[monic]
            .vars
            .iter()
            .map(|lp_var| FactorValue {
                variable: *lp_var,
                value: nla.val(*lp_var),
            })
            .collect();
        let Some(neutral) = Basics::get_neutral_not_one(nla, monic, &factors) else {
            return;
        };
        let lemma = LemmaBuilder::new(nla);
        for index in 0..nla.emons.monics[monic].vars.len() {
            let lp_var = nla.emons.monics[monic].vars[index];
            if neutral.not_one != lp_var {
                let value = nla.val(lp_var);
                lemma.add_ineq(nla, mk_ineq(lp_var, KIND_NE, value));
            }
        }
        Basics::add_neutral_conclusion(nla, &lemma, monic, &neutral);
    }

    fn add_neutral_conclusion(
        nla: &mut Nla<'_, '_>,
        lemma: &LemmaBuilder,
        monic: usize,
        neutral: &Neutral,
    ) {
        let variable = nla.emons.monics[monic].variable;
        if neutral.not_one == NULL_LPVAR {
            lemma.add_ineq(nla, mk_ineq(variable, KIND_EQ, neutral.sign.clone()));
            return;
        }
        let term = LarTerm::from_entries([
            (variable, &Rational::one()),
            (neutral.not_one, &neutral.sign.neg()),
        ]);
        lemma.add_ineq(nla, mk_term_ineq(term, KIND_EQ, Rational::zero()));
    }

    // basic_lemma_for_mon_neutral_monic_to_factor_model_based tests `j == null_lpvar` for the factor
    // equal to the monic in absolute value, which no factor's variable is, so it never makes a
    // lemma (nla_basics_lemmas.cpp, the loop over f).
    fn basic_lemma_for_mon_neutral_model_based(
        nla: &mut Nla<'_, '_>,
        rooted: usize,
        factorization: &Factorization,
    ) {
        match factorization.mon {
            Some(monic) => {
                Basics::basic_lemma_for_mon_neutral_from_factors_to_monic_model_based_fm(nla, monic)
            }
            None => Basics::basic_lemma_for_mon_neutral_from_factors_to_monic_model_based(
                nla,
                rooted,
                factorization,
            ),
        }
    }

    // can_create_lemma_for_mon_neutral_from_factors_to_monic_model_based: the one factor whose
    // value is not +-1, or none, and the product of the other values, when the monic's value
    // disagrees with them.
    fn get_neutral_not_one(
        nla: &Nla<'_, '_>,
        monic: usize,
        factors: &[FactorValue],
    ) -> Option<Neutral> {
        let mut sign = Rational::one();
        let mut not_one = NULL_LPVAR;
        for factor in factors {
            if factor.value == Rational::one() {
                continue;
            }
            if factor.value == Rational::minus_one() {
                sign = sign.neg();
                continue;
            }
            if not_one == NULL_LPVAR {
                not_one = factor.variable;
                continue;
            }
            return None;
        }
        let monic_value = nla.var_val(monic);
        if not_one == NULL_LPVAR && monic_value == sign {
            return None;
        }
        if not_one != NULL_LPVAR && monic_value == nla.val(not_one).mul(&sign) {
            return None;
        }
        Some(Neutral { not_one, sign })
    }

    fn basic_lemma_for_mon_neutral_from_factors_to_monic_model_based(
        nla: &mut Nla<'_, '_>,
        monic: usize,
        factorization: &Factorization,
    ) {
        let factors: Vec<FactorValue> = factorization
            .factors
            .iter()
            .map(|factor| FactorValue {
                variable: factor.variable,
                value: nla.val_factor(factor),
            })
            .collect();
        let Some(neutral) = Basics::get_neutral_not_one(nla, monic, &factors) else {
            return;
        };
        if factorization.factors.iter().any(|factor| factor.is_negated) {
            return;
        }
        let lemma = LemmaBuilder::new(nla);
        for factor in &factorization.factors {
            if neutral.not_one == factor.variable {
                continue;
            }
            let value = nla.val(factor.variable);
            lemma.add_ineq(nla, mk_ineq(factor.variable, KIND_NE, value));
        }
        Basics::add_neutral_conclusion(nla, &lemma, monic, &neutral);
        lemma.explain_monic(nla, monic);
        lemma.explain_factorization(nla, factorization);
    }

    // x = 0 or y = 0 -> xy = 0
    fn basic_lemma_for_mon_non_zero_model_based(
        nla: &mut Nla<'_, '_>,
        factorization: &Factorization,
    ) {
        let Some(monic) = factorization.mon else {
            return;
        };
        let Some(zero) = factorization
            .factors
            .iter()
            .find(|factor| nla.val_factor(factor).is_zero())
        else {
            return;
        };
        let lemma = LemmaBuilder::new(nla);
        lemma.add_ineq(nla, mk_ineq(zero.variable, KIND_NE, Rational::zero()));
        let variable = nla.emons.monics[monic].variable;
        lemma.add_ineq(nla, mk_ineq(variable, KIND_EQ, Rational::zero()));
        lemma.explain_factorization(nla, factorization);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lp::constraints::ConstraintKind;
    use crate::lp::nla_core::tests::{NlaFixture, show_lemmas};

    // Runs basic_lemma on the TS oracle's scenario and gives the state and the lemmas, which the
    // expectations below are the TS's output for.
    fn run_basic_lemma(
        num_vars: usize,
        monics: &[(usize, &[usize])],
        bounds: &[(usize, ConstraintKind, i64)],
        is_derived: bool,
    ) -> (String, Vec<String>) {
        let (mut fixture, _) = NlaFixture::mk_scenario(num_vars, monics, bounds);
        fixture.with_nla(|nla| Basics::basic_lemma(nla, is_derived));
        (fixture.show_state(), show_lemmas(&fixture.core))
    }

    // x fixed to 0 and x*y >= 1: the zero lemma, whose x != 0 the bounds explain away, and the
    // fixed-zero lemma.
    #[test]
    fn makes_the_zero_lemmas_of_a_factor_fixed_to_zero() {
        let result = run_basic_lemma(
            3,
            &[(2, &[0, 1])],
            &[(0, KIND_GE, 0), (0, KIND_LE, 0), (2, KIND_GE, 1)],
            false,
        );
        assert_eq!(result.0, "values 0,0,1 toRefine 2");
        assert_eq!(result.1, ["[1*v1 1 0] {0,1,2}", "[] {0,1,2}"]);
    }

    // x in [0, 5] and y <= 0 at 0, x*y*y >= 1: the strict case of the zero lemma.
    #[test]
    fn makes_the_strict_zero_lemma_from_the_bounds() {
        let result = run_basic_lemma(
            3,
            &[(2, &[0, 1, 1])],
            &[
                (0, KIND_GE, 0),
                (0, KIND_LE, 5),
                (1, KIND_LE, 0),
                (2, KIND_GE, 1),
            ],
            false,
        );
        assert_eq!(result.0, "values 0,0,1 toRefine 2");
        assert_eq!(result.1, ["[1*v0 1 0 | 1*v1 -1 0 | 1*v1 -1 0] {2,3}"]);
    }

    // x >= 2, y <= -3 and x*y >= 1: the sign lemma, a conflict of the bounds.
    #[test]
    fn makes_the_sign_lemma_of_a_monic() {
        let result = run_basic_lemma(
            3,
            &[(2, &[0, 1])],
            &[(0, KIND_GE, 2), (1, KIND_LE, -3), (2, KIND_GE, 1)],
            false,
        );
        assert_eq!(result.0, "values 2,-3,1 toRefine 2");
        assert_eq!(result.1, ["[] {0,1,2}"]);
    }

    // x*y >= 1 and y*x >= 2 are one monic up to sign: the derived sign lemma on each.
    #[test]
    fn makes_the_derived_sign_lemmas_of_equal_monics() {
        let result = run_basic_lemma(
            4,
            &[(2, &[0, 1]), (3, &[1, 0])],
            &[(2, KIND_GE, 1), (3, KIND_GE, 2)],
            true,
        );
        assert_eq!(result.0, "values 0,0,1,2 toRefine 2,3");
        assert_eq!(result.1, ["[1*v2+-1*v3 0 0] {}", "[-1*v2+1*v3 0 0] {}"]);
    }

    // x = 1, y = 3 and x*y = 5: the neutral lemma x != 1 or x*y = y.
    #[test]
    fn makes_the_neutral_lemma() {
        let result = run_basic_lemma(
            3,
            &[(2, &[0, 1])],
            &[
                (0, KIND_GE, 1),
                (0, KIND_LE, 1),
                (1, KIND_GE, 3),
                (2, KIND_GE, 5),
            ],
            false,
        );
        assert_eq!(result.0, "values 1,3,5 toRefine 2");
        assert_eq!(result.1, ["[-1*v1+1*v2 0 0] {0,1}"]);
    }

    // x >= 2, y >= 3 and x*y = 1: the proportion lemma |xy| >= |y|, a conflict of the bounds.
    #[test]
    fn makes_the_proportion_lemma() {
        let result = run_basic_lemma(
            3,
            &[(2, &[0, 1])],
            &[
                (0, KIND_GE, 2),
                (1, KIND_GE, 3),
                (2, KIND_GE, 1),
                (2, KIND_LE, 1),
            ],
            false,
        );
        assert_eq!(result.0, "values 2,3,1 toRefine 2");
        assert_eq!(result.1, ["[] {0,1,2,3}"]);
    }

    // x*y*z = 1 and y*z = 1 with x = 2, y = 3, z = -1: the lemmas stop at the first conflict.
    #[test]
    fn stops_at_the_first_conflict_over_the_binary_factorizations() {
        let result = run_basic_lemma(
            5,
            &[(3, &[0, 1, 2]), (4, &[1, 2])],
            &[
                (0, KIND_GE, 2),
                (1, KIND_GE, 3),
                (2, KIND_LE, -1),
                (3, KIND_GE, 1),
                (3, KIND_LE, 1),
                (4, KIND_GE, 1),
                (4, KIND_LE, 1),
            ],
            false,
        );
        assert_eq!(result.0, "values 2,3,-1,1,1 toRefine 3,4");
        assert_eq!(result.1, ["[] {0,1,2,3}"]);
    }
}
