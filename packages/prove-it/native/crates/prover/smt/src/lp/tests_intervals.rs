// tests/unit/smt-intervals.test.ts: dep_intervals, nex_creator and cross_nested.
use std::collections::HashSet;

use prove_decide::Limits;
use prove_num::{Int, Rational};

use crate::lp::cross_nested::CrossNested;
use crate::lp::dep_intervals::{
    DepInterval, DepsMode, add, check_interval_for_conflict_on_zero, display_dep_interval, div,
    intersect, is_empty, mk_dep_interval, mul, mul_scalar, power, separated_from_zero, set_value,
    set_zero_interval_deps_for_mult,
};
use crate::lp::dependency::{linearize, mk_leaf};
use crate::lp::nex::{Nex, NexId, get_nex_val, print_nex};
use crate::lp::nex_creator::{NexCreator, NexFactor};
use crate::util::random_gen::RandomGen;
use crate::util::rlimit::ResourceLimit;

const WITH_DEPS: DepsMode = DepsMode::WithDeps;

fn mk_closed(lower: Rational, upper: Rational, lower_leaf: u32, upper_leaf: u32) -> DepInterval {
    let mut interval = mk_dep_interval();
    set_value(&mut interval, &lower);
    interval.upper = upper;
    interval.lower_dep = mk_leaf(lower_leaf);
    interval.upper_dep = mk_leaf(upper_leaf);
    interval
}

fn int(value: i64) -> Rational {
    Rational::from_i64(value)
}

fn ratio(num: i64, den: i64) -> Rational {
    Rational::of(Int::from(num), Int::from(den))
}

// mk_random_interval from Z3's src/test/interval.cpp. Z3's rand() is RandomGen's generator.
fn mk_random_interval(random: &mut RandomGen, magnitude: u32) -> DepInterval {
    let mut interval = mk_dep_interval();
    let kind = random.next() % 3;
    if kind == 0 {
        if random.next().is_multiple_of(4) {
            interval.is_upper_open = random.next().is_multiple_of(2);
            interval.is_upper_inf = false;
            interval.upper = int(-i64::from(random.next() % magnitude));
            return interval;
        }
        interval.is_upper_open = random.next().is_multiple_of(2);
        interval.is_upper_inf = false;
        let upper = -i64::from(random.next() % magnitude);
        interval.upper = int(upper);
        interval.is_lower_open = random.next().is_multiple_of(2);
        interval.is_lower_inf = false;
        let gap = i64::from(random.next() % magnitude);
        let shift = i64::from(interval.is_lower_open || interval.is_upper_open);
        interval.lower = int(upper - gap - shift);
        return interval;
    }
    if kind == 1 {
        if !random.next().is_multiple_of(4) {
            interval.is_lower_open = random.next().is_multiple_of(2);
            interval.is_lower_inf = false;
            interval.lower = int(-i64::from(random.next() % magnitude) - 1);
        }
        if !random.next().is_multiple_of(4) {
            interval.is_upper_open = random.next().is_multiple_of(2);
            interval.is_upper_inf = false;
            interval.upper = int(i64::from(random.next() % magnitude) + 1);
        }
        return interval;
    }
    if random.next().is_multiple_of(4) {
        interval.is_lower_open = random.next().is_multiple_of(2);
        interval.is_lower_inf = false;
        interval.lower = int(i64::from(random.next() % magnitude));
        return interval;
    }
    interval.is_lower_open = random.next().is_multiple_of(2);
    interval.is_lower_inf = false;
    let lower = i64::from(random.next() % magnitude);
    interval.lower = int(lower);
    interval.is_upper_open = random.next().is_multiple_of(2);
    interval.is_upper_inf = false;
    let gap = i64::from(random.next() % magnitude);
    let shift = i64::from(interval.is_lower_open || interval.is_upper_open);
    interval.upper = int(lower + gap + shift);
    interval
}

// The points that satisfy the bounds the dependency names: leaf lower_leaf for the lower bound,
// upper_leaf for the upper bound. A bound the dependency leaves out does not constrain them.
fn get_samples(
    interval: &DepInterval,
    leaves: &[u32],
    lower_leaf: u32,
    upper_leaf: u32,
) -> Vec<Rational> {
    let is_lower_used = leaves.contains(&lower_leaf) && !interval.is_lower_inf;
    let is_upper_used = leaves.contains(&upper_leaf) && !interval.is_upper_inf;
    let grid = (0..33).map(|index| ratio(index - 16, 2));
    let near_bounds = [&interval.lower, &interval.upper]
        .into_iter()
        .flat_map(|bound| {
            [
                bound.clone(),
                bound.add(&ratio(1, 8)),
                bound.sub(&ratio(1, 8)),
            ]
        });
    grid.chain(near_bounds)
        .filter(|value| {
            if is_lower_used {
                let comparison = value.compare(&interval.lower);
                if comparison.is_lt() || (comparison.is_eq() && interval.is_lower_open) {
                    return false;
                }
            }
            if is_upper_used {
                let comparison = value.compare(&interval.upper);
                if comparison.is_gt() || (comparison.is_eq() && interval.is_upper_open) {
                    return false;
                }
            }
            true
        })
        .collect()
}

// The lemma Z3's test writes for each bound of the result: the argument bounds its dependency
// names imply the bound.
fn expect_deps_justify(
    first: &DepInterval,
    second: Option<&DepInterval>,
    result: &DepInterval,
    apply: &dyn Fn(&Rational, &Rational) -> Option<Rational>,
) {
    for is_lower in [true, false] {
        let is_inf = if is_lower {
            result.is_lower_inf
        } else {
            result.is_upper_inf
        };
        if is_inf {
            continue;
        }
        let leaves = linearize(&[if is_lower {
            result.lower_dep.clone()
        } else {
            result.upper_dep.clone()
        }]);
        let bound = if is_lower {
            &result.lower
        } else {
            &result.upper
        };
        let is_open = if is_lower {
            result.is_lower_open
        } else {
            result.is_upper_open
        };
        let rights = match second {
            None => vec![Rational::zero()],
            Some(second) => get_samples(second, &leaves, 3, 4),
        };
        for left in get_samples(first, &leaves, 1, 2) {
            for right in &rights {
                let Some(value) = apply(&left, right) else {
                    continue;
                };
                let comparison = if is_lower {
                    value.compare(bound)
                } else {
                    bound.compare(&value)
                };
                let is_sound = comparison.is_gt() || (comparison.is_eq() && !is_open);
                assert!(
                    is_sound,
                    "{} {} -> {} fails at {left}, {right}",
                    display_dep_interval(first),
                    second.map_or(String::new(), display_dep_interval),
                    display_dep_interval(result)
                );
            }
        }
    }
}

fn with_leaves(mut interval: DepInterval, lower_leaf: u32, upper_leaf: u32) -> DepInterval {
    interval.lower_dep = mk_leaf(lower_leaf);
    interval.upper_dep = mk_leaf(upper_leaf);
    interval
}

fn product(first: &DepInterval, second: &DepInterval) -> DepInterval {
    let mut result = mk_dep_interval();
    mul(first, second, &mut result, WITH_DEPS);
    result
}

fn get_bounds_text(interval: &DepInterval) -> String {
    display_dep_interval(interval)
        .split(' ')
        .next()
        .unwrap_or_default()
        .to_string()
}

#[test]
fn multiplies_the_intervals_of_z3s_nla_intervals_tests() {
    let positive = product(
        &mk_closed(int(1), int(3), 1, 2),
        &mk_closed(int(2), int(4), 3, 4),
    );
    assert_eq!(display_dep_interval(&positive), "[2,12] ld 1 3 ud 4 1 2");
    let negative = product(
        &mk_closed(int(-3), int(-1), 1, 2),
        &mk_closed(int(2), int(4), 3, 4),
    );
    assert_eq!(display_dep_interval(&negative), "[-12,-2] ld 4 1 2 ud 3 2");
    let crossing = product(
        &mk_closed(int(-2), int(3), 1, 2),
        &mk_closed(int(1), int(4), 3, 4),
    );
    assert_eq!(display_dep_interval(&crossing), "[-8,12] ld 4 1 3 ud 4 3 2");
    let mixed = product(
        &product(
            &mk_closed(int(-1), int(1), 1, 2),
            &mk_closed(int(-2), int(2), 3, 4),
        ),
        &mk_closed(int(1), int(3), 5, 6),
    );
    assert_eq!(get_bounds_text(&mixed), "[-6,6]");
    let fractional = product(
        &mk_closed(ratio(1, 2), ratio(3, 2), 1, 2),
        &mk_closed(ratio(5, 2), ratio(7, 2), 3, 4),
    );
    assert_eq!(get_bounds_text(&fractional), "[5/4,21/4]");
}

#[test]
fn squares_an_interval_that_crosses_zero_from_its_two_bounds() {
    let mut square = mk_dep_interval();
    power(&mk_closed(int(-3), int(2), 1, 2), 2, &mut square, WITH_DEPS);
    assert_eq!(display_dep_interval(&square), "[0,9] ud 1 2");
}

#[test]
fn keeps_open_bounds_open_and_closes_a_zero_bound_of_a_product() {
    let mut first = with_leaves(mk_dep_interval(), 1, 2);
    first.is_lower_inf = false;
    first.is_lower_open = false;
    first.lower = Rational::zero();
    first.is_upper_inf = false;
    first.is_upper_open = false;
    first.upper = int(2);
    let mut second = mk_closed(int(1), int(3), 3, 4);
    second.is_lower_open = true;
    let mut product = mk_dep_interval();
    mul(&first, &second, &mut product, DepsMode::WithoutDeps);
    assert_eq!(display_dep_interval(&product), "[0,6]");
    let mut sum = mk_dep_interval();
    add(&first, &second, &mut sum, WITH_DEPS);
    assert_eq!(display_dep_interval(&sum), "(1,5] ld 1 3 ud 2 4");
}

#[test]
fn swaps_the_dependencies_when_a_scalar_is_negative() {
    let mut scaled = mk_dep_interval();
    mul_scalar(
        &int(-2),
        &mk_closed(int(1), int(3), 1, 2),
        &mut scaled,
        WITH_DEPS,
    );
    assert_eq!(display_dep_interval(&scaled), "[-6,-2] ld 2 ud 1");
}

#[test]
fn divides_by_an_interval_that_excludes_zero() {
    let mut quotient = mk_dep_interval();
    let mut divisor = mk_closed(Rational::zero(), int(2), 3, 4);
    divisor.is_lower_open = true;
    div(
        &mk_closed(int(1), int(4), 1, 2),
        &divisor,
        &mut quotient,
        WITH_DEPS,
    );
    assert_eq!(display_dep_interval(&quotient), "[1/2,oo) ld 4 1 3");
}

#[test]
fn intersects_with_the_tighter_bound_and_finds_the_empty_intersection() {
    let mut result = mk_dep_interval();
    intersect(
        &mk_closed(int(0), int(5), 1, 2),
        &mk_closed(int(3), int(8), 3, 4),
        &mut result,
        WITH_DEPS,
    );
    assert_eq!(display_dep_interval(&result), "[3,5] ld 3 ud 2");
    assert!(!is_empty(&result));
    let mut disjoint = mk_dep_interval();
    intersect(
        &mk_closed(int(0), int(1), 1, 2),
        &mk_closed(int(3), int(8), 3, 4),
        &mut disjoint,
        WITH_DEPS,
    );
    assert!(is_empty(&disjoint));
}

#[test]
fn explains_the_bound_that_separates_an_interval_from_zero() {
    let interval = mk_closed(int(1), int(3), 1, 2);
    assert!(separated_from_zero(&interval));
    let mut explanations: Vec<Vec<u32>> = Vec::new();
    let is_conflict =
        check_interval_for_conflict_on_zero(&interval, &mk_leaf(7), &mut |explanation| {
            explanations.push(explanation)
        });
    assert!(is_conflict);
    assert_eq!(explanations, vec![vec![7, 1]]);
    assert!(!separated_from_zero(&mk_closed(int(0), int(3), 1, 2)));
}

#[test]
fn joins_both_dependencies_of_a_zero_factor() {
    let mut interval = mk_closed(Rational::zero(), Rational::zero(), 1, 2);
    set_zero_interval_deps_for_mult(&mut interval);
    assert_eq!(display_dep_interval(&interval), "[0,0] ld 1 2 ud 1 2");
}

#[test]
fn justifies_each_bound_by_the_bounds_its_dependency_names_like_z3s_interval_tests() {
    let mut random = RandomGen::new(0);
    for _ in 0..150 {
        let first = with_leaves(mk_random_interval(&mut random, 3), 1, 2);
        let second = with_leaves(mk_random_interval(&mut random, 3), 3, 4);
        let mut result = mk_dep_interval();
        mul(&first, &second, &mut result, WITH_DEPS);
        expect_deps_justify(&first, Some(&second), &result, &|left, right| {
            Some(left.mul(right))
        });
        add(&first, &second, &mut result, WITH_DEPS);
        expect_deps_justify(&first, Some(&second), &result, &|left, right| {
            Some(left.add(right))
        });
        power(&first, 2, &mut result, WITH_DEPS);
        expect_deps_justify(&first, None, &result, &|left, _| Some(left.mul(left)));
        power(&first, 3, &mut result, WITH_DEPS);
        expect_deps_justify(&first, None, &result, &|left, _| {
            Some(left.mul(left).mul(left))
        });
        let is_second_separated = (!second.is_lower_inf
            && (second.lower.is_positive() || (second.lower.is_zero() && second.is_lower_open)))
            || (!second.is_upper_inf
                && (second.upper.is_negative()
                    || (second.upper.is_zero() && second.is_upper_open)));
        if !is_second_separated {
            continue;
        }
        div(&first, &second, &mut result, WITH_DEPS);
        expect_deps_justify(&first, Some(&second), &result, &|left, right| {
            if right.is_zero() {
                None
            } else {
                Some(left.div(right))
            }
        });
    }
}

fn mk_creator(weights: &[u32]) -> NexCreator {
    let mut creator = NexCreator::new();
    creator.set_number_of_vars(weights.len());
    for (variable, weight) in weights.iter().enumerate() {
        creator.set_var_weight(variable, *weight);
    }
    creator
}

fn expr(id: NexId) -> NexFactor {
    NexFactor::Expr(id)
}

fn scalar(value: i64) -> NexFactor {
    NexFactor::Scalar(int(value))
}

#[test]
fn orders_expressions_like_z3s_test_nex_order() {
    let mut creator = mk_creator(&[10, 9, 8]);
    let a = creator.mk_var(0);
    let b = creator.mk_var(1);
    let c = creator.mk_var(2);
    assert!(creator.gt(a, b) && creator.gt(b, c) && creator.gt(a, c));
    let ab = creator.mk_mul(&[expr(a), expr(b)]);
    let ba = creator.mk_mul(&[expr(b), expr(a)]);
    let ac = creator.mk_mul(&[expr(a), expr(c)]);
    assert!(creator.gt(ab, ac));
    assert!(!creator.gt(ac, ab));
    let three_ac = creator.mk_mul(&[scalar(3), expr(a), expr(c)]);
    let two_ab = creator.mk_mul(&[scalar(2), expr(a), expr(b)]);
    assert!(creator.gt(ab, three_ac));
    assert!(!creator.gt(three_ac, ab));
    assert!(!creator.gt(a, ab));
    assert!(creator.gt(ab, a));
    assert!(creator.gt(two_ab, three_ac));
    assert!(!creator.gt(three_ac, two_ab));
    let two_a = creator.mk_mul(&[scalar(2), expr(a)]);
    assert!(!creator.gt(two_a, two_ab));
    assert!(creator.gt(two_ab, two_a));
    assert!(creator.equal(ab, ba));
    let five_a = creator.mk_mul(&[scalar(5), expr(a)]);
    let one = creator.mk_scalar(Rational::one());
    let sum = creator.mk_sum(&[five_a, one]);
    let poly = creator.mk_mul(&[expr(sum), expr(b)]);
    let simplified = creator.simplify(poly);
    assert_eq!(print_nex(&creator.nexes, simplified), "((5 *j0)+1)*j1");
}

#[test]
fn simplifies_like_z3s_test_simplify() {
    let mut creator = mk_creator(&[0, 1, 2]);
    let a = creator.mk_var(0);
    let b = creator.mk_var(1);
    let c = creator.mk_var(2);
    let bc = creator.mk_mul(&[expr(b), expr(c)]);
    let a_plus_bc = creator.mk_sum(&[a, bc]);
    let two = creator.mk_scalar(int(2));
    let two_a_plus_bc = creator.mk_mul(&[expr(two), expr(a_plus_bc)]);
    let simplified_two_a_plus_bc = creator.simplify(two_a_plus_bc);
    assert!(creator.equal(simplified_two_a_plus_bc, two_a_plus_bc));
    let simplified = creator.simplify(a_plus_bc);
    assert!(matches!(&creator.nexes[simplified], Nex::Sum(sum) if sum.children.len() > 1));
    let three = creator.mk_scalar(int(3));
    let three_ab = creator.mk_mul(&[expr(three), expr(a), expr(b)]);
    let cube_product = creator.mk_mul(&[expr(three_ab), expr(three_ab), expr(three_ab)]);
    let cube = creator.simplify(cube_product);
    assert!(matches!(&creator.nexes[cube], Nex::Mul(mul) if mul.coeff == int(27)));
    assert_eq!(print_nex(&creator.nexes, cube), "27 *(j1^3)*(j0^3)");
}

#[test]
fn merges_the_summands_that_differ_in_their_coefficient() {
    let mut creator = mk_creator(&[0, 1, 2]);
    let a = creator.mk_var(0);
    let b = creator.mk_var(1);
    let c = creator.mk_var(2);
    let three_bc = creator.mk_mul(&[scalar(3), expr(b), expr(c)]);
    let four = creator.mk_scalar(int(4));
    let two_cb = creator.mk_mul(&[scalar(2), expr(c), expr(b)]);
    let minus_one = creator.mk_scalar(int(-1));
    let sum = creator.mk_sum(&[a, three_bc, four, two_cb, minus_one]);
    let simplified = creator.simplify(sum);
    assert_eq!(print_nex(&creator.nexes, simplified), "(5 *j2*j1)+j0+3");
}

#[test]
fn divides_a_product_by_a_variable_and_by_a_product() {
    let mut creator = mk_creator(&[0, 1, 2]);
    let a = creator.mk_var(0);
    let b = creator.mk_var(1);
    let unsimplified = creator.mk_mul(&[scalar(6), expr(a), expr(a), expr(b)]);
    let product = creator.simplify(unsimplified);
    let by_var = creator.mk_div_by_var(product, 0);
    assert_eq!(print_nex(&creator.nexes, by_var), "6 *j1*j0");
    assert!(
        matches!(creator.nexes[product], Nex::Mul(_)),
        "expected a product"
    );
    let divisor = creator.mk_mul(&[scalar(2), expr(a)]);
    let quotient = creator.mk_div(product, divisor);
    assert_eq!(print_nex(&creator.nexes, quotient), "3 *j1*j0");
}

fn mk_sum_of_products(creator: &mut NexCreator) -> NexId {
    let a = creator.mk_var(0);
    let b = creator.mk_var(1);
    let ab = creator.mk_mul(&[expr(a), expr(b)]);
    let c = creator.mk_var(2);
    let ac = creator.mk_mul(&[expr(a), expr(c)]);
    let sum = creator.mk_sum(&[ab, ac]);
    creator.simplify(sum)
}

#[test]
fn stops_when_the_resource_limit_runs_out_like_z3s_test_simplify() {
    let mut creator = mk_creator(&[0, 0, 0]);
    let sum = mk_sum_of_products(&mut creator);
    let mut count = 0;
    let limits = Limits::new(f64::INFINITY, Some(1), None);
    let limit = ResourceLimit::new(&limits);
    CrossNested::new(
        (
            |_: &NexCreator, _: NexId| {
                count += 1;
                false
            },
            |_: usize| false,
        ),
        &|| limit.inc(),
        1,
        &mut creator,
    )
    .run(sum);
    assert_eq!(count, 0);
}

#[test]
fn extracts_the_common_factor_of_every_summand() {
    let mut creator = mk_creator(&[0, 0, 0]);
    let sum = mk_sum_of_products(&mut creator);
    let mut forms: Vec<String> = Vec::new();
    let limits = Limits::new(f64::INFINITY, None, None);
    let limit = ResourceLimit::new(&limits);
    CrossNested::new(
        (
            |creator: &NexCreator, expr: NexId| {
                forms.push(print_nex(&creator.nexes, expr));
                false
            },
            |_: usize| false,
        ),
        &|| limit.inc(),
        1,
        &mut creator,
    )
    .run(sum);
    assert_eq!(forms, vec!["(j0)*(j2+j1)".to_string()]);
}

#[test]
fn reports_forms_that_keep_the_value_of_the_sum() {
    let mut creator = mk_creator(&[0, 1, 2, 3]);
    let variables: Vec<NexId> = (0..4).map(|variable| creator.mk_var(variable)).collect();
    let summands = [
        creator.mk_mul(&[expr(variables[0]), expr(variables[1])]),
        creator.mk_mul(&[scalar(2), expr(variables[0]), expr(variables[2])]),
        creator.mk_mul(&[expr(variables[1]), expr(variables[2]), expr(variables[3])]),
        creator.mk_mul(&[expr(variables[3]), expr(variables[3])]),
        creator.mk_scalar(int(5)),
    ];
    let original = creator.mk_sum(&summands);
    let copy = creator.clone(original);
    let get_var_val = |variable: usize| int([2, -3, 5, 7][variable]);
    let expected = get_nex_val(&creator.nexes, copy, &get_var_val);
    let mut values: Vec<Rational> = Vec::new();
    let mut forms: HashSet<String> = HashSet::new();
    let simplified = creator.simplify(original);
    let limits = Limits::new(f64::INFINITY, None, None);
    let limit = ResourceLimit::new(&limits);
    CrossNested::new(
        (
            |creator: &NexCreator, expr: NexId| {
                values.push(get_nex_val(&creator.nexes, expr, &get_var_val));
                forms.insert(print_nex(&creator.nexes, expr));
                false
            },
            |_: usize| false,
        ),
        &|| limit.inc(),
        7,
        &mut creator,
    )
    .run(simplified);
    assert!(values.len() > 1);
    assert!(values.iter().all(|value| *value == expected));
    assert_eq!(forms.len(), values.len());
}
