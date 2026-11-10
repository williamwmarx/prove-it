//! Ported from Z3 (src/math/polynomial/algebraic_numbers.cpp, src/util/basic_interval.h,
//! src/util/mpbq.cpp), MIT license, see z3-license.txt. Real algebraic numbers: a rational, or the
//! root of a square-free integer polynomial in an open isolating interval of binary rationals whose
//! ends the polynomial has opposite signs at. Comparing and evaluating refine these intervals in
//! place, and may find a number rational, as Z3 does, so later operations see Z3's intervals.
//!
//! An `Anum` is a shared mutable handle, as the TypeScript object is: refining it through one
//! handle shows through every other, and the same number may be passed twice (`a + a`).

use std::cell::{Ref, RefCell, RefMut};
use std::cmp::Ordering;
use std::rc::Rc;

use super::mpbq::{Mpbq, get_log2};
use super::polynomial::{NULL_VAR, Polynomial, PolynomialManager, ValueOps, Var};
use super::upolynomial::{Upolynomial, UpolynomialManager};
use super::upolynomial_factorization::{FactorParams, UpolynomialFactors, factor_upolynomial};
use super::{Int, Rational, SmtError};

// algebraic.factor_max_prime, factor_num_primes and factor_search_size.
const FACTOR_PARAMS: FactorParams = FactorParams {
    max_prime: 31,
    prime_trials: 1,
    max_search_size: 5000,
};
// -algebraic.min_mag: a refined interval narrower than about 1/2^16 is not kept.
const MIN_MAGNITUDE: i64 = -16;
// DEFAULT_PRECISION: how far isolate_roots with signs refines each root first.
const SIGN_PRECISION: u32 = 2;
// The variables of the polynomials the binary operations build, m_x and m_y.
const X: Var = 0;
const Y: Var = 1;

const STILL_IRRATIONAL: &str = "a successful refinement leaves the number irrational";

#[derive(Clone, Debug)]
pub struct AlgebraicCell {
    pub p: Upolynomial,
    pub lower: Mpbq,
    pub upper: Mpbq,
    pub is_minimal: bool,
    pub is_sign_lower_neg: bool,
    pub is_not_rational: bool,
    /// m_i: which root of p the number is, from 1, or 0 when not yet computed.
    pub root_index: u32,
}

impl AlgebraicCell {
    pub fn sign_lower(&self) -> i32 {
        if self.is_sign_lower_neg { -1 } else { 1 }
    }
}

#[derive(Clone, Debug)]
pub enum AnumValue {
    Rational(Rational),
    Cell(AlgebraicCell),
}

/// anum: a mutable handle, since refining an algebraic number may turn it into a rational.
#[derive(Clone, Debug)]
pub struct Anum(Rc<RefCell<AnumValue>>);

impl Anum {
    pub fn new(value: Rational) -> Anum {
        Anum(Rc::new(RefCell::new(AnumValue::Rational(value))))
    }

    fn from_cell(cell: AlgebraicCell) -> Anum {
        Anum(Rc::new(RefCell::new(AnumValue::Cell(cell))))
    }

    pub fn value(&self) -> Ref<'_, AnumValue> {
        self.0.borrow()
    }

    pub fn set(&self, value: AnumValue) {
        *self.0.borrow_mut() = value;
    }

    /// The TypeScript `===` on numbers.
    pub fn ptr_eq(first: &Anum, second: &Anum) -> bool {
        Rc::ptr_eq(&first.0, &second.0)
    }

    fn value_mut(&self) -> RefMut<'_, AnumValue> {
        self.0.borrow_mut()
    }

    fn rational(&self) -> Option<Rational> {
        match &*self.value() {
            AnumValue::Rational(value) => Some(value.clone()),
            AnumValue::Cell(_) => None,
        }
    }

    fn cell(&self) -> Option<Ref<'_, AlgebraicCell>> {
        Ref::filter_map(self.value(), |value| match value {
            AnumValue::Cell(cell) => Some(cell),
            AnumValue::Rational(_) => None,
        })
        .ok()
    }

    fn cell_mut(&self) -> Option<RefMut<'_, AlgebraicCell>> {
        RefMut::filter_map(self.value_mut(), |value| match value {
            AnumValue::Cell(cell) => Some(cell),
            AnumValue::Rational(_) => None,
        })
        .ok()
    }
}

#[derive(Clone, Debug)]
struct BqInterval {
    lower: Mpbq,
    upper: Mpbq,
}

// One end of the interval select_small picks from: a binary rational end is closed, a rational one
// open.
struct SelectEnd {
    value: Rational,
    is_open: bool,
}

// save_intervals: an interval to restore when refining it made it too narrow to keep.
struct SavedInterval {
    anum: Anum,
    lower: Mpbq,
    upper: Mpbq,
    is_restored: bool,
}

// The factor whose Sturm sequence counts the one root in an interval.
struct IsolatingFactor {
    factor: Upolynomial,
    sequence: Vec<Upolynomial>,
    lower_variations: i64,
}

// What rational_root_in_interval finds: the rational root, or the refined interval.
enum RootOrInterval {
    Root(Rational),
    Interval(BqInterval),
}

pub struct ClosestAnums {
    pub roots: Vec<Anum>,
    pub indices: Vec<u32>,
}

pub struct SignedRoots {
    pub roots: Vec<Anum>,
    pub signs: Vec<i32>,
}

fn min_bq<'a>(first: &'a Mpbq, second: &'a Mpbq) -> &'a Mpbq {
    if second.compare(first) < 0 {
        second
    } else {
        first
    }
}

fn max_bq<'a>(first: &'a Mpbq, second: &'a Mpbq) -> &'a Mpbq {
    if second.compare(first) > 0 {
        second
    } else {
        first
    }
}

fn add_intervals(first: &BqInterval, second: &BqInterval) -> BqInterval {
    BqInterval {
        lower: first.lower.add(&second.lower),
        upper: first.upper.add(&second.upper),
    }
}

fn mul_intervals(first: &BqInterval, second: &BqInterval) -> BqInterval {
    let products = [
        first.lower.mul(&second.lower),
        first.lower.mul(&second.upper),
        first.upper.mul(&second.lower),
        first.upper.mul(&second.upper),
    ];
    BqInterval {
        lower: products[1..]
            .iter()
            .fold(&products[0], |result, product| min_bq(result, product))
            .clone(),
        upper: products[1..]
            .iter()
            .fold(&products[0], |result, product| max_bq(result, product))
            .clone(),
    }
}

// mpbqi_manager over open intervals, as t_eval uses it.
struct IntervalOps;

impl ValueOps<BqInterval> for IntervalOps {
    fn from_integer(&mut self, value: &Int) -> BqInterval {
        BqInterval {
            lower: Mpbq::of(value.clone(), 0),
            upper: Mpbq::of(value.clone(), 0),
        }
    }

    fn add(&mut self, first: &BqInterval, second: &BqInterval) -> Result<BqInterval, SmtError> {
        Ok(add_intervals(first, second))
    }

    fn mul(&mut self, first: &BqInterval, second: &BqInterval) -> Result<BqInterval, SmtError> {
        Ok(mul_intervals(first, second))
    }

    fn power(&mut self, base: &BqInterval, exponent: u32) -> Result<BqInterval, SmtError> {
        Ok(get_interval_power(base, exponent))
    }
}

fn get_interval_power(base: &BqInterval, exponent: u32) -> BqInterval {
    let lower = base.lower.power(exponent);
    let upper = base.upper.power(exponent);
    if exponent % 2 == 1 || !base.lower.is_neg() {
        return BqInterval { lower, upper };
    }
    if base.upper.is_neg() {
        return BqInterval {
            lower: upper,
            upper: lower,
        };
    }
    BqInterval {
        lower: Mpbq::zero(),
        upper: max_bq(&lower, &upper).clone(),
    }
}

fn contains_zero(interval: &BqInterval) -> bool {
    interval.lower.is_neg() && interval.upper.is_pos()
}

fn get_interval(cell: &AlgebraicCell) -> BqInterval {
    BqInterval {
        lower: cell.lower.clone(),
        upper: cell.upper.clone(),
    }
}

// mpz log2 and mlog2: 0 outside the sign they expect.
fn get_positive_log2(value: &Int) -> i64 {
    if !value.is_positive() {
        0
    } else {
        get_log2(value)
    }
}

fn get_negative_log2(value: &Int) -> i64 {
    if !value.is_negative() {
        0
    } else {
        get_log2(value)
    }
}

// magnitude_ub
fn get_magnitude_upper_bound(value: &Mpbq) -> i64 {
    if value.is_zero() {
        0
    } else if value.is_pos() {
        get_log2(&value.num) - i64::from(value.k) + 1
    } else {
        get_negative_log2(&value.num) - i64::from(value.k)
    }
}

// magnitude: about log2 of the width of (l, u).
fn get_magnitude(lower: &Mpbq, upper: &Mpbq) -> i64 {
    if lower.k == upper.k {
        return get_magnitude_upper_bound(lower);
    }
    let log2 = if lower.is_neg() {
        get_negative_log2
    } else {
        get_positive_log2
    };
    log2(&upper.num) - log2(&lower.num) - i64::from(upper.k) + i64::from(lower.k)
        - i64::from(upper.k)
}

// select_integer: the integer select_small takes from scaled ends, preferring a closed end.
fn select_integer(
    lower: &SelectEnd,
    upper: &SelectEnd,
    lower_value: &Rational,
    upper_value: &Rational,
) -> Option<Int> {
    if !lower.is_open && lower_value.is_int() {
        return Some(lower_value.num().clone());
    }
    if !upper.is_open && upper_value.is_int() {
        return Some(upper_value.num().clone());
    }
    let ceil_lower = if lower.is_open && lower_value.is_int() {
        lower_value.num() + &Int::one()
    } else {
        lower_value.ceil().num().clone()
    };
    let floor_upper = if upper.is_open && upper_value.is_int() {
        upper_value.num() - &Int::one()
    } else {
        upper_value.floor().num().clone()
    };
    (ceil_lower <= floor_upper).then_some(ceil_lower)
}

// select_small_core: the binary rational between two ends with the smallest power of two as its
// denominator.
fn select_small(lower: &SelectEnd, upper: &SelectEnd) -> Mpbq {
    let mut k: u32 = 0;
    loop {
        let scale = Rational::from_int(&Int::one() << u64::from(k));
        let integer = select_integer(
            lower,
            upper,
            &lower.value.mul(&scale),
            &upper.value.mul(&scale),
        );
        if let Some(integer) = integer {
            return Mpbq::of(integer, k);
        }
        k += 1;
    }
}

fn get_cell(anum: Option<&Anum>) -> Result<Ref<'_, AlgebraicCell>, SmtError> {
    let get_error = || SmtError::Invariant("expected an irrational algebraic number".to_string());
    anum.ok_or_else(get_error)?.cell().ok_or_else(get_error)
}

// values[variable], undefined past the end as in a sparse JavaScript array.
fn get_value(values: &[Option<Anum>], variable: Var) -> Option<&Anum> {
    usize::try_from(variable)
        .ok()
        .and_then(|index| values.get(index))
        .and_then(Option::as_ref)
}

fn get_assigned(values: &[Option<Anum>], variable: Var) -> Result<Anum, SmtError> {
    get_value(values, variable)
        .cloned()
        .ok_or_else(|| SmtError::Invariant(format!("x{variable} is unassigned")))
}

fn get_rational_values(values: &[Option<Anum>]) -> Vec<Option<Rational>> {
    values
        .iter()
        .map(|anum| anum.as_ref().and_then(Anum::rational))
        .collect()
}

fn get_extended(values: &[Option<Anum>], variable: Var, anum: &Anum) -> Vec<Option<Anum>> {
    let mut extended = values.to_vec();
    set_value(&mut extended, variable, anum);
    extended
}

// values[variable] = anum, growing the array as JavaScript does.
fn set_value(values: &mut Vec<Option<Anum>>, variable: Var, anum: &Anum) {
    let index = variable as usize;
    if values.len() <= index {
        values.resize(index + 1, None);
    }
    values[index] = Some(anum.clone());
}

// The cell compare_core holds on to: refining a number into a rational detaches it, and it keeps
// the interval it had then, as the TypeScript's reference to the old cell object does.
fn update_detached_cell(anum: &Anum, cell: &mut AlgebraicCell) {
    if let Some(current) = anum.cell() {
        cell.lower = current.lower.clone();
        cell.upper = current.upper.clone();
    }
}

// convert: p in the local manager, without its monomials of degree above maxDegree in x. With no
// source manager, p already is in the local one.
fn convert(
    local: &mut PolynomialManager,
    source: Option<&PolynomialManager>,
    polynomial: &Polynomial,
    x: Var,
    max_degree: Option<u32>,
) -> Polynomial {
    let Some(pm) = source else {
        return polynomial.clone();
    };
    let mut as_ = Vec::new();
    let mut ms = Vec::new();
    for index in 0..polynomial.size() {
        let monomial = polynomial.monomial_at(index);
        let vars = pm.monomial_vars(monomial);
        let degrees = pm.monomial_degrees(monomial);
        let degree = vars
            .iter()
            .position(|&variable| variable == x)
            .map_or(0, |position| degrees[position]);
        if x != NULL_VAR && max_degree.is_some_and(|max_degree| degree > max_degree) {
            continue;
        }
        as_.push(polynomial.coeff_at(index));
        ms.push(local.mk_monomial(vars, degrees));
    }
    local.mk_polynomial(&as_, &ms)
}

// The evaluation of the binary operations' anumOps: algebraic number arithmetic.
struct AnumOps<'a> {
    am: &'a mut AlgebraicManager,
}

impl ValueOps<Anum> for AnumOps<'_> {
    fn from_integer(&mut self, value: &Int) -> Anum {
        Anum::new(Rational::from_int(value.clone()))
    }

    fn add(&mut self, first: &Anum, second: &Anum) -> Result<Anum, SmtError> {
        self.am.add(first, second)
    }

    fn mul(&mut self, first: &Anum, second: &Anum) -> Result<Anum, SmtError> {
        self.am.mul(first, second)
    }

    fn power(&mut self, base: &Anum, exponent: u32) -> Result<Anum, SmtError> {
        self.am.power(base, exponent)
    }
}

pub struct AlgebraicManager {
    um: UpolynomialManager,
    pm: PolynomialManager,
}

impl Default for AlgebraicManager {
    fn default() -> AlgebraicManager {
        AlgebraicManager::new()
    }
}

impl AlgebraicManager {
    pub fn new() -> AlgebraicManager {
        AlgebraicManager {
            um: UpolynomialManager::new(None),
            pm: PolynomialManager::new(),
        }
    }

    // Queries.

    pub fn is_zero(&self, anum: &Anum) -> bool {
        matches!(&*anum.value(), AnumValue::Rational(value) if value.is_zero())
    }

    pub fn degree(&self, anum: &Anum) -> u32 {
        if self.is_zero(anum) {
            return 0;
        }
        match &*anum.value() {
            AnumValue::Rational(_) => 1,
            AnumValue::Cell(cell) => cell.p.len() as u32 - 1,
        }
    }

    pub fn copy(&self, anum: &Anum) -> Anum {
        Anum(Rc::new(RefCell::new(anum.value().clone())))
    }

    // is_int: refines the interval until it holds at most one integer, then tests it.
    pub fn is_int(&mut self, anum: &Anum) -> bool {
        match &*anum.value() {
            AnumValue::Rational(value) => return value.is_int(),
            AnumValue::Cell(cell) if cell.is_not_rational => return false,
            AnumValue::Cell(_) => {}
        }
        if !self.refine_until_precision(anum, 1) {
            return self.is_int(anum);
        }
        let candidate = {
            let cell = anum.cell().expect(STILL_IRRATIONAL);
            let candidate = Rational::from_int(cell.upper.floor());
            (cell.lower.compare_rational(&candidate) < 0
                && self.um.eval_sign_at_q(&cell.p, &candidate) == 0)
                .then_some(candidate)
        };
        let Some(candidate) = candidate else {
            return false;
        };
        anum.set(AnumValue::Rational(candidate));
        true
    }

    // is_rational: by the rational root theorem, the only candidate in an interval narrower than
    // 1/|a_n| is floor(u*|a_n|)/|a_n|.
    pub fn is_rational(&mut self, anum: &Anum) -> Result<bool, SmtError> {
        match &*anum.value() {
            AnumValue::Rational(_) => return Ok(true),
            AnumValue::Cell(cell) if cell.is_not_rational => return Ok(false),
            AnumValue::Cell(_) => {}
        }
        let mut saved = self.save_interval(anum)?;
        let abs_leading = {
            let cell = anum.cell().expect(STILL_IRRATIONAL);
            cell.p[cell.p.len() - 1].abs()
        };
        if !self.refine_until_precision(anum, (get_log2(&abs_leading) + 1) as u32) {
            return Ok(true);
        }
        let (candidate, is_root) = {
            let cell = anum.cell().expect(STILL_IRRATIONAL);
            let candidate = Rational::of(
                cell.upper.mul(&Mpbq::of(abs_leading.clone(), 0)).floor(),
                abs_leading,
            );
            let is_root = cell.lower.compare_rational(&candidate) < 0
                && self.um.eval_sign_at_q(&cell.p, &candidate) == 0;
            (candidate, is_root)
        };
        self.restore_if_too_small(&mut saved);
        if is_root {
            anum.set(AnumValue::Rational(candidate));
        } else {
            anum.cell_mut().expect(STILL_IRRATIONAL).is_not_rational = true;
        }
        Ok(is_root)
    }

    // get_i: which root of its polynomial the number is.
    pub fn get_root_index(&mut self, anum: &Anum) -> u32 {
        let mut value = anum.value_mut();
        match &mut *value {
            AnumValue::Rational(rational) => u32::from(!rational.is_zero()),
            AnumValue::Cell(cell) => {
                if cell.root_index == 0 {
                    cell.root_index = self.um.get_root_id(&cell.p, &cell.lower) + 1;
                }
                cell.root_index
            }
        }
    }

    // Cells.

    // mk_algebraic_cell: the coefficients made primitive with a positive leading coefficient.
    fn mk_cell(
        &mut self,
        p: Upolynomial,
        lower: Mpbq,
        upper: Mpbq,
        is_minimal: bool,
    ) -> AlgebraicCell {
        let mut cell = AlgebraicCell {
            p,
            lower,
            upper,
            is_minimal,
            is_sign_lower_neg: false,
            is_not_rational: is_minimal,
            root_index: 0,
        };
        self.update_sign_lower(&mut cell);
        cell.p = self.um.normalize(&cell.p);
        if cell.p.last().is_some_and(Int::is_negative) {
            cell.p = self.um.neg(&cell.p);
            cell.is_sign_lower_neg = !cell.is_sign_lower_neg;
        }
        cell
    }

    fn update_sign_lower(&self, cell: &mut AlgebraicCell) {
        cell.is_sign_lower_neg = self.um.eval_sign_at_bq(&cell.p, &cell.lower) < 0;
    }

    // set(a, p, l, u, minimal): the root of p in (l, u), a rational when p is linear.
    fn mk_anum(&mut self, p: Upolynomial, lower: Mpbq, upper: Mpbq, is_minimal: bool) -> Anum {
        if p.len() == 2 {
            return Anum::new(
                Rational::from_int(p[0].clone())
                    .div(&Rational::from_int(p[1].clone()))
                    .neg(),
            );
        }
        Anum::from_cell(self.mk_cell(p, lower, upper, is_minimal))
    }

    // normalize: an interval around zero shrunk to the side of zero holding the root.
    fn normalize(&mut self, anum: &Anum) {
        let interval = {
            let Some(cell) = anum.cell() else {
                return;
            };
            self.um
                .normalize_interval(&cell.p, &cell.lower, &cell.upper, cell.sign_lower())
        };
        let Some((lower, upper)) = interval else {
            anum.set(AnumValue::Rational(Rational::zero()));
            return;
        };
        let mut cell = anum.cell_mut().expect(STILL_IRRATIONAL);
        cell.lower = lower;
        cell.upper = upper;
    }

    // Refinement.

    // refine: halves the interval, or finds the number rational and returns false.
    fn refine(&mut self, anum: &Anum) -> bool {
        let refined = {
            let Some(cell) = anum.cell() else {
                return false;
            };
            self.um
                .refine_core(&cell.p, cell.sign_lower(), &cell.lower, &cell.upper)
        };
        if !refined.is_interval {
            anum.set(AnumValue::Rational(refined.lower.to_rational()));
            return false;
        }
        let mut cell = anum.cell_mut().expect(STILL_IRRATIONAL);
        cell.lower = refined.lower;
        cell.upper = refined.upper;
        true
    }

    fn refine_times(&mut self, anum: &Anum, count: i64) -> bool {
        for _ in 0..count {
            if !self.refine(anum) {
                return false;
            }
        }
        true
    }

    // refine_until_prec: refines until the interval is narrower than 1/2^precision.
    fn refine_until_precision(&mut self, anum: &Anum, precision: u32) -> bool {
        let refined = {
            let Some(cell) = anum.cell() else {
                return true;
            };
            self.um
                .refine_to_precision(&cell.p, &cell.lower, &cell.upper, precision)
        };
        if !refined.is_interval {
            anum.set(AnumValue::Rational(refined.lower.to_rational()));
            return false;
        }
        let mut cell = anum.cell_mut().expect(STILL_IRRATIONAL);
        cell.lower = refined.lower;
        cell.upper = refined.upper;
        true
    }

    fn get_cell_magnitude(&self, cell: &AlgebraicCell) -> i64 {
        get_magnitude(&cell.lower, &cell.upper)
    }

    fn save_interval(&self, anum: &Anum) -> Result<SavedInterval, SmtError> {
        let cell = get_cell(Some(anum))?;
        Ok(SavedInterval {
            anum: anum.clone(),
            lower: cell.lower.clone(),
            upper: cell.upper.clone(),
            is_restored: false,
        })
    }

    // restore_if_too_small: swaps the saved interval back in when the current one is too narrow.
    fn restore_if_too_small(&self, saved: &mut SavedInterval) {
        saved.is_restored = true;
        let Some(mut cell) = saved.anum.cell_mut() else {
            return;
        };
        if self.get_cell_magnitude(&cell) >= MIN_MAGNITUDE {
            return;
        }
        std::mem::swap(&mut cell.lower, &mut saved.lower);
        std::mem::swap(&mut cell.upper, &mut saved.upper);
    }

    // ~save_intervals
    fn release_interval(&self, saved: &mut SavedInterval) {
        if !saved.is_restored {
            self.restore_if_too_small(saved);
        }
    }

    // Root isolation.

    fn factor(&mut self, p: &[Int]) -> Result<(bool, UpolynomialFactors), SmtError> {
        factor_upolynomial(&mut self.um, p, &FACTOR_PARAMS)
    }

    // isolate_roots(up): the real roots of a univariate polynomial, factor by factor, sorted.
    fn isolate_univariate_roots(&mut self, up: &[Int]) -> Result<Vec<Anum>, SmtError> {
        let mut roots = Vec::new();
        if up.is_empty() {
            return Ok(roots);
        }
        let has_zero_root = self.um.has_zero_roots(up);
        if has_zero_root {
            roots.push(Anum::new(Rational::zero()));
        }
        let nonzero = if has_zero_root {
            self.um.remove_zero_roots(up)
        } else {
            up.to_vec()
        };
        let (is_complete, factors) = self.factor(&nonzero)?;
        for factor in &factors.factors {
            // The degree is factor.len() - 1.
            if factor.len() <= 1 {
                continue;
            }
            if factor.len() == 2 {
                roots.push(Anum::new(
                    Rational::from_int(factor[0].clone())
                        .div(&Rational::from_int(factor[1].clone()))
                        .neg(),
                ));
                continue;
            }
            let isolated = self.um.sqf_isolate_roots(factor);
            for root in &isolated.roots {
                roots.push(Anum::new(root.to_rational()));
            }
            for index in 0..isolated.lowers.len() {
                let refined = self.um.isolating2refinable(
                    factor,
                    &isolated.lowers[index],
                    &isolated.uppers[index],
                );
                roots.push(if refined.is_interval {
                    Anum::from_cell(self.mk_cell(
                        factor.clone(),
                        refined.lower,
                        refined.upper,
                        is_complete,
                    ))
                } else {
                    Anum::new(refined.lower.to_rational())
                });
            }
        }
        self.sort_roots(&mut roots)?;
        Ok(roots)
    }

    // sort_roots: Z3's stable bottom-up merge sort, since each comparison may refine the roots.
    fn sort_roots(&mut self, roots: &mut [Anum]) -> Result<(), SmtError> {
        let size = roots.len();
        if size < 2 {
            return Ok(());
        }
        let mut source: Vec<usize> = (0..size).collect();
        let mut target = source.clone();
        let mut width = 1;
        while width < size {
            let mut low = 0;
            while low < size {
                let middle = (low + width).min(size);
                let high = (low + 2 * width).min(size);
                let mut left = low;
                let mut right = middle;
                let mut next = low;
                while left < middle && right < high {
                    // isLess(source[right], source[left])
                    let sign = self.compare(&roots[source[right]], &roots[source[left]])?;
                    let is_less = if sign != 0 {
                        sign < 0
                    } else {
                        source[right] < source[left]
                    };
                    if is_less {
                        target[next] = source[right];
                        right += 1;
                    } else {
                        target[next] = source[left];
                        left += 1;
                    }
                    next += 1;
                }
                while left < middle {
                    target[next] = source[left];
                    next += 1;
                    left += 1;
                }
                while right < high {
                    target[next] = source[right];
                    next += 1;
                    right += 1;
                }
                low += 2 * width;
            }
            std::mem::swap(&mut source, &mut target);
            width *= 2;
        }
        let sorted: Vec<Anum> = source.iter().map(|&index| roots[index].clone()).collect();
        roots.clone_from_slice(&sorted);
        Ok(())
    }

    fn get_sign_variations_at_q(&self, sequence: &[Upolynomial], value: &Rational) -> u32 {
        if sequence.len() <= 1 {
            return 0;
        }
        let mut count = 0;
        let mut previous = 0;
        for coeffs in sequence {
            let sign = self.um.eval_sign_at_q(coeffs, value);
            if sign == 0 {
                continue;
            }
            if previous != 0 && sign != previous {
                count += 1;
            }
            previous = sign;
        }
        count
    }

    // isolate_kth_root: the i-th real root of a square-free p, by bisecting with its Sturm
    // sequence.
    fn isolate_kth_root(&mut self, p: &[Int], sequence: &[Upolynomial], root_index: u32) -> Anum {
        if p.len() == 2 {
            return Anum::new(
                Rational::from_int(p[0].clone())
                    .div(&Rational::from_int(p[1].clone()))
                    .neg(),
            );
        }
        let minus_inf = self.um.sign_variations_at_minus_inf(sequence);
        let at_zero = self.um.sign_variations_at_zero(sequence);
        let non_positive_count = minus_inf - at_zero;
        let is_non_positive = root_index <= non_positive_count;
        let mut low = if is_non_positive {
            Mpbq::of(
                -(&Int::one() << u64::from(self.um.knuth_negative_root_upper_bound(p))),
                0,
            )
        } else {
            Mpbq::zero()
        };
        let mut high = if is_non_positive {
            Mpbq::zero()
        } else {
            Mpbq::of(
                &Int::one() << u64::from(self.um.knuth_positive_root_upper_bound(p)),
                0,
            )
        };
        let mut low_variations = if is_non_positive { minus_inf } else { at_zero };
        let mut high_variations = if is_non_positive {
            at_zero
        } else {
            self.um.sign_variations_at_plus_inf(sequence)
        };
        let mut target = if is_non_positive {
            root_index
        } else {
            root_index - non_positive_count
        };
        while low_variations > high_variations + 1 {
            let middle = low.add(&high).div2();
            let middle_variations = self.um.sign_variations_at(sequence, &middle);
            let left_count = low_variations - middle_variations;
            if target <= left_count {
                high = middle;
                high_variations = middle_variations;
            } else {
                low = middle;
                low_variations = middle_variations;
                target -= left_count;
            }
        }
        if self.um.eval_sign_at_bq(p, &high) == 0 {
            return Anum::new(high.to_rational());
        }
        let refined = self.um.isolating2refinable(p, &low, &high);
        if !refined.is_interval {
            return Anum::new(refined.lower.to_rational());
        }
        match self.get_rational_root_in(p, &refined.lower, &refined.upper) {
            RootOrInterval::Root(root) => Anum::new(root),
            RootOrInterval::Interval(interval) => {
                Anum::from_cell(self.mk_cell(p.to_vec(), interval.lower, interval.upper, false))
            }
        }
    }

    // rational_root_in_interval: the root of p in (l, u) when it is rational, else the interval
    // refined below 1/|a_n|.
    fn get_rational_root_in(&self, p: &[Int], lower: &Mpbq, upper: &Mpbq) -> RootOrInterval {
        let abs_leading = p[p.len() - 1].abs();
        let refined =
            self.um
                .refine_to_precision(p, lower, upper, (get_log2(&abs_leading) + 1) as u32);
        if !refined.is_interval {
            return RootOrInterval::Root(refined.lower.to_rational());
        }
        let candidate = Rational::of(
            refined.upper.mul(&Mpbq::of(abs_leading.clone(), 0)).floor(),
            abs_leading,
        );
        if refined.lower.compare_rational(&candidate) < 0
            && self.um.eval_sign_at_q(p, &candidate) == 0
        {
            return RootOrInterval::Root(candidate);
        }
        RootOrInterval::Interval(BqInterval {
            lower: refined.lower,
            upper: refined.upper,
        })
    }

    // isolate_roots_closest_univariate: the roots next to s, s itself when it is a root.
    fn isolate_univariate_closest(
        &mut self,
        pm: &mut PolynomialManager,
        polynomial: &Polynomial,
        sample: &Rational,
    ) -> ClosestAnums {
        let mut result = ClosestAnums {
            roots: Vec::new(),
            indices: Vec::new(),
        };
        if pm.is_const(polynomial) {
            return result;
        }
        let up = pm.to_coeffs(polynomial);
        if up.is_empty() {
            return result;
        }
        let p = self.um.square_free(&up);
        if p.len() <= 1 {
            return result;
        }
        let sequence = self.um.sturm_seq(&p);
        let minus_inf = self.um.sign_variations_at_minus_inf(&sequence);
        let plus_inf = self.um.sign_variations_at_plus_inf(&sequence);
        if minus_inf <= plus_inf {
            return result;
        }
        let total = minus_inf - plus_inf;
        let below = minus_inf - self.get_sign_variations_at_q(&sequence, sample);
        if self.um.eval_sign_at_q(&p, sample) == 0 {
            return ClosestAnums {
                roots: vec![Anum::new(sample.clone())],
                indices: vec![below],
            };
        }
        if below > 0 {
            result
                .roots
                .push(self.isolate_kth_root(&p, &sequence, below));
            result.indices.push(below);
        }
        if below < total {
            result
                .roots
                .push(self.isolate_kth_root(&p, &sequence, below + 1));
            result.indices.push(below + 1);
        }
        result
    }

    // isolate_roots(p, x2v): the roots of p in its one unassigned variable at the values of the
    // others. Resultants eliminate the irrational values, and the roots of the result that are not
    // roots of p are filtered out.
    pub fn isolate_roots(
        &mut self,
        pm: &mut PolynomialManager,
        polynomial: &Polynomial,
        values: &[Option<Anum>],
    ) -> Result<Vec<Anum>, SmtError> {
        self.isolate_roots_core(pm, polynomial, values, false)
    }

    // The nested call passes the manager's own polynomial manager as pm, taken out of self.pm for
    // the call, so is_nested also tells that pm is this.pm.
    fn isolate_roots_core(
        &mut self,
        pm: &mut PolynomialManager,
        polynomial: &Polynomial,
        values: &[Option<Anum>],
        is_nested: bool,
    ) -> Result<Vec<Anum>, SmtError> {
        if pm.is_const(polynomial) {
            return Ok(Vec::new());
        }
        if pm.is_univariate(polynomial) {
            return self.isolate_univariate_roots(&pm.to_coeffs(polynomial));
        }
        let reduced = pm.substitute_rational(polynomial, &get_rational_values(values));
        if pm.is_const(&reduced) {
            return Ok(Vec::new());
        }
        if pm.is_univariate(&reduced) {
            if get_value(values, pm.max_var(&reduced)).is_some() {
                return Ok(Vec::new());
            }
            return self.isolate_univariate_roots(&pm.to_coeffs(&reduced));
        }
        let xs = self.sort_by_degree(&pm.get_vars(&reduced), values);
        let x = xs[xs.len() - 1];
        if get_value(values, x).is_some() {
            return Ok(Vec::new());
        }
        let mut q = reduced.clone();
        for &y in &xs[..xs.len() - 1] {
            let coeffs = get_cell(get_value(values, y))?.p.clone();
            let univariate = pm.from_coeffs(&coeffs, y);
            q = pm.resultant(&q, &univariate, y)?;
            if q.size() == 0 {
                break;
            }
        }
        if q.size() > 0 {
            if pm.is_const(&q) {
                return Ok(Vec::new());
            }
            let roots = self.isolate_univariate_roots(&pm.to_coeffs(&q))?;
            return self.filter_roots(pm, &reduced, values, x, roots, is_nested);
        }
        if is_nested {
            return Err(SmtError::Invariant(
                "resultant vanished during nested isolate_roots call".to_string(),
            ));
        }
        self.isolate_vanished_roots(pm, &reduced, values, &xs, x)
    }

    // t_eval with anumOps at the values.
    fn evaluate_anum(
        &mut self,
        pm: &mut PolynomialManager,
        polynomial: &Polynomial,
        values: &[Option<Anum>],
    ) -> Result<Anum, SmtError> {
        pm.evaluate_with(polynomial, &mut AnumOps { am: self }, &mut |variable| {
            get_assigned(values, variable)
        })
    }

    // The resultant vanished, perhaps at another root of a value's polynomial: p's leading
    // coefficient at the values decides.
    fn isolate_vanished_roots(
        &mut self,
        pm: &mut PolynomialManager,
        reduced: &Polynomial,
        values: &[Option<Anum>],
        xs: &[Var],
        x: Var,
    ) -> Result<Vec<Anum>, SmtError> {
        let degree = pm.degree(reduced, x);
        if degree == 1 {
            let constant_coeff = pm.coeff(reduced, x, 0);
            let constant = self.evaluate_anum(pm, &constant_coeff, values)?;
            let leading_coeff = pm.coeff(reduced, x, 1);
            let leading = self.evaluate_anum(pm, &leading_coeff, values)?;
            if self.is_zero(&leading) {
                return Ok(Vec::new());
            }
            let root = self.div(&constant, &leading)?;
            self.neg(&root);
            return Ok(vec![root]);
        }
        let mut power = degree;
        let mut leading = Anum::new(Rational::zero());
        while power >= 1 {
            let coeff = pm.coeff(reduced, x, power);
            leading = self.evaluate_anum(pm, &coeff, values)?;
            if !self.is_zero(&leading) {
                break;
            }
            power -= 1;
        }
        if power == 0 {
            return Ok(Vec::new());
        }
        // z*x^i + c_{i-1}*x^{i-1} + ... + c_0, with z the value of the leading coefficient.
        let z = xs.iter().copied().fold(NULL_VAR, Var::max) + 1;
        let var_z = self.pm.mk_var(z, 1);
        let var_x = self.pm.mk_var(x, power);
        let product = self.pm.mul(&var_z, &var_x);
        let converted = convert(&mut self.pm, Some(&*pm), reduced, x, Some(power - 1));
        let q = self.pm.add(&product, &converted);
        let extended = get_extended(values, z, &leading);
        let mut local = std::mem::take(&mut self.pm);
        let roots = self.isolate_roots_core(&mut local, &q, &extended, true);
        self.pm = local;
        roots
    }

    // std::stable_sort with var_degree_lt: by the degree of each value, unassigned last.
    fn sort_by_degree(&self, xs: &[Var], values: &[Option<Anum>]) -> Vec<Var> {
        let get_degree =
            |variable: Var| get_value(values, variable).map(|value| self.degree(value));
        let mut sorted = xs.to_vec();
        sorted.sort_by(
            |&first, &second| match (get_degree(first), get_degree(second)) {
                (Some(first), Some(second)) => first.cmp(&second),
                (Some(_), None) => Ordering::Less,
                (None, Some(_)) => Ordering::Greater,
                (None, None) => Ordering::Equal,
            },
        );
        sorted
    }

    // filter_roots: the roots at which p vanishes.
    fn filter_roots(
        &mut self,
        pm: &mut PolynomialManager,
        polynomial: &Polynomial,
        values: &[Option<Anum>],
        x: Var,
        roots: Vec<Anum>,
        is_local_pm: bool,
    ) -> Result<Vec<Anum>, SmtError> {
        let mut filtered = Vec::new();
        for root in roots {
            let extended = get_extended(values, x, &root);
            if self.eval_sign_at_core(pm, polynomial, &extended, is_local_pm)? == 0 {
                filtered.push(root);
            }
        }
        Ok(filtered)
    }

    // isolate_roots_closest: the roots of p next to the rational s, with their indices from 1.
    pub fn isolate_roots_closest(
        &mut self,
        pm: &mut PolynomialManager,
        polynomial: &Polynomial,
        values: &[Option<Anum>],
        sample: &Rational,
    ) -> Result<ClosestAnums, SmtError> {
        let mut result = ClosestAnums {
            roots: Vec::new(),
            indices: Vec::new(),
        };
        if pm.is_const(polynomial) {
            return Ok(result);
        }
        if pm.is_univariate(polynomial) {
            return Ok(self.isolate_univariate_closest(pm, polynomial, sample));
        }
        let reduced = pm.substitute_rational(polynomial, &get_rational_values(values));
        if pm.is_const(&reduced) {
            return Ok(result);
        }
        if pm.is_univariate(&reduced) {
            if get_value(values, pm.max_var(&reduced)).is_some() {
                return Ok(result);
            }
            return Ok(self.isolate_univariate_closest(pm, &reduced, sample));
        }
        let all = self.isolate_roots(pm, polynomial, values)?;
        let sample_anum = Anum::new(sample.clone());
        let mut lower = None;
        let mut upper = None;
        for (index, root) in all.iter().enumerate() {
            if self.compare(root, &sample_anum)? <= 0 {
                lower = Some(index);
            } else {
                upper = Some(index);
                break;
            }
        }
        if let Some(lower) = lower
            && self.compare(&all[lower], &sample_anum)? == 0
        {
            return Ok(ClosestAnums {
                roots: vec![all[lower].clone()],
                indices: vec![lower as u32 + 1],
            });
        }
        if let Some(lower) = lower {
            result.roots.push(all[lower].clone());
            result.indices.push(lower as u32 + 1);
        }
        if let Some(upper) = upper {
            result.roots.push(all[upper].clone());
            result.indices.push(upper as u32 + 1);
        }
        Ok(result)
    }

    // isolate_roots(p, x2v, roots, signs): the roots, and the sign of p below, between and above
    // them, at a sample the unassigned variables share.
    pub fn isolate_roots_with_signs(
        &mut self,
        pm: &mut PolynomialManager,
        polynomial: &Polynomial,
        values: &[Option<Anum>],
    ) -> Result<SignedRoots, SmtError> {
        let roots = self.isolate_roots(pm, polynomial, values)?;
        if roots.is_empty() {
            let zero = Anum::new(Rational::zero());
            let sign = self.get_sign_at_sample(pm, polynomial, values, &zero)?;
            return Ok(SignedRoots {
                roots,
                signs: vec![sign],
            });
        }
        for root in &roots {
            self.refine_until_precision(root, SIGN_PRECISION);
        }
        let below = self.int_lt(&roots[0]);
        let mut signs = vec![self.get_sign_at_sample(pm, polynomial, values, &below)?];
        for index in 1..roots.len() {
            let between = self.select(&roots[index - 1], &roots[index]);
            signs.push(self.get_sign_at_sample(pm, polynomial, values, &between)?);
        }
        let above = self.int_gt(&roots[roots.len() - 1]);
        signs.push(self.get_sign_at_sample(pm, polynomial, values, &above)?);
        Ok(SignedRoots { roots, signs })
    }

    // getSign of isolate_roots with signs: p's sign with every unassigned variable at sample.
    fn get_sign_at_sample(
        &mut self,
        pm: &mut PolynomialManager,
        polynomial: &Polynomial,
        values: &[Option<Anum>],
        sample: &Anum,
    ) -> Result<i32, SmtError> {
        let mut extended = values.to_vec();
        for variable in pm.get_vars(polynomial) {
            if get_value(&extended, variable).is_none() {
                set_value(&mut extended, variable, sample);
            }
        }
        self.eval_sign_at(pm, polynomial, &extended)
    }

    // Signs.

    // eval_sign_at: the sign of p at the values. Rational values are substituted, interval
    // arithmetic on the irrational ones decides most signs, and otherwise a lower bound on the
    // nonzero roots of the resultant with their polynomials tells zero apart.
    pub fn eval_sign_at(
        &mut self,
        pm: &mut PolynomialManager,
        polynomial: &Polynomial,
        values: &[Option<Anum>],
    ) -> Result<i32, SmtError> {
        self.eval_sign_at_core(pm, polynomial, values, false)
    }

    // is_local_pm: pm is this.pm, taken out of self.pm by a nested isolate_roots.
    fn eval_sign_at_core(
        &mut self,
        pm: &mut PolynomialManager,
        polynomial: &Polynomial,
        values: &[Option<Anum>],
        is_local_pm: bool,
    ) -> Result<i32, SmtError> {
        loop {
            let rational_values = get_rational_values(values);
            if pm.get_vars(polynomial).iter().all(|&variable| {
                usize::try_from(variable)
                    .ok()
                    .and_then(|index| rational_values.get(index))
                    .is_some_and(Option::is_some)
            }) {
                return pm.get_sign(polynomial, &rational_values);
            }
            let reduced = pm.substitute_rational(polynomial, &rational_values);
            if reduced.size() == 0 {
                return Ok(0);
            }
            if pm.is_const(&reduced) {
                return Ok(if reduced.coeff_at(0).is_positive() {
                    1
                } else {
                    -1
                });
            }
            let xs = pm.get_vars(&reduced);
            let mut interval = evaluate_interval(pm, &reduced, values)?;
            let mut is_restarted = false;
            loop {
                if !contains_zero(&interval) {
                    return Ok(if interval.lower.is_neg() { -1 } else { 1 });
                }
                let mut is_refined = false;
                for &variable in &xs {
                    let value = get_assigned(values, variable)?;
                    let magnitude = self.get_cell_magnitude(&*get_cell(Some(&value))?);
                    if magnitude <= MIN_MAGNITUDE {
                        continue;
                    }
                    if !self.refine(&value) {
                        is_restarted = true;
                        break;
                    }
                    is_refined = true;
                }
                if !is_refined || is_restarted {
                    break;
                }
                interval = evaluate_interval(pm, &reduced, values)?;
            }
            if is_restarted {
                continue;
            }
            let sign =
                self.eval_sign_by_resultant(pm, &reduced, values, &xs, &interval, is_local_pm)?;
            if let Some(sign) = sign {
                return Ok(sign);
            }
        }
    }

    // The resultant step of eval_sign_at, or None when a value turned rational and it restarts.
    fn eval_sign_by_resultant(
        &mut self,
        pm: &mut PolynomialManager,
        reduced: &Polynomial,
        values: &[Option<Anum>],
        xs: &[Var],
        initial: &BqInterval,
        is_local_pm: bool,
    ) -> Result<Option<i32>, SmtError> {
        let sorted = self.sort_by_degree(xs, values);
        let k = {
            let (local, source) = if is_local_pm {
                (&mut *pm, None)
            } else {
                (&mut self.pm, Some(&*pm))
            };
            let var = local.mk_var(xs.iter().copied().fold(NULL_VAR, Var::max) + 1, 1);
            let converted = convert(local, source, reduced, NULL_VAR, None);
            let mut resultant = local.sub(&var, &converted);
            for &variable in &sorted {
                let coeffs = get_cell(get_value(values, variable))?.p.clone();
                let univariate = local.from_coeffs(&coeffs, variable);
                resultant = local.resultant(&resultant, &univariate, variable)?;
            }
            self.um
                .nonzero_root_lower_bound(&local.to_coeffs(&resultant))
        };
        let bound = Mpbq::of(Int::one(), k);
        let is_inside_bound = |interval: &BqInterval| {
            bound.neg().compare(&interval.lower) < 0 && interval.upper.compare(&bound) < 0
        };
        if is_inside_bound(initial) {
            return Ok(Some(0));
        }
        let mut saved = Vec::new();
        for &variable in &sorted {
            saved.push(self.save_interval(&get_assigned(values, variable)?)?);
        }
        let mut sign = None;
        while sign.is_none() {
            let interval = evaluate_interval(pm, reduced, values)?;
            if !contains_zero(&interval) {
                sign = Some(if interval.lower.is_neg() { -1 } else { 1 });
            } else if is_inside_bound(&interval) {
                sign = Some(0);
            } else {
                let mut is_every_refined = true;
                for &variable in &sorted {
                    if !self.refine(&get_assigned(values, variable)?) {
                        is_every_refined = false;
                        break;
                    }
                }
                if !is_every_refined {
                    break;
                }
            }
        }
        for entry in &mut saved {
            self.release_interval(entry);
        }
        Ok(sign)
    }

    // Arithmetic.

    pub fn add(&mut self, first: &Anum, second: &Anum) -> Result<Anum, SmtError> {
        if self.is_zero(first) {
            return Ok(self.copy(second));
        }
        if self.is_zero(second) {
            return Ok(self.copy(first));
        }
        {
            let first_value = first.value();
            let second_value = second.value();
            match (&*first_value, &*second_value) {
                (AnumValue::Rational(first), AnumValue::Rational(second)) => {
                    return Ok(Anum::new(first.add(second)));
                }
                (AnumValue::Rational(first), AnumValue::Cell(second)) => {
                    return Ok(self.add_rational(second, first));
                }
                (AnumValue::Cell(first), AnumValue::Rational(second)) => {
                    return Ok(self.add_rational(first, second));
                }
                (AnumValue::Cell(_), AnumValue::Cell(_)) => {}
            }
        }
        self.mk_binary(first, second, true)
    }

    // add(cell, basic): p(x - b), with the interval shifted by b.
    fn add_rational(&mut self, cell: &AlgebraicCell, value: &Rational) -> Anum {
        let p = self.um.translate_q(&cell.p, &value.neg());
        let (shift, is_exact) = Mpbq::from_rational(value);
        let (lower, upper) = if is_exact {
            (cell.lower.add(&shift), cell.upper.add(&shift))
        } else {
            let interval = self.um.convert_q2bq_interval(
                &p,
                &cell.lower.to_rational().add(value),
                &cell.upper.to_rational().add(value),
            );
            (interval.lower, interval.upper)
        };
        let result = self.mk_anum(p, lower, upper, cell.is_minimal);
        self.normalize(&result);
        result
    }

    pub fn mul(&mut self, first: &Anum, second: &Anum) -> Result<Anum, SmtError> {
        if self.is_zero(first) || self.is_zero(second) {
            return Ok(Anum::new(Rational::zero()));
        }
        {
            let first_value = first.value();
            let second_value = second.value();
            match (&*first_value, &*second_value) {
                (AnumValue::Rational(first), AnumValue::Rational(second)) => {
                    return Ok(Anum::new(first.mul(second)));
                }
                (AnumValue::Rational(first), AnumValue::Cell(second)) => {
                    return Ok(self.mul_rational(second, first));
                }
                (AnumValue::Cell(first), AnumValue::Rational(second)) => {
                    return Ok(self.mul_rational(first, second));
                }
                (AnumValue::Cell(_), AnumValue::Cell(_)) => {}
            }
        }
        self.mk_binary(first, second, false)
    }

    // mul(cell, basic): b^n * p(x/b), with the interval scaled by b.
    fn mul_rational(&mut self, cell: &AlgebraicCell, value: &Rational) -> Anum {
        let p = self.um.compose_p_q_x(&cell.p, &Rational::one().div(value));
        let (scale, is_exact) = Mpbq::from_rational(value);
        let is_negative = value.is_negative();
        let (lower, upper) = if is_exact {
            let upper = cell.upper.mul(&scale);
            let lower = cell.lower.mul_into_other(&scale);
            if is_negative {
                (upper, lower)
            } else {
                (lower, upper)
            }
        } else {
            let rational_lower = cell.lower.to_rational().mul(value);
            let rational_upper = cell.upper.to_rational().mul(value);
            let (rational_lower, rational_upper) = if is_negative {
                (rational_upper, rational_lower)
            } else {
                (rational_lower, rational_upper)
            };
            let interval = self
                .um
                .convert_q2bq_interval(&p, &rational_lower, &rational_upper);
            (interval.lower, interval.upper)
        };
        let result = self.mk_anum(p, lower, upper, cell.is_minimal);
        self.normalize(&result);
        result
    }

    // neg: p(-x) with the interval mirrored, in place.
    pub fn neg(&mut self, anum: &Anum) {
        let mut value = anum.value_mut();
        match &mut *value {
            AnumValue::Rational(rational) => *rational = rational.neg(),
            AnumValue::Cell(cell) => {
                cell.p = self.um.p_minus_x(&cell.p);
                (cell.lower, cell.upper) = (cell.upper.neg(), cell.lower.neg());
                if cell.root_index != 0 {
                    cell.root_index = self.um.get_root_id(&cell.p, &cell.lower) + 1;
                }
                self.update_sign_lower(cell);
            }
        }
    }

    // refine_nz_bound: moves an interval end off zero, halving it until its sign is right.
    fn refine_nonzero_bound(&mut self, anum: &Anum) {
        let mut value = anum.value_mut();
        let AnumValue::Cell(cell) = &mut *value else {
            return;
        };
        if !cell.lower.is_zero() && !cell.upper.is_zero() {
            return;
        }
        let is_lower = cell.lower.is_zero();
        let target_sign = if is_lower {
            cell.sign_lower()
        } else {
            -cell.sign_lower()
        };
        let mut bound = if is_lower {
            cell.upper.clone()
        } else {
            cell.lower.clone()
        };
        loop {
            bound = bound.div2();
            if is_lower {
                cell.lower = bound.clone();
            } else {
                cell.upper = bound.clone();
            }
            let sign = self.um.eval_sign_at_bq(&cell.p, &bound);
            if sign == 0 {
                *value = AnumValue::Rational(bound.to_rational());
                return;
            }
            if sign == target_sign {
                return;
            }
        }
    }

    // inv: x^n * p(1/x), with the interval (1/u, 1/l), in place.
    pub fn inv(&mut self, anum: &Anum) -> Result<(), SmtError> {
        if self.is_zero(anum) {
            return Err(SmtError::Invariant("division by zero".to_string()));
        }
        self.refine_nonzero_bound(anum);
        let mut value = anum.value_mut();
        let cell = match &mut *value {
            AnumValue::Rational(rational) => {
                *rational = Rational::one().div(rational);
                return Ok(());
            }
            AnumValue::Cell(cell) => cell,
        };
        cell.p = self.um.p1_div_x(&cell.p);
        let interval = self.um.convert_q2bq_interval(
            &cell.p,
            &Rational::one().div(&cell.upper.to_rational()),
            &Rational::one().div(&cell.lower.to_rational()),
        );
        if !interval.is_interval {
            return Err(SmtError::Invariant(
                "inversion of algebraic number failed".to_string(),
            ));
        }
        cell.lower = interval.lower;
        cell.upper = interval.upper;
        self.update_sign_lower(cell);
        Ok(())
    }

    pub fn div(&mut self, first: &Anum, second: &Anum) -> Result<Anum, SmtError> {
        if self.is_zero(second) {
            return Err(SmtError::Invariant("division by zero".to_string()));
        }
        let inverse = self.copy(second);
        self.inv(&inverse)?;
        self.mul(first, &inverse)
    }

    pub fn power(&mut self, anum: &Anum, exponent: u32) -> Result<Anum, SmtError> {
        if exponent == 0 {
            if self.is_zero(anum) {
                return Err(SmtError::Invariant("0^0 is indeterminate".to_string()));
            }
            return Ok(Anum::new(Rational::one()));
        }
        if exponent == 1 {
            return Ok(self.copy(anum));
        }
        if let Some(value) = anum.rational() {
            return Ok(Anum::new(value.pow(exponent)));
        }
        self.mk_power(anum, exponent)
    }

    // mk_add_polynomial: Res_y(pa(x - y), pb(y)), which has a + b as a root.
    fn get_sum_polynomial(
        &mut self,
        first: &AlgebraicCell,
        second: &AlgebraicCell,
    ) -> Result<Upolynomial, SmtError> {
        let pa_x = self.pm.from_coeffs(&first.p, X);
        let pa = self.pm.compose_x_minus_y(&pa_x, Y);
        let pb = self.pm.from_coeffs(&second.p, Y);
        let resultant = self.pm.resultant(&pa, &pb, Y)?;
        Ok(self.pm.to_coeffs(&resultant))
    }

    // mk_mul_polynomial: Res_y(y^n * pa(x/y), pb(y)), which has a*b as a root.
    fn get_product_polynomial(
        &mut self,
        first: &AlgebraicCell,
        second: &AlgebraicCell,
    ) -> Result<Upolynomial, SmtError> {
        let pa_x = self.pm.from_coeffs(&first.p, X);
        let pa = self.pm.compose_x_div_y(&pa_x, Y);
        let pb = self.pm.from_coeffs(&second.p, Y);
        let resultant = self.pm.resultant(&pa, &pb, Y)?;
        Ok(self.pm.to_coeffs(&resultant))
    }

    // The factors of p whose Sturm sequence counts exactly one root in an interval, until only one
    // factor is left.
    fn find_isolating_factor(
        &self,
        factors: &[Upolynomial],
        sequences: &mut [Option<Vec<Upolynomial>>],
        interval: &BqInterval,
    ) -> Option<IsolatingFactor> {
        let mut remaining = 0;
        let mut target = None;
        let mut target_lower_variations = 0;
        for (index, slot) in sequences.iter_mut().enumerate() {
            let Some(sequence) = slot.as_ref() else {
                continue;
            };
            let lower_variations = i64::from(self.um.sign_variations_at(sequence, &interval.lower));
            let count =
                lower_variations - i64::from(self.um.sign_variations_at(sequence, &interval.upper));
            if count <= 0 {
                *slot = None;
                continue;
            }
            if count == 1 {
                target = Some(index);
                target_lower_variations = lower_variations;
            }
            remaining += 1;
        }
        if remaining != 1 {
            return None;
        }
        let target = target?;
        Some(IsolatingFactor {
            factor: factors[target].clone(),
            sequence: sequences[target].clone()?,
            lower_variations: target_lower_variations,
        })
    }

    // mk_binary: a + b or a*b for irrational a and b, refining both until the interval of the
    // result isolates a root of one factor of the resultant.
    fn mk_binary(&mut self, first: &Anum, second: &Anum, is_add: bool) -> Result<Anum, SmtError> {
        let polynomial = {
            let cell_a = get_cell(Some(first))?;
            let cell_b = get_cell(Some(second))?;
            if is_add {
                self.get_sum_polynomial(&cell_a, &cell_b)?
            } else {
                self.get_product_polynomial(&cell_a, &cell_b)?
            }
        };
        let (is_complete, factored) = self.factor(&polynomial)?;
        let factors = factored.factors;
        let mut sequences: Vec<Option<Vec<Upolynomial>>> = factors
            .iter()
            .map(|factor| Some(self.um.sturm_seq(factor)))
            .collect();
        let mut saved_a = self.save_interval(first)?;
        let mut saved_b = self.save_interval(second)?;
        loop {
            let interval = {
                // Both cells are read after both refinements, so a + a sees its one interval.
                let cell_a = get_cell(Some(first))?;
                let cell_b = get_cell(Some(second))?;
                debug_assert!(!Anum::ptr_eq(first, second) || cell_a.lower == cell_b.lower);
                if is_add {
                    add_intervals(&get_interval(&cell_a), &get_interval(&cell_b))
                } else {
                    mul_intervals(&get_interval(&cell_a), &get_interval(&cell_b))
                }
            };
            if let Some(found) = self.find_isolating_factor(&factors, &mut sequences, &interval) {
                self.restore_if_too_small(&mut saved_a);
                self.restore_if_too_small(&mut saved_b);
                return Ok(self.set_core(&found, &interval, is_complete));
            }
            if !self.refine(first) || !self.refine(second) {
                // Z3 restores a twice here, and b only once the operation is done.
                self.restore_if_too_small(&mut saved_a);
                self.restore_if_too_small(&mut saved_a);
                let result = if is_add {
                    self.add(first, second)?
                } else {
                    self.mul(first, second)?
                };
                self.release_interval(&mut saved_b);
                return Ok(result);
            }
        }
    }

    // mk_power_polynomial: Res_y(x - y^k, pa(y)), which has a^k as a root.
    fn get_power_polynomial(
        &mut self,
        cell: &AlgebraicCell,
        exponent: u32,
    ) -> Result<Upolynomial, SmtError> {
        let var_x = self.pm.mk_var(X, 1);
        let var_y = self.pm.mk_var(Y, exponent);
        let x = self.pm.sub(&var_x, &var_y);
        let pa = self.pm.from_coeffs(&cell.p, Y);
        let resultant = self.pm.resultant(&x, &pa, Y)?;
        Ok(self.pm.to_coeffs(&resultant))
    }

    // mk_unary with mk_power_polynomial: a^k for an irrational a.
    fn mk_power(&mut self, anum: &Anum, exponent: u32) -> Result<Anum, SmtError> {
        let polynomial = {
            let cell = get_cell(Some(anum))?;
            self.get_power_polynomial(&cell, exponent)?
        };
        let (is_complete, factored) = self.factor(&polynomial)?;
        let factors = factored.factors;
        let mut sequences: Vec<Option<Vec<Upolynomial>>> = factors
            .iter()
            .map(|factor| Some(self.um.sturm_seq(factor)))
            .collect();
        let mut saved = self.save_interval(anum)?;
        loop {
            let interval = get_interval_power(&get_interval(&*get_cell(Some(anum))?), exponent);
            if let Some(found) = self.find_isolating_factor(&factors, &mut sequences, &interval) {
                self.restore_if_too_small(&mut saved);
                return Ok(self.set_core(&found, &interval, is_complete));
            }
            if !self.refine(anum) {
                self.restore_if_too_small(&mut saved);
                return self.power(anum, exponent);
            }
        }
    }

    // set_core: the root of p in an isolating interval that may contain zero.
    fn set_core(
        &mut self,
        found: &IsolatingFactor,
        interval: &BqInterval,
        is_minimal: bool,
    ) -> Anum {
        let p = &found.factor;
        let mut lower = interval.lower.clone();
        let mut upper = interval.upper.clone();
        if contains_zero(interval) {
            if self.um.has_zero_roots(p) {
                return Anum::new(Rational::zero());
            }
            if found.lower_variations == i64::from(self.um.sign_variations_at_zero(&found.sequence))
            {
                lower = Mpbq::zero();
            } else {
                upper = Mpbq::zero();
            }
        }
        let nonzero = if self.um.has_zero_roots(p) {
            self.um.remove_zero_roots(p)
        } else {
            p.clone()
        };
        let refined = self.um.isolating2refinable(&nonzero, &lower, &upper);
        if !refined.is_interval {
            return Anum::new(refined.lower.to_rational());
        }
        self.mk_anum(nonzero, refined.lower, refined.upper, is_minimal)
    }

    // Comparison.

    // compare(cell, b): by the interval, or by the sign of p at b.
    fn compare_rational(&self, cell: &AlgebraicCell, value: &Rational) -> i32 {
        if cell.upper.compare_rational(value) <= 0 {
            return -1;
        }
        if cell.lower.compare_rational(value) >= 0 {
            return 1;
        }
        let sign = self.um.eval_sign_at_q(&cell.p, value);
        if sign == 0 {
            return 0;
        }
        if sign == cell.sign_lower() { 1 } else { -1 }
    }

    pub fn compare(&mut self, first: &Anum, second: &Anum) -> Result<i32, SmtError> {
        {
            let first_value = first.value();
            let second_value = second.value();
            match (&*first_value, &*second_value) {
                (AnumValue::Rational(first), AnumValue::Rational(second)) => {
                    return Ok(first.compare(second) as i32);
                }
                (AnumValue::Rational(first), AnumValue::Cell(second)) => {
                    return Ok(-self.compare_rational(second, first));
                }
                (AnumValue::Cell(first), AnumValue::Rational(second)) => {
                    return Ok(self.compare_rational(first, second));
                }
                (AnumValue::Cell(_), AnumValue::Cell(_)) => {}
            }
        }
        self.compare_core(first, second)
    }

    // compare_core: refines both intervals to a common magnitude, then tries a wider separation,
    // and last the sign of pb at a by a Sturm-Tarski sequence.
    fn compare_core(&mut self, first: &Anum, second: &Anum) -> Result<i32, SmtError> {
        let mut cell_a = get_cell(Some(first))?.clone();
        let mut cell_b = get_cell(Some(second))?.clone();
        let compare_intervals = |cell_a: &AlgebraicCell, cell_b: &AlgebraicCell| {
            if cell_a.upper.compare(&cell_b.lower) <= 0 {
                -1
            } else if cell_a.lower.compare(&cell_b.upper) >= 0 {
                1
            } else {
                0
            }
        };
        let mut sign = compare_intervals(&cell_a, &cell_b);
        if sign != 0 {
            return Ok(sign);
        }
        if cell_a.p == cell_b.p {
            return Ok(0);
        }
        // The same number has the same polynomial, so the two are distinct from here on.
        debug_assert!(!Anum::ptr_eq(first, second));
        if cell_a.is_minimal && cell_b.is_minimal {
            loop {
                self.refine(first);
                update_detached_cell(first, &mut cell_a);
                self.refine(second);
                update_detached_cell(second, &mut cell_b);
                sign = compare_intervals(&cell_a, &cell_b);
                if sign != 0 {
                    return Ok(sign);
                }
            }
        }
        let magnitude_a = self.get_cell_magnitude(&cell_a);
        let magnitude_b = self.get_cell_magnitude(&cell_b);
        let target = MIN_MAGNITUDE.max(magnitude_a.min(magnitude_b));
        if magnitude_b > target {
            if !self.refine_times(second, magnitude_b - target) {
                return self.compare(first, second);
            }
            update_detached_cell(second, &mut cell_b);
            sign = compare_intervals(&cell_a, &cell_b);
            if sign != 0 {
                return Ok(sign);
            }
        }
        if magnitude_a > target {
            if !self.refine_times(first, magnitude_a - target) {
                return self.compare(first, second);
            }
            update_detached_cell(first, &mut cell_a);
            sign = compare_intervals(&cell_a, &cell_b);
            if sign != 0 {
                return Ok(sign);
            }
        }
        for _ in 0..target - MIN_MAGNITUDE {
            if !self.refine(first) || !self.refine(second) {
                return self.compare(first, second);
            }
            update_detached_cell(first, &mut cell_a);
            update_detached_cell(second, &mut cell_b);
            sign = compare_intervals(&cell_a, &cell_b);
            if sign != 0 {
                return Ok(sign);
            }
        }
        // get_interval at precision 10: copies of the intervals refined below 1/2^40.
        let interval_a = self
            .um
            .refine_to_precision(&cell_a.p, &cell_a.lower, &cell_a.upper, 40);
        let interval_b = self
            .um
            .refine_to_precision(&cell_b.p, &cell_b.lower, &cell_b.upper, 40);
        if interval_a.is_interval && interval_b.is_interval {
            if interval_a.lower.compare(&interval_b.upper) > 0 {
                return Ok(1);
            }
            if interval_a.upper.compare(&interval_b.lower) < 0 {
                return Ok(-1);
            }
        }
        if self.compare_rational(&cell_a, &interval_b.lower.to_rational()) < 0 {
            return Ok(-1);
        }
        if self.compare_rational(&cell_a, &interval_b.upper.to_rational()) > 0 {
            return Ok(1);
        }
        if self.compare_rational(&cell_b, &interval_a.lower.to_rational()) < 0 {
            return Ok(1);
        }
        if self.compare_rational(&cell_b, &interval_a.upper.to_rational()) > 0 {
            return Ok(-1);
        }
        let sequence = self.um.sturm_tarski_seq(&cell_a.p, &cell_b.p);
        let variations = i64::from(self.um.sign_variations_at(&sequence, &cell_a.lower))
            - i64::from(self.um.sign_variations_at(&sequence, &cell_a.upper));
        if variations == 0 {
            return Ok(0);
        }
        Ok(if (variations < 0) == (cell_b.sign_lower() < 0) {
            -1
        } else {
            1
        })
    }

    // Sample points.

    // int_lt: an integer below a.
    pub fn int_lt(&mut self, anum: &Anum) -> Anum {
        self.refine_until_precision(anum, 1);
        let integer = match &*anum.value() {
            AnumValue::Rational(value) => value.floor().num() - &Int::one(),
            AnumValue::Cell(cell) => cell.lower.floor(),
        };
        Anum::new(Rational::from_int(integer))
    }

    // int_gt: an integer above a.
    pub fn int_gt(&mut self, anum: &Anum) -> Anum {
        self.refine_until_precision(anum, 1);
        let integer = match &*anum.value() {
            AnumValue::Rational(value) => value.ceil().num() + &Int::one(),
            AnumValue::Cell(cell) => cell.upper.ceil(),
        };
        Anum::new(Rational::from_int(integer))
    }

    // separate: refines until the intervals of prev and curr do not touch.
    fn separate(&mut self, previous: &Anum, current: &Anum) {
        // prev < curr: the same number would never separate from itself.
        debug_assert!(!Anum::ptr_eq(previous, current));
        if let Some(value) = previous.rational() {
            while current
                .cell()
                .is_some_and(|cell| cell.lower.compare_rational(&value) <= 0)
            {
                self.refine(current);
            }
            return;
        }
        if let Some(value) = current.rational() {
            while previous
                .cell()
                .is_some_and(|cell| cell.upper.compare_rational(&value) >= 0)
            {
                self.refine(previous);
            }
            return;
        }
        while match (&*previous.value(), &*current.value()) {
            (AnumValue::Cell(previous), AnumValue::Cell(current)) => {
                previous.upper.compare(&current.lower) >= 0
            }
            _ => false,
        } {
            self.refine(previous);
            self.refine(current);
        }
    }

    // select: a binary rational between prev < curr with the smallest denominator.
    pub fn select(&mut self, previous: &Anum, current: &Anum) -> Anum {
        self.separate(previous, current);
        let lower = match &*previous.value() {
            AnumValue::Rational(value) => SelectEnd {
                value: value.clone(),
                is_open: true,
            },
            AnumValue::Cell(cell) => SelectEnd {
                value: cell.upper.to_rational(),
                is_open: false,
            },
        };
        let upper = match &*current.value() {
            AnumValue::Rational(value) => SelectEnd {
                value: value.clone(),
                is_open: true,
            },
            AnumValue::Cell(cell) => SelectEnd {
                value: cell.lower.to_rational(),
                is_open: false,
            },
        };
        Anum::new(select_small(&lower, &upper).to_rational())
    }
}

// t_eval with INTERVAL_OPS: p's interval at the values' isolating intervals.
fn evaluate_interval(
    pm: &mut PolynomialManager,
    reduced: &Polynomial,
    values: &[Option<Anum>],
) -> Result<BqInterval, SmtError> {
    pm.evaluate_with(reduced, &mut IntervalOps, &mut |variable| {
        Ok(get_interval(&*get_cell(get_value(values, variable))?))
    })
}

#[cfg(test)]
mod tests {
    use super::super::Rational;
    use super::super::polynomial::PolynomialManager;
    use super::super::test_util::{parse_polynomial, parse_rational, read_fixture, show_anum};
    use super::{AlgebraicManager, Anum, AnumValue};

    // The harness commands: select a b, and closest x s n v0 ... v(n-1) poly, which leaves x
    // unassigned.
    fn run_algebraic_command(input: &str) -> String {
        let words: Vec<&str> = input.split(' ').collect();
        let mut am = AlgebraicManager::new();
        if words[0] == "select" {
            let selected = am.select(
                &Anum::new(parse_rational(words[1])),
                &Anum::new(parse_rational(words[2])),
            );
            return format!("select {}", show_value(&selected));
        }
        let variable: usize = words[1].parse().expect("a variable");
        let count: usize = words[3].parse().expect("a count");
        let sample: Vec<Option<Anum>> = words[4..4 + count]
            .iter()
            .enumerate()
            .map(|(index, word)| (index != variable).then(|| Anum::new(parse_rational(word))))
            .collect();
        let mut pm = PolynomialManager::new();
        let polynomial = parse_polynomial(&mut pm, &words[4 + count..].join(" "));
        let closest = am
            .isolate_roots_closest(&mut pm, &polynomial, &sample, &parse_rational(words[2]))
            .expect("isolate_roots_closest");
        let shown: Vec<String> = closest
            .roots
            .iter()
            .enumerate()
            .map(|(index, root)| format!(" {}@{}", closest.indices[index], show_value(root)))
            .collect();
        format!("closest{}", shown.concat())
    }

    // `${anum.value}` for a rational, "irrational" otherwise.
    fn show_value(anum: &Anum) -> String {
        match &*anum.value() {
            AnumValue::Rational(value) => value.to_string(),
            AnumValue::Cell(_) => "irrational".to_string(),
        }
    }

    // getRegister: the register, after filling the registers up to it with zeros.
    fn get_register(registers: &mut Vec<Option<Anum>>, index: usize) -> Anum {
        while registers.len() <= index {
            registers.push(Some(Anum::new(Rational::zero())));
        }
        registers[index].clone().expect("a register that was set")
    }

    // registers[index] = anum, leaving holes below it as JavaScript does.
    fn set_register(registers: &mut Vec<Option<Anum>>, index: usize, anum: Anum) {
        if registers.len() <= index {
            registers.resize(index + 1, None);
        }
        registers[index] = Some(anum);
    }

    fn show_flag(is_true: bool) -> String {
        format!(" {}", u8::from(is_true))
    }

    fn run_command(
        am: &mut AlgebraicManager,
        pm: &mut PolynomialManager,
        registers: &mut Vec<Option<Anum>>,
        words: &[&str],
    ) -> String {
        let numbers: Vec<Option<usize>> = words
            .iter()
            .skip(1)
            .take(3)
            .map(|word| word.parse().ok())
            .collect();
        let number = |index: usize| numbers[index].expect("a number");
        match words[0] {
            "q" => {
                set_register(registers, number(0), Anum::new(parse_rational(words[2])));
                let anum = get_register(registers, number(0));
                show_anum(am, &anum)
            }
            "root" => {
                let coeffs: Vec<_> = words[3..]
                    .iter()
                    .map(|word| word.parse().expect("an integer"))
                    .collect();
                let polynomial = pm.from_coeffs(&coeffs, 0);
                let roots = am
                    .isolate_roots(pm, &polynomial, &[])
                    .expect("isolate_roots");
                if number(1) > roots.len() {
                    return " error".to_string();
                }
                get_register(registers, number(0));
                set_register(registers, number(0), roots[number(1) - 1].clone());
                let anum = get_register(registers, number(0));
                show_anum(am, &anum)
            }
            "add" | "mul" | "div" | "sel" => {
                let first = get_register(registers, number(1));
                let second = get_register(registers, number(2));
                if words[0] == "div" && am.is_zero(&second) {
                    return " error".to_string();
                }
                let result = match words[0] {
                    "add" => am.add(&first, &second).expect("add"),
                    "mul" => am.mul(&first, &second).expect("mul"),
                    "div" => am.div(&first, &second).expect("div"),
                    _ => am.select(&first, &second),
                };
                get_register(registers, number(0));
                set_register(registers, number(0), am.copy(&result));
                let anum = get_register(registers, number(0));
                show_anum(am, &anum)
            }
            "pow" | "intlt" | "intgt" => {
                let anum = get_register(registers, number(1));
                let result = match words[0] {
                    "pow" => am
                        .power(&anum, u32::try_from(number(2)).expect("an exponent"))
                        .expect("power"),
                    "intlt" => am.int_lt(&anum),
                    _ => am.int_gt(&anum),
                };
                get_register(registers, number(0));
                set_register(registers, number(0), am.copy(&result));
                let anum = get_register(registers, number(0));
                show_anum(am, &anum)
            }
            "neg" => {
                let anum = get_register(registers, number(0));
                am.neg(&anum);
                show_anum(am, &anum)
            }
            "inv" => {
                let anum = get_register(registers, number(0));
                if am.is_zero(&anum) {
                    return " error".to_string();
                }
                am.inv(&anum).expect("inv");
                show_anum(am, &anum)
            }
            "cmp" => {
                let first = get_register(registers, number(0));
                let second = get_register(registers, number(1));
                let sign = am.compare(&first, &second).expect("compare");
                format!(" {sign}{}{}", show_anum(am, &first), show_anum(am, &second))
            }
            "isint" | "israt" => {
                let anum = get_register(registers, number(0));
                let flag = if words[0] == "isint" {
                    am.is_int(&anum)
                } else {
                    am.is_rational(&anum).expect("is_rational")
                };
                format!("{}{}", show_flag(flag), show_anum(am, &anum))
            }
            "show" => {
                let anum = get_register(registers, number(0));
                show_anum(am, &anum)
            }
            _ => run_values_command(am, pm, registers, words),
        }
    }

    // sign, iso, closest and isosig: a polynomial and the registers its variables take.
    fn run_values_command(
        am: &mut AlgebraicManager,
        pm: &mut PolynomialManager,
        registers: &mut Vec<Option<Anum>>,
        words: &[&str],
    ) -> String {
        let rest = if words[0] == "closest" {
            &words[2..]
        } else {
            &words[1..]
        };
        let separator = rest
            .iter()
            .position(|word| *word == ";")
            .expect("a separator");
        let polynomial = parse_polynomial(pm, &rest[..separator].join(" "));
        let bindings: Vec<(usize, usize)> = rest[separator + 1..]
            .iter()
            .map(|word| {
                let (variable, register) = word.split_once('=').expect("var=register");
                (
                    variable.parse().expect("a variable"),
                    register.parse().expect("a register"),
                )
            })
            .collect();
        let mut values: Vec<Option<Anum>> = Vec::new();
        for binding in &bindings {
            let copy = am.copy(&get_register(registers, binding.1));
            if values.len() <= binding.0 {
                values.resize(binding.0 + 1, None);
            }
            values[binding.0] = Some(copy);
        }
        let (mut output, roots) = if words[0] == "sign" {
            let sign = am
                .eval_sign_at(pm, &polynomial, &values)
                .expect("eval_sign_at");
            (format!(" {sign}"), Vec::new())
        } else if words[0] == "iso" {
            let roots = am
                .isolate_roots(pm, &polynomial, &values)
                .expect("isolate_roots");
            let shown: Vec<String> = roots.iter().map(|anum| show_anum(am, anum)).collect();
            (format!(" roots{}", shown.concat()), roots)
        } else if words[0] == "closest" {
            let closest = am
                .isolate_roots_closest(pm, &polynomial, &values, &parse_rational(words[1]))
                .expect("isolate_roots_closest");
            let shown: Vec<String> = closest
                .roots
                .iter()
                .map(|anum| show_anum(am, anum))
                .collect();
            let indices: Vec<String> = closest
                .indices
                .iter()
                .map(|index| format!(" {index}"))
                .collect();
            let output = format!(" roots{} idx{}", shown.concat(), indices.concat());
            (output, closest.roots)
        } else {
            let signed = am
                .isolate_roots_with_signs(pm, &polynomial, &values)
                .expect("isolate_roots_with_signs");
            let shown: Vec<String> = signed
                .roots
                .iter()
                .map(|anum| show_anum(am, anum))
                .collect();
            let signs: Vec<String> = signed.signs.iter().map(|sign| format!(" {sign}")).collect();
            let output = format!(" roots{} signs{}", shown.concat(), signs.concat());
            (output, signed.roots)
        };
        // The roots go to registers 8 and up, for later commands.
        for (index, root) in roots.iter().enumerate() {
            get_register(registers, 8 + index);
            set_register(registers, 8 + index, am.copy(root));
        }
        output += " after";
        for binding in &bindings {
            let value = values[binding.0].clone().expect("a bound value");
            set_register(registers, binding.1, am.copy(&value));
            let anum = get_register(registers, binding.1);
            output += &show_anum(am, &anum);
        }
        output
    }

    // The harness's an programs: registers of real algebraic numbers, one command per line, each
    // printing its result, the numbers it refined, and roots as polynomial, index and interval.
    fn run_anum_program(program: &str) -> String {
        let mut am = AlgebraicManager::new();
        let mut pm = PolynomialManager::new();
        let mut registers: Vec<Option<Anum>> = Vec::new();
        let lines: Vec<String> = program
            .split('\n')
            .map(|line| {
                let words: Vec<&str> = line.split(' ').collect();
                let shown = run_command(&mut am, &mut pm, &mut registers, &words);
                format!("{}{shown}", words[0])
            })
            .collect();
        lines.join("\n")
    }

    fn check_fixture(name: &str, run: fn(&str) -> String) {
        let failures: Vec<String> = read_fixture(name)
            .into_iter()
            .filter_map(|(input, expected)| {
                let actual = run(&input);
                (actual != expected)
                    .then(|| format!("input:\n{input}\nexpected:\n{expected}\nactual:\n{actual}\n"))
            })
            .collect();
        assert!(
            failures.is_empty(),
            "{} failing cases of {name}:\n{}",
            failures.len(),
            failures.join("\n")
        );
    }

    // nlsat real algebraic numbers: random programs over roots of univariate polynomials and
    // rationals: arithmetic, comparison, integrality, sample selection, and the roots and signs of
    // polynomials at algebraic points. Each line prints Z3's result and the intervals its
    // refinements left behind.
    #[test]
    fn runs_the_real_algebraic_number_programs() {
        check_fixture("algebraic-numbers.json", run_anum_program);
    }

    // nlsat algebraic numbers: random rational intervals and polynomials of degree 1 in the root
    // variable, with the numbers that Z3's algebraic number manager selects and isolates for them.
    #[test]
    fn selects_and_isolates_algebraic_numbers() {
        check_fixture("algebraic.json", run_algebraic_command);
    }

    #[test]
    fn isolates_the_irrational_roots_closest_to_the_sample() {
        assert_eq!(
            run_algebraic_command("closest 1 3 2 2 0 1:1^2 -2:"),
            "closest 2@irrational"
        );
    }
}
