// Ported from Z3 (src/math/lp/random_updater_def.h, and shift_var and
// get_freedom_interval_for_column in src/math/lp/int_solver.cpp), MIT license, see
// z3-license.txt. Moves non-basic columns to random values inside the interval that keeps every
// row feasible, so that columns with equal values, which theory combination would assume equal,
// become different.
use std::cmp::Ordering;

use prove_num::{Int, Rational, get_lcm};

use crate::lp::containers::IndexedUintSet;
use crate::lp::lar_solver::LarSolver;
use crate::lp::numeric_pair::Impq;

const RANGE: u32 = 100000;

struct FreedomInterval {
    lower: Option<Impq>,
    upper: Option<Impq>,
    multiple: Rational,
}

fn get_delta(coeff: &Rational, first: &Impq, second: &Impq) -> Impq {
    if *coeff == Rational::one() {
        return first.sub(second);
    }
    if *coeff == Rational::minus_one() {
        return second.sub(first);
    }
    first.sub(second).div(coeff)
}

fn set_lower(lower: &mut Option<Impq>, candidate: Impq) {
    if lower
        .as_ref()
        .is_none_or(|lower| candidate.compare(lower) == Ordering::Greater)
    {
        *lower = Some(candidate);
    }
}

fn set_upper(upper: &mut Option<Impq>, candidate: Impq) {
    if upper
        .as_ref()
        .is_none_or(|upper| candidate.compare(upper) == Ordering::Less)
    {
        *upper = Some(candidate);
    }
}

// get_freedom_interval_for_column: the values of a non-basic column that keep the basic columns
// that depend on it within their bounds.
fn get_freedom_interval(solver: &LarSolver<'_>, column: usize) -> Option<FreedomInterval> {
    let core = &solver.core;
    if core.is_base(column) || solver.is_fixed(column) {
        return None;
    }
    let value = solver.get_value(column);
    let mut lower: Option<Impq> = None;
    let mut upper: Option<Impq> = None;
    let mut multiple = Int::one();
    if core.has_lower_bound(column) {
        set_lower(&mut lower, solver.get_lower_bound(column).sub(value));
    }
    if core.has_upper_bound(column) {
        set_upper(&mut upper, solver.get_upper_bound(column).sub(value));
    }
    for cell in &core.matrix.columns[column] {
        let coeff = core.matrix.get_val(cell);
        let basic = core.basis[cell.row];
        let basic_value = solver.get_value(basic);
        if solver.is_int(basic) && !coeff.is_int() && basic_value.is_int() {
            multiple = get_lcm(&multiple, coeff.den());
        }
        if let (Some(lower), Some(upper)) = (&lower, &upper)
            && lower == upper
        {
            continue;
        }
        if coeff.is_negative() {
            if core.has_lower_bound(basic) {
                set_lower(
                    &mut lower,
                    get_delta(coeff, basic_value, solver.get_lower_bound(basic)),
                );
            }
            if core.has_upper_bound(basic) {
                set_upper(
                    &mut upper,
                    get_delta(coeff, basic_value, solver.get_upper_bound(basic)),
                );
            }
        } else {
            if core.has_upper_bound(basic) {
                set_lower(
                    &mut lower,
                    get_delta(coeff, basic_value, solver.get_upper_bound(basic)),
                );
            }
            if core.has_lower_bound(basic) {
                set_upper(
                    &mut upper,
                    get_delta(coeff, basic_value, solver.get_lower_bound(basic)),
                );
            }
        }
    }
    let shifted_lower = lower.map(|lower| lower.add(value));
    let shifted_upper = upper.map(|upper| upper.add(value));
    if let (Some(lower), Some(upper)) = (&shifted_lower, &shifted_upper)
        && lower.compare(upper) == Ordering::Greater
    {
        return None;
    }
    Some(FreedomInterval {
        lower: shifted_lower,
        upper: shifted_upper,
        multiple: Rational::from_int(multiple),
    })
}

// int_solver::shift_var.
fn shift_var(solver: &mut LarSolver<'_>, column: usize) -> bool {
    if solver.is_fixed(column) || solver.is_base(column) || solver.settings().is_canceled() {
        return false;
    }
    let Some(interval) = get_freedom_interval(solver, column) else {
        return false;
    };
    let value = solver.get_value(column).clone();
    let multiple = interval.multiple;
    let get_random_shift = |solver: &mut LarSolver<'_>, range: u32| {
        let random = solver.settings_mut().get_random_next() % (range + 1);
        Impq::from_x(multiple.mul(&Rational::from_i64(i64::from(random))))
    };
    if interval.lower.is_none() && interval.upper.is_none() {
        let target = get_random_shift(solver, RANGE).add(&value);
        solver.set_value_for_nbasic_column(column, target);
        return true;
    }
    let is_int = solver.is_int(column);
    let lower = interval.lower.map(|lower| {
        if is_int {
            Impq::from_x(lower.ceil())
        } else {
            lower
        }
    });
    let upper = interval.upper.map(|upper| {
        if is_int {
            Impq::from_x(upper.floor())
        } else {
            upper
        }
    });
    if let (Some(lower), Some(upper)) = (&lower, &upper)
        && lower.compare(upper) != Ordering::Less
    {
        return false;
    }
    let Some(upper) = upper else {
        let target = value.add(&get_random_shift(solver, RANGE));
        solver.set_value_for_nbasic_column(column, target);
        return true;
    };
    let Some(lower) = lower else {
        let target = value.sub(&get_random_shift(solver, RANGE));
        solver.set_value_for_nbasic_column(column, target);
        return true;
    };
    let high = upper.sub(&value).div(&multiple).floor();
    let low = lower.sub(&value).div(&multiple).ceil();
    let span = high.sub(&low);
    if !span.is_positive() {
        return false;
    }
    let range = if span.compare(&Rational::from_i64(i64::from(RANGE))) == Ordering::Less {
        span.num()
            .to_i64()
            .and_then(|span| u32::try_from(span).ok())
            .expect("a span below the range fits")
    } else {
        RANGE
    };
    let random = solver.settings_mut().get_random_next() % (range + 1);
    let step = low.add(&Rational::from_i64(i64::from(random)));
    let target = value.add(&Impq::from_x(multiple.mul(&step)));
    solver.set_value_for_nbasic_column(column, target);
    true
}

// random_updater::update over the given columns.
pub fn random_update(solver: &mut LarSolver<'_>, columns: &[usize]) {
    let mut var_set = IndexedUintSet::new();
    for column in columns {
        var_set.add(*column);
    }
    let shift = |solver: &mut LarSolver<'_>, var_set: &mut IndexedUintSet, column: usize| {
        if !shift_var(solver, column) {
            return false;
        }
        for cell in &solver.core.matrix.columns[column] {
            let basic = solver.core.basis[cell.row];
            if var_set.has(basic) {
                var_set.delete(basic);
            }
        }
        true
    };
    for column in var_set.elems.clone() {
        if !var_set.has(column) {
            continue;
        }
        if !solver.is_base(column) {
            shift(solver, &mut var_set, column);
            continue;
        }
        let row_index = solver.core.heading[column] as usize;
        for index in 0..solver.get_row(row_index).len() {
            let cell_column = solver.get_row(row_index)[index].column;
            if !solver.is_base(cell_column)
                && !solver.is_fixed(cell_column)
                && shift(solver, &mut var_set, cell_column)
            {
                break;
            }
        }
    }
}
