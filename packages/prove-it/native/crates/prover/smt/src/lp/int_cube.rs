// Ported from Z3 (src/math/lp/int_cube.cpp, and tighten_term_bounds_by_delta and
// round_to_integer_solution in src/math/lp/lar_solver.cpp), MIT license, see z3-license.txt. The
// cube test: when the bounds of every term shrunk by half the sum of its integer coefficients still
// admit a solution, rounding that solution gives an integer one. The largest cube test maximizes
// the edge of that cube instead, and when the edge is below 1 it rounds the center and flips
// rounded columns to repair the bounds the rounding broke.
use std::collections::{HashMap, HashSet};

use prove_num::Rational;

use crate::lp::constraints::{ConstraintKind, KIND_GE, KIND_GT, KIND_LE, KIND_LT};
use crate::lp::core_solver::{CoreSolver, LP_FEASIBLE, LP_OPTIMAL};
use crate::lp::lar_solver::{LarSolver, NULL_LPVAR};
use crate::lp::lar_term::LarTerm;
use crate::lp::maximize_term::maximize_term;
use crate::lp::numeric_pair::Impq;
use crate::util::error::SmtError;

fn get_half() -> Rational {
    Rational::from_i64(1).div(&Rational::from_i64(2))
}

// get_cube_delta_for_term: an infinitesimal for x - y over integers, nothing for x + y, and
// otherwise half the sum of the integer coefficients.
fn get_cube_delta(solver: &LarSolver<'_>, term: &LarTerm) -> Impq {
    if term.size() == 2 {
        let mut is_plus_seen = false;
        let mut is_minus_seen = false;
        let is_unit = term.iter().all(|entry| {
            if !solver.is_int(entry.0) {
                return false;
            }
            if *entry.1 == Rational::one() {
                is_plus_seen = true;
            } else if *entry.1 == Rational::minus_one() {
                is_minus_seen = true;
            } else {
                return false;
            }
            true
        });
        if is_unit {
            return if is_plus_seen && is_minus_seen {
                Impq::zero()
            } else {
                Impq::new(Rational::zero(), Rational::one())
            };
        }
    }
    let mut delta = Rational::zero();
    for entry in term.iter() {
        if solver.is_int(entry.0) {
            delta = delta.add(&entry.1.abs());
        }
    }
    Impq::from_x(delta.mul(&get_half()))
}

fn add_var_bound(solver: &mut LarSolver<'_>, column: usize, kind: ConstraintKind, rhs: &Rational) {
    let index = solver.mk_var_bound(column, kind, rhs);
    solver.activate(index);
}

// tighten_term_bounds_by_delta: whether the bounds of the column stay apart when each moves inward
// by delta.
fn tighten_term_bounds(solver: &mut LarSolver<'_>, column: usize, delta: &Impq) -> bool {
    let core = &solver.core;
    let has_upper = core.has_upper_bound(column);
    let has_lower = core.has_lower_bound(column);
    if has_upper
        && has_lower
        && solver
            .get_upper_bound(column)
            .sub(delta)
            .compare(&solver.get_lower_bound(column).add(delta))
            .is_lt()
    {
        return false;
    }
    if has_upper {
        let upper = solver.get_upper_bound(column);
        let is_strict = !delta.y.is_zero() || !upper.y.is_zero();
        let rhs = upper.x.sub(&delta.x);
        add_var_bound(
            solver,
            column,
            if is_strict { KIND_LT } else { KIND_LE },
            &rhs,
        );
    }
    if has_lower {
        let lower = solver.get_lower_bound(column);
        let is_strict = !delta.y.is_zero() || !lower.y.is_zero();
        let rhs = lower.x.add(&delta.x);
        add_var_bound(
            solver,
            column,
            if is_strict { KIND_GT } else { KIND_GE },
            &rhs,
        );
    }
    true
}

// round_to_integer_solution: integer columns without terms round to the nearest integer, and the
// terms that use them take their new values.
fn round_to_integer_solution(solver: &mut LarSolver<'_>) {
    // Only looked up, never iterated.
    let mut rounded = HashSet::new();
    for column in 0..solver.get_column_count() {
        if !solver.is_int(column) || solver.has_term(column) {
            continue;
        }
        let value = &solver.core.x[column];
        if value.is_int() {
            continue;
        }
        let floor = Impq::from_x(value.floor());
        let rounded_value = if floor
            .sub(value)
            .compare(&Impq::from_x(get_half().neg()))
            .is_lt()
        {
            Impq::from_x(value.ceil())
        } else {
            floor
        };
        solver.core.x[column] = rounded_value;
        rounded.insert(column);
    }
    if rounded.is_empty() {
        return;
    }
    for term in &solver.terms {
        if term.iter().any(|entry| rounded.contains(&entry.0)) {
            let value = term.apply(&solver.core.x);
            solver.core.x[term.column] = value;
        }
    }
}

// r_basis_has_inf_int.
fn has_basic_inf_int(solver: &LarSolver<'_>) -> bool {
    solver
        .core
        .basis
        .iter()
        .any(|column| solver.is_int(*column) && !solver.get_value(*column).is_int())
}

// int_cube::operator(): whether the cube test found an integer solution.
pub fn find_cube(solver: &mut LarSolver<'_>) -> bool {
    solver.push();
    for index in 0..solver.terms.len() {
        let delta = get_cube_delta(solver, &solver.terms[index]);
        let column = solver.terms[index].column;
        if delta.is_zero() || tighten_term_bounds(solver, column, &delta) {
            continue;
        }
        solver.pop(1);
        solver.status = LP_OPTIMAL;
        return false;
    }
    let status = solver.find_feasible_solution();
    if status != LP_FEASIBLE && status != LP_OPTIMAL {
        solver.pop(1);
        solver.move_non_basic_columns_to_bounds();
        return !has_basic_inf_int(solver);
    }
    solver.pop(1);
    round_to_integer_solution(solver);
    solver.status = LP_FEASIBLE;
    true
}

// add_edge_rows_for_term: the term column moved inward by the edge times delta stays within its
// bounds, through a new term for each bound.
fn add_edge_rows(solver: &mut LarSolver<'_>, column: usize, edge: usize) -> Result<bool, SmtError> {
    let delta = get_cube_delta(solver, solver.get_term(column)?);
    if delta.is_zero() {
        return Ok(true);
    }
    if !delta.y.is_zero() {
        return Ok(tighten_term_bounds(solver, column, &delta));
    }
    if solver.core.has_upper_bound(column) {
        let upper = solver.get_upper_bound(column).clone();
        let sum = solver.add_term(
            &[(column, Rational::one()), (edge, delta.x.clone())],
            NULL_LPVAR,
        );
        add_var_bound(
            solver,
            sum,
            if upper.y.is_zero() { KIND_LE } else { KIND_LT },
            &upper.x,
        );
    }
    if solver.core.has_lower_bound(column) {
        let lower = solver.get_lower_bound(column).clone();
        let difference = solver.add_term(
            &[(column, Rational::one()), (edge, delta.x.neg())],
            NULL_LPVAR,
        );
        add_var_bound(
            solver,
            difference,
            if lower.y.is_zero() { KIND_GE } else { KIND_GT },
            &lower.x,
        );
    }
    Ok(true)
}

// sat_after_rounding.
fn round_center(solver: &mut LarSolver<'_>) -> bool {
    round_to_integer_solution(solver);
    solver.status = LP_FEASIBLE;
    solver.settings_mut().stats.lcube_success += 1;
    true
}

// A rounded column, its floor, and whether it sits at its floor plus one.
struct FlipCandidate {
    column: usize,
    floor: Rational,
    is_at_high: bool,
}

// A term column with a bound, and its value while the repair flips columns.
struct BoundedRow {
    column: usize,
    value: Impq,
}

fn get_row_violation(core: &CoreSolver<'_>, column: usize, value: &Impq) -> Impq {
    let mut violation = Impq::zero();
    if core.has_upper_bound(column) && value.compare(&core.upper_bounds[column]).is_gt() {
        violation = violation.add(&value.sub(&core.upper_bounds[column]));
    }
    if core.has_lower_bound(column) && value.compare(&core.lower_bounds[column]).is_lt() {
        violation = violation.add(&core.lower_bounds[column].sub(value));
    }
    violation
}

fn get_step(flip: &FlipCandidate) -> Rational {
    if flip.is_at_high {
        Rational::minus_one()
    } else {
        Rational::one()
    }
}

// repair_rounded_candidate: while the bounded terms are violated, flips the rounded column that
// decreases the total violation most, within a budget, and keeps the values when none is left.
fn repair_rounded_candidate(
    solver: &mut LarSolver<'_>,
    flips: &mut [FlipCandidate],
) -> Result<bool, SmtError> {
    let core = &solver.core;
    let mut rows = Vec::new();
    for term in &solver.terms {
        if core.has_upper_bound(term.column) || core.has_lower_bound(term.column) {
            rows.push(BoundedRow {
                column: term.column,
                value: term.apply(&core.x),
            });
        }
    }
    let mut violation = Impq::zero();
    for row in &rows {
        violation = violation.add(&get_row_violation(core, row.column, &row.value));
    }
    if violation.is_zero() {
        return Ok(true);
    }
    if flips.is_empty() {
        return Ok(false);
    }
    // Only looked up, never iterated.
    let flip_of_column: HashMap<usize, usize> = flips
        .iter()
        .enumerate()
        .map(|(flip_index, flip)| (flip.column, flip_index))
        .collect();
    let mut occurrences: Vec<Vec<(usize, Rational)>> = flips.iter().map(|_| Vec::new()).collect();
    for (row_index, row) in rows.iter().enumerate() {
        for entry in solver.get_term(row.column)?.iter() {
            if let Some(flip_index) = flip_of_column.get(&entry.0) {
                occurrences[*flip_index].push((row_index, entry.1.clone()));
            }
        }
    }
    let mut budget = (2 * flips.len() as u64).min(solver.settings().lcube_flips) as i64;
    let mut is_flipped = false;
    while !violation.is_zero() {
        // budget-- > 0.
        let is_within_budget = budget > 0;
        budget -= 1;
        if !is_within_budget {
            break;
        }
        let mut best_flip = NULL_LPVAR;
        let mut best_gain = Impq::zero();
        for flip_index in 0..flips.len() {
            if occurrences[flip_index].is_empty() {
                continue;
            }
            let step = get_step(&flips[flip_index]);
            let mut gain = Impq::zero();
            for occurrence in &occurrences[flip_index] {
                let row = &rows[occurrence.0];
                let flipped = row.value.add(&Impq::from_x(step.mul(&occurrence.1)));
                gain = gain.add(
                    &get_row_violation(core, row.column, &flipped)
                        .sub(&get_row_violation(core, row.column, &row.value)),
                );
            }
            if gain.compare(&best_gain).is_lt() {
                best_gain = gain;
                best_flip = flip_index;
            }
        }
        if best_flip == NULL_LPVAR {
            return Ok(false);
        }
        let step = get_step(&flips[best_flip]);
        for occurrence in &occurrences[best_flip] {
            let row = &mut rows[occurrence.0];
            row.value = row.value.add(&Impq::from_x(step.mul(&occurrence.1)));
        }
        flips[best_flip].is_at_high = !flips[best_flip].is_at_high;
        violation = violation.add(&best_gain);
        is_flipped = true;
    }
    if !violation.is_zero() {
        return Ok(false);
    }
    for flip in flips.iter() {
        solver.core.x[flip.column] = Impq::from_x(if flip.is_at_high {
            flip.floor.add(&Rational::one())
        } else {
            flip.floor.clone()
        });
    }
    for index in 0..solver.terms.len() {
        let term = &solver.terms[index];
        let value = term.apply(&solver.core.x);
        solver.core.x[term.column] = value;
    }
    if is_flipped {
        solver.settings_mut().stats.lcube_flip_success += 1;
    }
    Ok(true)
}

// round_and_repair: rounds the center of the cube and repairs it, or restores the center.
fn round_and_repair(solver: &mut LarSolver<'_>) -> Result<bool, SmtError> {
    let backup = solver.core.x.clone();
    let mut flips = Vec::new();
    for column in 0..solver.get_column_count() {
        if !solver.is_int(column) || solver.has_term(column) {
            continue;
        }
        let value = &solver.core.x[column];
        if !value.is_int() {
            flips.push(FlipCandidate {
                column,
                floor: value.floor(),
                is_at_high: false,
            });
        }
    }
    round_to_integer_solution(solver);
    for flip in &mut flips {
        flip.is_at_high = solver.core.x[flip.column].x.compare(&flip.floor).is_gt();
    }
    solver.status = LP_FEASIBLE;
    if repair_rounded_candidate(solver, &mut flips)? {
        solver.settings_mut().stats.lcube_success += 1;
        return Ok(true);
    }
    solver.core.x.splice(0..backup.len(), backup);
    Ok(false)
}

// find_largest_cube: whether an integer solution comes from the largest cube that fits in the
// bounds of the terms, with its edge as a new column that the optimizing simplex maximizes.
pub fn find_largest_cube(solver: &mut LarSolver<'_>) -> Result<bool, SmtError> {
    solver.settings_mut().stats.lcube_calls += 1;
    solver.push();
    let is_add_term_hook_suspended = solver.is_add_term_hook_suspended;
    solver.is_add_term_hook_suspended = true;
    let edge = solver.add_var(NULL_LPVAR, false);
    add_var_bound(solver, edge, KIND_GE, &Rational::zero());
    let term_columns: Vec<usize> = solver.terms.iter().map(|term| term.column).collect();
    let mut is_added = true;
    for column in term_columns {
        if !add_edge_rows(solver, column, edge)? {
            is_added = false;
            break;
        }
    }
    solver.is_add_term_hook_suspended = is_add_term_hook_suspended;
    if !is_added {
        solver.pop(1);
        solver.status = LP_OPTIMAL;
        return Ok(false);
    }
    let status = solver.find_feasible_solution();
    if status != LP_FEASIBLE && status != LP_OPTIMAL {
        solver.pop(1);
        solver.move_non_basic_columns_to_bounds();
        return Ok(!has_basic_inf_int(solver));
    }
    let maximum = maximize_term(solver, edge);
    if solver.settings().is_canceled() {
        solver.pop(1);
        return Ok(false);
    }
    let Some(maximum) = maximum else {
        add_var_bound(solver, edge, KIND_GE, &Rational::one());
        let bounded_status = solver.find_feasible_solution();
        solver.pop(1);
        return Ok(
            if bounded_status == LP_FEASIBLE || bounded_status == LP_OPTIMAL {
                round_center(solver)
            } else {
                false
            },
        );
    };
    solver.pop(1);
    if maximum.compare(&Impq::from_x(Rational::one())).is_ge() {
        Ok(round_center(solver))
    } else {
        round_and_repair(solver)
    }
}
