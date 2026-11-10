// Ported from Z3 (src/math/lp/bound_analyzer_on_row.h, src/math/lp/lp_bound_propagator.h,
// src/math/lp/implied_bound.h, and propagate_bounds_for_touched_rows in src/math/lp/lar_solver.h),
// MIT license, see z3-license.txt. Bounds that a row implies on its columns from the bounds of the
// others, and equalities between columns that rows with fixed columns imply.
use std::collections::{HashMap, HashSet};

use prove_num::Rational;

use crate::lp::constraints::{ConstraintKind, KIND_GE, KIND_GT, KIND_LE, KIND_LT};
use crate::lp::core_solver::{COLUMN_FIXED, COLUMN_FREE, COLUMN_LOWER, COLUMN_UPPER};
use crate::lp::dependency::{Dependency, linearize};
use crate::lp::explanation::Explanation;
use crate::lp::lar_solver::{LarSolver, NULL_LPVAR};

// The theory side of lp_bound_propagator. TypeScript's host reaches the solver through its own
// back-pointer; here each call gets it.
pub trait BoundPropagatorHost {
    fn column_is_interesting(&mut self, solver: &LarSolver<'_>, column: usize) -> bool;
    fn bound_is_interesting(
        &mut self,
        solver: &LarSolver<'_>,
        column: usize,
        kind: ConstraintKind,
        value: &Rational,
    ) -> bool;
    fn is_equal(&mut self, solver: &LarSolver<'_>, first: usize, second: usize) -> bool;
    fn add_eq(
        &mut self,
        solver: &LarSolver<'_>,
        first: usize,
        second: usize,
        explanation: &Explanation,
        is_fixed: bool,
    ) -> bool;
}

// The -1 and -2 of analyzeRow: no column yet, and more than one.
const NO_COLUMN: usize = usize::MAX;
const MANY_COLUMNS: usize = usize::MAX - 1;

// implied_bound: the explanation is a weighted list of the witnesses of the other columns.
fn get_bound_kind(is_lower: bool, is_strict: bool) -> ConstraintKind {
    if is_lower {
        return if is_strict { KIND_GT } else { KIND_GE };
    }
    if is_strict { KIND_LT } else { KIND_LE }
}

// TypeScript's explain closure captures the row, the column's coefficient sign and the bound side;
// here they are fields, and explain reads the row from the solver, which nothing changes between
// the propagation and the explanation.
pub struct ImpliedBound {
    pub column: usize,
    pub bound: Rational,
    pub is_lower: bool,
    pub is_strict: bool,
    explain_row: usize,
    explain_is_coeff_positive: bool,
    explain_is_lower: bool,
}

impl ImpliedBound {
    pub fn explain(&self, solver: &LarSolver<'_>) -> Vec<(Rational, Dependency)> {
        let row = solver.get_row(self.explain_row);
        let column = self.column;
        let j_sign = (if self.explain_is_coeff_positive {
            1
        } else {
            -1
        }) * (if self.explain_is_lower { 1 } else { -1 });
        let own = row
            .iter()
            .find(|cell| cell.column == column)
            .map_or_else(Rational::one, |cell| cell.coeff.abs());
        let mut result = Vec::new();
        for cell in row {
            if cell.column == column {
                continue;
            }
            let sign = j_sign * if cell.coeff.is_positive() { 1 } else { -1 };
            let witness = if sign > 0 {
                solver.get_upper_witness(cell.column)
            } else {
                solver.get_lower_witness(cell.column)
            };
            result.push((cell.coeff.abs().div(&own), witness.clone()));
        }
        result
    }
}

// bound_kind: the kind of a lower or upper bound, strict or not.
pub fn get_implied_kind(bound: &ImpliedBound) -> ConstraintKind {
    get_bound_kind(bound.is_lower, bound.is_strict)
}

struct MonoidBound {
    value: Rational,
    is_strict: bool,
}

// extract_non_fixed's result.
struct NonFixed {
    count: usize,
    x: usize,
    y: usize,
    y_sign: i32,
}

#[derive(Default)]
pub struct BoundPropagator {
    pub ibounds: Vec<ImpliedBound>,
    improved_lower: HashMap<usize, usize>,
    improved_upper: HashMap<usize, usize>,
    visited_rows: HashSet<usize>,
    val2fixed_row: HashMap<String, usize>,
    row2index_pos: HashMap<String, usize>,
    row2index_neg: HashMap<String, usize>,
}

impl BoundPropagator {
    pub fn new() -> BoundPropagator {
        BoundPropagator::default()
    }

    pub fn init(&mut self) {
        self.improved_lower.clear();
        self.improved_upper.clear();
        self.ibounds.clear();
    }

    // propagate_bounds_for_touched_rows.
    pub fn propagate_bounds_for_touched_rows(
        &mut self,
        solver: &mut LarSolver<'_>,
        host: &mut dyn BoundPropagatorHost,
    ) {
        if solver.settings().is_propagating_eqs {
            if solver.settings_mut().get_random_next().is_multiple_of(10) {
                solver.remove_fixed_vars_from_base();
            }
            self.visited_rows.clear();
            for row_index in solver.core.touched_rows.elems.clone() {
                let offset_eqs = solver.settings().stats.offset_eqs;
                self.cheap_eq_on_nbase(solver, host, row_index);
                if solver.settings().is_canceled() {
                    return;
                }
                if solver.settings().stats.offset_eqs > offset_eqs {
                    solver.row_bounds_to_replay.push(row_index);
                }
            }
        }
        for row_index in solver.core.touched_rows.elems.clone() {
            if solver.get_row(row_index).len()
                <= solver.settings().max_row_length_for_bound_propagation
            {
                solver.settings_mut().stats.bp_rows_analyzed += 1;
                self.analyze_row(solver, host, row_index);
            }
            if solver.settings().is_canceled() {
                return;
            }
        }
        solver.core.touched_rows.clear();
    }

    // Bound analysis of a row whose sum is zero.

    fn analyze_row(
        &mut self,
        solver: &LarSolver<'_>,
        host: &mut dyn BoundPropagatorHost,
        row_index: usize,
    ) {
        let core = &solver.core;
        let row = solver.get_row(row_index);
        let mut column_of_u = NO_COLUMN;
        let mut column_of_l = NO_COLUMN;
        let advance = |slot: &mut usize, column: usize| {
            *slot = if *slot == NO_COLUMN {
                column
            } else {
                MANY_COLUMNS
            };
        };
        for cell in row {
            if column_of_l == MANY_COLUMNS && column_of_u == MANY_COLUMNS {
                return;
            }
            if cell.coeff.is_big() {
                return;
            }
            match core.get_column_type(cell.column) {
                COLUMN_LOWER => {
                    if cell.coeff.is_positive() {
                        advance(&mut column_of_u, cell.column);
                    } else {
                        advance(&mut column_of_l, cell.column);
                    }
                }
                COLUMN_UPPER => {
                    if cell.coeff.is_negative() {
                        advance(&mut column_of_u, cell.column);
                    } else {
                        advance(&mut column_of_l, cell.column);
                    }
                }
                COLUMN_FREE => {
                    advance(&mut column_of_u, cell.column);
                    advance(&mut column_of_l, cell.column);
                }
                _ => {}
            }
        }
        let mut some_is_interesting: Option<bool> = None;
        let mut is_some_interesting = |host: &mut dyn BoundPropagatorHost| {
            *some_is_interesting.get_or_insert_with(|| {
                row.iter()
                    .any(|cell| host.column_is_interesting(solver, cell.column))
            })
        };
        if column_of_u < MANY_COLUMNS {
            if host.column_is_interesting(solver, column_of_u) {
                self.limit_monoid_from_one(solver, host, row_index, column_of_u, true);
            }
        } else if column_of_u == NO_COLUMN && is_some_interesting(host) {
            self.limit_all_monoids(solver, host, row_index, true);
        }
        if column_of_l < MANY_COLUMNS {
            if host.column_is_interesting(solver, column_of_l) {
                self.limit_monoid_from_one(solver, host, row_index, column_of_l, false);
            }
        } else if column_of_l == NO_COLUMN && is_some_interesting(host) {
            self.limit_all_monoids(solver, host, row_index, false);
        }
    }

    // The bound of a monoid a * x at its maximum, or its minimum, and whether it is strict.
    fn get_monoid_bound(
        solver: &LarSolver<'_>,
        coeff: &Rational,
        column: usize,
        is_max: bool,
    ) -> MonoidBound {
        let is_upper = coeff.is_positive() == is_max;
        let bound = if is_upper {
            solver.get_upper_bound(column)
        } else {
            solver.get_lower_bound(column)
        };
        MonoidBound {
            value: bound.x.clone(),
            is_strict: !bound.y.is_zero(),
        }
    }

    // limit_all_monoids_from_below (is_from_below) and limit_all_monoids_from_above.
    fn limit_all_monoids(
        &mut self,
        solver: &LarSolver<'_>,
        host: &mut dyn BoundPropagatorHost,
        row_index: usize,
        is_from_below: bool,
    ) {
        let row = solver.get_row(row_index);
        let mut num_strict = 0;
        let mut total = Rational::zero();
        for cell in row {
            let bound =
                BoundPropagator::get_monoid_bound(solver, &cell.coeff, cell.column, is_from_below);
            total = total.sub(&cell.coeff.mul(&bound.value));
            if bound.is_strict {
                num_strict += 1;
            }
        }
        for cell in row {
            if !host.column_is_interesting(solver, cell.column) {
                continue;
            }
            let own =
                BoundPropagator::get_monoid_bound(solver, &cell.coeff, cell.column, is_from_below);
            let bound = total.div(&cell.coeff).add(&own.value);
            let is_positive = cell.coeff.is_positive();
            let is_strict = num_strict - i32::from(own.is_strict) > 0;
            self.limit_j(
                solver,
                host,
                row_index,
                cell.column,
                bound,
                is_positive,
                is_positive == is_from_below,
                is_strict,
            );
        }
    }

    // limit_monoid_u_from_below (is_from_below) and limit_monoid_l_from_above.
    fn limit_monoid_from_one(
        &mut self,
        solver: &LarSolver<'_>,
        host: &mut dyn BoundPropagatorHost,
        row_index: usize,
        target: usize,
        is_from_below: bool,
    ) {
        let mut bound = Rational::zero();
        let mut target_coeff = Rational::zero();
        let mut is_strict = false;
        for cell in solver.get_row(row_index) {
            if cell.column == target {
                target_coeff = cell.coeff.clone();
                continue;
            }
            let monoid =
                BoundPropagator::get_monoid_bound(solver, &cell.coeff, cell.column, is_from_below);
            bound = bound.sub(&cell.coeff.mul(&monoid.value));
            if monoid.is_strict {
                is_strict = true;
            }
        }
        bound = bound.div(&target_coeff);
        let is_positive = target_coeff.is_positive();
        self.limit_j(
            solver,
            host,
            row_index,
            target,
            bound,
            is_positive,
            is_positive == is_from_below,
            is_strict,
        );
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "TypeScript's limitJ takes these, and the solver and host its closures reach"
    )]
    fn limit_j(
        &mut self,
        solver: &LarSolver<'_>,
        host: &mut dyn BoundPropagatorHost,
        row_index: usize,
        column: usize,
        value: Rational,
        is_coeff_positive: bool,
        is_lower: bool,
        is_strict: bool,
    ) {
        if !host.bound_is_interesting(solver, column, get_bound_kind(is_lower, is_strict), &value) {
            return;
        }
        self.add_bound(
            value,
            column,
            is_lower,
            is_strict,
            row_index,
            is_coeff_positive,
        );
    }

    // TypeScript passes the explain closure; here what it captures.
    fn add_bound(
        &mut self,
        value: Rational,
        column: usize,
        is_lower: bool,
        is_strict: bool,
        explain_row: usize,
        explain_is_coeff_positive: bool,
    ) {
        let improved = if is_lower {
            &mut self.improved_lower
        } else {
            &mut self.improved_upper
        };
        let Some(index) = improved.get(&column).copied() else {
            improved.insert(column, self.ibounds.len());
            self.ibounds.push(ImpliedBound {
                column,
                bound: value,
                is_lower,
                is_strict,
                explain_row,
                explain_is_coeff_positive,
                explain_is_lower: is_lower,
            });
            return;
        };
        let found = &mut self.ibounds[index];
        let comparison = value.compare(&found.bound);
        if (if is_lower {
            comparison.is_gt()
        } else {
            comparison.is_lt()
        }) || (comparison.is_eq() && !found.is_strict && is_strict)
        {
            found.bound = value;
            found.is_strict = is_strict;
            found.explain_row = explain_row;
            found.explain_is_coeff_positive = explain_is_coeff_positive;
            found.explain_is_lower = is_lower;
        }
    }

    // Equalities from rows.

    // column_is_fixed: fixed, without an infinitesimal.
    fn is_fixed(solver: &LarSolver<'_>, column: usize) -> bool {
        solver.core.get_column_type(column) == COLUMN_FIXED
            && solver.get_lower_bound(column).y.is_zero()
    }

    fn get_val(solver: &LarSolver<'_>, column: usize) -> String {
        solver.get_value(column).x.to_string()
    }

    fn is_eq_new(
        solver: &LarSolver<'_>,
        host: &mut dyn BoundPropagatorHost,
        first: usize,
        second: usize,
    ) -> bool {
        let external1 = solver.get_external(first);
        let external2 = solver.get_external(second);
        external1 != NULL_LPVAR
            && external2 != NULL_LPVAR
            && !host.is_equal(solver, external1, external2)
    }

    fn explain_fixed_in_row(
        solver: &LarSolver<'_>,
        row_index: usize,
        explanation: &mut Explanation,
    ) {
        let mut witnesses: Vec<Dependency> = Vec::new();
        for cell in solver.get_row(row_index) {
            if !solver.is_fixed(cell.column) {
                continue;
            }
            witnesses.push(solver.get_lower_witness(cell.column).clone());
            witnesses.push(solver.get_upper_witness(cell.column).clone());
        }
        for constraint in linearize(&witnesses) {
            explanation.push(constraint as usize);
        }
    }

    fn add_eq_on_columns(
        solver: &mut LarSolver<'_>,
        host: &mut dyn BoundPropagatorHost,
        explanation: &Explanation,
        first: usize,
        second: usize,
        is_fixed: bool,
    ) {
        let is_added = host.add_eq(solver, first, second, explanation, is_fixed);
        if !is_added {
            return;
        }
        let stats = &mut solver.settings_mut().stats;
        if is_fixed {
            stats.fixed_eqs += 1;
        } else {
            stats.offset_eqs += 1;
        }
    }

    fn get_only_one_non_fixed(solver: &LarSolver<'_>, row_index: usize) -> usize {
        let mut result = NULL_LPVAR;
        for cell in solver.get_row(row_index) {
            if BoundPropagator::is_fixed(solver, cell.column) {
                continue;
            }
            if result != NULL_LPVAR {
                return NULL_LPVAR;
            }
            result = cell.column;
        }
        result
    }

    fn try_add_equation_with_internal_fixed_tables(
        &mut self,
        solver: &mut LarSolver<'_>,
        host: &mut dyn BoundPropagatorHost,
        row1: usize,
    ) {
        let v1 = BoundPropagator::get_only_one_non_fixed(solver, row1);
        if v1 == NULL_LPVAR {
            return;
        }
        let key = BoundPropagator::get_val(solver, v1);
        let row2 = match self.val2fixed_row.get(&key) {
            Some(row2) if *row2 < solver.get_row_count() => *row2,
            _ => {
                self.val2fixed_row.insert(key, row1);
                return;
            }
        };
        let v2 = BoundPropagator::get_only_one_non_fixed(solver, row2);
        if v2 == NULL_LPVAR
            || solver.get_value(v1) != solver.get_value(v2)
            || solver.is_int(v1) != solver.is_int(v2)
        {
            self.val2fixed_row.insert(key, row1);
            return;
        }
        if v1 == v2 || !BoundPropagator::is_eq_new(solver, host, v1, v2) {
            return;
        }
        let mut explanation = Explanation::new();
        BoundPropagator::explain_fixed_in_row(solver, row1, &mut explanation);
        BoundPropagator::explain_fixed_in_row(solver, row2, &mut explanation);
        BoundPropagator::add_eq_on_columns(solver, host, &explanation, v1, v2, true);
    }

    fn try_add_equation_with_lp_fixed_tables(
        &mut self,
        solver: &mut LarSolver<'_>,
        host: &mut dyn BoundPropagatorHost,
        row_index: usize,
        column: usize,
    ) {
        if BoundPropagator::is_fixed(solver, column) {
            return;
        }
        let value = solver.get_value(column);
        let other = if value.y.is_zero() {
            solver.find_in_fixed_tables(&value.x, solver.is_int(column))
        } else {
            None
        };
        let Some(other) = other else {
            self.try_add_equation_with_internal_fixed_tables(solver, host, row_index);
            return;
        };
        if !BoundPropagator::is_eq_new(solver, host, other, column) {
            return;
        }
        let mut explanation = Explanation::new();
        BoundPropagator::explain_fixed_in_row(solver, row_index, &mut explanation);
        for constraint in linearize(&[
            solver.get_lower_witness(other).clone(),
            solver.get_upper_witness(other).clone(),
        ]) {
            explanation.push(constraint as usize);
        }
        BoundPropagator::add_eq_on_columns(solver, host, &explanation, other, column, true);
    }

    // extract_non_fixed: the basic column, the other non-fixed column and the sign of its unit
    // coefficient, when the row has at most two non-fixed columns.
    fn extract_non_fixed(solver: &LarSolver<'_>, row_index: usize) -> NonFixed {
        let x = solver.core.basis[row_index];
        if BoundPropagator::is_fixed(solver, x) {
            return NonFixed {
                count: 0,
                x,
                y: NULL_LPVAR,
                y_sign: 0,
            };
        }
        let mut count = 1;
        let mut y = NULL_LPVAR;
        let mut y_sign = 0;
        for cell in solver.get_row(row_index) {
            if cell.column == x || BoundPropagator::is_fixed(solver, cell.column) {
                continue;
            }
            count += 1;
            if count > 2 {
                return NonFixed {
                    count,
                    x,
                    y,
                    y_sign,
                };
            }
            y = cell.column;
            y_sign = if cell.coeff == Rational::one() {
                1
            } else if cell.coeff == Rational::minus_one() {
                -1
            } else {
                0
            };
            if y_sign == 0 {
                return NonFixed {
                    count,
                    x,
                    y,
                    y_sign,
                };
            }
        }
        NonFixed {
            count,
            x,
            y,
            y_sign,
        }
    }

    fn cheap_eq_on_nbase(
        &mut self,
        solver: &mut LarSolver<'_>,
        host: &mut dyn BoundPropagatorHost,
        row_index: usize,
    ) {
        self.cheap_eq_on_nbase_core(solver, host, row_index);
        self.row2index_pos.clear();
        self.row2index_neg.clear();
    }

    fn cheap_eq_on_nbase_core(
        &mut self,
        solver: &mut LarSolver<'_>,
        host: &mut dyn BoundPropagatorHost,
        row_index: usize,
    ) {
        if self.visited_rows.contains(&row_index) {
            return;
        }
        self.visited_rows.insert(row_index);
        let extracted = BoundPropagator::extract_non_fixed(solver, row_index);
        if extracted.count == 0 || extracted.count > 2 {
            return;
        }
        if extracted.count == 1 {
            self.try_add_equation_with_lp_fixed_tables(solver, host, row_index, extracted.x);
            return;
        }
        if extracted.y_sign == 0 {
            return;
        }
        let key = BoundPropagator::get_val(solver, extracted.x);
        if extracted.y_sign == 1 {
            self.row2index_pos.insert(key, row_index);
        } else {
            self.row2index_neg.insert(key, row_index);
        }
        for index in 0..solver.core.matrix.columns[extracted.y].len() {
            let other = solver.core.matrix.columns[extracted.y][index].row;
            if other == row_index || self.visited_rows.contains(&other) {
                continue;
            }
            self.visited_rows.insert(other);
            let next = BoundPropagator::extract_non_fixed(solver, other);
            if next.count != 2 || next.y_sign == 0 {
                continue;
            }
            let table = if next.y_sign == 1 {
                &mut self.row2index_pos
            } else {
                &mut self.row2index_neg
            };
            let key = BoundPropagator::get_val(solver, next.x);
            let Some(found) = table.get(&key).copied() else {
                table.insert(key, other);
                continue;
            };
            let base_of_found = solver.core.basis[found];
            if solver.is_int(next.x) != solver.is_int(base_of_found)
                || solver.get_value(next.x).y != solver.get_value(base_of_found).y
            {
                continue;
            }
            if !BoundPropagator::is_eq_new(solver, host, next.x, base_of_found) {
                continue;
            }
            let mut explanation = Explanation::new();
            BoundPropagator::explain_fixed_in_row(solver, found, &mut explanation);
            BoundPropagator::explain_fixed_in_row(solver, other, &mut explanation);
            BoundPropagator::add_eq_on_columns(
                solver,
                host,
                &explanation,
                next.x,
                base_of_found,
                false,
            );
        }
    }
}
