// Ported from Z3 (src/math/lp/lar_core_solver.h, src/math/lp/lp_core_solver_base.h,
// src/math/lp/lp_primal_core_solver.h, src/math/lp/lp_primal_core_solver_tableau_def.h), MIT
// license, see z3-license.txt. The tableau, the column values and bounds, and the primal simplex
// that lar_solver runs with the tableau_rows strategy: the smallest infeasible basic column
// leaves, and the entering column is the one in its row that frees the fewest bounded basics.
use std::cmp::Ordering;

use prove_num::Rational;

use crate::lp::containers::{IndexedUintSet, StackedVector, VarHeap};
use crate::lp::lp_settings::LpSettings;
use crate::lp::numeric_pair::Impq;
use crate::lp::static_matrix::{RowCell, StaticMatrix};

// column_type: which bounds a column has.
pub type ColumnType = u8;
pub const COLUMN_FREE: ColumnType = 0;
pub const COLUMN_LOWER: ColumnType = 1;
pub const COLUMN_UPPER: ColumnType = 2;
pub const COLUMN_BOXED: ColumnType = 3;
pub const COLUMN_FIXED: ColumnType = 4;

pub type LpStatus = u8;
pub const LP_UNKNOWN: LpStatus = 0;
pub const LP_INFEASIBLE: LpStatus = 1;
pub const LP_OPTIMAL: LpStatus = 2;
pub const LP_FEASIBLE: LpStatus = 3;
pub const LP_CANCELLED: LpStatus = 4;
pub const LP_UNBOUNDED: LpStatus = 5;

// The -1 of TypeScript's infRowIndex.
const NO_ROW: usize = usize::MAX;

const BLAND_MODE_THRESHOLD: u64 = 1000;

// setAt: the value at the index, growing the vector by one when the index is its length.
fn set_at(values: &mut Vec<Impq>, index: usize, value: Impq) {
    if index < values.len() {
        values[index] = value;
    } else {
        values.resize(index, Impq::zero());
        values.push(value);
    }
}

pub struct CoreSolver<'l> {
    // TypeScript shares one LpSettings object between LarSolver and CoreSolver; here CoreSolver
    // owns it and LarSolver reaches it through `core`.
    pub settings: LpSettings<'l>,
    pub matrix: StaticMatrix,
    pub column_types: StackedVector<ColumnType>,
    pub lower_bounds: Vec<Impq>,
    pub upper_bounds: Vec<Impq>,
    pub x: Vec<Impq>,
    pub basis: Vec<usize>,
    pub nbasis: Vec<usize>,
    // The row of a basic column, and -index - 1 for a nonbasic column at that index of nbasis.
    pub heading: Vec<i64>,
    pub inf_heap: VarHeap,
    // TypeScript's touchedRows is LarSolver's set, which CoreSolver shares, or null while
    // withoutTouchedRows runs: the set lives here and is_recording_touched_rows is false for null.
    pub touched_rows: IndexedUintSet,
    pub is_recording_touched_rows: bool,
    pub status: LpStatus,
    pub inf_row_index: usize,
    pub infeasible_sum_sign: i32,
    pub infeasible_combination: Vec<(Rational, usize)>,
    // m_d: the reduced costs while maximize_term runs the tableau_costs strategy, kept on pivots.
    pub reduced_costs: Option<Vec<Rational>>,
    is_bland_mode: bool,
    left_basis: IndexedUintSet,
    left_basis_repeated: u64,
}

impl<'l> CoreSolver<'l> {
    pub fn new(settings: LpSettings<'l>) -> CoreSolver<'l> {
        CoreSolver {
            settings,
            matrix: StaticMatrix::new(),
            column_types: StackedVector::default(),
            lower_bounds: Vec::new(),
            upper_bounds: Vec::new(),
            x: Vec::new(),
            basis: Vec::new(),
            nbasis: Vec::new(),
            heading: Vec::new(),
            inf_heap: VarHeap::default(),
            touched_rows: IndexedUintSet::new(),
            is_recording_touched_rows: false,
            status: LP_FEASIBLE,
            inf_row_index: NO_ROW,
            infeasible_sum_sign: 0,
            infeasible_combination: Vec::new(),
            reduced_costs: None,
            is_bland_mode: false,
            left_basis: IndexedUintSet::new(),
            left_basis_repeated: 0,
        }
    }

    pub fn get_column_count(&self) -> usize {
        self.matrix.get_column_count()
    }

    // add_new_var_to_core_fields_for_mpq: a column at zero, basic in a new row or nonbasic.
    pub fn add_column(&mut self, is_basic: bool) {
        let column = self.matrix.get_column_count();
        self.matrix.add_column();
        self.x.push(Impq::zero());
        set_at(&mut self.lower_bounds, column, Impq::zero());
        set_at(&mut self.upper_bounds, column, Impq::zero());
        if is_basic {
            self.matrix.add_row();
            self.heading.push(self.basis.len() as i64);
            self.basis.push(column);
            return;
        }
        self.heading.push(-(self.nbasis.len() as i64) - 1);
        self.nbasis.push(column);
    }

    // remove_last_column_from_basis_tableau: the last column out of the basis or the nonbasic
    // columns, once the tableau no longer holds it.
    pub fn remove_last_column(&mut self, column: usize) {
        self.x.truncate(self.matrix.get_column_count());
        let position = self.heading[column];
        if position >= 0 {
            let position = position as usize;
            let last_position = self.basis.len() - 1;
            if position != last_position {
                let moved = self.basis[last_position];
                self.basis[position] = moved;
                self.heading[moved] = position as i64;
            }
            self.basis.pop();
        } else {
            let index = (-1 - position) as usize;
            let last_position = self.nbasis.len() - 1;
            if index != last_position {
                let moved = self.nbasis[last_position];
                self.nbasis[index] = moved;
                self.heading[moved] = -(index as i64) - 1;
            }
            self.nbasis.pop();
        }
        self.heading.pop();
    }

    // The action, with pivots not recording the rows they touch. TypeScript's closure reaches the
    // core through `this`; here the action gets the state that owns the core, which get_core
    // reaches.
    pub fn without_touched_rows<S, T>(
        state: &mut S,
        get_core: fn(&mut S) -> &mut CoreSolver<'l>,
        action: impl FnOnce(&mut S) -> T,
    ) -> T {
        let saved_touched_rows = get_core(state).is_recording_touched_rows;
        get_core(state).is_recording_touched_rows = false;
        let result = action(state);
        get_core(state).is_recording_touched_rows = saved_touched_rows;
        result
    }

    pub fn get_column_type(&self, column: usize) -> ColumnType {
        *self.column_types.get(column)
    }

    pub fn is_base(&self, column: usize) -> bool {
        self.heading[column] >= 0
    }

    pub fn is_fixed(&self, column: usize) -> bool {
        *self.column_types.get(column) == COLUMN_FIXED
    }

    pub fn has_lower_bound(&self, column: usize) -> bool {
        let column_type = *self.column_types.get(column);
        column_type != COLUMN_FREE && column_type != COLUMN_UPPER
    }

    pub fn has_upper_bound(&self, column: usize) -> bool {
        let column_type = *self.column_types.get(column);
        column_type != COLUMN_FREE && column_type != COLUMN_LOWER
    }

    pub fn is_feasible(&self) -> bool {
        self.inf_heap.size() == 0
    }

    pub fn column_is_feasible(&self, column: usize) -> bool {
        let value = &self.x[column];
        match *self.column_types.get(column) {
            COLUMN_FIXED | COLUMN_BOXED => {
                value.compare(&self.upper_bounds[column]) != Ordering::Greater
                    && value.compare(&self.lower_bounds[column]) != Ordering::Less
            }
            COLUMN_LOWER => value.compare(&self.lower_bounds[column]) != Ordering::Less,
            COLUMN_UPPER => value.compare(&self.upper_bounds[column]) != Ordering::Greater,
            _ => true,
        }
    }

    pub fn track_column_feasibility(&mut self, column: usize) {
        if self.column_is_feasible(column) {
            if self.inf_heap.has(column) {
                self.inf_heap.erase(column);
            }
        } else if !self.inf_heap.has(column) {
            self.inf_heap.insert(column);
        }
    }

    pub fn add_delta_to_x_and_track_feasibility(&mut self, column: usize, delta: &Impq) {
        self.x[column] = self.x[column].add(delta);
        self.track_column_feasibility(column);
    }

    pub fn submul_from_x_and_track_feasibility(
        &mut self,
        column: usize,
        delta: &Impq,
        coeff: &Rational,
    ) {
        self.x[column] = self.x[column].sub(&delta.mul(coeff));
        self.track_column_feasibility(column);
    }

    // make_column_feasible: moves the value of a column into its bounds, and returns the move.
    pub fn make_column_feasible(&mut self, column: usize) -> Option<Impq> {
        let value = &self.x[column];
        let lower = &self.lower_bounds[column];
        let upper = &self.upper_bounds[column];
        let target = match *self.column_types.get(column) {
            COLUMN_FIXED if value != lower => Some(lower),
            COLUMN_BOXED if value.compare(lower) == Ordering::Less => Some(lower),
            COLUMN_BOXED if value.compare(upper) == Ordering::Greater => Some(upper),
            COLUMN_LOWER if value.compare(lower) == Ordering::Less => Some(lower),
            COLUMN_UPPER if value.compare(upper) == Ordering::Greater => Some(upper),
            _ => None,
        }?
        .clone();
        let delta = target.sub(value);
        self.x[column] = target;
        Some(delta)
    }

    pub fn change_basis(&mut self, entering: usize, leaving: usize) {
        let place_in_basis = self.heading[leaving];
        let place_in_non_basis = -self.heading[entering] - 1;
        self.heading[entering] = place_in_basis;
        self.basis[place_in_basis as usize] = entering;
        self.heading[leaving] = -place_in_non_basis - 1;
        self.nbasis[place_in_non_basis as usize] = leaving;
    }

    pub fn change_basis_unconditionally(&mut self, entering: usize, leaving: usize) {
        let mut place_in_non_basis = -1 - self.heading[entering];
        if place_in_non_basis >= self.nbasis.len() as i64 {
            place_in_non_basis = self.nbasis.len() as i64;
            self.heading[entering] = place_in_non_basis;
            self.nbasis.push(entering);
        }
        let place_in_basis = self.heading[leaving];
        self.heading[entering] = place_in_basis;
        self.basis[place_in_basis as usize] = entering;
        self.heading[leaving] = -place_in_non_basis - 1;
        self.nbasis[place_in_non_basis as usize] = leaving;
    }

    fn divide_row_by_pivot(&mut self, pivot_row: usize, pivot_column: usize) -> bool {
        let row = &mut self.matrix.rows[pivot_row];
        let Some(pivot_index) = row.iter().position(|cell| cell.column == pivot_column) else {
            return false;
        };
        if row[pivot_index].coeff.is_zero() {
            return false;
        }
        let coeff = row[pivot_index].coeff.clone();
        for cell in row.iter_mut() {
            if cell.column != pivot_column {
                cell.coeff = cell.coeff.div(&coeff);
            }
        }
        row[pivot_index].coeff = coeff.div(&coeff);
        true
    }

    // pivot_column_tableau: makes the column a unit column with its one in the pivot row.
    pub fn pivot_column_tableau(&mut self, column: usize, pivot_row: usize) -> bool {
        if !self.divide_row_by_pivot(pivot_row, column) {
            return false;
        }
        self.settings.stats.pivots += 1;
        let matrix = &mut self.matrix;
        let Some(pivot_index) = matrix.columns[column]
            .iter()
            .position(|cell| cell.row == pivot_row)
        else {
            return false;
        };
        if pivot_index != 0 {
            let first = matrix.columns[column][0];
            matrix.columns[column].swap(0, pivot_index);
            let head = matrix.columns[column][0];
            matrix.rows[pivot_row][head.offset].offset = 0;
            matrix.rows[first.row][first.offset].offset = pivot_index;
        }
        while matrix.columns[column].len() > 1 {
            let cell = *matrix.columns[column]
                .last()
                .expect("the column has a cell");
            if self.is_recording_touched_rows {
                self.touched_rows.add(cell.row);
            }
            matrix.pivot_row_to_row_given_cell(pivot_row, cell, column);
        }
        if let Some(reduced_costs) = self.reduced_costs.as_mut() {
            CoreSolver::pivot_to_reduced_costs(&self.matrix, reduced_costs, pivot_row, column);
        }
        true
    }

    // pivot_to_reduced_costs_tableau: eliminates the reduced cost of the column that enters.
    fn pivot_to_reduced_costs(
        matrix: &StaticMatrix,
        reduced_costs: &mut [Rational],
        pivot_row: usize,
        column: usize,
    ) {
        let alpha = reduced_costs[column].clone();
        if alpha.is_zero() {
            return;
        }
        for cell in &matrix.rows[pivot_row] {
            if cell.column != column {
                reduced_costs[cell.column] =
                    reduced_costs[cell.column].sub(&alpha.mul(&cell.coeff));
            }
        }
        reduced_costs[column] = Rational::zero();
    }

    pub fn pivot(&mut self, entering: usize, leaving: usize) {
        self.pivot_column_tableau(entering, self.heading[leaving] as usize);
        self.change_basis(entering, leaving);
    }

    pub fn transpose_rows(&mut self, first: usize, second: usize) {
        self.basis.swap(first, second);
        let first_basic = self.basis[first];
        let second_basic = self.basis[second];
        self.heading.swap(first_basic, second_basic);
        self.matrix.transpose_rows(first, second);
    }

    // The simplex.

    fn needs_to_grow(&self, basic: usize) -> bool {
        let column_type = *self.column_types.get(basic);
        (column_type == COLUMN_FIXED || column_type == COLUMN_LOWER || column_type == COLUMN_BOXED)
            && self.x[basic].compare(&self.lower_bounds[basic]) == Ordering::Less
    }

    pub fn inf_sign_of_column(&self, basic: usize) -> i32 {
        match *self.column_types.get(basic) {
            COLUMN_FREE => 0,
            COLUMN_LOWER => 1,
            COLUMN_FIXED | COLUMN_BOXED => {
                if self.x[basic].compare(&self.upper_bounds[basic]) == Ordering::Greater {
                    -1
                } else {
                    1
                }
            }
            _ => -1,
        }
    }

    fn is_above_lower(&self, column: usize) -> bool {
        self.x[column].compare(&self.lower_bounds[column]) == Ordering::Greater
    }

    fn is_below_upper(&self, column: usize) -> bool {
        self.x[column].compare(&self.upper_bounds[column]) == Ordering::Less
    }

    fn monoid_can_decrease(&self, cell: &RowCell) -> bool {
        let column = cell.column;
        match *self.column_types.get(column) {
            COLUMN_FREE => true,
            COLUMN_FIXED => false,
            COLUMN_LOWER => !cell.coeff.is_positive() || self.is_above_lower(column),
            COLUMN_UPPER => cell.coeff.is_positive() || self.is_below_upper(column),
            _ => {
                if cell.coeff.is_positive() {
                    self.is_above_lower(column)
                } else {
                    self.is_below_upper(column)
                }
            }
        }
    }

    fn monoid_can_increase(&self, cell: &RowCell) -> bool {
        let column = cell.column;
        match *self.column_types.get(column) {
            COLUMN_FREE => true,
            COLUMN_FIXED => false,
            COLUMN_LOWER => !cell.coeff.is_negative() || self.is_above_lower(column),
            COLUMN_UPPER => cell.coeff.is_negative() || self.is_below_upper(column),
            _ => {
                if cell.coeff.is_negative() {
                    self.is_above_lower(column)
                } else {
                    self.is_below_upper(column)
                }
            }
        }
    }

    fn get_num_of_not_free_basic_dependent_vars(
        &self,
        column: usize,
        bound: usize,
        basic: usize,
    ) -> usize {
        let mut result = 0;
        for cell in &self.matrix.columns[column] {
            let basic_for_row = self.basis[cell.row];
            if basic_for_row == basic {
                continue;
            }
            if *self.column_types.get(basic_for_row) != COLUMN_FREE {
                let previous = result;
                result += 1;
                if previous > bound {
                    return result;
                }
            }
        }
        result
    }

    // find_beneficial_entering_tableau_rows: the offset in the row of the entering column's cell,
    // or None.
    fn find_beneficial_entering(&mut self, row_index: usize) -> Option<usize> {
        let basic = self.basis[row_index];
        let is_growing = self.needs_to_grow(basic);
        let can_move = |core: &CoreSolver<'l>, cell: &RowCell| {
            cell.column != basic
                && if is_growing {
                    core.monoid_can_decrease(cell)
                } else {
                    core.monoid_can_increase(cell)
                }
        };
        let row_length = self.matrix.rows[row_index].len();
        if self.is_bland_mode {
            let mut choice: Option<usize> = None;
            for index in 0..row_length {
                let cell = &self.matrix.rows[row_index][index];
                if can_move(self, cell)
                    && choice.is_none_or(|choice| {
                        cell.column < self.matrix.rows[row_index][choice].column
                    })
                {
                    choice = Some(index);
                }
            }
            if choice.is_none() {
                self.inf_row_index = row_index;
            }
            return choice;
        }
        let mut choice: Option<usize> = None;
        let mut num_choices: u32 = 0;
        let mut min_non_free = usize::MAX;
        let mut best_column_size = usize::MAX;
        for index in 0..row_length {
            let cell = &self.matrix.rows[row_index][index];
            if !can_move(self, cell) {
                continue;
            }
            let column = cell.column;
            let not_free =
                self.get_num_of_not_free_basic_dependent_vars(column, min_non_free, basic);
            let column_size = self.matrix.columns[column].len();
            if not_free < min_non_free
                || (not_free == min_non_free && column_size < best_column_size)
            {
                min_non_free = not_free;
                best_column_size = column_size;
                choice = Some(index);
                num_choices = 1;
            } else if not_free == min_non_free && column_size == best_column_size {
                num_choices += 1;
                if self.settings.get_random_next_below(num_choices) == 0 {
                    choice = Some(index);
                }
            }
        }
        if choice.is_none() {
            self.inf_row_index = row_index;
        }
        choice
    }

    fn get_val_for_leaving(&self, column: usize) -> Impq {
        match *self.column_types.get(column) {
            COLUMN_FIXED | COLUMN_UPPER => self.upper_bounds[column].clone(),
            COLUMN_BOXED => {
                if self.x[column].compare(&self.upper_bounds[column]) == Ordering::Greater {
                    self.upper_bounds[column].clone()
                } else {
                    self.lower_bounds[column].clone()
                }
            }
            _ => self.lower_bounds[column].clone(),
        }
    }

    fn one_iteration_tableau_rows(&mut self) {
        if self.inf_heap.size() == 0 {
            self.status = LP_OPTIMAL;
            return;
        }
        let leaving = self.inf_heap.get_min();
        if !self.is_bland_mode {
            if self.left_basis.has(leaving) {
                self.left_basis_repeated += 1;
                if self.left_basis_repeated > BLAND_MODE_THRESHOLD {
                    self.is_bland_mode = true;
                }
            } else {
                self.left_basis.add(leaving);
            }
        }
        let row_index = self.heading[leaving] as usize;
        let Some(entering_offset) = self.find_beneficial_entering(row_index) else {
            self.status = LP_INFEASIBLE;
            return;
        };
        if self.settings.is_canceled() {
            self.status = LP_CANCELLED;
            return;
        }
        let entering_cell = &self.matrix.rows[row_index][entering_offset];
        let entering = entering_cell.column;
        let new_value = self.get_val_for_leaving(leaving);
        let theta = self.x[leaving].sub(&new_value).div(&entering_cell.coeff);
        self.x[leaving] = new_value;
        self.inf_heap.erase(leaving);
        self.x[entering] = self.x[entering].add(&theta);
        for index in 0..self.matrix.columns[entering].len() {
            let cell = self.matrix.columns[entering][index];
            let basic = self.basis[cell.row];
            if basic != leaving {
                let coeff = self.matrix.get_val(&cell).clone();
                self.submul_from_x_and_track_feasibility(basic, &theta, &coeff);
            }
        }
        self.pivot_column_tableau(entering, self.heading[leaving] as usize);
        self.change_basis(entering, leaving);
        self.track_column_feasibility(entering);
        if self.is_feasible() {
            self.status = LP_OPTIMAL;
        }
    }

    // lp_primal_core_solver::solve, looking only for a feasible solution.
    fn solve_tableau(&mut self) {
        if self.is_feasible() {
            self.status = LP_FEASIBLE;
            return;
        }
        self.is_bland_mode = false;
        self.left_basis.clear();
        self.left_basis_repeated = 0;
        loop {
            if self.settings.is_canceled() {
                self.status = LP_CANCELLED;
                return;
            }
            self.one_iteration_tableau_rows();
            if self.status == LP_OPTIMAL
                || self.status == LP_INFEASIBLE
                || self.status == LP_CANCELLED
                || self.is_feasible()
            {
                return;
            }
        }
    }

    // lar_core_solver::solve.
    pub fn solve(&mut self) {
        if self.is_feasible() {
            self.status = LP_OPTIMAL;
            return;
        }
        self.status = LP_UNKNOWN;
        self.solve_tableau();
        if self.status == LP_INFEASIBLE {
            let basic = self.basis[self.inf_row_index];
            self.infeasible_sum_sign = self.inf_sign_of_column(basic);
            self.infeasible_combination = self.matrix.rows[self.inf_row_index]
                .iter()
                .map(|cell| (cell.coeff.clone(), cell.column))
                .collect();
        } else if self.status != LP_CANCELLED {
            self.status = LP_OPTIMAL;
        }
    }

    pub fn push_scope(&mut self) {
        self.column_types.push_scope();
    }

    pub fn pop_scope(&mut self, count: usize) {
        self.column_types.pop_scope(count);
        let column_count = self.matrix.get_column_count();
        self.x.truncate(column_count);
        self.infeasible_combination.clear();
    }
}
