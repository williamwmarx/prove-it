// Ported from Z3 (src/math/lp/lar_solver.h, src/math/lp/lar_solver.cpp, src/math/lp/column.h,
// src/math/lp/var_register.h), MIT license, see z3-license.txt. Columns for theory variables and
// for terms, whose rows the tableau keeps, bounds with dependencies on the constraints that set
// them, and the push and pop of all of it.
//
// How the TypeScript's shared objects and callbacks are held here:
// - `core` owns the settings and the touched rows, which TypeScript shares between the two.
// - The trail of closures is a Vec of `LarUndo`, applied in the same LIFO order by `pop`.
// - A column's term is an index into `terms` (both grow and shrink together), not a shared object.
// - `onChangedBounds` (nla's) is `is_reporting_changed_bounds`: findFeasibleSolution appends the
//   columns it would pass to `changed_bounds_pending`, which nla drains.
// - The Diophantine solver's `onAddTerm`/`onColumnBoundUpdate` are `dio_hooks`: the state its two
//   callbacks touch, with the callbacks as LarSolver methods called where TypeScript calls them
//   and their trail closures as `LarUndo` variants. Terms are referenced by their column, which
//   identifies a live term as the object does. int-cube's save, clear and restore of onAddTerm is
//   `is_add_term_hook_suspended`.
// - nla_throttle's set of lemma signatures, whose undo is this trail, lives here.
use std::cmp::Ordering;
use std::collections::{BTreeSet, HashMap, HashSet};

use prove_num::Rational;

use crate::lp::constraints::{
    ConstraintKind, ConstraintSet, KIND_EQ, KIND_GE, KIND_GT, KIND_LE, KIND_LT,
};
use crate::lp::containers::{IndexedUintSet, StackedVector};
use crate::lp::core_solver::{
    COLUMN_BOXED, COLUMN_FIXED, COLUMN_FREE, COLUMN_LOWER, COLUMN_UPPER, ColumnType, CoreSolver,
    LP_CANCELLED, LP_FEASIBLE, LP_INFEASIBLE, LP_OPTIMAL, LP_UNKNOWN, LpStatus,
};
use crate::lp::dependency::{Dependency, linearize, mk_join};
use crate::lp::explanation::Explanation;
use crate::lp::lar_term::LarTerm;
use crate::lp::lp_settings::LpSettings;
use crate::lp::numeric_pair::Impq;
use crate::lp::static_matrix::RowCell;
use crate::util::error::SmtError;

pub const NULL_LPVAR: usize = usize::MAX;

struct AdjustedBound {
    kind: ConstraintKind,
    bound: Rational,
}

// The column of a term, under its normalized term, with the first coefficient it was divided by.
pub struct NormalizedTermColumn {
    pub coeff: Rational,
    pub column: usize,
}

pub struct Column {
    pub lower_witness: Dependency,
    pub upper_witness: Dependency,
    // The index of the column's term in `terms`.
    pub term: Option<usize>,
}

// has_lower_bound and has_upper_bound: the witness, value and strictness of a bound.
pub struct BoundInfo {
    pub dep: Dependency,
    pub value: Rational,
    pub is_strict: bool,
}

// The state of the Diophantine solver that lar_solver's callbacks touch.
#[derive(Default)]
pub struct DioHooks {
    // m_some_terms_are_ignored: a term was not integral or had a big number, so the GCD test and
    // Gomory cuts run.
    pub has_ignored_terms: bool,
    // The columns of the terms added since the last check, and of those in the equations.
    pub added_terms: Vec<usize>,
    pub active_terms: Vec<usize>,
    pub changed_terms: IndexedUintSet,
    pub terms_to_tighten: IndexedUintSet,
    pub changed_fixed_columns: IndexedUintSet,
}

// The closures of TypeScript's trail.
enum LarUndo {
    AddColumn,
    UpperBound {
        column: usize,
        bound: Impq,
        witness: Dependency,
    },
    LowerBound {
        column: usize,
        bound: Impq,
        witness: Dependency,
    },
    // The Diophantine solver's undoAddTerm of the term of the column.
    DioAddTerm(usize),
    // The Diophantine solver's changedFixedColumns.add(column).
    DioChangedFixedColumn(usize),
    // nla_throttle's seen.delete(key).
    NlaThrottleSeen([u32; 8]),
}

fn get_term_key(term: &LarTerm) -> String {
    let mut entries: Vec<String> = term
        .iter()
        .map(|entry| format!("{}:{}", entry.0, entry.1))
        .collect();
    // TypeScript's comparator-less sort compares UTF-16 units, byte order for ASCII.
    debug_assert!(entries.iter().all(|entry| entry.is_ascii()));
    entries.sort();
    entries.join(",")
}

pub struct LarSolver<'l> {
    pub core: CoreSolver<'l>,
    pub constraints: ConstraintSet,
    pub columns: Vec<Column>,
    pub terms: Vec<LarTerm>,
    pub columns_with_changed_bounds: IndexedUintSet,
    pub row_bounds_to_replay: Vec<usize>,
    pub status: LpStatus,
    pub crossed_bounds_column: usize,
    pub crossed_bounds_deps: Dependency,
    external_to_local: HashMap<usize, usize>,
    local_to_external: Vec<usize>,
    local_is_int: Vec<bool>,
    trail: Vec<LarUndo>,
    trail_scopes: Vec<usize>,
    usage_in_terms: StackedVector<usize>,
    fixed_var_table_int: HashMap<String, usize>,
    fixed_var_table_real: HashMap<String, usize>,
    fixed_base_var_set: IndexedUintSet,
    normalized_terms_to_columns: HashMap<String, NormalizedTermColumn>,
    is_registering_terms: bool,
    // m_delta: zero until init_model sets it.
    delta: Rational,
    // The callback of nla for the columns whose bounds changed.
    pub is_reporting_changed_bounds: bool,
    pub changed_bounds_pending: Vec<usize>,
    // m_add_term_callback and m_update_column_bound_callback, which the Diophantine solver sets.
    pub dio_hooks: Option<DioHooks>,
    pub is_add_term_hook_suspended: bool,
    // nla_throttle's m_seen: the lemma signatures of the current scope.
    pub nla_throttle_seen: HashSet<[u32; 8]>,
}

impl<'l> LarSolver<'l> {
    pub fn new(is_canceled: Box<dyn Fn() -> bool + 'l>) -> LarSolver<'l> {
        let mut core = CoreSolver::new(LpSettings::new(is_canceled));
        core.is_recording_touched_rows = true;
        LarSolver {
            core,
            constraints: ConstraintSet::default(),
            columns: Vec::new(),
            terms: Vec::new(),
            columns_with_changed_bounds: IndexedUintSet::new(),
            row_bounds_to_replay: Vec::new(),
            status: LP_UNKNOWN,
            crossed_bounds_column: NULL_LPVAR,
            crossed_bounds_deps: None,
            external_to_local: HashMap::new(),
            local_to_external: Vec::new(),
            local_is_int: Vec::new(),
            trail: Vec::new(),
            trail_scopes: Vec::new(),
            usage_in_terms: StackedVector::default(),
            fixed_var_table_int: HashMap::new(),
            fixed_var_table_real: HashMap::new(),
            fixed_base_var_set: IndexedUintSet::new(),
            normalized_terms_to_columns: HashMap::new(),
            is_registering_terms: false,
            delta: Rational::zero(),
            is_reporting_changed_bounds: false,
            changed_bounds_pending: Vec::new(),
            dio_hooks: None,
            is_add_term_hook_suspended: false,
            nla_throttle_seen: HashSet::new(),
        }
    }

    pub fn settings(&self) -> &LpSettings<'l> {
        &self.core.settings
    }

    pub fn settings_mut(&mut self) -> &mut LpSettings<'l> {
        &mut self.core.settings
    }

    pub fn get_column_count(&self) -> usize {
        self.core.matrix.get_column_count()
    }

    pub fn get_row_count(&self) -> usize {
        self.core.matrix.get_row_count()
    }

    pub fn get_value(&self, column: usize) -> &Impq {
        &self.core.x[column]
    }

    pub fn get_lower_bound(&self, column: usize) -> &Impq {
        &self.core.lower_bounds[column]
    }

    pub fn get_upper_bound(&self, column: usize) -> &Impq {
        &self.core.upper_bounds[column]
    }

    pub fn is_int(&self, column: usize) -> bool {
        self.local_is_int[column]
    }

    pub fn is_base(&self, column: usize) -> bool {
        self.core.is_base(column)
    }

    pub fn is_fixed(&self, column: usize) -> bool {
        self.core.is_fixed(column)
    }

    pub fn is_free(&self, column: usize) -> bool {
        self.core.get_column_type(column) == COLUMN_FREE
    }

    pub fn has_term(&self, column: usize) -> bool {
        self.columns[column].term.is_some()
    }

    pub fn get_term(&self, column: usize) -> Result<&LarTerm, SmtError> {
        match self.columns[column].term {
            Some(index) => Ok(&self.terms[index]),
            None => Err(SmtError::Invariant(format!("column {column} has no term"))),
        }
    }

    pub fn external_to_local_column(&self, external: usize) -> usize {
        self.external_to_local
            .get(&external)
            .copied()
            .unwrap_or(NULL_LPVAR)
    }

    pub fn get_external(&self, column: usize) -> usize {
        self.local_to_external[column]
    }

    pub fn is_feasible(&self) -> bool {
        self.status == LP_OPTIMAL || self.status == LP_FEASIBLE
    }

    pub fn get_row(&self, row_index: usize) -> &[RowCell] {
        &self.core.matrix.rows[row_index]
    }

    pub fn get_usage_in_terms(&self, column: usize) -> usize {
        if column < self.usage_in_terms.values.len() {
            *self.usage_in_terms.get(column)
        } else {
            0
        }
    }

    // Columns.

    fn register_external(&mut self, external: usize, is_int: bool) {
        let local = self.local_to_external.len();
        self.local_to_external.push(external);
        self.local_is_int.push(is_int);
        if external != NULL_LPVAR {
            self.external_to_local.insert(external, local);
        }
    }

    fn add_new_var_to_core_fields(&mut self, is_basic: bool) {
        self.core.add_column(is_basic);
        if is_basic {
            self.add_touched_row(self.get_row_count() - 1);
        }
    }

    fn undo_add_column(&mut self) {
        let column = self.columns.len() - 1;
        if let Some(index) = self.columns[column].term {
            if self.is_registering_terms {
                let key = get_normalized_term_key(&self.terms[index]).0;
                self.normalized_terms_to_columns.remove(&key);
            }
            self.terms.pop();
        }
        self.remove_last_column_from_tableau();
        self.columns.pop();
        let index = self.columns.len();
        if self.columns_with_changed_bounds.has(index) {
            self.columns_with_changed_bounds.delete(index);
        }
    }

    pub fn add_var(&mut self, external: usize, is_int: bool) -> usize {
        if let Some(existing) = self.external_to_local.get(&external) {
            return *existing;
        }
        let column = self.get_column_count();
        self.columns.push(Column {
            lower_witness: None,
            upper_witness: None,
            term: None,
        });
        self.trail.push(LarUndo::AddColumn);
        while self.usage_in_terms.values.len() <= column {
            self.usage_in_terms.push(0);
        }
        self.register_external(external, is_int);
        self.core.column_types.push(COLUMN_FREE);
        self.add_new_var_to_core_fields(false);
        column
    }

    fn is_term_int(&self, term: &LarTerm) -> bool {
        term.iter()
            .all(|entry| self.is_int(entry.0) && entry.1.is_int())
    }

    // subst_known_terms: replaces term columns by their terms, the smallest column first.
    fn subst_known_terms(&self, term: &mut LarTerm) {
        let mut seen = BTreeSet::new();
        for entry in term.iter() {
            if self.has_term(entry.0) {
                seen.insert(entry.0);
            }
        }
        while let Some(column) = seen.pop_first() {
            let other = &self.terms[self.columns[column].term.expect("a seen column has a term")];
            for entry in other.iter() {
                if self.has_term(entry.0) {
                    seen.insert(entry.0);
                }
            }
            term.subst_by_term(other, column);
        }
    }

    pub fn add_term(&mut self, coeffs: &[(usize, Rational)], external: usize) -> usize {
        let mut term = LarTerm::from_entries(coeffs.iter().map(|entry| (entry.0, &entry.1)));
        self.subst_known_terms(&mut term);
        let column = self.get_column_count();
        let is_int = self.is_term_int(&term);
        self.register_external(external, is_int);
        term.column = column;
        self.terms.push(term);
        let term_index = self.terms.len() - 1;
        self.columns.push(Column {
            lower_witness: None,
            upper_witness: None,
            term: Some(term_index),
        });
        self.trail.push(LarUndo::AddColumn);
        self.core.column_types.push(COLUMN_FREE);
        self.add_new_var_to_core_fields(true);
        self.core.matrix.fill_last_row_with_pivoting(
            &self.terms[term_index],
            column,
            &self.core.heading,
        );
        self.core.x[column] = self.get_basic_var_value_from_row(self.get_row_count() - 1);
        let term_columns: Vec<usize> = self.terms[term_index].iter().map(|entry| entry.0).collect();
        for term_column in term_columns {
            while self.usage_in_terms.values.len() <= term_column {
                self.usage_in_terms.push(0);
            }
            let usage = *self.usage_in_terms.get(term_column);
            self.usage_in_terms.set(term_column, usage + 1);
        }
        if self.is_registering_terms {
            self.register_normalized_term(term_index, column);
        }
        if !self.is_add_term_hook_suspended && self.dio_hooks.is_some() {
            self.add_term_callback(column);
        }
        column
    }

    fn get_basic_var_value_from_row(&self, row_index: usize) -> Impq {
        let basic = self.core.basis[row_index];
        let mut result = Impq::zero();
        for cell in &self.core.matrix.rows[row_index] {
            if cell.column == basic {
                continue;
            }
            let value = &self.core.x[cell.column];
            if !value.is_zero() {
                result = result.sub(&value.mul(&cell.coeff));
            }
        }
        result
    }

    fn register_normalized_term(&mut self, term_index: usize, column: usize) {
        let (key, coeff) = get_normalized_term_key(&self.terms[term_index]);
        self.normalized_terms_to_columns
            .entry(key)
            .or_insert(NormalizedTermColumn { coeff, column });
    }

    pub fn register_existing_terms(&mut self) {
        if !self.is_registering_terms {
            for index in 0..self.terms.len() {
                let column = self.terms[index].column;
                self.register_normalized_term(index, column);
            }
        }
        self.is_registering_terms = true;
    }

    pub fn fetch_normalized_term_column(&self, term: &LarTerm) -> Option<&NormalizedTermColumn> {
        self.normalized_terms_to_columns.get(&get_term_key(term))
    }

    // Removing the last column on pop.

    fn remove_last_column_from_tableau(&mut self) {
        let column = self.core.matrix.get_column_count() - 1;
        if self.columns[column].term.is_some() {
            let core = &mut self.core;
            let row_index = core.matrix.get_row_count() - 1;
            let last_column = &core.matrix.columns[column];
            let mut non_zero_index = usize::MAX;
            let mut is_in_row = false;
            for index in (0..last_column.len()).rev() {
                if last_column[index].row == row_index {
                    is_in_row = true;
                    break;
                }
                non_zero_index = index;
            }
            if !is_in_row {
                let row = last_column[non_zero_index].row;
                core.transpose_rows(row, row_index);
            }
            if core.heading[column] < 0 {
                core.pivot_column_tableau(column, row_index);
            }
            for index in (0..core.matrix.rows[row_index].len()).rev() {
                core.matrix.remove_element(row_index, index);
            }
            core.matrix.rows.pop();
            core.matrix.pop_column();
            if core.heading[column] < 0 {
                let leaving = core.basis[core.matrix.get_row_count()];
                core.change_basis_unconditionally(column, leaving);
            }
        } else {
            self.core.matrix.pop_column();
        }
        self.core.remove_last_column(column);
    }

    // Bounds.

    fn set_upper_bound_witness(&mut self, column: usize, dep: Dependency, bound: Impq) {
        let saved_bound = std::mem::replace(&mut self.core.upper_bounds[column], bound);
        let saved_witness = std::mem::replace(&mut self.columns[column].upper_witness, dep);
        self.trail.push(LarUndo::UpperBound {
            column,
            bound: saved_bound,
            witness: saved_witness,
        });
        self.columns_with_changed_bounds.add(column);
    }

    fn set_lower_bound_witness(&mut self, column: usize, dep: Dependency, bound: Impq) {
        let saved_bound = std::mem::replace(&mut self.core.lower_bounds[column], bound);
        let saved_witness = std::mem::replace(&mut self.columns[column].lower_witness, dep);
        self.trail.push(LarUndo::LowerBound {
            column,
            bound: saved_bound,
            witness: saved_witness,
        });
        self.columns_with_changed_bounds.add(column);
    }

    fn set_crossed_bounds(&mut self, column: usize, is_lower: bool, dep: &Dependency) {
        if self.crossed_bounds_column != NULL_LPVAR {
            return;
        }
        self.status = LP_INFEASIBLE;
        self.crossed_bounds_column = column;
        let info = &self.columns[column];
        let witness = if is_lower {
            &info.lower_witness
        } else {
            &info.upper_witness
        };
        self.crossed_bounds_deps = mk_join(witness, dep);
    }

    // adjust_bound_for_int: a strict or fractional bound on an integer column, rounded.
    fn adjust_bound_for_int(
        &self,
        column: usize,
        kind: ConstraintKind,
        bound: &Rational,
    ) -> AdjustedBound {
        if !self.is_int(column) || bound.is_int() {
            return AdjustedBound {
                kind,
                bound: bound.clone(),
            };
        }
        if kind == KIND_LT || kind == KIND_LE {
            return AdjustedBound {
                kind: KIND_LE,
                bound: bound.floor(),
            };
        }
        if kind == KIND_GT || kind == KIND_GE {
            return AdjustedBound {
                kind: KIND_GE,
                bound: bound.ceil(),
            };
        }
        AdjustedBound {
            kind,
            bound: bound.clone(),
        }
    }

    pub fn mk_var_bound(&mut self, column: usize, kind: ConstraintKind, rhs: &Rational) -> usize {
        let adjusted = self.adjust_bound_for_int(column, kind, rhs);
        self.constraints
            .add(column, adjusted.kind, Impq::from_x(adjusted.bound))
    }

    // constraint_is_redundant: the current bound of the column is at least as strong.
    pub fn constraint_is_redundant(&self, index: usize) -> bool {
        let constraint = &self.constraints.constraints[index];
        let column = constraint.column;
        let rhs = &constraint.rhs;
        if self.is_int(column) && !rhs.x.is_int() {
            return false;
        }
        let kind = constraint.kind;
        if kind == KIND_LE || kind == KIND_LT {
            if !self.core.has_upper_bound(column) {
                return false;
            }
            let upper = self.get_upper_bound(column);
            if upper.x != rhs.x {
                return upper.x.compare(&rhs.x) == Ordering::Less;
            }
            let shifted = if kind == KIND_LT {
                upper.y.add(&Rational::one())
            } else {
                upper.y.clone()
            };
            return shifted.compare(&rhs.y) != Ordering::Greater;
        }
        if kind == KIND_GE || kind == KIND_GT {
            if !self.core.has_lower_bound(column) {
                return false;
            }
            let lower = self.get_lower_bound(column);
            if lower.x != rhs.x {
                return lower.x.compare(&rhs.x) == Ordering::Greater;
            }
            let shifted = if kind == KIND_GT {
                rhs.y.add(&Rational::one())
            } else {
                rhs.y.clone()
            };
            return shifted.compare(&lower.y) != Ordering::Greater;
        }
        false
    }

    pub fn activate(&mut self, index: usize) {
        self.constraints.activate(index);
        let constraint = &self.constraints.constraints[index];
        let column = constraint.column;
        let kind = constraint.kind;
        let rhs = constraint.rhs.clone();
        let dep = constraint.dep.clone();
        self.update_column_type_and_bound(column, kind, &rhs, dep);
    }

    // activate_check_on_equal: also the other column fixed to the same value, if there is one.
    pub fn activate_check_on_equal(&mut self, index: usize) -> usize {
        self.activate(index);
        let column = self.constraints.constraints[index].column;
        if !self.is_fixed(column) {
            return NULL_LPVAR;
        }
        let bound = self.get_lower_bound(column);
        if !bound.y.is_zero() {
            return NULL_LPVAR;
        }
        let key = bound.x.to_string();
        let table = if self.is_int(column) {
            &mut self.fixed_var_table_int
        } else {
            &mut self.fixed_var_table_real
        };
        let Some(other) = table.get(&key).copied() else {
            table.insert(key, column);
            return NULL_LPVAR;
        };
        if other != column && self.is_fixed(other) {
            other
        } else {
            NULL_LPVAR
        }
    }

    pub fn find_in_fixed_tables(&self, value: &Rational, is_int: bool) -> Option<usize> {
        let table = if is_int {
            &self.fixed_var_table_int
        } else {
            &self.fixed_var_table_real
        };
        table.get(&value.to_string()).copied()
    }

    pub fn update_column_type_and_bound(
        &mut self,
        column: usize,
        input_kind: ConstraintKind,
        rhs: &Impq,
        dep: Dependency,
    ) {
        let adjusted = self.adjust_bound_for_int(column, input_kind, &rhs.x);
        let kind = adjusted.kind;
        let has_upper = self.core.has_upper_bound(column);
        let has_lower = self.core.has_lower_bound(column);
        let is_upper_kind = kind == KIND_LE || kind == KIND_LT;
        let is_lower_kind = kind == KIND_GE || kind == KIND_GT;
        let y = if kind == KIND_LT {
            rhs.y.sub(&Rational::one())
        } else if kind == KIND_GT {
            rhs.y.add(&Rational::one())
        } else {
            rhs.y.clone()
        };
        let bound = Impq::new(
            adjusted.bound,
            if kind == KIND_EQ { Rational::zero() } else { y },
        );
        let lower = self.get_lower_bound(column).clone();
        let upper = self.get_upper_bound(column).clone();
        let set_type = |solver: &mut LarSolver<'l>, column_type: ColumnType| {
            solver.core.column_types.set(column, column_type)
        };
        if is_upper_kind {
            if has_lower && bound.compare(&lower) == Ordering::Less {
                self.set_crossed_bounds(column, true, &dep);
            } else if !has_upper || bound.compare(&upper) == Ordering::Less {
                let column_type = if has_lower {
                    if bound == lower {
                        COLUMN_FIXED
                    } else {
                        COLUMN_BOXED
                    }
                } else {
                    COLUMN_UPPER
                };
                self.set_upper_bound_witness(column, dep, bound);
                if !has_upper {
                    set_type(self, column_type);
                }
            }
        } else if is_lower_kind {
            if has_upper && bound.compare(&upper) == Ordering::Greater {
                self.set_crossed_bounds(column, false, &dep);
            } else if !has_lower || bound.compare(&lower) != Ordering::Less {
                let is_equal_to_upper = bound == upper;
                self.set_lower_bound_witness(column, dep, bound);
                if has_upper {
                    set_type(
                        self,
                        if is_equal_to_upper {
                            COLUMN_FIXED
                        } else {
                            COLUMN_BOXED
                        },
                    );
                } else if !has_lower {
                    set_type(self, COLUMN_LOWER);
                }
            }
        } else if kind == KIND_EQ {
            if has_upper && bound.compare(&upper) == Ordering::Greater {
                self.set_crossed_bounds(column, false, &dep);
            } else if has_lower && bound.compare(&lower) == Ordering::Less {
                self.set_crossed_bounds(column, true, &dep);
            } else {
                self.set_upper_bound_witness(column, dep.clone(), bound.clone());
                self.set_lower_bound_witness(column, dep, bound);
                set_type(self, COLUMN_FIXED);
            }
        }
        if has_upper && has_lower && self.get_lower_bound(column) == self.get_upper_bound(column) {
            set_type(self, COLUMN_FIXED);
        }
        if self.is_base(column) && self.is_fixed(column) {
            self.fixed_base_var_set.add(column);
        }
        if self.dio_hooks.is_some() {
            self.update_column_bound_callback(column);
        }
    }

    pub fn add_touched_row(&mut self, row_index: usize) {
        self.core.touched_rows.add(row_index);
    }

    pub fn add_column_rows_to_touched_rows(&mut self, column: usize) {
        for cell in &self.core.matrix.columns[column] {
            self.core.touched_rows.add(cell.row);
        }
    }

    // Solving.

    fn change_basic_columns_depending_on(&mut self, column: usize, delta: &Impq) {
        let core = &mut self.core;
        for index in 0..core.matrix.columns[column].len() {
            let cell = core.matrix.columns[column][index];
            let basic = core.basis[cell.row];
            let coeff = core.matrix.get_val(&cell).clone();
            core.submul_from_x_and_track_feasibility(basic, delta, &coeff);
        }
    }

    pub fn set_value_for_nbasic_column(&mut self, column: usize, value: Impq) {
        let delta = value.sub(&self.core.x[column]);
        self.core.x[column] = value;
        self.change_basic_columns_depending_on(column, &delta);
    }

    pub fn find_feasible_solution(&mut self) -> LpStatus {
        self.core.settings.stats.make_feasible += 1;
        if self.status == LP_INFEASIBLE {
            return self.status;
        }
        for index in 0..self.columns_with_changed_bounds.elems.len() {
            let column = self.columns_with_changed_bounds.elems[index];
            if self.core.is_base(column) {
                self.core.track_column_feasibility(column);
                continue;
            }
            if let Some(delta) = self.core.make_column_feasible(column) {
                self.change_basic_columns_depending_on(column, &delta);
            }
        }
        self.core.solve();
        self.status = self.core.status;
        if self.status == LP_INFEASIBLE || self.status == LP_CANCELLED {
            return self.status;
        }
        for index in 0..self.columns_with_changed_bounds.elems.len() {
            let column = self.columns_with_changed_bounds.elems[index];
            if self.core.is_base(column) {
                self.add_touched_row(self.core.heading[column] as usize);
            } else {
                self.add_column_rows_to_touched_rows(column);
            }
        }
        if self.is_reporting_changed_bounds {
            self.changed_bounds_pending
                .extend_from_slice(&self.columns_with_changed_bounds.elems);
        }
        self.columns_with_changed_bounds.clear();
        self.status
    }

    // get_infeasibility_explanation: the crossed bounds, or the bounds of the infeasible row.
    pub fn get_infeasibility_explanation(&self, explanation: &mut Explanation) {
        explanation.clear();
        if self.crossed_bounds_column != NULL_LPVAR {
            for constraint in linearize(std::slice::from_ref(&self.crossed_bounds_deps)) {
                explanation.add_pair(constraint as usize, Rational::minus_one());
            }
            return;
        }
        let sign = self.core.infeasible_sum_sign;
        if sign == 0 {
            return;
        }
        for entry in &self.core.infeasible_combination {
            let adjusted_sign = if entry.0.is_positive() { sign } else { -sign };
            let info = &self.columns[entry.1];
            let dep = if adjusted_sign < 0 {
                &info.upper_witness
            } else {
                &info.lower_witness
            };
            for constraint in linearize(std::slice::from_ref(dep)) {
                explanation.add_pair(constraint as usize, entry.0.clone());
            }
        }
    }

    // remove_fixed_vars_from_base: pivots fixed basic columns out of the basis.
    pub fn remove_fixed_vars_from_base(&mut self) {
        let column_count = self.get_column_count();
        let to_remove = CoreSolver::without_touched_rows(
            self,
            |solver| &mut solver.core,
            |solver| {
                let mut to_remove = Vec::new();
                for index in 0..solver.fixed_base_var_set.elems.len() {
                    let column = solver.fixed_base_var_set.elems[index];
                    if column >= column_count || !solver.is_base(column) || !solver.is_fixed(column)
                    {
                        to_remove.push(column);
                        continue;
                    }
                    let row_index = solver.core.heading[column] as usize;
                    let entering = solver.core.matrix.rows[row_index]
                        .iter()
                        .map(|cell| cell.column)
                        .find(|entering| !solver.is_fixed(*entering));
                    if let Some(entering) = entering {
                        solver.core.pivot(entering, column);
                        to_remove.push(column);
                    }
                }
                to_remove
            },
        );
        for column in to_remove {
            self.fixed_base_var_set.delete(column);
        }
    }

    // remove_from_basis: pivots a basic column with the first non-fixed column of its row.
    pub fn remove_from_basis(&mut self, column: usize) -> bool {
        let row_index = self.core.heading[column] as usize;
        let entering = self.core.matrix.rows[row_index]
            .iter()
            .map(|cell| cell.column)
            .find(|entering| *entering != column && !self.is_fixed(*entering));
        let Some(entering) = entering else {
            return false;
        };
        self.core.pivot(entering, column);
        true
    }

    pub fn inside_bounds(&self, column: usize, value: &Impq) -> bool {
        let core = &self.core;
        if core.has_upper_bound(column)
            && value.compare(&core.upper_bounds[column]) == Ordering::Greater
        {
            return false;
        }
        !(core.has_lower_bound(column)
            && value.compare(&core.lower_bounds[column]) == Ordering::Less)
    }

    // try_to_patch: sets a column to a value unless the column or a basic column it moves is blocked,
    // reporting each changed column. The callbacks get the solver, which TypeScript's closures
    // reach through their own back-pointers.
    pub fn try_to_patch(
        &mut self,
        column: usize,
        value: &Rational,
        mut is_blocked: impl FnMut(&LarSolver<'l>, usize, &Impq) -> bool,
        mut change_report: impl FnMut(&LarSolver<'l>, usize),
    ) -> bool {
        if self.is_base(column) && !self.remove_from_basis(column) {
            return false;
        }
        let target = Impq::from_x(value.clone());
        if is_blocked(self, column, &target) {
            return false;
        }
        let delta = self.core.x[column].sub(&target);
        for cell in &self.core.matrix.columns[column] {
            let basic = self.core.basis[cell.row];
            let moved = delta
                .mul(self.core.matrix.get_val(cell))
                .add(&self.core.x[basic]);
            if is_blocked(self, basic, &moved) {
                return false;
            }
        }
        let change = target.sub(&self.core.x[column]);
        self.core.x[column] = target;
        change_report(self, column);
        for index in 0..self.core.matrix.columns[column].len() {
            let cell = self.core.matrix.columns[column][index];
            let basic = self.core.basis[cell.row];
            let delta = change.mul(&self.core.matrix.get_val(&cell).neg());
            self.core
                .add_delta_to_x_and_track_feasibility(basic, &delta);
            change_report(self, basic);
        }
        true
    }

    pub fn move_non_basic_columns_to_bounds(&mut self) {
        let mut is_changed = false;
        for index in 0..self.core.nbasis.len() {
            let column = self.core.nbasis[index];
            if self.move_non_basic_column_to_bounds(column) {
                is_changed = true;
            }
        }
        if is_changed {
            self.find_feasible_solution();
        }
    }

    fn move_non_basic_column_to_bounds(&mut self, column: usize) -> bool {
        let core = &self.core;
        let value = &core.x[column];
        let lower = &core.lower_bounds[column];
        let upper = &core.upper_bounds[column];
        let target = match core.get_column_type(column) {
            COLUMN_BOXED => {
                if value == lower || value == upper {
                    return false;
                }
                lower.clone()
            }
            COLUMN_LOWER => {
                if value == lower {
                    return false;
                }
                lower.clone()
            }
            COLUMN_FIXED | COLUMN_UPPER => {
                if value == upper {
                    return false;
                }
                upper.clone()
            }
            _ => {
                if !self.is_int(column) || value.is_int() {
                    return false;
                }
                Impq::from_x(value.floor())
            }
        };
        self.set_value_for_nbasic_column(column, target);
        true
    }

    pub fn has_inf_int(&self) -> bool {
        (0..self.get_column_count())
            .any(|column| self.is_int(column) && !self.core.x[column].is_int())
    }

    // The model.

    // init_model: a δ that keeps strict bounds strict and distinct values distinct.
    pub fn init_model(&mut self) -> bool {
        if self.status != LP_OPTIMAL && self.status != LP_FEASIBLE {
            return false;
        }
        if self.columns_with_changed_bounds.size() > 0 {
            return false;
        }
        let core = &self.core;
        let mut delta = Rational::one();
        for column in 0..self.get_column_count() {
            if core.has_lower_bound(column) {
                update_delta(&mut delta, &core.lower_bounds[column], &core.x[column]);
            }
            if core.has_upper_bound(column) {
                update_delta(&mut delta, &core.x[column], &core.upper_bounds[column]);
            }
        }
        // TypeScript's map from the printed values to the values: only its size is compared, so
        // the distinct values in any order.
        let mut printed = HashSet::new();
        let mut pairs = Vec::new();
        for value in &core.x {
            if printed.insert(value.to_string()) {
                pairs.push(value);
            }
        }
        loop {
            let singles: HashSet<String> = pairs
                .iter()
                .map(|value| value.x.add(&delta.mul(&value.y)).to_string())
                .collect();
            if singles.len() == pairs.len() {
                break;
            }
            delta = delta.div(&Rational::from_i64(2));
        }
        self.delta = delta;
        true
    }

    pub fn get_model_value(&self, column: usize) -> Rational {
        let value = &self.core.x[column];
        value.x.add(&self.delta.mul(&value.y))
    }

    // has_value: the value of a column, or of the term of a column, when δ does not occur in it.
    pub fn get_exact_value(&self, column: usize) -> Option<Rational> {
        let Some(index) = self.columns[column].term else {
            let value = &self.core.x[column];
            return value.y.is_zero().then(|| value.x.clone());
        };
        let mut result = Rational::zero();
        for entry in self.terms[index].iter() {
            let value = &self.core.x[entry.0];
            if !value.y.is_zero() {
                return None;
            }
            result = result.add(&value.x.mul(entry.1));
        }
        Some(result)
    }

    // has_lower_bound and has_upper_bound: the witness, value and strictness of a bound.
    pub fn get_bound(&self, column: usize, is_upper: bool) -> Option<BoundInfo> {
        if column >= self.columns.len() {
            return None;
        }
        let info = &self.columns[column];
        let dep = if is_upper {
            &info.upper_witness
        } else {
            &info.lower_witness
        };
        dep.as_ref()?;
        let bound = if is_upper {
            &self.core.upper_bounds[column]
        } else {
            &self.core.lower_bounds[column]
        };
        Some(BoundInfo {
            dep: dep.clone(),
            value: bound.x.clone(),
            is_strict: if is_upper {
                bound.y.is_negative()
            } else {
                bound.y.is_positive()
            },
        })
    }

    // get_rid_of_inf_eps: the values with δ instantiated small enough to keep strict bounds strict.
    pub fn get_rid_of_inf_eps(&mut self) {
        let column_count = self.get_column_count();
        let core = &mut self.core;
        if core.x[..column_count].iter().all(|value| value.y.is_zero()) {
            return;
        }
        let mut delta = Rational::one();
        for column in 0..column_count {
            if core.has_lower_bound(column) {
                update_delta(&mut delta, &core.lower_bounds[column], &core.x[column]);
            }
            if core.has_upper_bound(column) {
                update_delta(&mut delta, &core.x[column], &core.upper_bounds[column]);
            }
        }
        for column in 0..column_count {
            let value = &core.x[column];
            if !value.y.is_zero() {
                let instantiated = Impq::from_x(value.x.add(&delta.mul(&value.y)));
                core.x[column] = instantiated;
            }
        }
    }

    // get_bound_constraint_witnesses_for_column: the witnesses of both bounds.
    pub fn get_bound_witnesses(&self, column: usize) -> Dependency {
        mk_join(
            &self.columns[column].lower_witness,
            &self.columns[column].upper_witness,
        )
    }

    // collect_more_rows_for_lp_propagation: the rows of the columns whose bounds nla changed.
    pub fn collect_more_rows_for_lp_propagation(&mut self) {
        for index in 0..self.columns_with_changed_bounds.elems.len() {
            let column = self.columns_with_changed_bounds.elems[index];
            if self.core.is_base(column) {
                self.add_touched_row(self.core.heading[column] as usize);
            } else {
                self.add_column_rows_to_touched_rows(column);
            }
        }
    }

    pub fn get_lower_witness(&self, column: usize) -> &Dependency {
        &self.columns[column].lower_witness
    }

    pub fn get_upper_witness(&self, column: usize) -> &Dependency {
        &self.columns[column].upper_witness
    }

    // The callbacks of the Diophantine solver.

    // addTermCallback.
    fn add_term_callback(&mut self, column: usize) {
        let is_int = self.is_int(column);
        let hooks = self
            .dio_hooks
            .as_mut()
            .expect("the add term callback has its hooks");
        if !is_int {
            hooks.has_ignored_terms = true;
            return;
        }
        hooks.added_terms.push(column);
        hooks.changed_terms.add(column);
        self.trail.push(LarUndo::DioAddTerm(column));
    }

    // updateColumnBoundCallback.
    fn update_column_bound_callback(&mut self, column: usize) {
        if !self.is_int(column) {
            return;
        }
        let has_term = self.has_term(column);
        let is_fixed = self.is_fixed(column);
        let hooks = self
            .dio_hooks
            .as_mut()
            .expect("the column bound callback has its hooks");
        if has_term {
            hooks.terms_to_tighten.add(column);
        }
        if !is_fixed {
            return;
        }
        hooks.changed_fixed_columns.add(column);
        self.trail.push(LarUndo::DioChangedFixedColumn(column));
    }

    // undoAddTerm: a term the equations do not hold yet leaves the added terms.
    fn undo_add_term(&mut self, column: usize) {
        let hooks = self
            .dio_hooks
            .as_mut()
            .expect("the undo of an added term has its hooks");
        if !hooks.active_terms.contains(&column) {
            if let Some(index) = hooks.added_terms.iter().rposition(|term| *term == column) {
                let last = *hooks.added_terms.last().expect("added terms is nonempty");
                hooks.added_terms[index] = last;
                hooks.added_terms.pop();
            }
            return;
        }
        // HACK: the rest of undoAddTerm needs the equations of the Diophantine solver, whose port
        // moves that state into DioHooks with this branch; until then no term is ever active.
        unreachable!("an active Diophantine term needs the Diophantine solver's port");
    }

    // nla_throttle's insert_new without the stats: whether the signature is new, recording it.
    pub fn insert_nla_throttle_seen(&mut self, key: [u32; 8]) -> bool {
        if !self.nla_throttle_seen.insert(key) {
            return false;
        }
        self.trail.push(LarUndo::NlaThrottleSeen(key));
        true
    }

    // Scopes.

    pub fn push(&mut self) {
        self.trail_scopes.push(self.trail.len());
        self.crossed_bounds_column = NULL_LPVAR;
        self.crossed_bounds_deps = None;
        self.core.push_scope();
        self.constraints.push_scope();
        self.usage_in_terms.push_scope();
    }

    pub fn pop(&mut self, count: usize) {
        self.crossed_bounds_column = NULL_LPVAR;
        self.crossed_bounds_deps = None;
        let scope_index = self.trail_scopes.len() - count;
        let trail_size = self.trail_scopes[scope_index];
        self.trail_scopes.truncate(scope_index);
        while self.trail.len() > trail_size {
            match self
                .trail
                .pop()
                .expect("the trail is longer than its scope")
            {
                LarUndo::AddColumn => self.undo_add_column(),
                LarUndo::UpperBound {
                    column,
                    bound,
                    witness,
                } => {
                    self.core.upper_bounds[column] = bound;
                    self.columns[column].upper_witness = witness;
                }
                LarUndo::LowerBound {
                    column,
                    bound,
                    witness,
                } => {
                    self.core.lower_bounds[column] = bound;
                    self.columns[column].lower_witness = witness;
                }
                LarUndo::DioAddTerm(column) => self.undo_add_term(column),
                LarUndo::DioChangedFixedColumn(column) => self
                    .dio_hooks
                    .as_mut()
                    .expect("the undo of a fixed column has its hooks")
                    .changed_fixed_columns
                    .add(column),
                LarUndo::NlaThrottleSeen(key) => {
                    self.nla_throttle_seen.remove(&key);
                }
            }
        }
        let column_count = self.columns.len();
        for column in (column_count..self.local_to_external.len()).rev() {
            let external = self.local_to_external[column];
            if external != NULL_LPVAR {
                self.external_to_local.remove(&external);
            }
        }
        self.local_to_external.truncate(column_count);
        self.local_is_int.truncate(column_count);
        self.core.pop_scope(count);
        let core = &self.core;
        let is_kept = |column: usize| column < column_count && core.is_fixed(column);
        #[expect(
            clippy::disallowed_methods,
            reason = "each entry is kept or deleted by its own column, whatever the order"
        )]
        self.fixed_var_table_int
            .retain(|_key, column| is_kept(*column));
        #[expect(
            clippy::disallowed_methods,
            reason = "each entry is kept or deleted by its own column, whatever the order"
        )]
        self.fixed_var_table_real
            .retain(|_key, column| is_kept(*column));
        for row_index in std::mem::take(&mut self.row_bounds_to_replay) {
            self.add_touched_row(row_index);
        }
        let row_count = self.get_row_count();
        let out_of_range: Vec<usize> = self
            .core
            .touched_rows
            .elems
            .iter()
            .copied()
            .filter(|row| *row >= row_count)
            .collect();
        for row_index in out_of_range {
            self.core.touched_rows.delete(row_index);
        }
        self.clean_inf_heap_after_pop();
        self.constraints.pop_scope(count);
        self.usage_in_terms.pop_scope(count);
        self.status = LP_UNKNOWN;
    }

    fn clean_inf_heap_after_pop(&mut self) {
        let column_count = self.get_column_count();
        let out_of_range: Vec<usize> = self
            .core
            .inf_heap
            .iter()
            .filter(|value| *value >= column_count)
            .collect();
        for column in out_of_range {
            self.core.inf_heap.erase(column);
        }
        let mut became_feasible = Vec::new();
        let heap: Vec<usize> = self.core.inf_heap.iter().collect();
        for column in heap {
            if self.core.is_base(column) {
                continue;
            }
            if let Some(delta) = self.core.make_column_feasible(column) {
                self.change_basic_columns_depending_on(column, &delta);
            }
            became_feasible.push(column);
        }
        for column in became_feasible {
            if self.core.inf_heap.has(column) {
                self.core.inf_heap.erase(column);
            }
        }
        let heap: Vec<usize> = self.core.inf_heap.iter().collect();
        for column in heap {
            if self.core.column_is_feasible(column) {
                self.core.inf_heap.erase(column);
            }
        }
    }

    // add_equality: the term j - k bounded above and below by 0.
    pub fn add_equality(&mut self, first: usize, second: usize) -> [usize; 2] {
        let column = self.add_term(
            &[(first, Rational::one()), (second, Rational::minus_one())],
            NULL_LPVAR,
        );
        if self.get_value(first) != self.get_value(second) {
            self.status = LP_UNKNOWN;
        }
        let le = self.mk_var_bound(column, KIND_LE, &Rational::zero());
        self.activate(le);
        let ge = self.mk_var_bound(column, KIND_GE, &Rational::zero());
        self.activate(ge);
        [le, ge]
    }
}

// The key of the normalized term, and the coefficient the term was divided by.
fn get_normalized_term_key(term: &LarTerm) -> (String, Rational) {
    let (normalized, coeff) = term.get_normalized();
    (get_term_key(normalized.as_ref().unwrap_or(term)), coeff)
}

// updateDelta of init_model and get_rid_of_inf_eps.
fn update_delta(delta: &mut Rational, low: &Impq, high: &Impq) {
    if low.x.compare(&high.x) == Ordering::Less && low.y.compare(&high.y) == Ordering::Greater {
        let candidate = high.x.sub(&low.x).div(&low.y.sub(&high.y));
        if candidate.compare(delta) == Ordering::Less {
            *delta = candidate;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lp::maximize_term::maximize_term;

    // The expected values come from running the same steps through the TypeScript LarSolver.

    fn get_rational(num: i64, den: i64) -> Rational {
        Rational::from_i64(num).div(&Rational::from_i64(den))
    }

    fn add_bound(solver: &mut LarSolver<'_>, column: usize, kind: ConstraintKind, rhs: Rational) {
        let index = solver.mk_var_bound(column, kind, &rhs);
        solver.activate(index);
    }

    fn get_values(solver: &LarSolver<'_>) -> Vec<String> {
        (0..solver.get_column_count())
            .map(|column| solver.get_value(column).to_string())
            .collect()
    }

    fn get_explanation(solver: &LarSolver<'_>) -> Vec<String> {
        let mut explanation = Explanation::new();
        solver.get_infeasibility_explanation(&mut explanation);
        explanation
            .pairs()
            .iter()
            .map(|pair| format!("{}:{}", pair.0, pair.1))
            .collect()
    }

    #[test]
    fn finds_a_feasible_solution_and_maximizes() {
        let mut solver = LarSolver::new(Box::new(|| false));
        let x = solver.add_var(0, false);
        let y = solver.add_var(1, false);
        let t = solver.add_term(&[(x, Rational::one()), (y, Rational::from_i64(2))], 2);
        add_bound(&mut solver, x, KIND_GE, Rational::one());
        add_bound(&mut solver, y, KIND_GT, Rational::from_i64(2));
        add_bound(&mut solver, t, KIND_LE, Rational::from_i64(7));
        assert_eq!(solver.find_feasible_solution(), LP_OPTIMAL);
        assert_eq!(get_values(&solver), ["1", "(2, 1)", "(5, 2)"]);
        assert_eq!(solver.settings().stats.pivots, 0);
        assert!(solver.init_model());
        let model: Vec<String> = (0..3)
            .map(|column| solver.get_model_value(column).to_string())
            .collect();
        assert_eq!(model, ["1", "3", "7"]);
        let maximum = maximize_term(&mut solver, x).map(|value| value.to_string());
        assert_eq!(maximum.as_deref(), Some("(3, -2)"));
        assert_eq!(get_values(&solver), ["(3, -2)", "(2, 1)", "7"]);
    }

    #[test]
    fn explains_an_infeasible_row() {
        let mut solver = LarSolver::new(Box::new(|| false));
        let x = solver.add_var(0, false);
        let y = solver.add_var(1, false);
        let t = solver.add_term(&[(x, Rational::one()), (y, Rational::one())], 2);
        let u = solver.add_term(&[(x, Rational::one()), (y, Rational::minus_one())], 3);
        add_bound(&mut solver, x, KIND_GE, Rational::from_i64(3));
        add_bound(&mut solver, y, KIND_GE, get_rational(3, 2));
        add_bound(&mut solver, u, KIND_LE, Rational::one());
        add_bound(&mut solver, t, KIND_LT, Rational::from_i64(5));
        assert_eq!(solver.find_feasible_solution(), LP_INFEASIBLE);
        assert_eq!(get_explanation(&solver), ["0:-2", "3:1", "2:1"]);
        assert_eq!(get_values(&solver), ["3", "2", "5", "1"]);
        assert_eq!(solver.core.infeasible_sum_sign, -1);
    }

    #[test]
    fn explains_crossed_bounds_and_pops_them() {
        let mut solver = LarSolver::new(Box::new(|| false));
        let x = solver.add_var(0, true);
        add_bound(&mut solver, x, KIND_GE, get_rational(1, 2));
        assert_eq!(solver.find_feasible_solution(), LP_OPTIMAL);
        assert_eq!(get_values(&solver), ["1"]);
        assert_eq!(solver.get_lower_bound(x).to_string(), "1");
        solver.push();
        let y = solver.add_var(1, true);
        let t = solver.add_term(&[(x, Rational::one()), (y, Rational::one())], 2);
        add_bound(&mut solver, t, KIND_LE, Rational::zero());
        add_bound(&mut solver, y, KIND_GE, Rational::zero());
        assert_eq!(solver.find_feasible_solution(), LP_INFEASIBLE);
        assert_eq!(get_explanation(&solver), ["0:-1", "2:-1", "1:1"]);
        assert_eq!(get_values(&solver), ["1", "0", "1"]);
        add_bound(&mut solver, x, KIND_LE, Rational::minus_one());
        assert_eq!(solver.status, LP_INFEASIBLE);
        assert_eq!(solver.crossed_bounds_column, 0);
        assert_eq!(get_explanation(&solver), ["0:-1", "3:-1"]);
        solver.pop(1);
        assert_eq!(solver.get_column_count(), 1);
        assert_eq!(solver.constraints.constraints.len(), 1);
        assert_eq!(solver.find_feasible_solution(), LP_OPTIMAL);
        assert_eq!(get_values(&solver), ["1"]);
        assert_eq!(solver.external_to_local_column(1), NULL_LPVAR);
    }

    #[test]
    fn undoes_nla_throttle_signatures() {
        let mut solver = LarSolver::new(Box::new(|| false));
        solver.push();
        assert!(solver.insert_nla_throttle_seen([1; 8]));
        assert!(!solver.insert_nla_throttle_seen([1; 8]));
        solver.pop(1);
        assert!(solver.insert_nla_throttle_seen([1; 8]));
    }
}
