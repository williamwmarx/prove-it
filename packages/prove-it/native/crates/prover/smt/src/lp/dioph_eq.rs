// Ported from Z3 (src/math/lp/dioph_eq.cpp, src/math/lp/var_register.h), MIT license, see
// z3-license.txt. The Diophantine solver of Griggio's "A Practical Approach to Satisfiability
// Modulo Linear Integer Arithmetic": every integer term t with column j gives the equation
// t - j = 0 over the columns that are not fixed. The equations are normalized by the gcd of their
// coefficients, which finds a conflict when the gcd does not divide the constant, and solved for a
// column with a unit coefficient, or rewritten with a fresh column until one appears. The bounds of
// the term columns are then tightened modulo the gcd of their terms after the substitutions.
//
// The state that lar_solver's callbacks and the undo of an added term touch lives in
// `LarSolver::dio_hooks` (lar_solver.rs); the methods on `DioHooks` here are the parts of
// undoAddTerm that lar_solver's pop runs. `DiophantineSolver` keeps the rest, m_c and the gcd of a
// conflict.
use std::collections::{HashMap, HashSet, VecDeque};

use prove_num::{Int, Rational, get_gcd, get_lcm};

use crate::lp::constraints::{KIND_GE, KIND_LE};
use crate::lp::containers::UnorderedUintMap;
use crate::lp::core_solver::{LP_CANCELLED, LP_FEASIBLE, LP_OPTIMAL};
use crate::lp::dependency::{Dependency, mk_join};
use crate::lp::explanation::Explanation;
use crate::lp::int_solver::Lia;
use crate::lp::lar_solver::{DioHooks, LarSolver};
use crate::lp::lar_term::LarTerm;
use crate::lp::lp_settings::LpStats;
use crate::lp::numeric_pair::Impq;
use crate::lp::static_matrix::StaticMatrix;
use crate::util::error::SmtError;
use crate::util::ordered_map::OrderedSet;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum DioMove {
    Undef,
    Conflict,
    Continue,
}

#[derive(Clone)]
pub(crate) struct Monomial {
    pub(crate) coeff: Rational,
    pub(crate) column: usize,
}

pub(crate) struct FreshDefinition {
    term: LarTerm,
    row: usize,
}

pub(crate) const NO_VAR: usize = usize::MAX;
// m_tighten_size_max: a longer term likely has gcd one.
const TIGHTEN_SIZE_MAX: usize = 10;

// join of lia_move, for the moves the Diophantine solver makes.
fn join_moves(first: DioMove, second: DioMove) -> DioMove {
    if first == second || second == DioMove::Undef {
        return first;
    }
    if first == DioMove::Undef {
        return second;
    }
    if first == DioMove::Conflict || second == DioMove::Conflict {
        DioMove::Conflict
    } else {
        DioMove::Continue
    }
}

fn get_term_monomials(term: &LarTerm) -> Vec<Monomial> {
    term.iter()
        .map(|entry| Monomial {
            coeff: entry.1.clone(),
            column: entry.0,
        })
        .collect()
}

// ext_coeffs: the monomials of the term and then the term column with coefficient -1.
fn get_extended_monomials(term: &LarTerm) -> Vec<Monomial> {
    let mut monomials = get_term_monomials(term);
    monomials.push(Monomial {
        coeff: Rational::minus_one(),
        column: term.column,
    });
    monomials
}

fn is_unit(value: &Rational) -> bool {
    *value == Rational::one() || *value == Rational::minus_one()
}

// rem and machine_div_rem of integers: truncating, so the remainder has the sign of the dividend.
fn get_remainder(left: &Rational, right: &Rational) -> Rational {
    Rational::from_int(left.num() % right.num())
}

fn get_truncated_quotient(left: &Rational, right: &Rational) -> Rational {
    Rational::from_int(left.num() / right.num())
}

// bitsize of an mpq: the bits of the numerator, and of the denominator when it is not one.
fn get_bitsize(value: &Rational) -> u64 {
    let get_int_bitsize = |part: &Int| {
        if part.is_zero() { 1 } else { part.bit_length() }
    };
    if value.is_int() {
        get_int_bitsize(value.num())
    } else {
        get_int_bitsize(value.num()) + get_int_bitsize(value.den())
    }
}

// gcd_of_coeffs: one as soon as a unit coefficient shows up when asked to look for one.
fn get_gcd_of_coeffs<'r>(
    coeffs: impl Iterator<Item = &'r Rational> + Clone,
    is_checking_for_one: bool,
) -> Rational {
    if is_checking_for_one {
        for coeff in coeffs.clone() {
            if is_unit(coeff) {
                return Rational::one();
            }
        }
    }
    let mut gcd = Rational::zero();
    for coeff in coeffs {
        gcd = if gcd.is_zero() {
            coeff.abs()
        } else {
            Rational::from_int(get_gcd(gcd.num(), coeff.num()))
        };
        if gcd == Rational::one() {
            break;
        }
    }
    gcd
}

// term_with_index: the monomials in a vector with the position of every column, and a removal
// that moves the last monomial into the gap.
#[derive(Default)]
pub(crate) struct TermWithIndex {
    pub(crate) data: Vec<Monomial>,
    // NO_VAR where TypeScript's array has a hole or -1.
    positions: Vec<usize>,
}

impl TermWithIndex {
    fn size(&self) -> usize {
        self.data.len()
    }

    fn get_position(&self, column: usize) -> usize {
        self.positions.get(column).copied().unwrap_or(NO_VAR)
    }

    fn set_position(&mut self, column: usize, position: usize) {
        if self.positions.len() <= column {
            self.positions.resize(column + 1, NO_VAR);
        }
        self.positions[column] = position;
    }

    fn has(&self, column: usize) -> bool {
        self.get_position(column) != NO_VAR
    }

    fn get(&self, column: usize) -> &Rational {
        &self.data[self.positions[column]].coeff
    }

    fn erase(&mut self, column: usize) {
        let position = self.get_position(column);
        if position == NO_VAR {
            return;
        }
        let last = self.data.len() - 1;
        if position != last {
            self.data[position] = self.data[last].clone();
            let moved = self.data[position].column;
            self.set_position(moved, position);
        }
        self.data.pop();
        self.set_position(column, NO_VAR);
    }

    fn add(&mut self, coeff: Rational, column: usize) {
        let position = self.get_position(column);
        if position == NO_VAR {
            self.data.push(Monomial { coeff, column });
            self.set_position(column, self.data.len() - 1);
            return;
        }
        let sum = self.data[position].coeff.add(&coeff);
        if sum.is_zero() {
            self.erase(column);
        } else {
            self.data[position] = Monomial { coeff: sum, column };
        }
    }

    pub(crate) fn clear(&mut self) {
        for index in 0..self.data.len() {
            let column = self.data[index].column;
            self.set_position(column, NO_VAR);
        }
        self.data.clear();
    }
}

// protected_queue: a queue of distinct columns that can also lose a column in the middle.
#[derive(Default)]
pub(crate) struct ProtectedQueue {
    items: VecDeque<usize>,
    // Only looked up, never iterated.
    members: HashSet<usize>,
}

impl ProtectedQueue {
    fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    fn push(&mut self, column: usize) {
        if self.members.contains(&column) {
            return;
        }
        self.items.push_back(column);
        self.members.insert(column);
    }

    fn pop_front(&mut self) -> usize {
        let column = self.items.pop_front().unwrap_or(NO_VAR);
        self.members.remove(&column);
        column
    }

    fn remove(&mut self, column: usize) {
        if !self.members.remove(&column) {
            return;
        }
        let position = self
            .items
            .iter()
            .position(|item| *item == column)
            .expect("a member of the queue is in its items");
        self.items.remove(position);
    }

    pub(crate) fn reset(&mut self) {
        self.items.clear();
        self.members.clear();
    }
}

// var_register: the local columns of the equations, and the lar_solver column of each, or none
// for a fresh column.
#[derive(Default)]
pub(crate) struct VarRegister {
    local_to_external: Vec<usize>,
    // Only looked up, never iterated.
    external_to_local: HashMap<usize, usize>,
}

impl VarRegister {
    fn add_var(&mut self, external: usize) -> usize {
        let existing = if external == NO_VAR {
            None
        } else {
            self.external_to_local.get(&external).copied()
        };
        if let Some(existing) = existing {
            return existing;
        }
        let local = self.local_to_external.len();
        self.local_to_external.push(external);
        if external != NO_VAR {
            self.external_to_local.insert(external, local);
        }
        local
    }

    fn get_external(&self, local: usize) -> usize {
        if local < self.local_to_external.len() {
            self.local_to_external[local]
        } else {
            NO_VAR
        }
    }

    fn is_used(&self, external: usize) -> bool {
        self.external_to_local.contains_key(&external)
    }

    // external_to_local, which Z3 asserts finds the column.
    fn get_local(&self, external: usize) -> Result<usize, SmtError> {
        self.external_to_local
            .get(&external)
            .copied()
            .ok_or_else(|| {
                SmtError::Invariant(format!(
                    "the Diophantine solver has no column for {}",
                    external as isize
                ))
            })
    }

    pub(crate) fn shrink(&mut self, size: usize) {
        for local in (size..self.local_to_external.len()).rev() {
            self.external_to_local
                .remove(&self.local_to_external[local]);
        }
        self.local_to_external.truncate(size);
    }

    pub(crate) fn clear(&mut self) {
        self.local_to_external.clear();
        self.external_to_local.clear();
    }
}

// m_fresh_k2xt_terms: the definition of a substituted column k by a fresh column xt, reachable
// from both. The map from k to xt is an unordered_map whose order Z3 iterates.
#[derive(Default)]
pub(crate) struct FreshDefinitions {
    key_to_fresh: UnorderedUintMap<usize>,
    // Only looked up, never iterated.
    fresh_to_key: HashMap<usize, usize>,
    definitions: HashMap<usize, FreshDefinition>,
}

impl FreshDefinitions {
    fn add(&mut self, key: usize, fresh: usize, definition: FreshDefinition) {
        self.key_to_fresh.insert(key, fresh);
        self.fresh_to_key.insert(fresh, key);
        self.definitions.insert(fresh, definition);
    }

    fn has_key(&self, key: usize) -> bool {
        self.key_to_fresh.has(key)
    }

    fn has_fresh(&self, fresh: usize) -> bool {
        self.definitions.contains_key(&fresh)
    }

    fn get_by_key(&self, key: usize) -> Result<&FreshDefinition, SmtError> {
        self.get_by_fresh(self.key_to_fresh.get(key).copied().unwrap_or(NO_VAR))
    }

    fn get_by_fresh(&self, fresh: usize) -> Result<&FreshDefinition, SmtError> {
        self.definitions.get(&fresh).ok_or_else(|| {
            SmtError::Invariant(format!(
                "the Diophantine solver has no definition for {}",
                fresh as isize
            ))
        })
    }

    fn erase_by_fresh(&mut self, fresh: usize) {
        self.key_to_fresh
            .remove(self.fresh_to_key.get(&fresh).copied().unwrap_or(NO_VAR));
        self.fresh_to_key.remove(&fresh);
        self.definitions.remove(&fresh);
    }

    pub(crate) fn clear(&mut self) {
        self.key_to_fresh.clear();
        self.fresh_to_key.clear();
        self.definitions.clear();
    }
}

fn remove_last_row(matrix: &mut StaticMatrix) {
    let last_row = matrix.get_row_count() - 1;
    for index in (0..matrix.rows[last_row].len()).rev() {
        matrix.remove_element(last_row, index);
    }
    matrix.rows.pop();
}

fn pop_empty_columns(matrix: &mut StaticMatrix) {
    while matrix.get_column_count() > 0 && matrix.columns[matrix.get_column_count() - 1].is_empty()
    {
        matrix.pop_column();
    }
}

// Swaps the cell of the pivot row to the head of the column, as the pivots of Z3 do.
fn move_cell_to_front(matrix: &mut StaticMatrix, column: usize, index: usize) {
    let cells = &mut matrix.columns[column];
    let first = cells[0];
    cells.swap(0, index);
    let front = cells[0];
    matrix.rows[front.row][front.offset].offset = 0;
    matrix.rows[first.row][first.offset].offset = index;
}

fn get_row_monomials(matrix: &StaticMatrix, row: usize) -> Vec<Monomial> {
    matrix.rows[row]
        .iter()
        .map(|cell| Monomial {
            coeff: cell.coeff.clone(),
            column: cell.column,
        })
        .collect()
}

// The parts of the Diophantine solver that the undo of an added term runs, inside lar_solver's pop.
impl DioHooks {
    pub(crate) fn deregister_columns_of_term(&mut self, term: &LarTerm) {
        for monomial in get_extended_monomials(term) {
            let Some(terms) = self.columns_to_terms.get_mut(&monomial.column) else {
                continue;
            };
            terms.remove(&term.column);
            if terms.is_empty() {
                self.columns_to_terms.remove(&monomial.column);
            }
        }
    }

    // elimination_work_estimate: the words that eliminating the column of the retired term from
    // m_l_matrix touches.
    pub(crate) fn get_elimination_work_estimate(&self) -> u64 {
        let l_matrix = &self.l_matrix;
        if l_matrix.get_column_count() == 0 || l_matrix.get_row_count() == 0 {
            return 0;
        }
        let column_size = l_matrix.columns[l_matrix.get_column_count() - 1].len() as u64;
        if column_size <= 1 {
            return 0;
        }
        let mut words = 0;
        for cell in &l_matrix.rows[l_matrix.get_row_count() - 1] {
            words += 1 + get_bitsize(&cell.coeff) / 32;
        }
        (column_size - 1) * words
    }

    // reset_state: drops what was derived, and puts the active terms back to be added again in the
    // order of their columns.
    pub(crate) fn reset_state<'t>(
        &mut self,
        get_term: impl Fn(usize) -> &'t LarTerm,
        stats: &mut LpStats,
    ) {
        let active_terms: Vec<usize> = self.active_terms.iter().copied().collect();
        for column in active_terms {
            self.deregister_columns_of_term(get_term(column));
            self.added_terms.push(column);
        }
        self.active_terms.clear();
        self.added_terms.sort();
        self.e_matrix.clear();
        self.l_matrix.clear();
        self.sum_of_fixed.clear();
        self.var_register.clear();
        self.key_to_row.clear();
        self.row_to_key.clear();
        self.fresh_definitions.clear();
        self.row_to_fresh_defs.clear();
        self.changed_rows.clear();
        self.changed_fixed_columns.clear();
        self.changed_terms.clear();
        self.terms_to_tighten.clear();
        self.espace.clear();
        self.lspace.clear();
        self.queue.reset();
        self.infeas_explanation.clear();
        self.conflict_row = NO_VAR;
        self.undo_work = 0;
        stats.dio_state_resets += 1;
    }

    // shrink_matrices: removes the equation of the retired term, the last one.
    pub(crate) fn shrink_matrices(&mut self) {
        let last_row = self.l_matrix.get_row_count() - 1;
        self.eliminate_last_term_column();
        remove_last_row(&mut self.l_matrix);
        remove_last_row(&mut self.e_matrix);
        for fresh in self
            .row_to_fresh_defs
            .get(&last_row)
            .cloned()
            .unwrap_or_default()
        {
            if fresh < self.e_matrix.get_column_count() {
                for cell in &self.e_matrix.columns[fresh] {
                    self.changed_rows.add(cell.row);
                }
            }
        }
        pop_empty_columns(&mut self.l_matrix);
        pop_empty_columns(&mut self.e_matrix);
        self.var_register.shrink(self.e_matrix.get_column_count());
        self.remove_out_of_bounds_fresh_defs();
        self.remove_irrelevant_fresh_defs_for_row(last_row);
        if self.row_to_key.contains_key(&last_row) {
            self.remove_from_s(last_row);
        }
        self.sum_of_fixed.pop();
    }

    // eliminate_last_term_column: pivots the last column of m_l_matrix into its last row, and marks
    // the rows that change, whose equations are recalculated later.
    fn eliminate_last_term_column(&mut self) {
        let l_matrix = &mut self.l_matrix;
        let term_column = l_matrix.get_column_count() - 1;
        let last_row_index = l_matrix.get_row_count() - 1;
        if !l_matrix.rows[last_row_index]
            .iter()
            .any(|cell| cell.column == term_column)
        {
            let from = l_matrix.columns[term_column][0].row;
            l_matrix.add_rows(&Rational::one(), from, last_row_index);
        }
        let Some(alpha) = l_matrix.rows[last_row_index]
            .iter()
            .find(|cell| cell.column == term_column)
            .map(|cell| cell.coeff.clone())
        else {
            return;
        };
        l_matrix.divide_row(last_row_index, &alpha);
        let pivot_index = l_matrix.columns[term_column]
            .iter()
            .position(|cell| cell.row == last_row_index);
        if let Some(pivot_index) = pivot_index
            && pivot_index > 0
        {
            move_cell_to_front(l_matrix, term_column, pivot_index);
        }
        while l_matrix.columns[term_column].len() > 1 {
            let cell = *l_matrix.columns[term_column]
                .last()
                .expect("the column has a cell");
            self.changed_rows.add(cell.row);
            l_matrix.pivot_row_to_row_given_cell(last_row_index, cell, term_column);
        }
    }

    // collect_dependent_fresh_vars: the fresh columns whose definitions use a removed one.
    fn collect_dependent_fresh_vars(&self, removed: usize, to_remove: &mut Vec<usize>) {
        let mut newly_found = Vec::new();
        for entry in self.fresh_definitions.key_to_fresh.iter() {
            let fresh = *entry.1;
            if fresh == removed || to_remove.contains(&fresh) {
                continue;
            }
            let term = &self
                .fresh_definitions
                .get_by_fresh(fresh)
                .expect("a fresh column of the map has its definition")
                .term;
            if term.get(removed).is_some()
                || to_remove.iter().any(|marked| term.get(*marked).is_some())
            {
                newly_found.push(fresh);
            }
        }
        to_remove.extend_from_slice(&newly_found);
        for fresh in newly_found {
            self.collect_dependent_fresh_vars(fresh, to_remove);
        }
    }

    // deep_remove_fresh_var: removes the fresh column and those that depend on it, and marks the
    // rows that use them.
    fn deep_remove_fresh_var(&mut self, removed: usize) {
        if !self.fresh_definitions.has_fresh(removed) {
            return;
        }
        let mut to_remove = vec![removed];
        self.collect_dependent_fresh_vars(removed, &mut to_remove);
        for fresh in to_remove {
            if !self.fresh_definitions.has_fresh(fresh) {
                continue;
            }
            let row = self
                .fresh_definitions
                .get_by_fresh(fresh)
                .expect("a fresh column it has has its definition")
                .row;
            self.fresh_definitions.erase_by_fresh(fresh);
            if let Some(defs) = self.row_to_fresh_defs.get(&row) {
                let kept: Vec<usize> = defs.iter().copied().filter(|def| *def != fresh).collect();
                if kept.is_empty() {
                    self.row_to_fresh_defs.remove(&row);
                } else {
                    self.row_to_fresh_defs.insert(row, kept);
                }
            }
            if fresh < self.e_matrix.get_column_count() {
                for cell in &self.e_matrix.columns[fresh] {
                    self.changed_rows.add(cell.row);
                }
            }
        }
    }

    fn remove_irrelevant_fresh_defs_for_row(&mut self, row: usize) {
        let Some(defs) = self.row_to_fresh_defs.get(&row).cloned() else {
            return;
        };
        for fresh in defs {
            self.deep_remove_fresh_var(fresh);
        }
        self.row_to_fresh_defs.remove(&row);
    }

    fn remove_out_of_bounds_fresh_defs(&mut self) {
        let mut fresh_to_remove = Vec::new();
        let mut rows = Vec::new();
        for entry in self.fresh_definitions.key_to_fresh.iter() {
            if *entry.1 < self.e_matrix.get_column_count() {
                continue;
            }
            fresh_to_remove.push(*entry.1);
            rows.push(
                self.fresh_definitions
                    .get_by_fresh(*entry.1)
                    .expect("a fresh column of the map has its definition")
                    .row,
            );
        }
        for fresh in fresh_to_remove {
            self.deep_remove_fresh_var(fresh);
        }
        for row in rows {
            self.remove_irrelevant_fresh_defs_for_row(row);
        }
    }

    fn remove_from_s(&mut self, row: usize) {
        let Some(key) = self.row_to_key.remove(&row) else {
            return;
        };
        self.key_to_row.remove(&key);
    }

    fn can_substitute(&self, column: usize) -> bool {
        self.key_to_row.contains_key(&column) || self.fresh_definitions.has_key(column)
    }

    fn is_fresh(&self, column: usize) -> bool {
        self.fresh_definitions.has_fresh(column)
    }

    fn get_coeff_in_e_row(&self, row: usize, column: usize) -> Rational {
        self.e_matrix.rows[row]
            .iter()
            .find(|cell| cell.column == column)
            .map_or_else(Rational::zero, |cell| cell.coeff.clone())
    }

    fn get_sign_in_e_row(&self, row: usize, column: usize) -> i64 {
        if self.get_coeff_in_e_row(row, column).is_positive() {
            1
        } else {
            -1
        }
    }
}

pub struct DiophantineSolver {
    // m_c, the constant of m_espace.
    constant: Rational,
    conflict_gcd: Rational,
}

impl DiophantineSolver {
    // The constructor: installs lar_solver's callbacks.
    pub fn new(lra: &mut LarSolver<'_>) -> DiophantineSolver {
        lra.dio_hooks = Some(DioHooks::default());
        DiophantineSolver {
            constant: Rational::zero(),
            conflict_gcd: Rational::zero(),
        }
    }

    pub fn check(lia: &mut Lia<'_, '_>) -> Result<DioMove, SmtError> {
        Dio::new(&mut lia.lia.dio, lia.lra).check(&mut lia.lia.term)
    }

    pub fn explain(lia: &mut Lia<'_, '_>) -> Result<(), SmtError> {
        Dio::new(&mut lia.lia.dio, lia.lra).explain(&mut lia.lia.explanation)
    }
}

// The solver at work: its own state, lar_solver's hooks and lar_solver.
struct Dio<'a, 'l> {
    dio: &'a mut DiophantineSolver,
    // HACK: lar_solver's hooks, moved out of it while the solver runs so that both can be borrowed,
    // moved back around the one call that fires a callback and when the view drops.
    hooks: DioHooks,
    lra: &'a mut LarSolver<'l>,
}

impl Drop for Dio<'_, '_> {
    fn drop(&mut self) {
        self.lra.dio_hooks = Some(std::mem::take(&mut self.hooks));
    }
}

impl<'a, 'l> Dio<'a, 'l> {
    fn new(dio: &'a mut DiophantineSolver, lra: &'a mut LarSolver<'l>) -> Dio<'a, 'l> {
        let hooks = lra
            .dio_hooks
            .take()
            .expect("the Diophantine solver installed its hooks");
        Dio { dio, hooks, lra }
    }

    fn check(&mut self, term: &mut LarTerm) -> Result<DioMove, SmtError> {
        self.lra.settings_mut().stats.dio_calls += 1;
        let mut f_vector = Vec::new();
        loop {
            self.init(&mut f_vector, term)?;
            let dio_move = self.process_f_and_tighten_terms(&mut f_vector)?;
            if dio_move != DioMove::Continue {
                return Ok(dio_move);
            }
        }
    }

    fn explain(&mut self, explanation: &mut Explanation) -> Result<(), SmtError> {
        explanation.clear();
        if self.hooks.conflict_row == NO_VAR {
            for constraint in self.hooks.infeas_explanation.iter() {
                explanation.push(constraint);
            }
            return Ok(());
        }
        let monomials = get_row_monomials(&self.hooks.l_matrix, self.hooks.conflict_row);
        let dep = self.explain_fixed_in_meta_term(&monomials, &self.dio.conflict_gcd)?;
        explanation.push_dependency(&dep);
        Ok(())
    }

    // Filling the equations.

    fn init(&mut self, f_vector: &mut Vec<usize>, term: &mut LarTerm) -> Result<(), SmtError> {
        self.hooks.infeas_explanation.clear();
        term.clear();
        self.hooks.conflict_row = NO_VAR;
        self.hooks.undo_work = 0;
        self.process_changed_fixed_columns(f_vector)?;
        for column in std::mem::take(&mut self.hooks.added_terms) {
            self.hooks.active_terms.insert(column);
            f_vector.push(self.hooks.e_matrix.get_row_count());
            self.fill_entry(column)?;
            self.register_columns_to_term(column)?;
        }
        Ok(())
    }

    fn register_columns_to_term(&mut self, column: usize) -> Result<(), SmtError> {
        for monomial in get_extended_monomials(self.lra.get_term(column)?) {
            match self.hooks.columns_to_terms.get_mut(&monomial.column) {
                None => {
                    let mut terms = OrderedSet::new();
                    terms.insert(column);
                    self.hooks.columns_to_terms.insert(monomial.column, terms);
                }
                Some(terms) => {
                    terms.insert(column);
                }
            }
        }
        Ok(())
    }

    // fill_entry: the equation t - j = 0 with the fixed columns in the constant, explained by j.
    fn fill_entry(&mut self, column: usize) -> Result<(), SmtError> {
        let hooks = &mut self.hooks;
        let row = hooks.e_matrix.get_row_count();
        hooks.l_matrix.add_row();
        hooks.l_matrix.add_columns_up_to(column);
        hooks.l_matrix.add_new_element(row, column, Rational::one());
        hooks.e_matrix.add_row();
        let mut fixed_sum = Rational::zero();
        for monomial in get_extended_monomials(self.lra.get_term(column)?) {
            if self.lra.is_fixed(monomial.column) {
                fixed_sum = fixed_sum.add(
                    &monomial
                        .coeff
                        .mul(&self.lra.get_lower_bound(monomial.column).x),
                );
                continue;
            }
            let local = hooks.var_register.add_var(monomial.column);
            hooks.e_matrix.add_columns_up_to(local);
            hooks.e_matrix.add_new_element(row, local, monomial.coeff);
        }
        hooks.sum_of_fixed.push(fixed_sum);
        self.subs_entry(row)
    }

    // subs_entry: substitutes the solved and the freshly defined columns in the equation.
    fn subs_entry(&mut self, row: usize) -> Result<(), SmtError> {
        let hooks = &mut self.hooks;
        if row >= hooks.e_matrix.get_row_count() {
            return Ok(());
        }
        hooks.queue.reset();
        hooks.push_substitutable_columns_of_row(row);
        while !hooks.queue.is_empty() {
            let column = hooks.queue.pop_front();
            let alpha = hooks.get_coeff_in_e_row(row, column);
            if alpha.is_zero() {
                continue;
            }
            match hooks.key_to_row.get(&column).copied() {
                None => hooks.e_matrix.add_term_to_row(
                    &alpha.neg(),
                    &hooks.fresh_definitions.get_by_key(column)?.term,
                    row,
                ),
                Some(solved_row) => {
                    let sign = hooks.get_sign_in_e_row(solved_row, column);
                    hooks.add_two_entries(
                        &alpha.neg().mul(&Rational::from_i64(sign)),
                        solved_row,
                        row,
                    );
                }
            }
            hooks.push_substitutable_columns_of_row(row);
        }
        Ok(())
    }

    // recalculate_entry: the equation again from its explanation, scaled to integers.
    fn recalculate_entry(&mut self, row: usize) -> Result<(), SmtError> {
        let mut fixed_sum = self.open_l_term_to_espace(row)?;
        let hooks = &mut self.hooks;
        while let Some(last) = hooks.e_matrix.rows[row].len().checked_sub(1) {
            hooks.e_matrix.remove_element(row, last);
        }
        let mut denominator = Int::one();
        for index in 0..hooks.espace.data.len() {
            let monomial = hooks.espace.data[index].clone();
            let local = hooks.var_register.add_var(monomial.column);
            hooks.e_matrix.add_columns_up_to(local);
            if *monomial.coeff.den() != 1 {
                denominator = get_lcm(&denominator, monomial.coeff.den());
            }
            hooks.e_matrix.add_new_element(row, local, monomial.coeff);
        }
        if denominator != 1 {
            let scale = Rational::from_int(denominator);
            fixed_sum = fixed_sum.mul(&scale);
            hooks.l_matrix.multiply_row(row, &scale);
            hooks.e_matrix.multiply_row(row, &scale);
        }
        hooks.sum_of_fixed[row] = fixed_sum;
        if hooks.row_to_key.contains_key(&row) {
            hooks.remove_from_s(row);
        }
        Ok(())
    }

    // open_l_term_to_espace: the combination of term definitions of the row, over lar_solver
    // columns, with the fixed ones in the returned constant.
    fn open_l_term_to_espace(&mut self, row: usize) -> Result<Rational, SmtError> {
        let hooks = &mut self.hooks;
        let solver = &*self.lra;
        hooks.espace.clear();
        let mut constant = Rational::zero();
        for cell in &hooks.l_matrix.rows[row] {
            for monomial in get_extended_monomials(solver.get_term(cell.column)?) {
                let coeff = cell.coeff.mul(&monomial.coeff);
                if solver.is_fixed(monomial.column) {
                    constant = constant.add(&coeff.mul(&solver.get_lower_bound(monomial.column).x));
                } else {
                    hooks.espace.add(coeff, monomial.column);
                }
            }
        }
        Ok(constant)
    }

    // process_m_changed_f_columns: recalculates the equations that the columns that became fixed or
    // stopped being fixed, and the changed terms, touch.
    fn process_changed_fixed_columns(&mut self, f_vector: &mut Vec<usize>) -> Result<(), SmtError> {
        for column in self.hooks.changed_fixed_columns.elems.clone() {
            let hooks = &mut self.hooks;
            if let Some(terms) = hooks.columns_to_terms.get(&column) {
                let mut sorted: Vec<usize> = terms.iter().copied().collect();
                sorted.sort();
                for term_column in sorted {
                    hooks.changed_terms.add(term_column);
                }
            }
            if !hooks.var_register.is_used(column) {
                continue;
            }
            let local = hooks.var_register.get_local(column)?;
            for cell in &hooks.e_matrix.columns[local] {
                hooks.changed_rows.add(cell.row);
            }
        }
        for column in self.hooks.changed_terms.elems.clone() {
            if !self.is_big_term_or_no_term(column)? {
                self.hooks.terms_to_tighten.add(column);
            }
            let hooks = &mut self.hooks;
            if column < hooks.l_matrix.get_column_count() {
                for cell in &hooks.l_matrix.columns[column] {
                    hooks.changed_rows.add(cell.row);
                }
            }
        }
        let hooks = &mut self.hooks;
        let mut more_changed_rows = Vec::new();
        for row in &hooks.changed_rows.elems {
            for fresh in hooks.row_to_fresh_defs.get(row).into_iter().flatten() {
                for cell in &hooks.e_matrix.columns[*fresh] {
                    more_changed_rows.push(cell.row);
                }
            }
        }
        for row in more_changed_rows {
            hooks.changed_rows.add(row);
        }
        hooks.remove_out_of_bounds_fresh_defs();
        for row in hooks.changed_rows.elems.clone() {
            hooks.remove_irrelevant_fresh_defs_for_row(row);
        }
        for row in self.hooks.changed_rows.elems.clone() {
            if row >= self.hooks.e_matrix.get_row_count() {
                continue;
            }
            if self.hooks.row_to_key.contains_key(&row) {
                f_vector.push(row);
            }
            self.recalculate_entry(row)?;
            let hooks = &mut self.hooks;
            let e_matrix = &mut hooks.e_matrix;
            if e_matrix.get_column_count() > 0
                && e_matrix.columns[e_matrix.get_column_count() - 1].is_empty()
            {
                e_matrix.pop_column();
                let column_count = e_matrix.get_column_count();
                hooks.var_register.shrink(column_count);
                hooks.remove_out_of_bounds_fresh_defs();
            }
            let l_matrix = &mut hooks.l_matrix;
            if l_matrix.get_column_count() > 0
                && l_matrix.columns[l_matrix.get_column_count() - 1].is_empty()
            {
                l_matrix.pop_column();
            }
        }
        for row in self.hooks.changed_rows.elems.clone() {
            self.subs_entry(row)?;
        }
        let hooks = &mut self.hooks;
        hooks.changed_fixed_columns.clear();
        hooks.changed_rows.clear();
        hooks.changed_terms.clear();
        Ok(())
    }

    // is_big_term_or_no_term: also marks the terms ignored for their big numbers.
    fn is_big_term_or_no_term(&mut self, column: usize) -> Result<bool, SmtError> {
        let solver = &*self.lra;
        if column >= solver.get_column_count() || !solver.has_term(column) {
            return Ok(true);
        }
        if !solver.settings().is_dio_ignoring_big_nums {
            return Ok(false);
        }
        for entry in solver.get_term(column)?.iter() {
            let is_big_fixed =
                solver.is_fixed(entry.0) && solver.get_lower_bound(entry.0).x.is_big();
            if !entry.1.is_big() && !is_big_fixed {
                continue;
            }
            self.hooks.has_ignored_terms = true;
            return Ok(true);
        }
        Ok(false)
    }

    // Fresh definitions.

    // fresh_var_step: step 7 of the paper. With the smallest coefficient a of k in row h, the fresh
    // column xt = k + sum (a_i div a) x_i replaces k in the equations of F.
    fn fresh_var_step(&mut self, row: usize, key: usize, ahk: &Rational) {
        let hooks = &mut self.hooks;
        let fresh = hooks.var_register.add_var(NO_VAR);
        while fresh >= hooks.e_matrix.get_column_count() {
            hooks.e_matrix.add_column();
        }
        let mut fresh_term = LarTerm::new();
        fresh_term.add_monomial(&Rational::minus_one(), fresh);
        fresh_term.add_monomial(&Rational::one(), key);
        for cell in &hooks.e_matrix.rows[row] {
            if cell.column == key {
                continue;
            }
            let quotient = get_truncated_quotient(&cell.coeff, ahk);
            if !quotient.is_zero() {
                fresh_term.add_monomial(&quotient, cell.column);
            }
        }
        // std::make_pair copies the term with lar_term's copy constructor, and the bij_map assigns
        // it, so the stored term is reinserted twice in iteration order.
        let copied = LarTerm::from_entries(fresh_term.iter());
        let stored = LarTerm::from_entries(copied.iter());
        hooks
            .fresh_definitions
            .add(key, fresh, FreshDefinition { term: stored, row });
        match hooks.row_to_fresh_defs.get_mut(&row) {
            None => {
                hooks.row_to_fresh_defs.insert(row, vec![fresh]);
            }
            Some(defs) => defs.push(fresh),
        }
        for index in (0..hooks.e_matrix.columns[key].len()).rev() {
            let cell = hooks.e_matrix.columns[key][index];
            if hooks.row_to_key.contains_key(&cell.row) {
                continue;
            }
            hooks
                .e_matrix
                .pivot_term_to_row_given_cell(&fresh_term, cell, key, 1);
        }
    }

    // Solving F.

    fn process_f_and_tighten_terms(
        &mut self,
        f_vector: &mut Vec<usize>,
    ) -> Result<DioMove, SmtError> {
        let dio_move = self.process_f(f_vector)?;
        if dio_move != DioMove::Undef {
            return Ok(dio_move);
        }
        let tightened = self.tighten_terms_with_s()?;
        if tightened == DioMove::Conflict {
            self.lra.settings_mut().stats.dio_tighten_conflicts += 1;
        }
        Ok(tightened)
    }

    fn process_f(&mut self, f_vector: &mut Vec<usize>) -> Result<DioMove, SmtError> {
        if self.hooks.conflict_row != NO_VAR {
            return Ok(DioMove::Conflict);
        }
        let mut dio_move;
        loop {
            dio_move = self.rewrite_eqs(f_vector);
            if self.lra.settings().is_canceled() {
                return Ok(DioMove::Undef);
            }
            if dio_move != DioMove::Continue || f_vector.is_empty() {
                break;
            }
        }
        Ok(if dio_move == DioMove::Conflict {
            DioMove::Conflict
        } else {
            DioMove::Undef
        })
    }

    fn set_rewrite_conflict(&mut self, row: usize, gcd: Rational) {
        self.hooks.conflict_row = row;
        self.dio.conflict_gcd = gcd;
        self.lra.settings_mut().stats.dio_rewrite_conflicts += 1;
    }

    // rewrite_eqs: steps 6 and 7 of the paper on the equation of F with the smallest coefficient,
    // and of those the one whose substitution fills the fewest cells.
    fn rewrite_eqs(&mut self, f_vector: &mut Vec<usize>) -> DioMove {
        if f_vector.is_empty() {
            return DioMove::Undef;
        }
        let mut chosen_row = NO_VAR;
        let mut chosen_key = 0;
        let mut chosen_index = NO_VAR;
        let mut chosen_sign = 0;
        let mut chosen_markovich = 0;
        let mut min_ahk = Rational::zero();
        let mut num_choices = 0;
        for (index, row) in f_vector.iter().copied().enumerate() {
            if self.hooks.e_matrix.rows[row].is_empty() {
                if self.hooks.sum_of_fixed[row].is_zero() {
                    continue;
                }
                self.set_rewrite_conflict(row, Rational::zero());
                return DioMove::Conflict;
            }
            if !self.hooks.sum_of_fixed[row].is_int() {
                self.set_rewrite_conflict(row, Rational::zero());
                return DioMove::Conflict;
            }
            let minimal = self.find_minimal_abs_coeff(row);
            let Some(gcd) = self.normalize_e_by_gcd(row) else {
                return DioMove::Conflict;
            };
            let ahk = if gcd == Rational::one() {
                minimal.ahk
            } else {
                minimal.ahk.div(&gcd)
            };
            if num_choices == 0 || min_ahk.compare(&ahk).is_gt() {
                chosen_index = index;
                num_choices = 1;
                min_ahk = ahk;
                chosen_row = row;
                chosen_key = minimal.column;
                chosen_sign = minimal.sign;
                chosen_markovich = minimal.markovich;
                continue;
            }
            if min_ahk == ahk && chosen_markovich > minimal.markovich {
                chosen_index = index;
                chosen_row = row;
                chosen_key = minimal.column;
                chosen_sign = minimal.sign;
                chosen_markovich = minimal.markovich;
            }
            if min_ahk == Rational::one() && chosen_markovich == 0 {
                break;
            }
        }
        if chosen_row == NO_VAR {
            return DioMove::Undef;
        }
        if min_ahk == Rational::one() {
            self.hooks.key_to_row.insert(chosen_key, chosen_row);
            self.hooks.row_to_key.insert(chosen_row, chosen_key);
            self.eliminate_var_in_f(chosen_row, chosen_key, chosen_sign);
            // TypeScript moves the last row into the gap.
            f_vector.swap_remove(chosen_index);
        } else {
            self.fresh_var_step(
                chosen_row,
                chosen_key,
                &min_ahk.mul(&Rational::from_i64(chosen_sign)),
            );
        }
        DioMove::Continue
    }

    // find_minimal_abs_coeff: the first column with the smallest coefficient, its sign, and the
    // Markowitz number of the pivot.
    fn find_minimal_abs_coeff(&self, row: usize) -> MinimalCoeff {
        let e_matrix = &self.hooks.e_matrix;
        let mut ahk = Rational::zero();
        let mut column = NO_VAR;
        let mut sign = 0;
        for cell in &e_matrix.rows[row] {
            let magnitude = cell.coeff.abs();
            if column != NO_VAR && magnitude.compare(&ahk).is_ge() {
                continue;
            }
            ahk = magnitude;
            sign = if cell.coeff.is_positive() { 1 } else { -1 };
            column = cell.column;
            if ahk == Rational::one() {
                break;
            }
        }
        let markovich = (e_matrix.columns[column].len() - 1) * (e_matrix.rows[row].len() - 1);
        MinimalCoeff {
            ahk,
            column,
            sign,
            markovich,
        }
    }

    // normalize_e_by_gcd: the gcd of the coefficients after dividing the equation by it, or None
    // on the conflict of a gcd that does not divide the constant.
    fn normalize_e_by_gcd(&mut self, row: usize) -> Option<Rational> {
        let gcd = get_gcd_of_coeffs(
            self.hooks.e_matrix.rows[row].iter().map(|cell| &cell.coeff),
            true,
        );
        if gcd.is_zero() || gcd == Rational::one() {
            return Some(gcd);
        }
        let quotient = self.hooks.sum_of_fixed[row].div(&gcd);
        if !quotient.is_int() {
            self.set_rewrite_conflict(row, gcd);
            return None;
        }
        let hooks = &mut self.hooks;
        hooks.e_matrix.divide_row(row, &gcd);
        hooks.sum_of_fixed[row] = quotient;
        hooks.l_matrix.divide_row(row, &gcd);
        Some(gcd)
    }

    // eliminate_var_in_f: substitutes the column solved by the row in the other equations of F.
    fn eliminate_var_in_f(&mut self, row: usize, key: usize, sign: i64) {
        let hooks = &mut self.hooks;
        let constant = hooks.sum_of_fixed[row].clone();
        let pivot_index = hooks.e_matrix.columns[key]
            .iter()
            .position(|cell| cell.row == row);
        if let Some(pivot_index) = pivot_index
            && pivot_index > 0
        {
            move_cell_to_front(&mut hooks.e_matrix, key, pivot_index);
        }
        let sign_value = Rational::from_i64(sign);
        for index in (0..hooks.e_matrix.columns[key].len()).rev() {
            let cell = hooks.e_matrix.columns[key][index];
            if hooks.row_to_key.contains_key(&cell.row) {
                continue;
            }
            let coeff = hooks.e_matrix.get_val(&cell).clone();
            let target = cell.row;
            hooks.sum_of_fixed[target] =
                hooks.sum_of_fixed[target].sub(&sign_value.mul(&coeff).mul(&constant));
            hooks
                .e_matrix
                .pivot_row_to_row_given_cell_with_sign(row, cell, key, sign);
            hooks
                .l_matrix
                .add_rows(&sign_value.neg().mul(&coeff), row, target);
        }
    }

    // Tightening the bounds of term columns.

    // tighten_terms_with_S: the terms whose bounds changed, the most shared first.
    fn tighten_terms_with_s(&mut self) -> Result<DioMove, SmtError> {
        let mut sorted_terms = Vec::new();
        let mut processed_terms = Vec::new();
        let solver = &*self.lra;
        for column in self.hooks.terms_to_tighten.elems.iter().copied() {
            if column >= solver.get_column_count()
                || !solver.has_term(column)
                || solver.is_free(column)
                || !solver.is_int(column)
            {
                processed_terms.push(column);
            } else {
                sorted_terms.push(column);
            }
        }
        let mut weights = HashMap::new();
        for column in &sorted_terms {
            weights.insert(*column, self.get_term_weight(solver.get_term(*column)?));
        }
        sorted_terms.sort_by(|first, second| {
            let first_weight = weights.get(first).copied().unwrap_or(0);
            let second_weight = weights.get(second).copied().unwrap_or(0);
            second_weight
                .cmp(&first_weight)
                .then_with(|| first.cmp(second))
        });
        let mut dio_move = DioMove::Undef;
        for column in sorted_terms {
            if self.is_big_term_or_no_term(column)? {
                self.hooks.terms_to_tighten.delete(column);
                continue;
            }
            let tightened = self.tighten_bounds_for_term_column(column)?;
            self.hooks.terms_to_tighten.delete(column);
            dio_move = join_moves(tightened, dio_move);
            if dio_move == DioMove::Conflict {
                break;
            }
        }
        for column in processed_terms {
            self.hooks.terms_to_tighten.delete(column);
        }
        Ok(dio_move)
    }

    fn get_term_weight(&self, term: &LarTerm) -> usize {
        let mut weight = 0;
        for entry in term.iter() {
            weight = weight.max(
                self.hooks
                    .columns_to_terms
                    .get(&entry.0)
                    .map_or(0, |terms| terms.len()),
            );
        }
        weight
    }

    fn tighten_bounds_for_term_column(&mut self, column: usize) -> Result<DioMove, SmtError> {
        let mut queue = ProtectedQueue::default();
        if !self.init_substitutions(column, &mut queue)? {
            return Ok(DioMove::Undef);
        }
        if self.subs_with_s_and_fresh(&mut queue, column)? == DioMove::Conflict {
            return Ok(DioMove::Conflict);
        }
        self.process_fixed_in_espace();
        self.tighten_on_espace(column)
    }

    // init_substitutions: m_espace is the term over local columns with its fixed part in m_c, and
    // m_lspace explains it. False on a big number.
    fn init_substitutions(
        &mut self,
        column: usize,
        queue: &mut ProtectedQueue,
    ) -> Result<bool, SmtError> {
        let solver = &*self.lra;
        let hooks = &mut self.hooks;
        let is_ignoring_big_nums = solver.settings().is_dio_ignoring_big_nums;
        let term = solver.get_term(column)?;
        hooks.espace.clear();
        self.dio.constant = Rational::zero();
        hooks.lspace.clear();
        hooks.lspace.add(Rational::one(), term.column);
        for entry in term.iter() {
            let column = entry.0;
            let coeff = entry.1;
            if solver.is_fixed(column) {
                let bound = &solver.get_lower_bound(column).x;
                if is_ignoring_big_nums && bound.is_big() {
                    return Ok(false);
                }
                self.dio.constant = self.dio.constant.add(&coeff.mul(bound));
                continue;
            }
            let local = hooks.var_register.get_local(column)?;
            if is_ignoring_big_nums && coeff.is_big() {
                return Ok(false);
            }
            hooks.espace.add(coeff.clone(), local);
            if hooks.can_substitute(local) {
                queue.push(local);
            }
        }
        Ok(true)
    }

    fn subs_with_s_and_fresh(
        &mut self,
        queue: &mut ProtectedQueue,
        column: usize,
    ) -> Result<DioMove, SmtError> {
        let mut dio_move = DioMove::Undef;
        while !queue.is_empty()
            && dio_move != DioMove::Conflict
            && self.hooks.espace.size() <= TIGHTEN_SIZE_MAX
        {
            dio_move = join_moves(self.subs_front_with_s_and_fresh(queue, column)?, dio_move);
        }
        Ok(dio_move)
    }

    fn subs_front_with_s_and_fresh(
        &mut self,
        queue: &mut ProtectedQueue,
        column: usize,
    ) -> Result<DioMove, SmtError> {
        self.process_fixed_in_espace();
        let tightened = self.tighten_on_espace(column)?;
        if tightened == DioMove::Conflict {
            return Ok(DioMove::Conflict);
        }
        let key = self.find_var_to_substitute_on_espace(queue)?;
        if key == NO_VAR {
            return Ok(DioMove::Undef);
        }
        let dio_move = if self.hooks.fresh_definitions.has_key(key) {
            self.subs_by_fresh(key, queue, column)?
        } else {
            self.subs_by_s(key, queue, column)?
        };
        Ok(join_moves(dio_move, tightened))
    }

    // find_var_to_substitute_on_espace: the queued column whose substitution adds the fewest new
    // columns, drawn at random among ties, and the queued columns no longer in m_espace dropped.
    fn find_var_to_substitute_on_espace(
        &mut self,
        queue: &mut ProtectedQueue,
    ) -> Result<usize, SmtError> {
        let hooks = &self.hooks;
        let espace = &hooks.espace;
        let mut best = NO_VAR;
        let mut min_new_vars = usize::MAX;
        let mut num_candidates = 0;
        let mut to_remove = Vec::new();
        for column in queue.items.iter().copied() {
            if !espace.has(column) {
                to_remove.push(column);
                continue;
            }
            let mut new_vars = 0;
            if let Some(solved_row) = hooks.key_to_row.get(&column) {
                for cell in &hooks.e_matrix.rows[*solved_row] {
                    if cell.column != column && !espace.has(cell.column) {
                        new_vars += 1;
                    }
                }
            } else if hooks.fresh_definitions.has_key(column) {
                for entry in hooks.fresh_definitions.get_by_key(column)?.term.iter() {
                    if entry.0 != column && !espace.has(entry.0) {
                        new_vars += 1;
                    }
                }
            }
            if new_vars < min_new_vars {
                min_new_vars = new_vars;
                best = column;
                num_candidates = 1;
            } else if new_vars == min_new_vars {
                num_candidates += 1;
                if self
                    .lra
                    .settings_mut()
                    .get_random_next()
                    .is_multiple_of(num_candidates)
                {
                    best = column;
                }
            }
        }
        if best != NO_VAR {
            queue.remove(best);
        }
        for column in to_remove {
            queue.remove(column);
        }
        Ok(best)
    }

    // subs_qfront_by_fresh: replaces k by its fresh definition, which leaves m_lspace as it is.
    fn subs_by_fresh(
        &mut self,
        key: usize,
        queue: &mut ProtectedQueue,
        column: usize,
    ) -> Result<DioMove, SmtError> {
        let hooks = &mut self.hooks;
        let entries: Vec<(usize, Rational)> = hooks
            .fresh_definitions
            .get_by_key(key)?
            .term
            .iter()
            .map(|entry| (entry.0, entry.1.clone()))
            .collect();
        let coeff = hooks.espace.get(key).neg();
        hooks.espace.erase(key);
        for entry in entries {
            if entry.0 == key {
                continue;
            }
            hooks.espace.add(entry.1.mul(&coeff), entry.0);
            if hooks.espace.has(entry.0) && hooks.can_substitute(entry.0) {
                queue.push(entry.0);
            }
        }
        self.tighten_on_espace(column)
    }

    // subs_qfront_by_S: replaces k by the equation solved for it, and adds that equation's
    // explanation to m_lspace.
    fn subs_by_s(
        &mut self,
        key: usize,
        queue: &mut ProtectedQueue,
        column: usize,
    ) -> Result<DioMove, SmtError> {
        let hooks = &mut self.hooks;
        let row = hooks.key_to_row.get(&key).copied().unwrap_or(NO_VAR);
        let constant = hooks.sum_of_fixed[row].clone();
        let mut coeff = hooks.espace.get(key).clone();
        hooks.espace.erase(key);
        if hooks.get_coeff_in_e_row(row, key) == Rational::one() {
            coeff = coeff.neg();
        }
        for index in 0..hooks.e_matrix.rows[row].len() {
            let cell = &hooks.e_matrix.rows[row][index];
            if cell.column == key {
                continue;
            }
            let cell_column = cell.column;
            hooks.espace.add(cell.coeff.mul(&coeff), cell_column);
            if hooks.espace.has(cell_column) && hooks.can_substitute(cell_column) {
                queue.push(cell_column);
            }
        }
        self.dio.constant = self.dio.constant.add(&coeff.mul(&constant));
        for cell in &hooks.l_matrix.rows[row] {
            hooks.lspace.add(coeff.mul(&cell.coeff), cell.column);
        }
        self.tighten_on_espace(column)
    }

    fn process_fixed_in_espace(&mut self) {
        let solver = &*self.lra;
        let hooks = &mut self.hooks;
        // TypeScript's isFixed of a column out of range, as of a fresh column's -1, is false.
        let is_fixed =
            |external: usize| external < solver.get_column_count() && solver.is_fixed(external);
        let mut fixed = Vec::new();
        for monomial in &hooks.espace.data {
            if !hooks.is_fresh(monomial.column)
                && is_fixed(hooks.var_register.get_external(monomial.column))
            {
                fixed.push(monomial.column);
            }
        }
        for local in fixed {
            let bound = &solver
                .get_lower_bound(hooks.var_register.get_external(local))
                .x;
            self.dio.constant = self.dio.constant.add(&hooks.espace.get(local).mul(bound));
            hooks.espace.erase(local);
        }
    }

    // tighten_on_espace: with g the gcd of m_espace, the bounds of the term column move to the
    // nearest values congruent to m_c modulo g, and a constant m_espace is checked against them.
    fn tighten_on_espace(&mut self, column: usize) -> Result<DioMove, SmtError> {
        let gcd = get_gcd_of_coeffs(
            self.hooks
                .espace
                .data
                .iter()
                .map(|monomial| &monomial.coeff),
            true,
        );
        if gcd == Rational::one() {
            return Ok(DioMove::Undef);
        }
        if gcd.is_zero() {
            self.handle_constant_term(column)?;
            return Ok(if self.hooks.infeas_explanation.is_empty() {
                DioMove::Undef
            } else {
                DioMove::Conflict
            });
        }
        if self.tighten_bounds_for_non_trivial_gcd(&gcd, column, true)? {
            return Ok(DioMove::Conflict);
        }
        if self.tighten_bounds_for_non_trivial_gcd(&gcd, column, false)? {
            return Ok(DioMove::Conflict);
        }
        Ok(if self.hooks.changed_fixed_columns.has(column) {
            DioMove::Continue
        } else {
            DioMove::Undef
        })
    }

    fn handle_constant_term(&mut self, column: usize) -> Result<(), SmtError> {
        let solver = &*self.lra;
        let constant = &self.dio.constant;
        if constant.is_zero() {
            return Ok(());
        }
        let upper = solver.get_bound(column, true);
        let is_above_upper = upper.as_ref().is_some_and(|upper| {
            constant.compare(&upper.value).is_gt() || (upper.is_strict && *constant == upper.value)
        });
        let lower = if is_above_upper {
            None
        } else {
            solver.get_bound(column, false)
        };
        let is_below_lower = lower.as_ref().is_some_and(|lower| {
            constant.compare(&lower.value).is_lt() || (lower.is_strict && *constant == lower.value)
        });
        if !is_above_upper && !is_below_lower {
            return Ok(());
        }
        let dep = mk_join(
            &mk_join(
                &self.explain_fixed(
                    &get_term_monomials(solver.get_term(column)?),
                    &Rational::zero(),
                ),
                &self.explain_fixed_in_meta_term(&self.hooks.lspace.data, &Rational::zero())?,
            ),
            &solver.get_bound_witnesses(column),
        );
        self.hooks.infeas_explanation.push_dependency(&dep);
        Ok(())
    }

    // tighten_bounds_for_non_trivial_gcd: whether tightening the bound found a conflict.
    fn tighten_bounds_for_non_trivial_gcd(
        &mut self,
        gcd: &Rational,
        column: usize,
        is_upper: bool,
    ) -> Result<bool, SmtError> {
        let Some(bound) = self.lra.get_bound(column, is_upper) else {
            return Ok(false);
        };
        let mut remainder = get_remainder(&bound.value.sub(&self.dio.constant), gcd);
        if remainder.is_negative() {
            remainder = remainder.add(gcd);
        }
        Ok(!remainder.is_zero()
            && self.tighten_bound_kind(gcd, column, &bound.value, &remainder, is_upper)?)
    }

    // tighten_bound_kind: t = g*t' + m_c <= rs gives t <= rs - (rs - m_c) mod g, and a lower bound
    // likewise. The fixed columns whose coefficients g divides do not explain the new bound.
    fn tighten_bound_kind(
        &mut self,
        gcd: &Rational,
        column: usize,
        rs: &Rational,
        remainder: &Rational,
        is_upper: bool,
    ) -> Result<bool, SmtError> {
        let solver = &*self.lra;
        let bound = if is_upper {
            rs.sub(remainder)
        } else {
            rs.add(gcd).sub(remainder)
        };
        let mut dep = if is_upper {
            solver.get_upper_witness(column).clone()
        } else {
            solver.get_lower_witness(column).clone()
        };
        let mut fixed_part = self.open_fixed_from_ml(&self.hooks.lspace.data)?;
        if solver.is_fixed(column) {
            fixed_part.add(Rational::one(), column);
        }
        for monomial in &fixed_part.data {
            if monomial.coeff.is_int() && get_remainder(&monomial.coeff, gcd).is_zero() {
                continue;
            }
            dep = mk_join(&dep, &solver.get_bound_witnesses(monomial.column));
        }
        if solver.settings().is_canceled() {
            return Ok(false);
        }
        self.lra.dio_hooks = Some(std::mem::take(&mut self.hooks));
        self.lra.update_column_type_and_bound(
            column,
            if is_upper { KIND_LE } else { KIND_GE },
            &Impq::from_x(bound),
            dep,
        );
        self.hooks = self
            .lra
            .dio_hooks
            .take()
            .expect("lar_solver keeps the Diophantine solver's hooks");
        let status = self.lra.find_feasible_solution();
        if status == LP_FEASIBLE || status == LP_OPTIMAL || status == LP_CANCELLED {
            return Ok(false);
        }
        self.lra
            .get_infeasibility_explanation(&mut self.hooks.infeas_explanation);
        Ok(true)
    }

    // open_fixed_from_ml: the fixed columns of a combination of term definitions.
    fn open_fixed_from_ml(&self, monomials: &[Monomial]) -> Result<TermWithIndex, SmtError> {
        let solver = &*self.lra;
        let mut result = TermWithIndex::default();
        for outer in monomials {
            for monomial in get_extended_monomials(solver.get_term(outer.column)?) {
                if solver.is_fixed(monomial.column) {
                    result.add(outer.coeff.mul(&monomial.coeff), monomial.column);
                }
            }
        }
        Ok(result)
    }

    fn explain_fixed_in_meta_term(
        &self,
        monomials: &[Monomial],
        gcd: &Rational,
    ) -> Result<Dependency, SmtError> {
        Ok(self.explain_fixed(&self.open_fixed_from_ml(monomials)?.data, gcd))
    }

    // explain_fixed: the bounds of the fixed columns, but those whose coefficients a nonzero gcd
    // divides.
    fn explain_fixed(&self, monomials: &[Monomial], gcd: &Rational) -> Dependency {
        let solver = &*self.lra;
        let mut dep = None;
        for monomial in monomials {
            if !solver.is_fixed(monomial.column) {
                continue;
            }
            if !gcd.is_zero() && monomial.coeff.div(gcd).is_int() {
                continue;
            }
            dep = mk_join(&dep, &solver.get_bound_witnesses(monomial.column));
        }
        dep
    }
}

// The result of find_minimal_abs_coeff.
struct MinimalCoeff {
    ahk: Rational,
    column: usize,
    sign: i64,
    markovich: usize,
}

impl DioHooks {
    // The columns of the row that a solved or a fresh definition substitutes, queued.
    fn push_substitutable_columns_of_row(&mut self, row: usize) {
        let columns: Vec<usize> = self.e_matrix.rows[row]
            .iter()
            .map(|cell| cell.column)
            .filter(|column| self.can_substitute(*column))
            .collect();
        for column in columns {
            self.queue.push(column);
        }
    }

    // add_two_entries: adds an equation times coeff to another.
    fn add_two_entries(&mut self, coeff: &Rational, from: usize, to: usize) {
        self.e_matrix.add_rows(coeff, from, to);
        self.l_matrix.add_rows(coeff, from, to);
        self.sum_of_fixed[to] = self.sum_of_fixed[to].add(&coeff.mul(&self.sum_of_fixed[from]));
    }
}
