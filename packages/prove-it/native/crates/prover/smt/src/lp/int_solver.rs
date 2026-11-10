// Ported from Z3 (src/math/lp/int_solver.cpp, src/math/lp/int_gcd_test.cpp,
// src/math/lp/int_branch.cpp), MIT license, see z3-license.txt. The integer check of the final
// check: the GCD test on rows, patching fractional basic columns through integer non-basic ones,
// the cube and largest cube tests, HNF cuts, the Diophantine solver, Gomory cuts, and a branch on a
// fractional basic column.
//
// TypeScript's IntSolver holds the LarSolver; here `Lia` is the view that holds both while a
// method runs, and dereferences to the IntSolver's own state.
use std::collections::{HashMap, HashSet};
use std::ops::{Deref, DerefMut};

use prove_num::{Int, Rational, get_gcd, get_lcm};

use crate::lp::core_solver::{
    COLUMN_BOXED, COLUMN_FIXED, COLUMN_FREE, COLUMN_LOWER, COLUMN_UPPER, CoreSolver,
};
use crate::lp::dioph_eq::{DioMove, DiophantineSolver};
use crate::lp::explanation::Explanation;
use crate::lp::gomory::get_gomory_cuts;
use crate::lp::hnf_cutter::make_hnf_cut;
use crate::lp::int_cube::{find_cube, find_largest_cube};
use crate::lp::lar_solver::{LarSolver, NULL_LPVAR};
use crate::lp::lar_term::LarTerm;
use crate::lp::numeric_pair::Impq;
use crate::util::error::SmtError;

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum LiaMove {
    Sat,
    Undef,
    Conflict,
    Continue,
    Cut { offset: Rational, is_upper: bool },
    Branch { is_upper: bool, offset: Rational },
}

fn get_fractional_part(value: &Rational) -> Rational {
    value.sub(&value.floor())
}

// gcd(a, b, u, v): the gcd of a and b, with a * u + b * v equal to it.
fn get_extended_gcd(first: &Int, second: &Int) -> [Int; 3] {
    let mut previous = [first.clone(), Int::one(), Int::zero()];
    let mut current = [second.clone(), Int::zero(), Int::one()];
    while !current[0].is_zero() {
        let quotient = &previous[0] / &current[0];
        let next = [
            &previous[0] - &(&quotient * &current[0]),
            &previous[1] - &(&quotient * &current[1]),
            &previous[2] - &(&quotient * &current[2]),
        ];
        previous = current;
        current = next;
    }
    if previous[0].is_negative() {
        previous.map(|value| -value)
    } else {
        previous
    }
}

struct PatchingDeltas {
    plus: Rational,
    minus: Rational,
}

// get_patching_deltas: the moves of a column with coefficient alpha that make x integral.
fn get_patching_deltas(x: &Rational, alpha: &Rational) -> Option<PatchingDeltas> {
    if !(alpha.den() % x.den()).is_zero() {
        return None;
    }
    let scale = alpha.den() / x.den();
    let [_, coeff, _] = get_extended_gcd(alpha.num(), x.den());
    let product = &(&coeff * &scale) * x.num();
    let remainder = &(&(&product % alpha.den()) + alpha.den()) % alpha.den();
    let plus = Rational::from_int(remainder);
    let minus = plus.sub(&Rational::from_int(alpha.den().clone()));
    Some(PatchingDeltas { plus, minus })
}

struct Parity {
    offset: Int,
    modulus: Int,
    // The row of the tableau, which no pivot changes during one GCD test.
    row: usize,
}

pub struct IntSolver {
    number_of_calls: u64,
    // m_parities and m_inserted_vars of the GCD test, for one test. Only looked up.
    parities: HashMap<usize, Vec<Parity>>,
    parity_columns: Vec<usize>,
    lcube_period: u64,
    pub explanation: Explanation,
    // m_t: the term of a branch or a cut, kept across calls as Z3 keeps its table.
    pub term: LarTerm,
    pub(crate) dio: DiophantineSolver,
    initial_dio_calls_period: u64,
    // m_dio_undef_in_a_row: the Diophantine solver's calls in a row that found nothing.
    dio_undef_in_a_row: u64,
}

impl IntSolver {
    pub fn new(lra: &mut LarSolver<'_>) -> IntSolver {
        IntSolver {
            number_of_calls: 0,
            parities: HashMap::new(),
            parity_columns: Vec::new(),
            lcube_period: lra.settings().int_find_cube_period,
            explanation: Explanation::new(),
            term: LarTerm::new(),
            initial_dio_calls_period: lra.settings().dio_calls_period,
            dio: DiophantineSolver::new(lra),
            dio_undef_in_a_row: 0,
        }
    }
}

// The integer solver with the LarSolver it works on.
pub struct Lia<'a, 'l> {
    pub lia: &'a mut IntSolver,
    pub lra: &'a mut LarSolver<'l>,
}

impl Deref for Lia<'_, '_> {
    type Target = IntSolver;

    fn deref(&self) -> &IntSolver {
        self.lia
    }
}

impl DerefMut for Lia<'_, '_> {
    fn deref_mut(&mut self) -> &mut IntSolver {
        self.lia
    }
}

impl<'l> Lia<'_, 'l> {
    pub fn is_column_int_inf(&self, column: usize) -> bool {
        self.lra.is_int(column) && !self.lra.get_value(column).is_int()
    }

    pub fn at_bound(&self, column: usize) -> bool {
        let core = &self.lra.core;
        let value = &core.x[column];
        match core.get_column_type(column) {
            COLUMN_FIXED | COLUMN_BOXED => {
                core.lower_bounds[column] == *value || core.upper_bounds[column] == *value
            }
            COLUMN_LOWER => core.lower_bounds[column] == *value,
            COLUMN_UPPER => core.upper_bounds[column] == *value,
            _ => false,
        }
    }

    pub fn at_lower(&self, column: usize) -> bool {
        let core = &self.lra.core;
        let column_type = core.get_column_type(column);
        let has_lower = column_type == COLUMN_FIXED
            || column_type == COLUMN_BOXED
            || column_type == COLUMN_LOWER;
        has_lower && core.lower_bounds[column] == core.x[column]
    }

    pub fn at_upper(&self, column: usize) -> bool {
        let core = &self.lra.core;
        let column_type = core.get_column_type(column);
        let has_upper = column_type == COLUMN_FIXED
            || column_type == COLUMN_BOXED
            || column_type == COLUMN_UPPER;
        has_upper && core.upper_bounds[column] == core.x[column]
    }

    fn hit_period(&mut self, period: u64) -> bool {
        period <= 1 || u64::from(self.lra.settings_mut().get_random_next()) % period == 0
    }

    fn has_ignored_terms(&self) -> bool {
        self.lra
            .dio_hooks
            .as_ref()
            .expect("the Diophantine solver installed its hooks")
            .has_ignored_terms
    }

    pub fn check(&mut self) -> Result<LiaMove, SmtError> {
        if !self.lra.has_inf_int() {
            return Ok(LiaMove::Sat);
        }
        self.lia.term.clear();
        self.lia.explanation.clear();
        // lp.dio_run_gcd is off, so the GCD test runs only when the Diophantine solver ignores terms.
        let lia_move = if self.has_ignored_terms() {
            self.gcd_test()
        } else {
            LiaMove::Undef
        };
        CoreSolver::without_touched_rows(
            self,
            |lia| &mut lia.lra.core,
            |lia| lia.check_after_gcd(lia_move),
        )
    }

    fn check_after_gcd(&mut self, gcd_move: LiaMove) -> Result<LiaMove, SmtError> {
        if self.lra.settings().is_canceled() {
            return Ok(LiaMove::Undef);
        }
        self.lia.number_of_calls += 1;
        let lia_move = if gcd_move == LiaMove::Undef {
            self.get_move_after_gcd()?
        } else {
            gcd_move
        };
        Ok(if self.lra.settings().is_canceled() {
            LiaMove::Undef
        } else {
            lia_move
        })
    }

    fn get_move_after_gcd(&mut self) -> Result<LiaMove, SmtError> {
        if self.patch_basic_columns() {
            return Ok(LiaMove::Sat);
        }
        let int_find_cube_period = self.lra.settings().int_find_cube_period;
        if self.hit_period(int_find_cube_period) && find_cube(self.lra) {
            return Ok(LiaMove::Sat);
        }
        let lcube_period = self.lia.lcube_period;
        if self.hit_period(lcube_period) && self.find_lcube()? {
            return Ok(LiaMove::Sat);
        }
        self.lra.move_non_basic_columns_to_bounds();
        let hnf_cut_period = self.lra.settings().hnf_cut_period;
        if self.hit_period(hnf_cut_period) {
            let lia_move = make_hnf_cut(self);
            if lia_move != LiaMove::Undef {
                return Ok(lia_move);
            }
        }
        if self.should_solve_diophantine_equations() {
            let lia_move = self.solve_diophantine_equations()?;
            if lia_move != LiaMove::Undef {
                return Ok(lia_move);
            }
        }
        let is_gomory_allowed =
            self.lra.settings().is_running_gomory_with_dio || self.has_ignored_terms();
        let int_gomory_cut_period = self.lra.settings().int_gomory_cut_period;
        if is_gomory_allowed && self.hit_period(int_gomory_cut_period) {
            let lia_move = get_gomory_cuts(self, 2);
            if lia_move != LiaMove::Undef {
                return Ok(lia_move);
            }
        }
        Ok(self.branch())
    }

    // find_lcube: the period doubles while the largest cube finds nothing, and resets when it finds a
    // solution.
    fn find_lcube(&mut self) -> Result<bool, SmtError> {
        let is_sat = find_largest_cube(self.lra)?;
        if is_sat {
            self.lia.lcube_period = self.lra.settings().int_find_cube_period;
        } else if self.lia.lcube_period < 1 << 30 {
            self.lia.lcube_period *= 2;
        }
        Ok(is_sat)
    }

    // should_solve_dioph_eq: a draw with the current period, which relaxes toward the initial one
    // when it misses.
    fn should_solve_diophantine_equations(&mut self) -> bool {
        let dio_calls_period = self.lra.settings().dio_calls_period;
        let is_hit = self.hit_period(dio_calls_period);
        let initial = self.lia.initial_dio_calls_period;
        let settings = self.lra.settings_mut();
        if !is_hit && settings.dio_calls_period > initial {
            let decrease = settings.dio_calls_period_decrease;
            settings.dio_calls_period = if settings.dio_calls_period > initial + decrease {
                settings.dio_calls_period - decrease
            } else {
                initial
            };
        }
        is_hit
    }

    // solve_dioph_eq: a conflict resets the period and stops Gomory cuts, and nothing found doubles
    // the period and starts Gomory cuts after enough failures in a row. Z3 also sets the GCD test's
    // flag, which it does not read while the Diophantine solver is on.
    fn solve_diophantine_equations(&mut self) -> Result<LiaMove, SmtError> {
        if DiophantineSolver::check(self)? == DioMove::Conflict {
            DiophantineSolver::explain(self)?;
            let initial = self.lia.initial_dio_calls_period;
            self.lia.dio_undef_in_a_row = 0;
            let settings = self.lra.settings_mut();
            settings.dio_calls_period = initial;
            settings.is_running_gomory_with_dio = false;
            return Ok(LiaMove::Conflict);
        }
        let settings = self.lra.settings_mut();
        // JavaScript's number doubles past any u64, where this saturates.
        settings.dio_calls_period = settings.dio_calls_period.saturating_mul(2);
        self.lia.dio_undef_in_a_row += 1;
        if self.lia.dio_undef_in_a_row >= self.lra.settings().dio_gomory_enable_period {
            self.lra.settings_mut().is_running_gomory_with_dio = true;
        }
        Ok(LiaMove::Undef)
    }

    // GCD test.

    fn gcd_test(&mut self) -> LiaMove {
        self.lra.settings_mut().stats.gcd_calls += 1;
        if self.is_gcd_test_feasible() {
            return LiaMove::Undef;
        }
        self.lra.settings_mut().stats.gcd_conflicts += 1;
        LiaMove::Conflict
    }

    // gcd_test: the rows of fractional basic columns, then the other rows of the columns whose
    // parity a row fixed.
    fn is_gcd_test_feasible(&mut self) -> bool {
        self.lia.parities.clear();
        self.lia.parity_columns.clear();
        // Only looked up, never iterated.
        let mut visited = HashSet::new();
        for row_index in 0..self.lra.get_row_count() {
            let basic = self.lra.core.basis[row_index];
            if !self.lra.is_int(basic) || self.lra.get_value(basic).is_int() {
                continue;
            }
            if !self.gcd_test_for_row(row_index) {
                return false;
            }
            visited.insert(row_index);
        }
        for index in (0..self.lia.parity_columns.len()).rev() {
            let column = self.lia.parity_columns[index];
            let cells = self.lra.core.matrix.columns[column].clone();
            for cell in cells {
                if !visited.insert(cell.row) {
                    continue;
                }
                if !self.gcd_test_for_row(cell.row) {
                    return false;
                }
            }
        }
        true
    }

    fn gcd_test_for_row(&mut self, row_index: usize) -> bool {
        let solver = &*self.lra;
        let basic = solver.core.basis[row_index];
        if !solver.is_int(basic) {
            return true;
        }
        let row = solver.get_row(row_index);
        let mut lcm_den = Int::one();
        for cell in row {
            lcm_den = get_lcm(&lcm_den, cell.coeff.den());
        }
        let lcm = Rational::from_int(lcm_den);
        let mut consts = Rational::zero();
        let mut gcds = Rational::zero();
        let mut least_coeff = Rational::zero();
        let mut is_least_coeff_bounded = false;
        let mut is_least_coeff_unique = false;
        let mut least_coeff_column = 0;
        for cell in row {
            let column = cell.column;
            let scaled = lcm.mul(&cell.coeff);
            if solver.is_fixed(column) {
                consts = consts.add(&scaled.mul(&solver.get_lower_bound(column).x));
                continue;
            }
            if !solver.is_int(column) {
                return true;
            }
            let magnitude = scaled.abs();
            let is_bounded = self.is_bounded(column);
            if gcds.is_zero() {
                gcds = magnitude.clone();
                least_coeff = magnitude;
                is_least_coeff_bounded = is_bounded;
                is_least_coeff_unique = true;
                least_coeff_column = column;
                continue;
            }
            gcds = Rational::from_int(get_gcd(gcds.num(), magnitude.num()));
            let comparison = magnitude.compare(&least_coeff);
            if comparison.is_lt() {
                least_coeff = magnitude;
                is_least_coeff_bounded = is_bounded;
                is_least_coeff_unique = true;
                least_coeff_column = column;
            } else if comparison.is_eq() {
                is_least_coeff_bounded = is_least_coeff_bounded && is_bounded;
                is_least_coeff_unique = false;
            }
        }
        if gcds.is_zero() {
            return true;
        }
        if !consts.div(&gcds).is_int() {
            self.fill_explanation_from_fixed_columns(row_index);
            return false;
        }
        if is_least_coeff_bounded
            && least_coeff != Rational::one()
            && !self.lra.get_value(basic).is_int()
            && !self.ext_gcd_test(row_index, &lcm, &consts, &least_coeff)
        {
            return false;
        }
        if !is_least_coeff_unique {
            return true;
        }
        self.accumulate_parity(row_index, least_coeff_column, &lcm, &consts, &least_coeff)
    }

    // accumulate_parity: the row fixes the residue of its unique least column modulo the gcd of the
    // others, and two rows that fix different residues for the same modulus conflict.
    fn accumulate_parity(
        &mut self,
        row_index: usize,
        least_column: usize,
        lcm: &Rational,
        consts: &Rational,
        least_coeff: &Rational,
    ) -> bool {
        let solver = &*self.lra;
        let mut modulus = Int::zero();
        let mut is_least_negative = false;
        for cell in solver.get_row(row_index) {
            if cell.column == least_column {
                is_least_negative = cell.coeff.is_negative();
            } else if !solver.is_fixed(cell.column) {
                let magnitude = lcm.mul(&cell.coeff).abs().num().clone();
                if get_gcd(least_coeff.num(), &magnitude) != *least_coeff.num() {
                    return true;
                }
                modulus = if modulus.is_zero() {
                    magnitude
                } else {
                    get_gcd(&modulus, &magnitude)
                };
                if modulus == 1 {
                    return true;
                }
            }
        }
        modulus = &modulus / least_coeff.num();
        if modulus.is_zero() {
            return true;
        }
        let quotient = consts.div(least_coeff);
        if !quotient.is_int() {
            return true;
        }
        let mut offset = &(&(quotient.num() % &modulus) + &modulus) % &modulus;
        if !is_least_negative && !offset.is_zero() {
            offset = &modulus - &offset;
        }
        self.insert_parity(least_column, row_index, offset, modulus)
    }

    fn insert_parity(
        &mut self,
        column: usize,
        row_index: usize,
        offset: Int,
        modulus: Int,
    ) -> bool {
        let parities = self.lia.parities.get(&column);
        for parity in parities.into_iter().flatten() {
            if parity.modulus != modulus {
                continue;
            }
            if parity.offset == offset {
                return true;
            }
            let parity_row = parity.row;
            self.fill_explanation_from_fixed_columns(row_index);
            self.fill_explanation_from_fixed_columns(parity_row);
            return false;
        }
        self.lia.parity_columns.push(column);
        self.lia.parities.entry(column).or_default().push(Parity {
            offset,
            modulus,
            row: row_index,
        });
        true
    }

    fn is_bounded(&self, column: usize) -> bool {
        let column_type = self.lra.core.get_column_type(column);
        column_type == COLUMN_BOXED || column_type == COLUMN_FIXED
    }

    fn ext_gcd_test(
        &mut self,
        row_index: usize,
        lcm: &Rational,
        consts: &Rational,
        least_coeff: &Rational,
    ) -> bool {
        let solver = &*self.lra;
        let mut gcds = Rational::zero();
        let mut lower = consts.clone();
        let mut upper = consts.clone();
        let mut boxed = Vec::new();
        for cell in solver.get_row(row_index) {
            let column = cell.column;
            if solver.is_fixed(column) {
                continue;
            }
            let scaled = lcm.mul(&cell.coeff);
            let magnitude = scaled.abs();
            if magnitude == *least_coeff {
                let low = &solver.get_lower_bound(column).x;
                let high = &solver.get_upper_bound(column).x;
                lower = lower.add(&scaled.mul(if scaled.is_positive() { low } else { high }));
                upper = upper.add(&scaled.mul(if scaled.is_positive() { high } else { low }));
                boxed.push(column);
            } else {
                gcds = if gcds.is_zero() {
                    magnitude
                } else {
                    Rational::from_int(get_gcd(gcds.num(), magnitude.num()))
                };
            }
        }
        if gcds.is_zero() {
            return true;
        }
        if upper
            .div(&gcds)
            .floor()
            .compare(&lower.div(&gcds).ceil())
            .is_ge()
        {
            return true;
        }
        for column in boxed {
            self.add_bound_witnesses(column);
        }
        self.fill_explanation_from_fixed_columns(row_index);
        false
    }

    fn add_bound_witnesses(&mut self, column: usize) {
        self.lia
            .explanation
            .push_dependency(&self.lra.get_bound_witnesses(column));
    }

    fn fill_explanation_from_fixed_columns(&mut self, row_index: usize) {
        for cell in self.lra.get_row(row_index) {
            if self.lra.is_fixed(cell.column) {
                self.lia
                    .explanation
                    .push_dependency(&self.lra.get_bound_witnesses(cell.column));
            }
        }
    }

    // Patching.

    fn patch_basic_columns(&mut self) -> bool {
        self.lra.settings_mut().stats.patches += 1;
        self.lra.remove_fixed_vars_from_base();
        for index in 0..self.lra.core.basis.len() {
            let column = self.lra.core.basis[index];
            if !self.lra.get_model_value(column).is_int()
                && self.lra.is_int(column)
                && !self.lra.is_fixed(column)
            {
                self.patch_basic_column(column);
            }
        }
        if self.lra.has_inf_int() {
            return false;
        }
        self.lra.settings_mut().stats.patches_success += 1;
        true
    }

    fn patch_basic_column(&mut self, basic: usize) {
        let row = self
            .lra
            .get_row(self.lra.core.heading[basic] as usize)
            .to_vec();
        for cell in row {
            if cell.column == basic || !self.lra.is_int(cell.column) || cell.coeff.is_int() {
                continue;
            }
            let Some(deltas) = get_patching_deltas(
                &get_fractional_part(&self.lra.get_model_value(basic)),
                &get_fractional_part(&cell.coeff),
            ) else {
                continue;
            };
            let is_plus_first = !self.lra.settings_mut().get_random_next().is_multiple_of(2);
            let first = if is_plus_first {
                &deltas.plus
            } else {
                &deltas.minus
            };
            let second = if is_plus_first {
                &deltas.minus
            } else {
                &deltas.plus
            };
            if self.try_patch_column(cell.column, first)
                || self.try_patch_column(cell.column, second)
            {
                return;
            }
        }
    }

    fn try_patch_column(&mut self, column: usize, delta: &Rational) -> bool {
        let solver = &*self.lra;
        let core = &solver.core;
        let value = solver.get_value(column).add(&Impq::from_x(delta.clone()));
        if delta.is_negative() {
            if core.has_lower_bound(column) && value.compare(solver.get_lower_bound(column)).is_lt()
            {
                return false;
            }
        } else if core.has_upper_bound(column)
            && value.compare(solver.get_upper_bound(column)).is_gt()
        {
            return false;
        }
        for cell in &core.matrix.columns[column] {
            let basic = core.basis[cell.row];
            let old_value = solver.get_value(basic);
            let new_value = Impq::new(
                old_value.x.sub(&core.matrix.get_val(cell).mul(delta)),
                old_value.y.clone(),
            );
            if core.has_lower_bound(basic)
                && new_value.compare(solver.get_lower_bound(basic)).is_lt()
            {
                return false;
            }
            if core.has_upper_bound(basic)
                && new_value.compare(solver.get_upper_bound(basic)).is_gt()
            {
                return false;
            }
            if old_value.is_int() && !new_value.is_int() {
                return false;
            }
        }
        self.lra.set_value_for_nbasic_column(column, value);
        true
    }

    // Branching.

    fn branch(&mut self) -> LiaMove {
        self.lra.move_non_basic_columns_to_bounds();
        let column = self.find_inf_int_base_column();
        if column == NULL_LPVAR {
            return LiaMove::Sat;
        }
        self.lra.settings_mut().stats.branches += 1;
        self.lia.term.clear();
        self.lia.term.add_monomial(&Rational::one(), column);
        let is_upper = !self.lra.settings_mut().get_random_next().is_multiple_of(2);
        let value = self.lra.get_value(column);
        let is_free = self.lra.core.get_column_type(column) == COLUMN_FREE;
        let offset = if is_free {
            Rational::zero()
        } else if is_upper {
            value.floor()
        } else {
            value.ceil()
        };
        LiaMove::Branch { is_upper, offset }
    }

    fn find_inf_int_base_column(&mut self) -> usize {
        let small_value = Rational::from_i64(1024);
        let mut small_box = NULL_LPVAR;
        let mut small_value_column = NULL_LPVAR;
        let mut any_value = NULL_LPVAR;
        let mut num_small_box = 1;
        let mut num_small_value = 1;
        let mut num_any_value = 1;
        let mut range = Rational::zero();
        let mut min_any_value = Rational::zero();
        let mut previous_usage = 0;
        for index in 0..self.lra.core.basis.len() {
            let column = self.lra.core.basis[index];
            if !self.is_column_int_inf(column) {
                continue;
            }
            if self.lra.settings().is_canceled() {
                return NULL_LPVAR;
            }
            let usage = self.lra.get_usage_in_terms(column);
            if self.lra.core.get_column_type(column) == COLUMN_BOXED {
                let new_range = self
                    .lra
                    .get_upper_bound(column)
                    .x
                    .sub(&self.lra.get_lower_bound(column).x)
                    .sub(&Rational::from_i64(2 * usage as i64));
                if new_range.compare(&small_value).is_le() {
                    let is_improved = small_box == NULL_LPVAR || new_range.compare(&range).is_le();
                    if is_improved {
                        range = new_range;
                    }
                    if small_box == NULL_LPVAR {
                        small_box = column;
                    } else if is_improved {
                        num_small_box += 1;
                        if self
                            .lra
                            .settings_mut()
                            .get_random_next()
                            .is_multiple_of(num_small_box)
                        {
                            small_box = column;
                        }
                    }
                    continue;
                }
            }
            let solver = &*self.lra;
            let core = &solver.core;
            let value = solver.get_value(column);
            if value.x.abs().compare(&small_value).is_lt()
                || (core.has_upper_bound(column)
                    && small_value
                        .compare(&solver.get_upper_bound(column).x.sub(&value.x))
                        .is_gt())
                || (core.has_lower_bound(column)
                    && small_value
                        .compare(&value.x.sub(&solver.get_lower_bound(column).x))
                        .is_gt())
            {
                if small_value_column == NULL_LPVAR {
                    small_value_column = column;
                } else {
                    num_small_value += 1;
                    if self
                        .lra
                        .settings_mut()
                        .get_random_next()
                        .is_multiple_of(num_small_value)
                    {
                        small_value_column = column;
                    }
                }
                continue;
            }
            let magnitude = value.x.abs();
            if any_value == NULL_LPVAR || magnitude.compare(&min_any_value).is_lt() {
                any_value = column;
                min_any_value = magnitude;
                num_any_value = 1;
                previous_usage = usage;
            } else if magnitude == min_any_value {
                if usage >= previous_usage {
                    num_any_value += 1;
                    if self
                        .lra
                        .settings_mut()
                        .get_random_next()
                        .is_multiple_of(num_any_value)
                    {
                        any_value = column;
                    }
                }
                if usage > previous_usage {
                    previous_usage = usage;
                }
            }
        }
        if small_box != NULL_LPVAR && !self.lra.settings_mut().get_random_next().is_multiple_of(3) {
            return small_box;
        }
        if small_value_column != NULL_LPVAR
            && !self.lra.settings_mut().get_random_next().is_multiple_of(3)
        {
            return small_value_column;
        }
        if any_value != NULL_LPVAR {
            return any_value;
        }
        if small_box != NULL_LPVAR {
            small_box
        } else {
            small_value_column
        }
    }
}
