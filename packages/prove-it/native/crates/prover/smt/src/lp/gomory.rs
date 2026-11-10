// Ported from Z3 (src/math/lp/gomory.cpp), MIT license, see z3-license.txt. Gomory cuts: from the
// row of a fractional basic column whose non-basic columns sit at bounds, the inequality that every
// integer solution meets and the current solution violates.
use std::collections::HashMap;

use prove_num::Rational;

use crate::lp::constraints::{KIND_GE, KIND_LE};
use crate::lp::core_solver::LP_CANCELLED;
use crate::lp::dependency::{Dependency, mk_join, mk_leaf};
use crate::lp::int_solver::{Lia, LiaMove};
use crate::lp::lar_solver::{LarSolver, NULL_LPVAR};
use crate::lp::numeric_pair::Impq;
use crate::lp::static_matrix::RowCell;

const POLARITY_UNDEF: u8 = 0;
const POLARITY_MIN: u8 = 1;
const POLARITY_MAX: u8 = 2;
const POLARITY_MIXED: u8 = 3;

fn get_half() -> Rational {
    Rational::from_i64(1).div(&Rational::from_i64(2))
}

fn get_fractional_part(value: &Rational) -> Rational {
    value.sub(&value.floor())
}

struct Cut {
    coeffs: Vec<(usize, Rational)>,
    offset: Rational,
    dep: Dependency,
}

// The "undef", "conflict" and "cut" that TypeScript's create_cut returns.
#[derive(PartialEq, Eq)]
enum CutResult {
    Undef,
    Conflict,
    Cut,
}

// create_cut: the cut of one row, in the term and the offset of the integer solver.
struct CutBuilder {
    polarity: u8,
    offset: Rational,
    dep: Dependency,
    f: Rational,
    one_minus_f: Rational,
    big_number: Rational,
    is_big_found: bool,
    inf_column: usize,
    // The row of the tableau, which nothing pivots while the cut is built.
    row: Vec<RowCell>,
}

impl CutBuilder {
    fn new(lia: &Lia<'_, '_>, inf_column: usize, row: Vec<RowCell>) -> CutBuilder {
        let f = get_fractional_part(&lia.lra.get_value(inf_column).x);
        let one_minus_f = Rational::one().sub(&f);
        CutBuilder {
            polarity: POLARITY_UNDEF,
            offset: Rational::one(),
            dep: None,
            f,
            one_minus_f,
            big_number: Rational::zero(),
            is_big_found: false,
            inf_column,
            row,
        }
    }

    fn set_polarity(&mut self, polarity: u8) {
        if self.polarity == POLARITY_MIXED {
            return;
        }
        if self.polarity == POLARITY_UNDEF {
            self.polarity = polarity;
        } else if self.polarity != polarity {
            self.polarity = POLARITY_MIXED;
        }
    }

    fn set_polarity_for_int(&mut self, lia: &Lia<'_, '_>, coeff: &Rational, column: usize) {
        let is_lower = lia.at_lower(column);
        let is_upper = !is_lower && lia.at_upper(column);
        let toward_max = if coeff.is_positive() {
            is_lower
        } else {
            is_upper
        };
        let toward_min = if coeff.is_positive() {
            is_upper
        } else {
            is_lower
        };
        self.set_polarity(if toward_max {
            POLARITY_MAX
        } else if toward_min {
            POLARITY_MIN
        } else {
            POLARITY_MIXED
        });
    }

    fn add_monomial(&mut self, lia: &mut Lia<'_, '_>, new_a: &Rational, column: usize) {
        lia.lia.term.add_monomial(new_a, column);
        if Rational::from_int(new_a.num().clone())
            .compare(&self.big_number)
            .is_gt()
        {
            self.is_big_found = true;
        }
    }

    // int_case_in_gomory_cut, with fj the fractional part of the negated coefficient.
    fn add_int_case(&mut self, lia: &mut Lia<'_, '_>, column: usize, fj: &Rational) {
        let one_minus_fj = Rational::one().sub(fj);
        if lia.at_lower(column) {
            let new_a = if fj.compare(&self.one_minus_f).is_le() {
                fj.div(&self.one_minus_f)
            } else {
                one_minus_fj.div(&self.f)
            };
            self.offset = self
                .offset
                .add(&new_a.mul(&lia.lra.get_lower_bound(column).x));
            lia.lia
                .explanation
                .push_dependency(lia.lra.get_lower_witness(column));
            self.add_monomial(lia, &new_a, column);
            return;
        }
        let new_a = if fj.compare(&self.f).is_le() {
            fj.div(&self.f)
        } else {
            one_minus_fj.div(&self.one_minus_f)
        }
        .neg();
        self.offset = self
            .offset
            .add(&new_a.mul(&lia.lra.get_upper_bound(column).x));
        lia.lia
            .explanation
            .push_dependency(lia.lra.get_upper_witness(column));
        self.add_monomial(lia, &new_a, column);
    }

    // real_case_in_gomory_cut, with a the negated coefficient.
    fn add_real_case(&mut self, lia: &mut Lia<'_, '_>, a: &Rational, column: usize) {
        let is_lower = lia.at_lower(column);
        let is_growing = a.is_positive() == is_lower;
        let new_a = if is_growing {
            a.div(&self.one_minus_f)
        } else {
            a.neg().div(&self.f)
        };
        self.set_polarity(if is_growing {
            POLARITY_MIN
        } else {
            POLARITY_MAX
        });
        let bound = if is_lower {
            lia.lra.get_lower_bound(column)
        } else {
            lia.lra.get_upper_bound(column)
        };
        self.offset = self.offset.add(&new_a.mul(&bound.x));
        lia.lia.explanation.push_dependency(if is_lower {
            lia.lra.get_lower_witness(column)
        } else {
            lia.lra.get_upper_witness(column)
        });
        self.add_monomial(lia, &new_a, column);
    }

    fn cut(&mut self, lia: &mut Lia<'_, '_>) -> CutResult {
        lia.lia.term.clear();
        lia.lia.explanation.clear();
        let mut abs_max = Rational::zero();
        for cell in &self.row {
            let value = cell.coeff.ceil().abs();
            if value.compare(&abs_max).is_gt() {
                abs_max = value;
            }
        }
        self.big_number = abs_max.mul(&abs_max);
        for index in 0..self.row.len() {
            let column = self.row[index].column;
            let coeff = self.row[index].coeff.clone();
            if column == self.inf_column {
                continue;
            }
            if lia.lra.is_fixed(column) {
                lia.lia
                    .explanation
                    .push_dependency(lia.lra.get_lower_witness(column));
                lia.lia
                    .explanation
                    .push_dependency(lia.lra.get_upper_witness(column));
                continue;
            }
            if !lia.lra.is_int(column) {
                self.add_real_case(lia, &coeff.neg(), column);
            } else {
                if !coeff.is_int() {
                    self.add_int_case(lia, column, &get_fractional_part(&coeff.neg()));
                }
                if self.polarity != POLARITY_MIXED {
                    self.set_polarity_for_int(lia, &coeff, column);
                }
            }
            if self.is_big_found {
                return CutResult::Undef;
            }
        }
        if lia.lia.term.size() == 0 {
            return CutResult::Conflict;
        }
        for constraint in lia.lia.explanation.iter() {
            self.dep = mk_join(&mk_leaf(constraint as u32), &self.dep);
        }
        CutResult::Cut
    }
}

// get_gomory_score: the distance of the value of the column to the nearest integer.
fn get_gomory_score(lia: &Lia<'_, '_>, column: usize) -> Rational {
    let value = &lia.lra.get_value(column).x;
    let fraction = get_fractional_part(value);
    if fraction.compare(&get_half()).is_le() {
        fraction
    } else {
        Rational::one().sub(&fraction)
    }
}

// is_gomory_cut_target: every other column of the row is integral with an integral coefficient,
// or sits at a bound without an infinitesimal.
fn is_gomory_cut_target(lia: &Lia<'_, '_>, column: usize) -> bool {
    let solver = &*lia.lra;
    for cell in solver.get_row(solver.core.heading[column] as usize) {
        if cell.column == column {
            continue;
        }
        let value = solver.get_value(cell.column);
        if cell.coeff.is_int() && solver.is_int(cell.column) && value.is_int() {
            continue;
        }
        if !lia.at_bound(cell.column) || !value.y.is_zero() {
            return false;
        }
    }
    true
}

// gomory_select_int_infeasible_vars: up to the given number of target columns, drawn with a bias
// toward the values closest to integers.
fn select_columns(lia: &mut Lia<'_, '_>, cut_count: usize) -> Vec<usize> {
    // Only looked up, never iterated.
    let mut scores = HashMap::new();
    let mut sorted = Vec::new();
    for index in 0..lia.lra.core.basis.len() {
        let column = lia.lra.core.basis[index];
        if !lia.is_column_int_inf(column) || !is_gomory_cut_target(lia, column) {
            continue;
        }
        sorted.push(column);
        scores.insert(column, get_gomory_score(lia, column));
    }
    let solver = &*lia.lra;
    let zero = Rational::zero();
    sorted.sort_by(|first, second| {
        let by_score = scores
            .get(first)
            .unwrap_or(&zero)
            .compare(scores.get(second).unwrap_or(&zero));
        if by_score.is_ne() {
            return by_score;
        }
        solver
            .get_usage_in_terms(*second)
            .cmp(&solver.get_usage_in_terms(*first))
    });
    let mut selected = Vec::new();
    let mut remaining = cut_count;
    while remaining > 0 && !sorted.is_empty() {
        let count = sorted.len();
        let ratio =
            (lia.lra.settings_mut().get_random_next() as usize % count) as f64 / count as f64;
        let index = (ratio * ratio * ratio * count as f64).floor() as usize;
        selected.push(sorted[index]);
        sorted.remove(index);
        remaining -= 1;
    }
    selected
}

// add_deps: the bounds of the integer columns with integral coefficients, which the cut leaves
// out of its explanation.
fn add_deps(lia: &Lia<'_, '_>, dep: &Dependency, row: &[RowCell], basic: usize) -> Dependency {
    let solver = &*lia.lra;
    let mut result = dep.clone();
    for cell in row {
        let column = cell.column;
        if column == basic || solver.is_fixed(column) || !solver.is_int(column) {
            continue;
        }
        if !cell.coeff.is_int() {
            continue;
        }
        let witness = if lia.at_lower(column) {
            solver.get_lower_witness(column)
        } else {
            solver.get_upper_witness(column)
        };
        result = mk_join(witness, &result);
    }
    result
}

fn add_cut(solver: &mut LarSolver<'_>, cut: &Cut) {
    let column = solver.add_term(&cut.coeffs, NULL_LPVAR);
    solver.update_column_type_and_bound(
        column,
        KIND_GE,
        &Impq::from_x(cut.offset.clone()),
        cut.dep.clone(),
    );
}

fn is_feasible(lia: &mut Lia<'_, '_>) -> bool {
    lia.lra.find_feasible_solution();
    if lia.lra.is_feasible() || lia.lra.settings().is_canceled() {
        return true;
    }
    lia.lra
        .get_infeasibility_explanation(&mut lia.lia.explanation);
    false
}

// get_gomory_cuts: cuts for the selected rows. Cuts with big coefficients stay out unless the
// small ones alone leave the problem feasible.
pub fn get_gomory_cuts(lia: &mut Lia<'_, '_>, cut_count: usize) -> LiaMove {
    let mut big_cuts = Vec::new();
    let mut has_small_cut = false;
    for column in select_columns(lia, cut_count) {
        let row = lia
            .lra
            .get_row(lia.lra.core.heading[column] as usize)
            .to_vec();
        let mut builder = CutBuilder::new(lia, column, row);
        match builder.cut(lia) {
            CutResult::Conflict => return LiaMove::Conflict,
            CutResult::Undef => continue,
            CutResult::Cut => {}
        }
        let value = lia.lra.get_value(column).x.clone();
        if builder.polarity == POLARITY_MAX {
            let dep = add_deps(lia, &builder.dep, &builder.row, column);
            lia.lra.update_column_type_and_bound(
                column,
                KIND_LE,
                &Impq::from_x(value.floor()),
                dep,
            );
        } else if builder.polarity == POLARITY_MIN {
            let dep = add_deps(lia, &builder.dep, &builder.row, column);
            lia.lra
                .update_column_type_and_bound(column, KIND_GE, &Impq::from_x(value.ceil()), dep);
        }
        let cut = Cut {
            coeffs: lia
                .lia
                .term
                .iter()
                .map(|entry| (entry.0, entry.1.clone()))
                .collect(),
            offset: builder.offset,
            dep: builder.dep,
        };
        if cut.coeffs.iter().any(|entry| entry.1.is_big()) {
            big_cuts.push(cut);
            continue;
        }
        has_small_cut = true;
        add_cut(lia.lra, &cut);
        if lia.lra.settings().is_canceled() {
            return LiaMove::Undef;
        }
    }
    if !big_cuts.is_empty() {
        lia.lra.push();
        for cut in &big_cuts {
            add_cut(lia.lra, cut);
        }
        let is_big_feasible = is_feasible(lia);
        lia.lra.pop(1);
        if !is_big_feasible {
            for cut in &big_cuts {
                add_cut(lia.lra, cut);
            }
        }
    }
    if !is_feasible(lia) {
        return LiaMove::Conflict;
    }
    if lia.lra.status == LP_CANCELLED {
        return LiaMove::Undef;
    }
    if !lia.lra.has_inf_int() {
        return LiaMove::Sat;
    }
    if has_small_cut || !big_cuts.is_empty() {
        return LiaMove::Continue;
    }
    lia.lra.move_non_basic_columns_to_bounds();
    LiaMove::Undef
}
