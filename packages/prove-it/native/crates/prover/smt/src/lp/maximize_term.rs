// Ported from Z3 (maximize_term and its helpers in src/math/lp/lar_solver.cpp, and the tableau
// part of src/math/lp/lp_primal_core_solver.h, src/math/lp/lp_primal_core_solver_def.h,
// src/math/lp/lp_primal_core_solver_tableau_def.h), MIT license, see z3-license.txt. The primal
// simplex with the tableau_costs strategy: from a feasible solution, a non-basic column whose
// reduced cost improves the objective enters, the ratio test picks the basic column that leaves,
// and the reduced costs follow every pivot.
use std::cmp::Ordering;

use prove_num::Rational;

use crate::lp::core_solver::{
    COLUMN_BOXED, COLUMN_FIXED, COLUMN_FREE, COLUMN_LOWER, COLUMN_UPPER, CoreSolver, LP_CANCELLED,
    LP_FEASIBLE, LP_INFEASIBLE, LP_OPTIMAL, LP_UNBOUNDED,
};
use crate::lp::lar_solver::LarSolver;
use crate::lp::lar_term::LarTerm;
use crate::lp::numeric_pair::Impq;

// m_nbasis_sort_counter: the non-basic columns are sorted again after this many choices.
const NBASIS_SORT_PERIOD: u64 = 20;
// percent_of_entering_to_check, for more than 300 non-basic columns.
const PERCENT_OF_ENTERING_TO_CHECK: usize = 5;

// The theta of a ratio test, and whether a bound limits it yet.
struct ThetaLimit {
    theta: Impq,
    is_unlimited: bool,
}

impl ThetaLimit {
    fn new() -> ThetaLimit {
        ThetaLimit {
            theta: Impq::zero(),
            is_unlimited: true,
        }
    }
}

fn limit_theta(limit: &mut ThetaLimit, value: Impq) {
    if limit.is_unlimited {
        limit.theta = value;
        limit.is_unlimited = false;
    } else if value.compare(&limit.theta) == Ordering::Less {
        limit.theta = value;
    }
}

fn clamp_theta(limit: &mut ThetaLimit) {
    if limit.theta.compare(&Impq::zero()) == Ordering::Less {
        limit.theta = Impq::zero();
    }
}

fn stop_at_zero(limit: &mut ThetaLimit) {
    limit.theta = Impq::zero();
    limit.is_unlimited = false;
}

// TypeScript's CostsSimplex holds the reduced costs, the same array as core.reducedCosts; here it
// reads them from the core.
struct CostsSimplex<'a, 'l> {
    core: &'a mut CoreSolver<'l>,
    sort_counter: u64,
    non_basis_list: Vec<usize>,
    sign_of_entering_delta: i64,
}

impl<'l> CostsSimplex<'_, 'l> {
    fn get_reduced_cost(&self, column: usize) -> &Rational {
        &self
            .core
            .reduced_costs
            .as_ref()
            .expect("the costs simplex has reduced costs")[column]
    }

    // lar_core_solver::solve and lp_primal_core_solver::solve, not only looking for a feasible
    // solution.
    fn solve(&mut self) {
        self.core.status = LP_FEASIBLE;
        loop {
            if self.core.settings.is_canceled() {
                self.core.status = LP_CANCELLED;
                return;
            }
            self.one_iteration();
            if self.core.settings.is_canceled() {
                self.core.status = LP_CANCELLED;
                return;
            }
            let status = self.core.status;
            if status == LP_UNBOUNDED || status == LP_OPTIMAL || status == LP_INFEASIBLE {
                return;
            }
        }
    }

    // one_iteration_tableau.
    fn one_iteration(&mut self) {
        let Some(entering) = self.choose_entering() else {
            self.core.status = if self.core.is_feasible() {
                LP_OPTIMAL
            } else {
                LP_INFEASIBLE
            };
            return;
        };
        let mut limit = ThetaLimit::new();
        let Some(leaving) = self.find_leaving(entering, &mut limit) else {
            self.core.status = LP_UNBOUNDED;
            return;
        };
        self.advance(entering, leaving, &limit.theta);
    }

    // sort_non_basis: the non-basic columns by the size of their columns, the empty ones last.
    fn sort_non_basis(&mut self) {
        let core = &mut *self.core;
        let columns = &core.matrix.columns;
        core.nbasis.sort_by(|first, second| {
            let first_size = columns[*first].len();
            let second_size = columns[*second].len();
            if first_size == 0 && second_size != 0 {
                return Ordering::Greater;
            }
            if first_size != 0 && second_size == 0 {
                return Ordering::Less;
            }
            if first_size != second_size {
                first_size.cmp(&second_size)
            } else {
                first.cmp(second)
            }
        });
        self.non_basis_list = core.nbasis.clone();
        for (index, column) in core.nbasis.iter().enumerate() {
            core.heading[*column] = -(index as i64) - 1;
        }
    }

    // get_number_of_non_basic_column_to_try_for_enter.
    fn get_number_to_try(&mut self) -> usize {
        let count = self.core.nbasis.len();
        let scaled = if count > 300 {
            count * PERCENT_OF_ENTERING_TO_CHECK / 100
        } else {
            count
        };
        if scaled == 0 {
            return 0;
        }
        (self.core.settings.get_random_next() as usize % scaled).max(1)
    }

    // choose_entering_column_tableau: among the first beneficial columns, the one with the fewest
    // cells, and a random one among ties. It moves to the end of the list.
    fn choose_entering(&mut self) -> Option<usize> {
        if self.sort_counter == 0 {
            self.sort_non_basis();
            self.sort_counter = NBASIS_SORT_PERIOD;
        } else {
            self.sort_counter -= 1;
        }
        let mut num_to_go_over = self.get_number_to_try();
        if num_to_go_over == 0 {
            return None;
        }
        let mut min_cells = self.core.matrix.get_row_count() + 1;
        let mut entering_index: Option<usize> = None;
        let mut num_ties: u32 = 0;
        let mut index = 0;
        while num_to_go_over > 0 && index < self.non_basis_list.len() {
            let column = self.non_basis_list[index];
            if self.is_beneficial(column) {
                let cells = self.core.matrix.columns[column].len();
                if cells < min_cells {
                    min_cells = cells;
                    entering_index = Some(index);
                    num_to_go_over -= 1;
                    num_ties = 1;
                } else if cells == min_cells {
                    num_ties += 1;
                    if self.core.settings.get_random_next_below(num_ties) == 0 {
                        entering_index = Some(index);
                    }
                }
            }
            index += 1;
        }
        let entering_index = entering_index?;
        let entering = self.non_basis_list[entering_index];
        self.sign_of_entering_delta = if self.get_reduced_cost(entering).is_positive() {
            1
        } else {
            -1
        };
        self.non_basis_list.remove(entering_index);
        self.non_basis_list.push(entering);
        Some(entering)
    }

    // column_is_benefitial_for_entering_basis.
    fn is_beneficial(&self, column: usize) -> bool {
        let core = &self.core;
        let reduced_cost = self.get_reduced_cost(column);
        if reduced_cost.is_zero() {
            return false;
        }
        match core.get_column_type(column) {
            COLUMN_FREE => true,
            COLUMN_LOWER => reduced_cost.is_positive(),
            COLUMN_UPPER => reduced_cost.is_negative(),
            COLUMN_BOXED => {
                if reduced_cost.is_positive() {
                    core.x[column] == core.lower_bounds[column]
                } else {
                    core.x[column] == core.upper_bounds[column]
                }
            }
            _ => false,
        }
    }

    // find_leaving_and_t_tableau: the basic column that the ratio test stops first, with ties
    // broken by the shortest row and then at random, or the entering column itself when it reaches
    // its other bound first.
    fn find_leaving(&mut self, entering: usize, limit: &mut ThetaLimit) -> Option<usize> {
        let sign = Rational::from_i64(self.sign_of_entering_delta);
        let column_length = self.core.matrix.columns[entering].len();
        let mut candidates: Vec<usize> = Vec::new();
        let mut min_row_cells = self.core.matrix.get_column_count() + 1;
        let mut index = 0;
        while index < column_length && limit.is_unlimited {
            let cell = self.core.matrix.columns[entering][index];
            index += 1;
            let basic = self.core.basis[cell.row];
            let m = self.core.matrix.get_val(&cell).neg().mul(&sign);
            self.limit_theta_on_basis_column(basic, &m, limit);
            if limit.is_unlimited {
                continue;
            }
            candidates.push(basic);
            min_row_cells = self.core.matrix.rows[cell.row].len();
        }
        let core = &mut *self.core;
        if limit.is_unlimited {
            if core.get_column_type(entering) != COLUMN_BOXED {
                return None;
            }
            limit.theta = if self.sign_of_entering_delta > 0 {
                core.upper_bounds[entering].sub(&core.x[entering])
            } else {
                core.x[entering].sub(&core.lower_bounds[entering])
            };
            return Some(entering);
        }
        while index < column_length {
            let cell = self.core.matrix.columns[entering][index];
            index += 1;
            let basic = self.core.basis[cell.row];
            let mut ratio = ThetaLimit::new();
            let m = self.core.matrix.get_val(&cell).neg().mul(&sign);
            self.limit_theta_on_basis_column(basic, &m, &mut ratio);
            if ratio.is_unlimited {
                continue;
            }
            let row_cells = self.core.matrix.rows[cell.row].len();
            let comparison = ratio.theta.compare(&limit.theta);
            if comparison == Ordering::Less {
                limit.theta = ratio.theta;
                candidates = vec![basic];
                min_row_cells = row_cells;
            } else if comparison == Ordering::Equal && row_cells < min_row_cells {
                candidates = vec![basic];
                min_row_cells = row_cells;
            } else if comparison == Ordering::Equal && row_cells == min_row_cells {
                candidates.push(basic);
            }
        }
        let core = &mut *self.core;
        if core.get_column_type(entering) == COLUMN_BOXED {
            let span = core.upper_bounds[entering].sub(&core.lower_bounds[entering]);
            if span.compare(&limit.theta) != Ordering::Greater {
                limit.theta = span;
                return Some(entering);
            }
        }
        if candidates.len() == 1 {
            return Some(candidates[0]);
        }
        Some(candidates[core.settings.get_random_next() as usize % candidates.len()])
    }

    // limit_theta_on_basis_column: x[basic] + theta * m stays within the bounds of the column, or
    // moves toward them when it is outside.
    fn limit_theta_on_basis_column(&self, basic: usize, m: &Rational, limit: &mut ThetaLimit) {
        let core = &self.core;
        let x = &core.x[basic];
        let lower = &core.lower_bounds[basic];
        let upper = &core.upper_bounds[basic];
        let is_feasible = core.is_feasible();
        let limit_by =
            |limit: &mut ThetaLimit, bound: &Impq| limit_theta(limit, bound.sub(x).div(m));
        let limit_feasibly = |limit: &mut ThetaLimit, bound: &Impq| {
            limit_by(limit, bound);
            clamp_theta(limit);
        };
        match core.get_column_type(basic) {
            COLUMN_UPPER => {
                if is_feasible {
                    if m.is_positive() {
                        limit_feasibly(limit, upper);
                    }
                } else if m.is_positive() {
                    match x.compare(upper) {
                        Ordering::Less => limit_by(limit, upper),
                        Ordering::Equal => stop_at_zero(limit),
                        Ordering::Greater => {}
                    }
                } else if x.compare(upper) == Ordering::Greater {
                    limit_by(limit, upper);
                }
            }
            COLUMN_LOWER => {
                if is_feasible {
                    if m.is_negative() {
                        limit_feasibly(limit, lower);
                    }
                } else if m.is_negative() {
                    match x.compare(lower) {
                        Ordering::Greater => limit_by(limit, lower),
                        Ordering::Equal => stop_at_zero(limit),
                        Ordering::Less => {}
                    }
                } else if x.compare(lower) == Ordering::Less {
                    limit_by(limit, lower);
                }
            }
            COLUMN_FIXED | COLUMN_BOXED => {
                if is_feasible {
                    limit_feasibly(limit, if m.is_positive() { upper } else { lower });
                } else if m.is_positive() {
                    if x.compare(lower) == Ordering::Less {
                        limit_by(limit, lower);
                    } else if x.compare(upper) == Ordering::Less {
                        limit_by(limit, upper);
                    } else if x.compare(upper) != Ordering::Greater {
                        stop_at_zero(limit);
                    }
                } else if x.compare(upper) == Ordering::Greater {
                    limit_by(limit, upper);
                } else if x.compare(lower) == Ordering::Greater {
                    limit_by(limit, lower);
                } else if x.compare(lower) != Ordering::Less {
                    stop_at_zero(limit);
                }
            }
            _ => {}
        }
        if !limit.is_unlimited {
            clamp_theta(limit);
        }
    }

    // advance_on_entering_and_leaving_tableau.
    fn advance(&mut self, entering: usize, leaving: usize, theta: &Impq) {
        let sign = Rational::from_i64(self.sign_of_entering_delta);
        if entering == leaving {
            self.update_x(entering, &theta.mul(&sign));
            return;
        }
        if !theta.is_zero() {
            let delta = if self.core.is_feasible() {
                theta.mul(&sign)
            } else {
                theta.clone()
            };
            self.update_x(entering, &delta);
        }
        self.core.pivot(entering, leaving);
        let last = self.non_basis_list.len() - 1;
        self.non_basis_list[last] = leaving;
    }

    // update_x_tableau.
    fn update_x(&mut self, entering: usize, delta: &Impq) {
        let core = &mut *self.core;
        core.x[entering] = core.x[entering].add(delta);
        for index in 0..core.matrix.columns[entering].len() {
            let cell = core.matrix.columns[entering][index];
            let basic = core.basis[cell.row];
            let change = delta.mul(core.matrix.get_val(&cell)).neg();
            core.add_delta_to_x_and_track_feasibility(basic, &change);
        }
    }
}

// maximize_term_on_feasible_r_solver: the costs of the term and their reduced costs, the simplex,
// and the term's value at the optimum, or None when it is unbounded or cancelled.
fn maximize_on_feasible_solver(solver: &mut LarSolver<'_>, term: &LarTerm) -> Option<Impq> {
    solver.move_non_basic_columns_to_bounds();
    let core = &mut solver.core;
    let mut reduced_costs = vec![Rational::zero(); core.x.len()];
    for (column, coeff) in term.iter() {
        let row_index = core.heading[column];
        if row_index < 0 {
            reduced_costs[column] = reduced_costs[column].add(coeff);
            continue;
        }
        for cell in &core.matrix.rows[row_index as usize] {
            if cell.column != column {
                reduced_costs[cell.column] =
                    reduced_costs[cell.column].sub(&coeff.mul(&cell.coeff));
            }
        }
    }
    core.reduced_costs = Some(reduced_costs);
    CostsSimplex {
        core: &mut *core,
        sort_counter: 0,
        non_basis_list: Vec::new(),
        sign_of_entering_delta: 1,
    }
    .solve();
    core.reduced_costs = None;
    let status = core.status;
    core.status = LP_OPTIMAL;
    if status == LP_UNBOUNDED || status == LP_CANCELLED {
        None
    } else {
        Some(term.apply(&core.x))
    }
}

// maximize_term without fixing the integer columns: the maximum of the column or of its term, or
// None, with the values restored, when it is unbounded.
pub fn maximize_term(solver: &mut LarSolver<'_>, column: usize) -> Option<Impq> {
    let term = match solver.columns[column].term {
        Some(index) => solver.terms[index].clone(),
        None => LarTerm::from_entries([(column, &Rational::one())]),
    };
    let backup = solver.core.x.clone();
    let Some(maximum) = maximize_on_feasible_solver(solver, &term) else {
        solver.core.x.splice(0..backup.len(), backup);
        return None;
    };
    solver.status = LP_OPTIMAL;
    Some(maximum)
}
