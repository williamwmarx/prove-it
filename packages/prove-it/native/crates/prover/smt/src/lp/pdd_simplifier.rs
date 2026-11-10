// Ported from Z3 (src/math/grobner/pdd_simplifier.h, src/math/grobner/pdd_simplifier.cpp), MIT
// license, see z3-license.txt. The passes that dd::solver::simplify runs before saturation: solve
// linear equations for their top variable, retire equations whose top variable occurs nowhere
// else, subtract equations that share a lo part, and eliminate variables that occur as leaves.
// The extended linear pass works only modulo 2 and the dual elimination is disabled in Z3, so
// neither is ported. No pass makes a value outside an operation, so none can run out of nodes.
use std::collections::HashMap;

use crate::lp::dependency::mk_join;
use crate::lp::pdd_solver::{PddSolver, SOLVED, SetUpdate, TO_SIMPLIFY};

pub struct PddSimplifier<'a> {
    solver: &'a mut PddSolver,
}

impl<'a> PddSimplifier<'a> {
    pub fn new(solver: &'a mut PddSolver) -> PddSimplifier<'a> {
        PddSimplifier { solver }
    }

    pub fn run(&mut self, is_canceled: &dyn Fn() -> bool) {
        while !self.solver.is_done(is_canceled)
            && (self.simplify_linear_step(true)
                || self.simplify_elim_pure_step()
                || self.simplify_cc_step()
                || self.simplify_leaf_step()
                || self.simplify_linear_step(false))
        {}
    }

    fn simplify_linear_step(&mut self, is_binary: bool) -> bool {
        let mut linear = Vec::new();
        for index in 0..self.solver.to_simplify.len() {
            let equation = self.solver.to_simplify[index];
            let poly = self.solver.arena[equation].poly;
            let is_kept = if is_binary {
                self.solver.manager.is_binary(poly)
            } else {
                self.solver.manager.is_linear(poly)
            };
            if is_kept {
                linear.push(equation);
            }
        }
        if linear.is_empty() {
            return false;
        }
        self.simplify_linear(linear)
    }

    // simplify_linear_step: solves each linear equation for its top variable, which it eliminates
    // from the others, and moves it to the solved equations.
    fn simplify_linear(&mut self, mut linear: Vec<usize>) -> bool {
        let mut use_list = self.get_use_list();
        let solver = &mut *self.solver;
        linear.sort_by(|first, second| {
            let first_var = solver.manager.var(solver.arena[*first].poly);
            let second_var = solver.manager.var(solver.arena[*second].poly);
            first_var.cmp(&second_var)
        });
        let mut trivial = Vec::new();
        let mut kept = 0;
        let mut has_conflict = false;
        for position in 0..linear.len() {
            let source = linear[position];
            if has_conflict {
                break;
            }
            if self.solver.is_trivial(source) {
                continue;
            }
            let source_poly = self.solver.arena[source].poly;
            let variable = self.solver.manager.var(source_poly);
            let mut is_all_reduced = true;
            // Equations added to the uses of the variable during the walk are not walked.
            let length = use_list[variable].len();
            for index in 0..length {
                let target = use_list[variable][index];
                if source == target || self.solver.is_trivial(target) {
                    continue;
                }
                let target_poly = self.solver.arena[target].poly;
                if !self.solver.manager.is_binary(source_poly)
                    && !self.solver.manager.is_linear(target_poly)
                {
                    is_all_reduced = false;
                    continue;
                }
                self.remove_from_use(target, &mut use_list, Some(variable));
                let is_leading_term_changed = self.solver.simplify_using(target, source);
                if self.solver.is_trivial(target) {
                    trivial.push(target);
                } else if self.solver.is_conflict(target) {
                    self.solver.pop_equation(target);
                    self.solver.set_conflict(target);
                    has_conflict = true;
                } else if is_leading_term_changed {
                    self.solver.pop_equation(target);
                    self.solver.push_equation(TO_SIMPLIFY, target);
                }
                self.add_to_use(target, &mut use_list);
            }
            if is_all_reduced {
                linear[kept] = source;
                kept += 1;
            }
        }
        if !has_conflict {
            linear.truncate(kept);
            for &source in &linear {
                self.solver.pop_equation(source);
                self.solver.push_equation(SOLVED, source);
            }
        }
        for &equation in &trivial {
            self.solver.pop_equation(equation);
        }
        kept > 0 || has_conflict
    }

    // simplify_cc_step: replaces p*x + q and r*y + q by p*x + q and p*x - r*y, when p or r is a value.
    fn simplify_cc_step(&mut self) -> bool {
        let solver = &mut *self.solver;
        let mut los = HashMap::new();
        let mut is_reduced = false;
        let mut update = SetUpdate::new(solver, TO_SIMPLIFY);
        while update.i < update.size {
            let first = update.get(solver);
            let poly = solver.arena[first].poly;
            let lo = solver.manager.lo(poly);
            let second = *los.get(&lo).unwrap_or(&first);
            if second == first {
                los.insert(lo, first);
            }
            let second_poly = solver.arena[second].poly;
            if second != first
                && (solver.manager.is_val(solver.manager.hi(poly))
                    || solver.manager.is_val(solver.manager.hi(second_poly)))
                && !solver.manager.is_val(lo)
            {
                solver.arena[first].poly = solver.manager.sub(poly, second_poly);
                solver.arena[first].dep =
                    mk_join(&solver.arena[first].dep, &solver.arena[second].dep);
                is_reduced = true;
                if solver.is_trivial(first) || solver.check_conflict(first) {
                    update.i += 1;
                    continue;
                }
            }
            update.nextj(solver);
            update.i += 1;
        }
        update.finish(solver);
        is_reduced
    }

    // simplify_leaf_step: removes a*x + b from the equations where x occurs as a leaf, for a value a.
    fn simplify_leaf_step(&mut self) -> bool {
        let mut use_list = self.get_use_list();
        let mut index = 0;
        while index < self.solver.to_simplify.len() {
            let source = self.solver.to_simplify[index];
            index += 1;
            let poly = self.solver.arena[source].poly;
            if self.solver.manager.is_val(poly)
                || !self.solver.manager.is_val(self.solver.manager.hi(poly))
            {
                continue;
            }
            let variable = self.solver.manager.var(poly);
            let leaves: Vec<usize> = use_list[variable]
                .iter()
                .copied()
                .filter(|&target| {
                    target != source
                        && self
                            .solver
                            .manager
                            .var_is_leaf(self.solver.arena[target].poly, variable)
                })
                .collect();
            for target in leaves {
                self.remove_from_use(target, &mut use_list, None);
                let is_leading_term_changed = self.solver.simplify_using(target, source);
                self.add_to_use(target, &mut use_list);
                if self.solver.is_trivial(target) {
                    self.solver.pop_equation(target);
                } else if self.solver.manager.is_val(self.solver.arena[target].poly) {
                    self.solver.pop_equation(target);
                    self.solver.set_conflict(target);
                    return true;
                } else if is_leading_term_changed {
                    self.solver.pop_equation(target);
                    self.solver.push_equation(TO_SIMPLIFY, target);
                }
            }
        }
        false
    }

    // simplify_elim_pure_step: an equation linear in its top variable, which occurs nowhere else, is
    // solved.
    fn simplify_elim_pure_step(&mut self) -> bool {
        let use_list = self.get_use_list();
        let solver = &mut *self.solver;
        let mut update = SetUpdate::new(solver, TO_SIMPLIFY);
        let mut has_solved = false;
        while update.i < update.size {
            let equation = update.get(solver);
            let poly = solver.arena[equation].poly;
            if !solver.manager.is_val(poly)
                && solver.manager.is_val(solver.manager.hi(poly))
                && use_list[solver.manager.var(poly)].len() == 1
            {
                solver.push_equation(SOLVED, equation);
                has_solved = true;
            } else {
                update.nextj(solver);
            }
            update.i += 1;
        }
        update.finish(solver);
        has_solved
    }

    fn add_to_use(&self, equation: usize, use_list: &mut Vec<Vec<usize>>) {
        for variable in self
            .solver
            .manager
            .free_vars(self.solver.arena[equation].poly)
        {
            while use_list.len() <= variable {
                use_list.push(Vec::new());
            }
            use_list[variable].push(equation);
        }
    }

    fn remove_from_use(
        &self,
        equation: usize,
        use_list: &mut Vec<Vec<usize>>,
        except_var: Option<usize>,
    ) {
        for variable in self
            .solver
            .manager
            .free_vars(self.solver.arena[equation].poly)
        {
            if Some(variable) == except_var {
                continue;
            }
            while use_list.len() <= variable {
                use_list.push(Vec::new());
            }
            let uses = &mut use_list[variable];
            if let Some(index) = uses
                .iter()
                .position(|&use_equation| use_equation == equation)
            {
                uses.remove(index);
            }
        }
    }

    fn get_use_list(&self) -> Vec<Vec<usize>> {
        let mut use_list = Vec::new();
        for &equation in &self.solver.to_simplify {
            self.add_to_use(equation, &mut use_list);
        }
        for &equation in &self.solver.processed {
            self.add_to_use(equation, &mut use_list);
        }
        use_list
    }
}
