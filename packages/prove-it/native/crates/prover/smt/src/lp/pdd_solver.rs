// Ported from Z3 (src/math/grobner/pdd_solver.h, src/math/grobner/pdd_solver.cpp), MIT license,
// see z3-license.txt. dd::solver, the Grobner basis completion that nla runs on polynomials as
// pdds. Each step picks the simplest equation whose leading variable is highest, simplifies it by
// the processed equations and them by it, and adds its S-polynomials with them to be simplified.
// Equations move between the solved, processed and to-simplify sets, each in an array where an
// equation knows its index. Z3's solver::simplify runs the simplifier, which here is PddSimplifier
// in pdd-simplifier, run by its caller.
//
// The equations live in the solver's arena, and the sets hold their indices there, which stand for
// the TypeScript's object identity.
use crate::lp::dependency::{Dependency, mk_join};
use crate::lp::pdd::{Pdd, PddManager};
use crate::util::error::SmtError;

pub const SOLVED: u8 = 0;
const PROCESSED: u8 = 1;
pub const TO_SIMPLIFY: u8 = 2;

const UINT_MAX: usize = 0xffffffff;

#[derive(Debug, Clone)]
pub struct PddSolverConfig {
    pub eqs_threshold: usize,
    pub expr_size_limit: usize,
    pub expr_degree_limit: usize,
    pub max_steps: usize,
    pub max_simplified: usize,
    pub eqs_growth: usize,
    pub expr_size_growth: usize,
    pub expr_degree_growth: usize,
    pub number_of_conflicts_to_report: usize,
}

pub fn get_default_pdd_solver_config() -> PddSolverConfig {
    PddSolverConfig {
        eqs_threshold: UINT_MAX,
        expr_size_limit: UINT_MAX,
        expr_degree_limit: UINT_MAX,
        max_steps: UINT_MAX,
        max_simplified: UINT_MAX,
        eqs_growth: 10,
        expr_size_growth: 10,
        expr_degree_growth: 5,
        number_of_conflicts_to_report: 1,
    }
}

struct Subst {
    variable: usize,
    poly: Pdd,
    dep: Dependency,
}

#[derive(Debug, Clone, Default)]
pub struct PddSolverStats {
    pub simplified: usize,
    pub max_expr_size: usize,
    pub max_expr_degree: usize,
    pub superposed: usize,
    pub compute_steps: usize,
}

pub struct Equation {
    pub state: u8,
    pub idx: usize,
    pub poly: Pdd,
    pub dep: Dependency,
}

impl Equation {
    fn new(poly: Pdd, dep: Dependency) -> Equation {
        Equation {
            state: TO_SIMPLIFY,
            idx: 0,
            poly,
            dep,
        }
    }
}

// scoped_update: walks a set with i and keeps the equations that nextj moves to j. finish keeps
// those not walked and drops the rest, as Z3's destructor does. The set is the solver's set of the
// state.
pub struct SetUpdate {
    pub i: usize,
    j: usize,
    pub size: usize,
    state: u8,
}

impl SetUpdate {
    pub fn new(solver: &PddSolver<'_>, state: u8) -> SetUpdate {
        SetUpdate {
            i: 0,
            j: 0,
            size: solver.get_queue(state).len(),
            state,
        }
    }

    pub fn get(&self, solver: &PddSolver<'_>) -> usize {
        solver.get_queue(self.state)[self.i]
    }

    pub fn nextj(&mut self, solver: &mut PddSolver<'_>) {
        let equation = solver.get_queue(self.state)[self.i];
        solver.get_queue_mut(self.state)[self.j] = equation;
        solver.arena[equation].idx = self.j;
        self.j += 1;
    }

    pub fn finish(&mut self, solver: &mut PddSolver<'_>) {
        while self.i < self.size {
            self.nextj(solver);
            self.i += 1;
        }
        solver.get_queue_mut(self.state).truncate(self.j);
    }
}

// The simplifiers that simplify_using(set, simplifier) applies: the substitution of add_subst, or
// try_simplify_using by the source equation.
enum Simplifier {
    Subst {
        variable: usize,
        poly: Pdd,
        dep: Dependency,
    },
    Using(usize),
}

pub struct PddSolver<'l> {
    pub stats: PddSolverStats,
    pub config: PddSolverConfig,
    pub solved: Vec<usize>,
    pub processed: Vec<usize>,
    pub to_simplify: Vec<usize>,
    substs: Vec<Subst>,
    pub conflict: Option<usize>,
    is_too_complex_found: bool,
    levelp1: usize,
    level2var: Vec<usize>,
    var2level: Vec<usize>,
    pub manager: PddManager,
    // Every equation made since the last reset, indexed by the sets and the conflict.
    pub arena: Vec<Equation>,
    is_canceled: Box<dyn Fn() -> bool + 'l>,
}

impl<'l> PddSolver<'l> {
    pub fn new(manager: PddManager, is_canceled: Box<dyn Fn() -> bool + 'l>) -> PddSolver<'l> {
        PddSolver {
            stats: PddSolverStats::default(),
            config: get_default_pdd_solver_config(),
            solved: Vec::new(),
            processed: Vec::new(),
            to_simplify: Vec::new(),
            substs: Vec::new(),
            conflict: None,
            is_too_complex_found: false,
            levelp1: 0,
            level2var: Vec::new(),
            var2level: Vec::new(),
            manager,
            arena: Vec::new(),
            is_canceled,
        }
    }

    pub fn equation(&self, equation: usize) -> &Equation {
        &self.arena[equation]
    }

    pub fn adjust_config(&mut self) {
        let count = self.to_simplify.len();
        self.config.eqs_threshold =
            (self.config.eqs_growth as f64 * (1.0 + count as f64).ln().ceil() * count as f64)
                .trunc() as usize;
        self.config.expr_size_limit = 0;
        self.config.expr_degree_limit = 0;
        for index in 0..self.to_simplify.len() {
            let poly = self.arena[self.to_simplify[index]].poly;
            self.config.expr_size_limit = self
                .config
                .expr_size_limit
                .max(self.manager.tree_size(poly));
            self.config.expr_degree_limit =
                self.config.expr_degree_limit.max(self.manager.degree(poly));
        }
        self.config.expr_size_limit *= self.config.expr_size_growth;
        self.config.expr_degree_limit *= self.config.expr_degree_growth;
    }

    pub fn reset(&mut self) {
        self.substs.clear();
        self.solved.clear();
        self.processed.clear();
        self.to_simplify.clear();
        self.arena.clear();
        self.stats = PddSolverStats::default();
        self.level2var.clear();
        self.var2level.clear();
        self.conflict = None;
    }

    pub fn add(&mut self, poly: Pdd, dep: Dependency) {
        if self.manager.is_zero(poly) {
            return;
        }
        let equation = self.arena.len();
        self.arena.push(Equation::new(poly, dep));
        if self.check_conflict(equation) {
            return;
        }
        self.push_equation(TO_SIMPLIFY, equation);
        if !self.var2level.is_empty() {
            self.levelp1 = (self.var2level[self.manager.var(poly)] + 1).max(self.levelp1);
        }
        self.update_stats(equation);
    }

    // simplify: applies the substitutions to p, and returns it with its dependency.
    pub fn simplify(&mut self, poly: Pdd, dep: Dependency) -> Result<(Pdd, Dependency), SmtError> {
        let mut result = poly;
        let mut result_dep = dep;
        for subst in &self.substs {
            let substituted = self.manager.subst_pdd(result, subst.variable, subst.poly)?;
            if substituted == result {
                continue;
            }
            result = substituted;
            result_dep = mk_join(&result_dep, &subst.dep);
        }
        Ok((result, result_dep))
    }

    pub fn add_subst(
        &mut self,
        variable: usize,
        poly: Pdd,
        dep: Dependency,
    ) -> Result<(), SmtError> {
        self.substs.push(Subst {
            variable,
            poly,
            dep: dep.clone(),
        });
        if !self.var2level.is_empty() {
            self.levelp1 = (self.var2level[variable] + 1)
                .max((self.var2level[self.manager.var(poly)] + 1).max(self.levelp1));
        }
        let simplifier = Simplifier::Subst {
            variable,
            poly,
            dep,
        };
        if !self.is_done() {
            self.simplify_set_using(PROCESSED, &simplifier)?;
        }
        if !self.is_done() {
            self.simplify_set_using(TO_SIMPLIFY, &simplifier)?;
        }
        if !self.is_done() {
            self.simplify_set_using(SOLVED, &simplifier)?;
        }
        Ok(())
    }

    pub fn saturate(&mut self) -> Result<(), SmtError> {
        if self.is_done() {
            return Ok(());
        }
        self.init_saturate();
        loop {
            if self.is_done() {
                return Ok(());
            }
            match self.step() {
                Ok(true) => {}
                Ok(false) | Err(SmtError::PddMemoryOut) => return Ok(()),
                Err(error) => return Err(error),
            }
        }
    }

    pub fn equations(&self) -> Vec<usize> {
        let mut equations = self.solved.clone();
        equations.extend_from_slice(&self.to_simplify);
        equations.extend_from_slice(&self.processed);
        equations
    }

    fn step(&mut self) -> Result<bool, SmtError> {
        self.stats.compute_steps += 1;
        let Some(equation) = self.pick_next() else {
            return Ok(false);
        };
        // scoped_process: the equation goes back to processed unless the step settles it.
        let mut pending = Some(equation);
        let result = 'step: {
            self.simplify_using_all(equation, PROCESSED);
            if self.is_trivial(equation) {
                pending = None;
                break 'step Ok(true);
            }
            if self.check_conflict(equation) {
                pending = None;
                break 'step Ok(false);
            }
            self.is_too_complex_found = false;
            if let Err(error) = self.simplify_set_using(PROCESSED, &Simplifier::Using(equation)) {
                break 'step Err(error);
            }
            if self.is_done() {
                break 'step Ok(false);
            }
            let mut index = 0;
            while index < self.processed.len() {
                if let Err(error) = self.superpose(equation, self.processed[index]) {
                    break 'step Err(error);
                }
                index += 1;
            }
            if let Err(error) = self.simplify_set_using(TO_SIMPLIFY, &Simplifier::Using(equation)) {
                break 'step Err(error);
            }
            if self.is_done() {
                break 'step Ok(false);
            }
            if !self.is_too_complex_found {
                pending = None;
                let poly = self.arena[equation].poly;
                let state = if self.manager.degree(poly) == 1 {
                    SOLVED
                } else {
                    PROCESSED
                };
                self.push_equation(state, equation);
            }
            Ok(true)
        };
        if let Some(pending) = pending {
            self.push_equation(PROCESSED, pending);
        }
        result
    }

    fn init_saturate(&mut self) {
        let level2var = &self.manager.level2var;
        self.level2var = level2var.clone();
        self.var2level = vec![0; level2var.len()];
        for (level, &variable) in level2var.iter().enumerate() {
            self.var2level[variable] = level;
        }
        self.levelp1 = level2var.len();
    }

    fn pick_next(&mut self) -> Option<usize> {
        while self.levelp1 > 0 {
            let variable = self.level2var[self.levelp1 - 1];
            let mut picked: Option<usize> = None;
            for index in 0..self.to_simplify.len() {
                let current = self.to_simplify[index];
                if self.arena[current].state != TO_SIMPLIFY
                    || self.manager.var(self.arena[current].poly) != variable
                {
                    continue;
                }
                if picked.is_none_or(|picked| self.is_simpler(current, picked)) {
                    picked = Some(current);
                }
            }
            if let Some(picked) = picked {
                self.pop_equation(picked);
                return Some(picked);
            }
            self.levelp1 -= 1;
        }
        None
    }

    fn superpose(&mut self, first: usize, second: usize) -> Result<(), SmtError> {
        let Some(poly) = self
            .manager
            .try_spoly(self.arena[first].poly, self.arena[second].poly)?
        else {
            return Ok(());
        };
        if self.manager.is_zero(poly) {
            return Ok(());
        }
        if self.is_too_complex(poly) {
            self.is_too_complex_found = true;
            return Ok(());
        }
        self.stats.superposed += 1;
        let dep = mk_join(&self.arena[first].dep, &self.arena[second].dep);
        self.add(poly, dep);
        Ok(())
    }

    // simplify_using(eq, eqs): reduces eq by the set until no reduction applies.
    fn simplify_using_all(&mut self, equation: usize, state: u8) {
        loop {
            let mut is_simplified = false;
            let mut index = 0;
            while index < self.get_queue(state).len() {
                let source = self.get_queue(state)[index];
                if self.try_simplify_using(equation, source).is_some() {
                    is_simplified = true;
                }
                if (self.is_canceled)() || self.manager.is_val(self.arena[equation].poly) {
                    break;
                }
                index += 1;
            }
            if !(is_simplified && !self.manager.is_val(self.arena[equation].poly)) {
                break;
            }
        }
        let poly = self.arena[equation].poly;
        if self.manager.is_unary(poly) && self.manager.val(self.manager.hi(poly)).is_negative() {
            self.arena[equation].poly = self.manager.minus(poly);
        }
    }

    // simplify_using(set, simplifier): the simplifier returns None when it leaves the target, and
    // otherwise whether the leading term changed.
    fn simplify_set_using(&mut self, state: u8, simplifier: &Simplifier) -> Result<(), SmtError> {
        let mut update = SetUpdate::new(self, state);
        while update.i < update.size {
            let target = self.get_queue(state)[update.i];
            let is_leading_term_changed = if self.is_done() {
                None
            } else {
                self.apply_simplifier(simplifier, target)?
            };
            let is_dropped = is_leading_term_changed.is_some()
                && (self.is_trivial(target) || self.check_conflict(target));
            if is_dropped {
                // The set drops a trivial equation, and check_conflict moved a conflict to solved.
            } else if is_leading_term_changed == Some(true) {
                if state == TO_SIMPLIFY {
                    update.nextj(self);
                } else {
                    self.push_equation(TO_SIMPLIFY, target);
                }
                if !self.var2level.is_empty() {
                    let variable = self.manager.var(self.arena[target].poly);
                    self.levelp1 = (self.var2level[variable] + 1).max(self.levelp1);
                }
            } else {
                update.nextj(self);
            }
            update.i += 1;
        }
        update.finish(self);
        Ok(())
    }

    fn apply_simplifier(
        &mut self,
        simplifier: &Simplifier,
        target: usize,
    ) -> Result<Option<bool>, SmtError> {
        match simplifier {
            Simplifier::Subst {
                variable,
                poly,
                dep,
            } => {
                let target_poly = self.arena[target].poly;
                let substituted = self.manager.subst_pdd(target_poly, *variable, *poly)?;
                if substituted == target_poly {
                    return Ok(None);
                }
                if self.is_too_complex(substituted) {
                    self.is_too_complex_found = true;
                    return Ok(None);
                }
                let is_leading_term_changed = self
                    .manager
                    .different_leading_term(substituted, target_poly);
                self.arena[target].poly = substituted;
                self.arena[target].dep = mk_join(&self.arena[target].dep, dep);
                self.update_stats(target);
                Ok(Some(is_leading_term_changed))
            }
            Simplifier::Using(source) => Ok(self.try_simplify_using(target, *source)),
        }
    }

    // try_simplify_using: None when the target stays, and otherwise whether its leading term
    // changed while it was processed.
    fn try_simplify_using(&mut self, target: usize, source: usize) -> Option<bool> {
        if source == target {
            return None;
        }
        self.stats.simplified += 1;
        let target_poly = self.arena[target].poly;
        let reduced = self.manager.reduce(target_poly, self.arena[source].poly);
        if reduced == target_poly {
            return None;
        }
        if self.is_too_complex(reduced) {
            self.is_too_complex_found = true;
            return None;
        }
        let is_leading_term_changed = self.arena[target].state == PROCESSED
            && self.manager.different_leading_term(reduced, target_poly);
        self.arena[target].poly = reduced;
        self.arena[target].dep = mk_join(&self.arena[target].dep, &self.arena[source].dep);
        self.update_stats(target);
        Some(is_leading_term_changed)
    }

    // simplify_using(dst, src): reduces dst by src whatever the result, and returns whether its
    // leading term changed while it was processed.
    pub fn simplify_using(&mut self, target: usize, source: usize) -> bool {
        if source == target {
            return false;
        }
        self.stats.simplified += 1;
        let target_poly = self.arena[target].poly;
        let reduced = self.manager.reduce(target_poly, self.arena[source].poly);
        let is_leading_term_changed = self.arena[target].state == PROCESSED
            && self.manager.different_leading_term(reduced, target_poly);
        if reduced == target_poly {
            return is_leading_term_changed;
        }
        self.arena[target].poly = reduced;
        self.arena[target].dep = mk_join(&self.arena[target].dep, &self.arena[source].dep);
        self.update_stats(target);
        is_leading_term_changed
    }

    pub fn is_done(&self) -> bool {
        self.to_simplify.len() + self.processed.len() >= self.config.eqs_threshold
            || self.stats.simplified >= self.config.max_simplified
            || (self.is_canceled)()
            || self.stats.compute_steps > self.config.max_steps
            || self.conflict.is_some()
    }

    pub fn is_trivial(&self, equation: usize) -> bool {
        self.manager.is_zero(self.arena[equation].poly)
    }

    pub fn is_conflict(&self, equation: usize) -> bool {
        self.manager.is_val(self.arena[equation].poly) && !self.is_trivial(equation)
    }

    pub fn check_conflict(&mut self, equation: usize) -> bool {
        if !self.is_conflict(equation) {
            return false;
        }
        self.set_conflict(equation);
        true
    }

    pub fn set_conflict(&mut self, equation: usize) {
        self.conflict = Some(equation);
        self.push_equation(SOLVED, equation);
    }

    fn is_simpler(&mut self, first: usize, second: usize) -> bool {
        self.manager
            .lm_lt(self.arena[first].poly, self.arena[second].poly)
    }

    fn is_too_complex(&mut self, poly: Pdd) -> bool {
        self.manager.tree_size(poly) > self.config.expr_size_limit
            || self.manager.degree(poly) > self.config.expr_degree_limit
    }

    fn get_queue(&self, state: u8) -> &Vec<usize> {
        if state == PROCESSED {
            return &self.processed;
        }
        if state == TO_SIMPLIFY {
            &self.to_simplify
        } else {
            &self.solved
        }
    }

    fn get_queue_mut(&mut self, state: u8) -> &mut Vec<usize> {
        if state == PROCESSED {
            return &mut self.processed;
        }
        if state == TO_SIMPLIFY {
            &mut self.to_simplify
        } else {
            &mut self.solved
        }
    }

    pub fn pop_equation(&mut self, equation: usize) {
        let idx = self.arena[equation].idx;
        let set = self.get_queue_mut(self.arena[equation].state);
        let last = *set.last().expect("pop_equation on an empty set");
        let is_moved = idx != set.len() - 1;
        if is_moved {
            set[idx] = last;
        }
        set.pop();
        if is_moved {
            self.arena[last].idx = idx;
        }
    }

    pub fn push_equation(&mut self, state: u8, equation: usize) {
        self.arena[equation].state = state;
        let set = self.get_queue_mut(state);
        let idx = set.len();
        set.push(equation);
        self.arena[equation].idx = idx;
    }

    fn update_stats(&mut self, equation: usize) {
        let poly = self.arena[equation].poly;
        self.stats.max_expr_size = self.stats.max_expr_size.max(self.manager.tree_size(poly));
        self.stats.max_expr_degree = self.stats.max_expr_degree.max(self.manager.degree(poly));
    }
}

// Ported from Z3's src/test/pdd_solver.cpp, which prints the results.
#[cfg(test)]
mod tests {
    use std::cell::RefCell;

    use super::{PddSolver, SOLVED};
    use crate::lp::dependency::{linearize, mk_leaf};
    use crate::lp::pdd::tests::{Poly, get_vars};
    use crate::lp::pdd::{Pdd, PddManager};
    use crate::lp::pdd_simplifier::PddSimplifier;

    fn solve(polys: impl for<'m> Fn(&[Poly<'m>]) -> Vec<Poly<'m>>) -> PddSolver<'static> {
        let manager = RefCell::new(PddManager::new(4));
        let pdds: Vec<Pdd> = polys(&get_vars(&manager, 4))
            .iter()
            .map(|poly| poly.pdd)
            .collect();
        let mut solver = PddSolver::new(manager.into_inner(), Box::new(|| false));
        for (index, &poly) in pdds.iter().enumerate() {
            solver.add(poly, mk_leaf(index as u32));
        }
        solver.saturate().unwrap();
        solver
    }

    fn get_polys(solver: &PddSolver<'_>, equations: &[usize]) -> Vec<String> {
        equations
            .iter()
            .map(|&equation| solver.manager.display(solver.equation(equation).poly))
            .collect()
    }

    fn get_sorted_polys(solver: &PddSolver<'_>) -> Vec<String> {
        let mut polys = get_polys(solver, &solver.equations());
        polys.sort();
        polys
    }

    #[test]
    fn solves_for_a_variable_and_substitutes_it() {
        let solver = solve(|vars| vec![vars[1] * vars[2] + vars[1] * vars[3], vars[1] - 1]);
        assert_eq!(get_sorted_polys(&solver), vec!["v1 - 1", "v3 + v2"]);
    }

    #[test]
    fn stops_at_a_contradiction() {
        let solver = solve(|vars| {
            let v1v3 = vars[3] * vars[1];
            let cubic = vars[1] * vars[3] * vars[3] + v1v3;
            let sum = v1v3 + vars[1] * vars[2] + vars[2] * vars[3];
            vec![cubic + 2, cubic, sum, sum + vars[1], sum + vars[2]]
        });
        let conflict = solver.equation(solver.conflict.expect("a conflict"));
        assert!(solver.manager.is_val(conflict.poly));
        assert_eq!(conflict.state, SOLVED);
        let mut leaves = linearize(std::slice::from_ref(&conflict.dep));
        leaves.sort();
        assert_eq!(leaves, vec![0, 1]);
    }

    #[test]
    fn finds_that_two_variables_are_zero() {
        let solver = solve(|vars| {
            let v1v3 = vars[3] * vars[1];
            let sum = v1v3 + vars[1] * vars[2] + vars[2] * vars[3];
            vec![
                vars[1] * vars[3] * vars[3] + v1v3,
                sum,
                sum + vars[1],
                sum + vars[2],
            ]
        });
        assert!(solver.conflict.is_none());
        let polys = get_polys(&solver, &solver.equations());
        assert!(polys.iter().any(|poly| poly == "v1"));
        assert!(polys.iter().any(|poly| poly == "v2"));
    }

    // Linear equations are solved and solved equations simplify nothing, so the triangular form
    // stays.
    #[test]
    fn keeps_triangular_linear_equations() {
        let solver = solve(|vars| {
            vec![
                vars[3] - vars[2] * 2,
                vars[2] - vars[1] * 2,
                vars[1] - vars[0] * 2,
            ]
        });
        assert_eq!(
            get_sorted_polys(&solver),
            vec!["v1 - 2*v0", "v2 - 2*v1", "v3 - 2*v2"]
        );
    }

    #[test]
    fn simplifies_linear_equations_before_saturation() {
        let manager = RefCell::new(PddManager::new(4));
        let vars = get_vars(&manager, 4);
        let (v0, v1, v2, v3) = (vars[0], vars[1], vars[2], vars[3]);
        let first = (v3 - v2 - 1).pdd;
        let second = (v3 * v1 + v0).pdd;
        drop(vars);
        let mut solver = PddSolver::new(manager.into_inner(), Box::new(|| false));
        solver.add(first, None);
        solver.add(second, None);
        PddSimplifier::new(&mut solver).run();
        assert_eq!(get_polys(&solver, &solver.solved), vec!["v3 - v2 - 1"]);
        assert_eq!(
            get_polys(&solver, &solver.to_simplify),
            vec!["v2*v1 + v1 + v0"]
        );
    }
}
