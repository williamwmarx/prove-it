//! A conflict-driven clause learning SAT solver for the clauses of one tableau node. A literal is a
//! variable number, negated when below zero. The solver keeps what it learns across calls, which
//! add clauses or assume literals. It decides each open variable false first, so a model sets few
//! variables, and a model holds 1 for each true variable and -1 for each false one. It gives up at
//! the first conflict after `is_expired` turns true.
//!
//! A clause is an index into the solver's clauses, which the watches and the reasons share: moving a
//! watch reorders the clause's literals in place.

/// What `solve` found.
#[derive(Debug, PartialEq)]
pub enum Solution {
    /// The value of each variable, by number, with 0 unused.
    Model(Vec<i8>),
    Unsat,
    Unknown,
}

fn get_index(literal: i32) -> usize {
    if literal > 0 {
        2 * literal as usize
    } else {
        2 * (-literal) as usize + 1
    }
}

fn get_variable(literal: i32) -> usize {
    literal.unsigned_abs() as usize
}

pub struct Solver {
    values: Vec<i8>,
    levels: Vec<usize>,
    reasons: Vec<Option<usize>>,
    activities: Vec<f64>,
    seen: Vec<bool>,
    watches: Vec<Vec<usize>>,
    clauses: Vec<Vec<i32>>,
    trail: Vec<i32>,
    level_starts: Vec<usize>,
    head: usize,
    bump: f64,
    is_unsatisfiable: bool,
}

impl Solver {
    pub fn new(variable_count: usize) -> Self {
        Solver {
            values: vec![0; variable_count + 1],
            levels: vec![0; variable_count + 1],
            reasons: vec![None; variable_count + 1],
            activities: vec![0.0; variable_count + 1],
            seen: vec![false; variable_count + 1],
            watches: vec![Vec::new(); 2 * variable_count + 2],
            clauses: Vec::new(),
            trail: Vec::new(),
            level_starts: Vec::new(),
            head: 0,
            bump: 1.0,
            is_unsatisfiable: false,
        }
    }

    fn get_value(&self, literal: i32) -> i8 {
        if literal > 0 {
            self.values[literal as usize]
        } else {
            -self.values[(-literal) as usize]
        }
    }

    fn assign(&mut self, literal: i32, reason: Option<usize>) {
        let variable = get_variable(literal);
        self.values[variable] = if literal > 0 { 1 } else { -1 };
        self.levels[variable] = self.level_starts.len();
        self.reasons[variable] = reason;
        self.trail.push(literal);
    }

    fn watch(&mut self, literals: Vec<i32>) -> usize {
        let clause = self.clauses.len();
        self.watches[get_index(literals[0])].push(clause);
        self.watches[get_index(literals[1])].push(clause);
        self.clauses.push(literals);
        clause
    }

    /// Moves each watch off a literal that turned false, and returns the clause of a conflict. The
    /// literal a clause implies sits first in it.
    fn propagate(&mut self) -> Option<usize> {
        while self.head < self.trail.len() {
            let falsified = -self.trail[self.head];
            let watching = get_index(falsified);
            let mut position = 0;
            while position < self.watches[watching].len() {
                let clause = self.watches[watching][position];
                if self.clauses[clause][0] == falsified {
                    self.clauses[clause].swap(0, 1);
                }
                if self.get_value(self.clauses[clause][0]) > 0 {
                    position += 1;
                    continue;
                }
                let replacement = (2..self.clauses[clause].len())
                    .find(|&index| self.get_value(self.clauses[clause][index]) >= 0);
                if let Some(replacement) = replacement {
                    self.clauses[clause].swap(1, replacement);
                    let watched = self.clauses[clause][1];
                    self.watches[get_index(watched)].push(clause);
                    self.watches[watching].swap_remove(position);
                    continue;
                }
                if self.get_value(self.clauses[clause][0]) < 0 {
                    return Some(clause);
                }
                self.assign(self.clauses[clause][0], Some(clause));
                position += 1;
            }
            self.head += 1;
        }
        None
    }

    fn backtrack(&mut self, level: usize) {
        if level >= self.level_starts.len() {
            return;
        }
        let size = self.level_starts[level];
        while self.trail.len() > size {
            let literal = self.trail.pop().unwrap_or(0);
            self.values[get_variable(literal)] = 0;
        }
        self.level_starts.truncate(level);
        self.head = self.trail.len();
    }

    /// Resolves the conflict back to the first literal of the current level that all its paths
    /// pass through, and returns the learned clause with that literal first.
    fn analyze(&mut self, conflict: usize) -> Vec<i32> {
        let mut learned = vec![0];
        let current = self.level_starts.len();
        let mut pending = 0;
        let mut walked = 0;
        let mut index = self.trail.len() - 1;
        let mut clause = Some(conflict);
        loop {
            let literals = clause.map_or(&[][..], |clause| {
                let skipped = if walked == 0 { 0 } else { 1 };
                &self.clauses[clause][skipped.min(self.clauses[clause].len())..]
            });
            for &literal in literals {
                let variable = get_variable(literal);
                if self.seen[variable] || self.levels[variable] == 0 {
                    continue;
                }
                self.seen[variable] = true;
                self.activities[variable] += self.bump;
                if self.levels[variable] == current {
                    pending += 1;
                } else {
                    learned.push(literal);
                }
            }
            while !self.seen[get_variable(self.trail[index])] {
                index -= 1;
            }
            walked = self.trail[index];
            index = index.wrapping_sub(1);
            self.seen[get_variable(walked)] = false;
            clause = self.reasons[get_variable(walked)];
            pending -= 1;
            if pending == 0 {
                break;
            }
        }
        learned[0] = -walked;
        for &literal in &learned {
            self.seen[get_variable(literal)] = false;
        }
        self.bump *= 1.05;
        learned
    }

    /// Adds a clause. Literals false for good are dropped, since the solver adds clauses only at
    /// level 0.
    pub fn add_clause(&mut self, clause: &[i32]) {
        self.backtrack(0);
        let mut literals: Vec<i32> = Vec::with_capacity(clause.len());
        for &literal in clause {
            if !literals.contains(&literal) {
                literals.push(literal);
            }
        }
        if self.is_unsatisfiable || literals.iter().any(|&literal| self.get_value(literal) > 0) {
            return;
        }
        if literals.iter().any(|&literal| literals.contains(&-literal)) {
            return;
        }
        let open: Vec<i32> = literals
            .into_iter()
            .filter(|&literal| self.get_value(literal) == 0)
            .collect();
        match open.len() {
            0 => self.is_unsatisfiable = true,
            1 => {
                self.assign(open[0], None);
                if self.propagate().is_some() {
                    self.is_unsatisfiable = true;
                }
            }
            _ => {
                self.watch(open);
            }
        }
    }

    /// A model of the clauses in which every assumed literal holds, or unsat when there is none.
    pub fn solve(&mut self, assumptions: &[i32], is_expired: &mut dyn FnMut() -> bool) -> Solution {
        self.backtrack(0);
        if self.is_unsatisfiable {
            return Solution::Unsat;
        }
        loop {
            if let Some(conflict) = self.propagate() {
                if self.level_starts.is_empty() {
                    self.is_unsatisfiable = true;
                    return Solution::Unsat;
                }
                if is_expired() {
                    return Solution::Unknown;
                }
                let mut learned = self.analyze(conflict);
                let level_of = |solver: &Solver, literal: i32| solver.levels[get_variable(literal)];
                let mut deepest = 1;
                for index in 1..learned.len() {
                    if level_of(self, learned[index]) > level_of(self, learned[deepest]) {
                        deepest = index;
                    }
                }
                if learned.len() > 1 {
                    learned.swap(1, deepest);
                }
                let level = if learned.len() == 1 {
                    0
                } else {
                    level_of(self, learned[1])
                };
                self.backtrack(level);
                let implied = learned[0];
                let reason = if learned.len() > 1 {
                    Some(self.watch(learned))
                } else {
                    None
                };
                self.assign(implied, reason);
                continue;
            }
            let assumption = assumptions
                .iter()
                .copied()
                .find(|&literal| self.get_value(literal) <= 0);
            if assumption.is_some_and(|literal| self.get_value(literal) < 0) {
                return Solution::Unsat;
            }
            let decision = assumption.unwrap_or_else(|| {
                let mut best = 0;
                for variable in 1..self.values.len() {
                    if self.values[variable] == 0
                        && (best == 0 || self.activities[variable] > self.activities[best])
                    {
                        best = variable;
                    }
                }
                -(best as i32)
            });
            if decision == 0 {
                return Solution::Model(self.values.clone());
            }
            self.level_starts.push(self.trail.len());
            self.assign(decision, None);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn never() -> impl FnMut() -> bool {
        || false
    }

    #[test]
    fn decides_open_variables_false_first() {
        let mut solver = Solver::new(2);
        solver.add_clause(&[1, 2]);
        assert_eq!(
            solver.solve(&[], &mut never()),
            Solution::Model(vec![0, -1, 1])
        );
    }

    #[test]
    fn learns_and_finds_a_contradiction() {
        let mut solver = Solver::new(2);
        for clause in [[1, 2], [1, -2], [-1, 2], [-1, -2]] {
            solver.add_clause(&clause);
        }
        assert_eq!(solver.solve(&[], &mut never()), Solution::Unsat);
    }

    #[test]
    fn an_assumption_that_cannot_hold_is_unsat_without_ending_the_solver() {
        let mut solver = Solver::new(2);
        solver.add_clause(&[-1, 2]);
        solver.add_clause(&[-2]);
        assert_eq!(solver.solve(&[1], &mut never()), Solution::Unsat);
        assert_eq!(
            solver.solve(&[], &mut never()),
            Solution::Model(vec![0, -1, -1])
        );
    }
}
