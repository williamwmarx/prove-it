// Ported from Z3 (src/nlsat/nlsat_solver.cpp, src/nlsat/nlsat_justification.h), MIT license, see
// z3-license.txt. The nlsat search of Jovanovic and de Moura: Boolean variables first, then the
// arithmetic variables in order, each a stage. A stage assigns its variable outside the intervals
// that the clauses watching it exclude, and a conflict learns the explanation of the excluded
// line. Only Z3's default nlsat parameters are ported: lazy 0, simplify_conflicts, reorder and
// randomize on, shuffle_vars, inline_vars, minimize_conflicts and check_lemmas off, seed 0. So
// nlsat_simplify and the bounds of eliminated variables, which only inline_vars makes, are not
// ported. Neither are what nra never uses: Boolean variables beyond true, transcendental
// constraints, check(assumptions), check_limit, retract, and set_max_var, without which
// select_witness never picks the maximal value. The search counts its steps against the resource
// limit, but not the memory, which Z3 also bounds by max_memory.
//
// The TypeScript solver keeps the resource limit it was made with; here `check` and
// `check_assignment` take it, and the search passes it down to `checkpoint`.

use std::cell::Cell;
use std::cmp::Ordering;
use std::collections::HashSet;
use std::rc::Rc;

use super::algebraic::{AlgebraicManager, Anum, AnumValue};
use super::atoms::{AtomTable, BoolVarHooks, FALSE_LITERAL, ScopedLiterals, TRUE_LITERAL};
use super::evaluator::{Evaluator, get_assigned_value, get_literal_value};
use super::explain::{Explain, ExplainContext};
use super::interval_set::IntervalSet;
use super::polynomial::{NULL_VAR, Polynomial, PolynomialCache, PolynomialManager, Var};
use super::types::{Atom, AtomRef, Clause, ClauseRef, IneqKind, RootKind};
use super::{
    Dependency, Int, L_FALSE, L_TRUE, L_UNDEF, LBool, RandomGen, Rational, ResourceLimit, SmtError,
    linearize, mk_join, mk_leaf,
};

// null_bool_var: past every Boolean variable.
const NULL_BOOL_VAR: u32 = u32::MAX;

// The level of an unassigned Boolean variable, past every level.
const NULL_LEVEL: i64 = i64::MAX;

// m_restart_threshold: the conflicts between two reorderings of the variables.
const RESTART_THRESHOLD: u64 = 10000;

#[derive(Clone)]
enum Justification {
    Decision,
    Clause(ClauseRef),
    Lazy {
        literals: Vec<u32>,
        clauses: Vec<ClauseRef>,
    },
}

enum Trail {
    Assignment(u32),
    Infeasible(Option<IntervalSet>),
    Level,
    Stage,
    Eq(Option<AtomRef>),
}

// What learn gives for one conflict: the empty lemma, the conflict clause itself as the lemma,
// which now propagates, or the learned clause.
enum Learned {
    Empty,
    Conflict,
    Clause(ClauseRef),
}

#[derive(Clone, Debug, Default)]
pub struct NlsatStats {
    pub conflicts: u64,
    pub restarts: u64,
    pub propagations: u64,
    pub decisions: u64,
    pub stages: u64,
    pub irrational_assignments: u64,
}

// What the solver keeps per Boolean variable, which the atom table resets when it makes or
// deletes a variable.
#[derive(Default)]
struct BoolVars {
    bvalues: Vec<LBool>,
    levels: Vec<i64>,
    justifications: Vec<Option<Justification>>,
    bwatches: Vec<Vec<ClauseRef>>,
    is_dead: Vec<bool>,
}

impl BoolVarHooks for BoolVars {
    fn on_mk(&mut self, bool_var: u32) {
        let index = bool_var as usize;
        if index == self.bvalues.len() {
            self.bvalues.push(L_UNDEF);
            self.levels.push(NULL_LEVEL);
            self.justifications.push(None);
            self.bwatches.push(Vec::new());
            self.is_dead.push(false);
            return;
        }
        self.bvalues[index] = L_UNDEF;
        self.levels[index] = NULL_LEVEL;
        self.justifications[index] = None;
        self.bwatches[index] = Vec::new();
        self.is_dead[index] = false;
    }

    fn on_delete(&mut self, bool_var: u32) {
        self.is_dead[bool_var as usize] = true;
        self.bvalues[bool_var as usize] = L_UNDEF;
    }

    fn bvalues(&self) -> &[LBool] {
        &self.bvalues
    }
}

// values[index] = value, as JavaScript sets an array element: past the end, the array grows.
fn set_value(values: &mut Vec<Option<Anum>>, index: usize, value: Option<Anum>) {
    if index >= values.len() {
        values.resize(index + 1, None);
    }
    values[index] = value;
}

fn is_eq_atom(atom: &Atom) -> bool {
    matches!(atom, Atom::Ineq(ineq) if ineq.kind == IneqKind::Eq)
}

pub struct NlsatSolver {
    pub pm: PolynomialManager,
    pub am: AlgebraicManager,
    cache: PolynomialCache,
    bool_vars: BoolVars,
    atoms: AtomTable,
    assignment: Vec<Option<Anum>>,
    evaluator: Evaluator,
    clauses: Vec<ClauseRef>,
    learned: Vec<ClauseRef>,
    next_clause_id: u32,
    is_int: Vec<bool>,
    watches: Vec<Vec<ClauseRef>>,
    infeasible: Vec<Option<IntervalSet>>,
    var2eq: Vec<Option<AtomRef>>,
    // perm: internal to external variables. inv_perm: external to internal.
    perm: Vec<Var>,
    inv_perm: Vec<Var>,
    explain: Explain,
    bk: u32,
    xk: Var,
    scope_level: i64,
    trail: Vec<Trail>,
    marks: Vec<bool>,
    mark_count: u32,
    lemma: ScopedLiterals,
    lazy_clause: ScopedLiterals,
    lemma_assumptions: Dependency,
    random_seed: u32,
    is_reordered: bool,
    // max_conflicts: nra sets it before each check; None is no bound.
    pub max_conflicts: Option<u64>,
    pub stats: NlsatStats,
    // m_rlimit: the steps of the search count against the limit, and against the budget of this
    // solver, which Z3 sets with a scoped_rlimit on a child limit.
    pub steps: u64,
    budget: Option<u64>,
}

impl NlsatSolver {
    pub fn new(budget: Option<u64>) -> NlsatSolver {
        let pm = PolynomialManager::new();
        let am = AlgebraicManager::new();
        let cache = PolynomialCache::new();
        let mut bool_vars = BoolVars::default();
        let atoms = AtomTable::new(Some(&mut bool_vars));
        let mut solver = NlsatSolver {
            pm,
            am,
            cache,
            bool_vars,
            atoms,
            assignment: Vec::new(),
            evaluator: Evaluator::new(),
            clauses: Vec::new(),
            learned: Vec::new(),
            next_clause_id: 0,
            is_int: Vec::new(),
            watches: Vec::new(),
            infeasible: Vec::new(),
            var2eq: Vec::new(),
            perm: Vec::new(),
            inv_perm: Vec::new(),
            explain: Explain::new(),
            bk: 0,
            xk: NULL_VAR,
            scope_level: 0,
            trail: Vec::new(),
            marks: Vec::new(),
            mark_count: 0,
            lemma: ScopedLiterals::new(),
            lazy_clause: ScopedLiterals::new(),
            lemma_assumptions: None,
            random_seed: 0,
            is_reordered: false,
            max_conflicts: None,
            stats: NlsatStats::default(),
            steps: 0,
            budget,
        };
        // mk_true_bvar: the clause [true], whose literal the first Boolean stage assigns.
        solver.mk_clause(&[TRUE_LITERAL], false, None);
        solver
    }

    fn checkpoint(&mut self, limit: Option<&ResourceLimit>) -> Result<(), SmtError> {
        self.steps += 1;
        if limit.is_some_and(|limit| !limit.inc())
            || self.budget.is_some_and(|budget| self.steps > budget)
        {
            return Err(SmtError::Canceled);
        }
        Ok(())
    }

    pub fn mk_var(&mut self, is_int: bool) -> Var {
        let variable = self.is_int.len() as Var;
        self.is_int.push(is_int);
        self.watches.push(Vec::new());
        self.infeasible.push(None);
        self.var2eq.push(None);
        self.perm.push(variable);
        self.inv_perm.push(variable);
        variable
    }

    pub fn mk_ineq_literal(
        &mut self,
        kind: IneqKind,
        polynomials: &[Polynomial],
        is_even: &[bool],
    ) -> u32 {
        self.atoms.mk_ineq_literal(
            &mut self.pm,
            &mut self.cache,
            Some(&mut self.bool_vars),
            kind,
            polynomials,
            is_even,
        )
    }

    pub fn get_atom(&self, literal: u32) -> Option<AtomRef> {
        self.atoms.get_atom(literal).cloned()
    }

    // mk_external_clause: an input clause, which depends on assumption when it is not None.
    pub fn mk_external_clause(&mut self, literals: &[u32], assumption: Option<u32>) {
        self.mk_clause(literals, false, assumption.and_then(mk_leaf));
    }

    // value(x): the model's value of x, zero when unassigned.
    pub fn get_value(&self, variable: Var) -> Anum {
        self.assignment
            .get(variable as usize)
            .cloned()
            .flatten()
            .unwrap_or_else(|| Anum::new(Rational::zero()))
    }

    // get_core: the assumptions of the input clauses the last conflict depends on.
    pub fn get_core(&self) -> Vec<u32> {
        linearize(std::slice::from_ref(&self.lemma_assumptions))
    }

    fn get_max_var(&self, clause: &Clause) -> Var {
        let mut result = NULL_VAR;
        for &literal in &clause.literals {
            if let Some(atom) = self.atoms.get_atom(literal)
                && (result == NULL_VAR || atom.max_var() > result)
            {
                result = atom.max_var();
            }
        }
        result
    }

    fn get_clause_degree(&self, clause: &Clause) -> u32 {
        if self.get_max_var(clause) == NULL_VAR {
            return 0;
        }
        let mut max = 0;
        for &literal in &clause.literals {
            if let Some(atom) = self.atoms.get_atom(literal) {
                max = max.max(self.atoms.get_degree(&self.pm, atom));
            }
        }
        max
    }

    // lit_lt: Boolean literals first, then by maximal variable, degree, inequalities before
    // equations, and index.
    fn compare_literals(&self, first: u32, second: u32) -> Ordering {
        let first_atom = self.atoms.get_atom(first);
        let second_atom = self.atoms.get_atom(second);
        let (Some(first_atom), Some(second_atom)) = (&first_atom, &second_atom) else {
            if first_atom.is_none() && second_atom.is_none() {
                return first.cmp(&second);
            }
            return if first_atom.is_none() {
                Ordering::Less
            } else {
                Ordering::Greater
            };
        };
        if first_atom.max_var() != second_atom.max_var() {
            return first_atom.max_var().cmp(&second_atom.max_var());
        }
        let first_degree = self.atoms.get_degree(&self.pm, first_atom);
        let second_degree = self.atoms.get_degree(&self.pm, second_atom);
        if first_degree != second_degree {
            return first_degree.cmp(&second_degree);
        }
        let is_first_eq = is_eq_atom(first_atom);
        let is_second_eq = is_eq_atom(second_atom);
        if is_first_eq != is_second_eq {
            return if is_first_eq {
                Ordering::Greater
            } else {
                Ordering::Less
            };
        }
        first.cmp(&second)
    }

    fn mk_clause(
        &mut self,
        literals: &[u32],
        is_learned: bool,
        assumptions: Dependency,
    ) -> ClauseRef {
        let id = self.next_clause_id;
        self.next_clause_id += 1;
        let mut clause_literals = if literals.is_empty() {
            vec![FALSE_LITERAL]
        } else {
            literals.to_vec()
        };
        for &literal in &clause_literals {
            self.atoms.inc_ref(literal);
        }
        clause_literals.sort_by(|first, second| self.compare_literals(*first, *second));
        let clause = Rc::new(Clause {
            id,
            literals: clause_literals,
            is_learned,
            assumptions,
            is_active: Cell::new(false),
        });
        if is_learned {
            self.learned.push(clause.clone());
        } else {
            self.clauses.push(clause.clone());
        }
        self.add_clause_to_watches(&clause);
        clause
    }

    fn add_clause_to_watches(&mut self, clause: &ClauseRef) {
        let variable = self.get_max_var(clause);
        if variable != NULL_VAR {
            self.watches[variable as usize].push(clause.clone());
            return;
        }
        // Math.max over the Boolean variables: mk_clause never makes a clause without literals.
        let bool_var = clause
            .literals
            .iter()
            .fold(0, |max, literal| max.max(literal >> 1));
        self.bool_vars.bwatches[bool_var as usize].push(clause.clone());
    }

    fn del_clause(&mut self, clause: &ClauseRef) {
        let variable = self.get_max_var(clause);
        let watches = if variable != NULL_VAR {
            &mut self.watches[variable as usize]
        } else {
            let bool_var = clause
                .literals
                .iter()
                .fold(0, |max, literal| max.max(literal >> 1));
            &mut self.bool_vars.bwatches[bool_var as usize]
        };
        if let Some(index) = watches.iter().position(|watch| Rc::ptr_eq(watch, clause)) {
            watches.remove(index);
        }
        for &literal in &clause.literals {
            self.atoms.dec_ref(Some(&mut self.bool_vars), literal);
        }
    }

    // Search.

    fn unassign_bool_var(&mut self, bool_var: u32) {
        let index = bool_var as usize;
        self.bool_vars.bvalues[index] = L_UNDEF;
        self.bool_vars.levels[index] = NULL_LEVEL;
        self.bool_vars.justifications[index] = None;
        if self.atoms.atoms[index].is_none() && bool_var < self.bk {
            self.bk = bool_var;
        }
    }

    fn undo_until(&mut self, predicate: impl Fn(&NlsatSolver) -> bool) {
        while predicate(self) {
            let Some(entry) = self.trail.pop() else {
                return;
            };
            match entry {
                Trail::Assignment(bool_var) => self.unassign_bool_var(bool_var),
                Trail::Infeasible(old) => {
                    if self.xk != NULL_VAR && (self.xk as usize) < self.infeasible.len() {
                        self.infeasible[self.xk as usize] = old;
                    }
                }
                Trail::Stage => {
                    if self.xk == 0 {
                        self.xk = NULL_VAR;
                    } else if self.xk != NULL_VAR {
                        self.xk -= 1;
                        set_value(&mut self.assignment, self.xk as usize, None);
                    }
                }
                Trail::Level => self.scope_level -= 1,
                Trail::Eq(old) => {
                    if self.xk != NULL_VAR && self.var2eq.len() > self.xk as usize {
                        self.var2eq[self.xk as usize] = old;
                    }
                }
            }
        }
    }

    fn undo_until_level(&mut self, level: i64) {
        self.undo_until(|solver| solver.scope_level > level);
    }

    fn undo_until_stage(&mut self, variable: Var) {
        self.undo_until(|solver| solver.xk != variable);
    }

    fn new_level(&mut self) {
        self.scope_level += 1;
        self.trail.push(Trail::Level);
    }

    fn get_assigned_value(&self, literal: u32) -> LBool {
        get_assigned_value(&self.bool_vars.bvalues, literal)
    }

    fn set_literal_to_true(
        &mut self,
        literal: u32,
        justification: Justification,
    ) -> Result<(), SmtError> {
        if matches!(justification, Justification::Decision) {
            self.stats.decisions += 1;
        } else {
            self.stats.propagations += 1;
        }
        let bool_var = literal >> 1;
        let index = bool_var as usize;
        self.bool_vars.bvalues[index] = if literal & 1 == 1 { L_FALSE } else { L_TRUE };
        self.bool_vars.levels[index] = self.scope_level;
        self.trail.push(Trail::Assignment(bool_var));
        // update_eq does not read the justifications, so storing it after is the same.
        self.update_eq(bool_var, &justification)?;
        self.bool_vars.justifications[index] = Some(justification);
        Ok(())
    }

    fn decide_literal(&mut self, literal: u32) -> Result<(), SmtError> {
        self.new_level();
        self.set_literal_to_true(literal, Justification::Decision)
    }

    // value: the assigned value, else the atom's value once its maximal variable is assigned.
    fn value(&mut self, literal: u32) -> Result<LBool, SmtError> {
        get_literal_value(
            &self.evaluator,
            &mut self.pm,
            &mut self.am,
            &self.atoms,
            &self.bool_vars.bvalues,
            &self.assignment,
            literal,
        )
    }

    fn is_clause_satisfied(&mut self, clause: &Clause) -> Result<bool, SmtError> {
        for &literal in &clause.literals {
            if self.value(literal)? == L_TRUE {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn process_boolean_clause(&mut self, clause: &ClauseRef) -> Result<bool, SmtError> {
        let mut undef_count = 0;
        let mut selected = None;
        for (index, &literal) in clause.literals.iter().enumerate() {
            if self.value(literal)? == L_FALSE {
                continue;
            }
            undef_count += 1;
            if selected.is_none() {
                selected = Some(index);
            }
        }
        let Some(selected) = selected else {
            return Ok(false);
        };
        if undef_count == 1 {
            self.set_literal_to_true(
                clause.literals[selected],
                Justification::Clause(clause.clone()),
            )?;
        } else {
            self.decide_literal(clause.literals[selected])?;
        }
        Ok(true)
    }

    // R_propagate: literal is true, because with the justifications of set it is infeasible.
    fn propagate(
        &mut self,
        literal: u32,
        set: Option<&IntervalSet>,
        is_literal_included: bool,
    ) -> Result<(), SmtError> {
        let justifications = self.evaluator.ism.get_justifications(set);
        let mut literals = justifications.literals;
        if is_literal_included {
            literals.push(literal ^ 1);
        }
        self.set_literal_to_true(
            literal,
            Justification::Lazy {
                literals,
                clauses: justifications.clauses,
            },
        )
    }

    fn update_infeasible(&mut self, set: Option<IntervalSet>) -> Result<(), SmtError> {
        let xk = self.xk as usize;
        let old = self.infeasible[xk].clone();
        self.trail.push(Trail::Infeasible(old.clone()));
        self.infeasible[xk] =
            self.evaluator
                .ism
                .mk_union(&mut self.am, set.as_ref(), old.as_ref())?;
        Ok(())
    }

    // updt_eq: the equation of least degree that holds for the current variable, for the
    // explanation to simplify with.
    fn update_eq(&mut self, bool_var: u32, justification: &Justification) -> Result<(), SmtError> {
        if self.bool_vars.bvalues[bool_var as usize] != L_TRUE {
            return Ok(());
        }
        let Some(atom) = self.atoms.atoms[bool_var as usize].clone() else {
            return Ok(());
        };
        let Atom::Ineq(ineq) = &*atom else {
            return Ok(());
        };
        if ineq.kind != IneqKind::Eq || ineq.polynomials.len() > 1 || ineq.is_even[0] {
            return Ok(());
        }
        match justification {
            Justification::Clause(clause) if clause.assumptions.is_some() => return Ok(()),
            Justification::Lazy { literals, clauses }
                if !clauses.is_empty() || !literals.is_empty() =>
            {
                return Ok(());
            }
            _ => {}
        }
        let xk = usize::try_from(self.xk)
            .ok()
            .filter(|&xk| xk < self.var2eq.len())
            .ok_or_else(|| {
                SmtError::Invariant(format!("an equation is assigned at stage x{}", self.xk))
            })?;
        let old = self.var2eq[xk].clone();
        if let Some(old_atom) = &old
            && self.atoms.get_degree(&self.pm, old_atom) <= self.atoms.get_degree(&self.pm, &atom)
        {
            return Ok(());
        }
        self.trail.push(Trail::Eq(old));
        self.var2eq[xk] = Some(atom);
        Ok(())
    }

    fn process_arith_clause(
        &mut self,
        clause: &ClauseRef,
        limit: Option<&ResourceLimit>,
    ) -> Result<bool, SmtError> {
        let mut undef_count = 0;
        let mut selected = None;
        let mut selected_set = None;
        let xk_set = self.infeasible[self.xk as usize].clone();
        for (index, &literal) in clause.literals.iter().enumerate() {
            self.checkpoint(limit)?;
            if self.value(literal)? == L_FALSE {
                continue;
            }
            if self.value(literal)? == L_TRUE {
                return Ok(true);
            }
            let atom = self.atoms.get_atom(literal).cloned().ok_or_else(|| {
                SmtError::Invariant(format!("the arithmetic literal {literal} has no atom"))
            })?;
            let set = self.evaluator.infeasible_intervals(
                &mut self.pm,
                &mut self.am,
                &self.assignment,
                &atom,
                literal & 1 == 1,
                Some(clause),
            )?;
            let Some(set) = set else {
                self.propagate(literal, None, true)?;
                return Ok(true);
            };
            if self.evaluator.ism.is_full(Some(&set)) {
                self.propagate(literal ^ 1, None, true)?;
                continue;
            }
            if self
                .evaluator
                .ism
                .subset(&mut self.am, Some(&set), xk_set.as_ref())?
            {
                self.propagate(literal, xk_set.as_ref(), true)?;
                return Ok(true);
            }
            let union = self
                .evaluator
                .ism
                .mk_union(&mut self.am, Some(&set), xk_set.as_ref())?;
            if self.evaluator.ism.is_full(union.as_ref()) {
                self.propagate(literal ^ 1, union.as_ref(), false)?;
                continue;
            }
            undef_count += 1;
            if selected.is_none() {
                selected = Some(index);
                selected_set = Some(set);
            }
        }
        let Some(selected) = selected else {
            return Ok(false);
        };
        if undef_count == 1 {
            self.set_literal_to_true(
                clause.literals[selected],
                Justification::Clause(clause.clone()),
            )?;
        } else {
            self.decide_literal(clause.literals[selected])?;
        }
        self.update_infeasible(selected_set)?;
        Ok(true)
    }

    fn process_clause(
        &mut self,
        clause: &ClauseRef,
        limit: Option<&ResourceLimit>,
    ) -> Result<bool, SmtError> {
        if self.is_clause_satisfied(clause)? {
            return Ok(true);
        }
        if self.xk == NULL_VAR {
            self.process_boolean_clause(clause)
        } else {
            self.process_arith_clause(clause, limit)
        }
    }

    // The clauses watching the current Boolean variable, or the current stage's variable: the
    // first that is false, read from the live watch list as the TypeScript's for-of does.
    fn process_clauses(
        &mut self,
        limit: Option<&ResourceLimit>,
    ) -> Result<Option<ClauseRef>, SmtError> {
        let is_boolean = self.xk == NULL_VAR;
        let bk = self.bk as usize;
        let xk = self.xk as usize;
        let mut index = 0;
        loop {
            let watches = if is_boolean {
                &self.bool_vars.bwatches[bk]
            } else {
                &self.watches[xk]
            };
            let Some(clause) = watches.get(index).cloned() else {
                return Ok(None);
            };
            if !self.process_clause(&clause, limit)? {
                return Ok(Some(clause));
            }
            index += 1;
        }
    }

    fn peek_next_bool_var(&mut self) {
        while (self.bk as usize) < self.atoms.atoms.len() {
            let bk = self.bk as usize;
            if !self.bool_vars.is_dead[bk]
                && self.atoms.atoms[bk].is_none()
                && self.bool_vars.bvalues[bk] == L_UNDEF
            {
                return;
            }
            self.bk += 1;
        }
        self.bk = NULL_BOOL_VAR;
    }

    fn new_stage(&mut self) {
        self.stats.stages += 1;
        self.trail.push(Trail::Stage);
        self.xk = if self.xk == NULL_VAR { 0 } else { self.xk + 1 };
    }

    // select_witness: a value outside the infeasible intervals, at random among the candidates.
    fn select_witness(&mut self) -> Result<(), SmtError> {
        let xk = self.xk as usize;
        let witness = self.evaluator.ism.pick_in_complement(
            &mut self.am,
            self.infeasible[xk].as_ref(),
            true,
        )?;
        if !self.am.is_rational(&witness)? {
            self.stats.irrational_assignments += 1;
        }
        set_value(&mut self.assignment, xk, Some(witness));
        Ok(())
    }

    fn search(&mut self, limit: Option<&ResourceLimit>) -> Result<LBool, SmtError> {
        self.bk = 0;
        self.xk = NULL_VAR;
        loop {
            if self.stats.conflicts > 0 && self.stats.conflicts.is_multiple_of(RESTART_THRESHOLD) {
                self.reorder_at_restart();
            }
            if self.xk == NULL_VAR {
                self.peek_next_bool_var();
                if self.bk == NULL_BOOL_VAR {
                    self.new_stage();
                }
            } else {
                self.new_stage();
            }
            if self.bk == NULL_BOOL_VAR && self.xk >= self.is_int.len() as Var {
                return Ok(L_TRUE);
            }
            loop {
                self.checkpoint(limit)?;
                let Some(conflict) = self.process_clauses(limit)? else {
                    break;
                };
                if !self.resolve(conflict, limit)? {
                    return Ok(L_FALSE);
                }
                if self
                    .max_conflicts
                    .is_some_and(|max_conflicts| self.stats.conflicts >= max_conflicts)
                {
                    return Ok(L_UNDEF);
                }
            }
            if self.xk == NULL_VAR {
                if self.bool_vars.bvalues[self.bk as usize] == L_UNDEF {
                    self.decide_literal(2 * self.bk + 1)?;
                    self.bk += 1;
                }
            } else {
                self.select_witness()?;
            }
        }
    }

    // gc: drops the learned clauses that took no part in a conflict since the last collection,
    // once they outnumber the input clauses four to one.
    fn gc(&mut self) {
        if self.learned.len() <= 4 * self.clauses.len() {
            return;
        }
        self.reset_watches();
        self.atoms.reinit_cache(&mut self.pm, &mut self.cache);
        let learned = std::mem::take(&mut self.learned);
        let mut kept = Vec::new();
        for (index, clause) in learned.into_iter().enumerate() {
            if index - kept.len() < self.clauses.len()
                && clause.literals.len() > 1
                && !clause.is_active.get()
            {
                self.del_clause(&clause);
            } else {
                clause.is_active.set(false);
                kept.push(clause);
            }
        }
        self.learned = kept;
        let clauses = self.clauses.clone();
        self.reattach_arith_clauses(&clauses);
        let learned = self.learned.clone();
        self.reattach_arith_clauses(&learned);
    }

    fn undo_to_base(&mut self) {
        self.init_search();
        self.bk = 0;
        self.xk = NULL_VAR;
    }

    // do_reorder
    fn reorder_at_restart(&mut self) {
        self.undo_to_base();
        self.stats.restarts += 1;
        self.stats.conflicts += 1;
        if self.is_reordered {
            self.restore_order();
        }
        self.apply_reorder();
    }

    // try_reorder
    fn try_reorder(&mut self) {
        self.gc();
        if !self.stats.restarts.is_multiple_of(10) {
            return;
        }
        if self.is_reordered {
            self.restore_order();
        }
        self.apply_reorder();
    }

    // search_check: the search, again after each model that gives an integer variable a fraction,
    // with the lemma that the variable lies outside the open interval between the integers around
    // its value.
    fn search_check(&mut self, limit: Option<&ResourceLimit>) -> Result<LBool, SmtError> {
        self.stats.conflicts = 0;
        self.stats.restarts = 0;
        loop {
            let result = self.search(limit)?;
            if result != L_TRUE {
                return Ok(result);
            }
            self.stats.restarts += 1;
            self.try_reorder();
            let mut bounds: Vec<(Var, Rational)> = Vec::new();
            for variable in 0..self.is_int.len() {
                if !self.is_int[variable] {
                    continue;
                }
                let Some(value) = self.assignment.get(variable).cloned().flatten() else {
                    continue;
                };
                if self.am.is_int(&value) {
                    continue;
                }
                let below = match &*self.am.int_lt(&value).value() {
                    AnumValue::Rational(below) => below.clone(),
                    AnumValue::Cell(_) => continue,
                };
                let mut lower = below;
                loop {
                    lower = lower.add(&Rational::one());
                    if self.am.compare(&value, &Anum::new(lower.clone()))? <= 0 {
                        lower = lower.sub(&Rational::one());
                        break;
                    }
                }
                bounds.push((variable as Var, lower));
            }
            if bounds.is_empty() {
                return Ok(result);
            }
            self.init_search();
            for (variable, lower) in &bounds {
                self.lemma.reset(&mut self.atoms, Some(&mut self.bool_vars));
                let below = self
                    .pm
                    .mk_linear(&[Int::one()], &[*variable], &-lower.num());
                let literal = self.mk_ineq_literal(IneqKind::Gt, &[below], &[false]) ^ 1;
                self.lemma.push(&mut self.atoms, literal);
                let above =
                    self.pm
                        .mk_linear(&[Int::one()], &[*variable], &(-lower.num() - Int::one()));
                let literal = self.mk_ineq_literal(IneqKind::Lt, &[above], &[false]) ^ 1;
                self.lemma.push(&mut self.atoms, literal);
                let literals = self.lemma.literals.clone();
                self.mk_clause(&literals, true, None);
            }
        }
    }

    fn init_search(&mut self) {
        self.undo_until(|_| true);
        while self.scope_level > 0 {
            self.scope_level -= 1;
        }
        self.xk = NULL_VAR;
        self.bool_vars.bvalues.fill(L_UNDEF);
        self.assignment.clear();
    }

    // check: satisfiable, unsatisfiable or unknown once max_conflicts conflicts passed. The
    // variables are reordered for the search and restored after it.
    pub fn check(&mut self, limit: Option<&ResourceLimit>) -> Result<LBool, SmtError> {
        self.init_search();
        self.explain.is_full_dimensional = self.clauses.iter().all(|clause| {
            clause
                .literals
                .iter()
                .all(|&literal| self.is_full_dimensional(literal))
        });
        let is_reordered = self.can_reorder();
        if is_reordered {
            self.reorder_heuristically();
        }
        for variable in 0..self.watches.len() {
            self.sort_clauses_by_degree(variable);
        }
        let result = self.search_check(limit)?;
        if is_reordered {
            self.restore_order();
        }
        Ok(result)
    }

    fn is_full_dimensional(&self, literal: u32) -> bool {
        let Some(atom) = self.atoms.get_atom(literal) else {
            return true;
        };
        let is_neg = literal & 1 == 1;
        match &**atom {
            Atom::Ineq(ineq) if ineq.kind == IneqKind::Eq => is_neg,
            Atom::Root(root)
                if matches!(
                    root.kind,
                    RootKind::RootEq | RootKind::RootLe | RootKind::RootGe
                ) =>
            {
                is_neg
            }
            _ => !is_neg,
        }
    }

    // sort_clauses_by_degree, on the clauses watching variable.
    fn sort_clauses_by_degree(&mut self, variable: usize) {
        let clauses = &self.watches[variable];
        if clauses.len() <= 1 {
            return;
        }
        let degrees: Vec<u32> = clauses
            .iter()
            .map(|clause| self.get_clause_degree(clause))
            .collect();
        let mut order: Vec<usize> = (0..clauses.len()).collect();
        order.sort_by(|&first, &second| {
            degrees[first]
                .cmp(&degrees[second])
                .then(first.cmp(&second))
        });
        let sorted: Vec<ClauseRef> = order.iter().map(|&index| clauses[index].clone()).collect();
        self.watches[variable] = sorted;
    }

    // check(rvalues, clause): the assignment's verdict on the clauses. A falsified clause gives
    // the literal of least degree among the falsified clauses, and the lemma of the linear cell
    // around the assignment in which that literal stays false. Like Z3, only that case restores
    // the assignment. No step is counted here, so the limit goes unused, as in the TypeScript.
    pub fn check_assignment(
        &mut self,
        values: &[Option<Anum>],
        _limit: Option<&ResourceLimit>,
    ) -> Result<(LBool, Vec<u32>), SmtError> {
        let saved: Vec<Option<Anum>> = self
            .assignment
            .iter()
            .map(|value| value.as_ref().map(|value| self.am.copy(value)))
            .collect();
        self.set_assignment(values);
        let mut best: Option<u32> = None;
        let mut result = L_TRUE;
        for clause_index in 0..self.clauses.len() {
            let clause = self.clauses[clause_index].clone();
            let mut literal_values = Vec::new();
            for &literal in &clause.literals {
                literal_values.push(self.value(literal)?);
            }
            if literal_values.contains(&L_TRUE) {
                continue;
            }
            if !literal_values.iter().all(|&value| value == L_FALSE) {
                result = L_UNDEF;
                continue;
            }
            for &literal in &clause.literals {
                let is_less = match best {
                    None => true,
                    Some(best) => {
                        let atom = self.get_falsified_atom(literal)?;
                        let best_atom = self.get_falsified_atom(best)?;
                        self.atoms.get_degree(&self.pm, &atom)
                            < self.atoms.get_degree(&self.pm, &best_atom)
                    }
                };
                if is_less {
                    best = Some(literal);
                }
            }
        }
        let Some(best) = best else {
            return Ok((result, Vec::new()));
        };
        self.lazy_clause
            .reset(&mut self.atoms, Some(&mut self.bool_vars));
        let mut context = ExplainContext {
            pm: &mut self.pm,
            am: &mut self.am,
            cache: &mut self.cache,
            atoms: &mut self.atoms,
            sample: &mut self.assignment,
            evaluator: &mut self.evaluator,
            hooks: &mut self.bool_vars,
            var2eq: &self.var2eq,
        };
        self.explain
            .compute_linear_explanation(&mut context, &[best], &mut self.lazy_clause)?;
        let mut clause = self.lazy_clause.literals.clone();
        clause.push(best ^ 1);
        self.set_assignment(&saved);
        Ok((L_FALSE, clause))
    }

    // The TS getAtom(literal)! of a literal of a falsified clause.
    fn get_falsified_atom(&self, literal: u32) -> Result<AtomRef, SmtError> {
        self.atoms.get_atom(literal).cloned().ok_or_else(|| {
            SmtError::Invariant(format!("the falsified literal {literal} has no atom"))
        })
    }

    fn set_assignment(&mut self, values: &[Option<Anum>]) {
        self.assignment = values
            .iter()
            .map(|value| value.as_ref().map(|value| self.am.copy(value)))
            .collect();
    }

    // Conflict resolution.

    fn is_marked(&self, bool_var: u32) -> bool {
        self.marks.get(bool_var as usize).copied().unwrap_or(false)
    }

    fn set_mark(&mut self, bool_var: u32, is_marked: bool) {
        let index = bool_var as usize;
        if index >= self.marks.len() {
            self.marks.resize(index + 1, false);
        }
        self.marks[index] = is_marked;
    }

    fn process_antecedent(
        &mut self,
        antecedent: u32,
        limit: Option<&ResourceLimit>,
    ) -> Result<(), SmtError> {
        self.checkpoint(limit)?;
        let bool_var = antecedent >> 1;
        if self.get_assigned_value(antecedent) == L_UNDEF {
            self.checkpoint(limit)?;
            if !self.is_marked(bool_var) {
                self.set_mark(bool_var, true);
                self.lemma.push(&mut self.atoms, antecedent);
            }
            return Ok(());
        }
        if self.is_marked(bool_var) {
            return Ok(());
        }
        self.set_mark(bool_var, true);
        if self.bool_vars.levels[bool_var as usize] == self.scope_level
            && self.atoms.get_max_var(antecedent) == self.xk
        {
            self.mark_count += 1;
        } else {
            self.lemma.push(&mut self.atoms, antecedent);
        }
        Ok(())
    }

    // bool_var is None for the conflict clause, which resolves every literal.
    fn resolve_literals(
        &mut self,
        bool_var: Option<u32>,
        literals: &[u32],
        limit: Option<&ResourceLimit>,
    ) -> Result<(), SmtError> {
        for &literal in literals {
            if Some(literal >> 1) != bool_var {
                self.process_antecedent(literal, limit)?;
            }
        }
        Ok(())
    }

    fn resolve_clause(
        &mut self,
        bool_var: Option<u32>,
        clause: &ClauseRef,
        limit: Option<&ResourceLimit>,
    ) -> Result<(), SmtError> {
        clause.is_active.set(true);
        self.resolve_literals(bool_var, &clause.literals, limit)?;
        self.lemma_assumptions = mk_join(&clause.assumptions, &self.lemma_assumptions);
        Ok(())
    }

    // resolve_lazy_justification: the explanation of the excluded line, with the negations of the
    // literals that excluded it, as the clause to resolve with.
    fn resolve_lazy_justification(
        &mut self,
        bool_var: u32,
        literals: &[u32],
        clauses: &[ClauseRef],
        limit: Option<&ResourceLimit>,
    ) -> Result<(), SmtError> {
        self.lazy_clause
            .reset(&mut self.atoms, Some(&mut self.bool_vars));
        let mut context = ExplainContext {
            pm: &mut self.pm,
            am: &mut self.am,
            cache: &mut self.cache,
            atoms: &mut self.atoms,
            sample: &mut self.assignment,
            evaluator: &mut self.evaluator,
            hooks: &mut self.bool_vars,
            var2eq: &self.var2eq,
        };
        self.explain
            .compute_conflict_explanation(&mut context, literals, &mut self.lazy_clause)?;
        for &literal in literals {
            self.lazy_clause.push(&mut self.atoms, literal ^ 1);
        }
        self.checkpoint(limit)?;
        let lazy_literals = self.lazy_clause.literals.clone();
        self.resolve_literals(Some(bool_var), &lazy_literals, limit)?;
        for clause in clauses {
            self.lemma_assumptions = mk_join(&clause.assumptions, &self.lemma_assumptions);
        }
        Ok(())
    }

    fn reset_marks(&mut self) {
        for index in 0..self.lemma.literals.len() {
            self.set_mark(self.lemma.literals[index] >> 1, false);
        }
    }

    // scoped_reset_marks
    fn release_marks(&mut self) {
        if self.mark_count > 0 {
            self.mark_count = 0;
            self.marks.fill(false);
        } else {
            self.reset_marks();
        }
    }

    // resolve: learns a lemma from the conflict and backjumps. False when the lemma is empty.
    fn resolve(
        &mut self,
        conflict: ClauseRef,
        limit: Option<&ResourceLimit>,
    ) -> Result<bool, SmtError> {
        let mut conflict_clause = conflict;
        loop {
            self.stats.conflicts += 1;
            self.mark_count = 0;
            self.lemma.reset(&mut self.atoms, Some(&mut self.bool_vars));
            self.lemma_assumptions = None;
            let outcome = match self.learn(&conflict_clause, limit) {
                Err(error) => Err(error),
                Ok(Learned::Empty) => Ok(Some(false)),
                Ok(Learned::Conflict) => Ok(Some(true)),
                Ok(Learned::Clause(lemma)) => {
                    self.process_clause(&lemma, limit).map(|is_propagated| {
                        if is_propagated {
                            return Some(true);
                        }
                        conflict_clause = lemma;
                        None
                    })
                }
            };
            // The TypeScript's finally.
            self.release_marks();
            if let Some(is_resolved) = outcome? {
                return Ok(is_resolved);
            }
        }
    }

    // The body of resolve for one conflict: Empty for the empty lemma, Conflict when the conflict
    // clause itself is the lemma and now propagates, else the learned clause.
    fn learn(
        &mut self,
        conflict: &ClauseRef,
        limit: Option<&ResourceLimit>,
    ) -> Result<Learned, SmtError> {
        self.resolve_clause(None, conflict, limit)?;
        let mut top = self.trail.len();
        let mut is_decision = false;
        loop {
            while self.mark_count > 0 {
                self.checkpoint(limit)?;
                let entry = top
                    .checked_sub(1)
                    .and_then(|index| self.trail.get(index))
                    .ok_or_else(|| {
                        SmtError::Invariant("marked literals past the trail".to_string())
                    })?;
                let marked = match *entry {
                    Trail::Assignment(bool_var) if self.is_marked(bool_var) => Some(bool_var),
                    _ => None,
                };
                if let Some(bool_var) = marked {
                    self.mark_count -= 1;
                    self.set_mark(bool_var, false);
                    let justification = self.bool_vars.justifications[bool_var as usize]
                        .clone()
                        .ok_or_else(|| {
                            SmtError::Invariant(format!("b{bool_var} has no justification"))
                        })?;
                    match justification {
                        Justification::Clause(clause) => {
                            self.resolve_clause(Some(bool_var), &clause, limit)?;
                        }
                        Justification::Lazy { literals, clauses } => {
                            self.resolve_lazy_justification(bool_var, &literals, &clauses, limit)?;
                        }
                        Justification::Decision => {
                            is_decision = true;
                            let is_true = self.bool_vars.bvalues[bool_var as usize] == L_TRUE;
                            self.lemma
                                .push(&mut self.atoms, 2 * bool_var + u32::from(is_true));
                        }
                    }
                }
                top -= 1;
            }
            if is_decision {
                break;
            }
            if self
                .lemma
                .literals
                .iter()
                .all(|&literal| self.atoms.get_max_var(literal) != self.xk)
            {
                break;
            }
            let mut max_level = 0;
            for &literal in &self.lemma.literals {
                if self.get_assigned_value(literal) == L_FALSE {
                    max_level = max_level.max(self.bool_vars.levels[(literal >> 1) as usize]);
                }
            }
            // remove_literals_from_lvl
            let mut kept = 0;
            for index in 0..self.lemma.literals.len() {
                let literal = self.lemma.literals[index];
                let bool_var = literal >> 1;
                if self.get_assigned_value(literal) == L_FALSE
                    && self.bool_vars.levels[bool_var as usize] == max_level
                    && self.atoms.get_max_var(literal) == self.xk
                {
                    self.mark_count += 1;
                    continue;
                }
                self.lemma
                    .set(&mut self.atoms, Some(&mut self.bool_vars), kept, literal);
                kept += 1;
            }
            self.lemma
                .shrink(&mut self.atoms, Some(&mut self.bool_vars), kept);
            self.undo_until_level(max_level);
            top = self.trail.len();
        }
        if self.lemma.size() == 0 {
            return Ok(Learned::Empty);
        }
        self.reset_marks();
        let literals = self.lemma.literals.clone();
        if !is_decision {
            let mut max_var = NULL_VAR;
            for &literal in &literals {
                let variable = self.atoms.get_max_var(literal);
                if variable != NULL_VAR && (max_var == NULL_VAR || variable > max_var) {
                    max_var = variable;
                }
            }
            self.undo_until_stage(max_var);
            return Ok(Learned::Clause(self.mk_clause(
                &literals,
                true,
                self.lemma_assumptions.clone(),
            )));
        }
        if literals
            .iter()
            .all(|&literal| self.atoms.get_atom(literal).is_none())
        {
            let bool_var = (literals[literals.len() - 1] >> 1) as usize;
            self.undo_until(|solver| solver.bool_vars.bvalues[bool_var] != L_UNDEF);
        } else {
            let level = self.find_new_level(&literals);
            self.undo_until_level(level);
        }
        if literals == conflict.literals {
            self.process_clause(conflict, limit)?;
            return Ok(Learned::Conflict);
        }
        Ok(Learned::Clause(self.mk_clause(
            &literals,
            true,
            self.lemma_assumptions.clone(),
        )))
    }

    // find_new_level_arith_lemma: the highest level of a literal of the current stage other than
    // the last, else the level below the current one.
    fn find_new_level(&self, literals: &[u32]) -> i64 {
        let mut level = -1;
        for &literal in &literals[..literals.len() - 1] {
            if self.atoms.get_max_var(literal) == self.xk {
                level = level.max(self.bool_vars.levels[(literal >> 1) as usize]);
            }
        }
        if level == -1 {
            self.scope_level - 1
        } else {
            level
        }
    }

    // Variable order.

    fn can_reorder(&self) -> bool {
        self.learned.iter().chain(&self.clauses).all(|clause| {
            clause.literals.iter().all(|&literal| {
                !self
                    .atoms
                    .get_atom(literal)
                    .is_some_and(|atom| matches!(**atom, Atom::Root(_)))
            })
        })
    }

    // apply_reorder
    fn apply_reorder(&mut self) {
        self.is_reordered = false;
        if !self.can_reorder() {
            return;
        }
        self.reorder_heuristically();
        self.is_reordered = true;
    }

    // heuristic_reorder: higher maximal degree first, then more occurrences, then a random order.
    fn reorder_heuristically(&mut self) {
        let count = self.is_int.len();
        let mut max_degrees = vec![0; count];
        let mut occurrences = vec![0u32; count];
        let pm = &self.pm;
        let mut collect = |polynomial: &Polynomial| {
            let mut variables: Vec<Var> = Vec::new();
            for index in 0..polynomial.size() {
                for &variable in pm.monomial_vars(polynomial.monomial_at(index)) {
                    if !variables.contains(&variable) {
                        variables.push(variable);
                    }
                }
            }
            for variable in variables {
                let index = variable as usize;
                occurrences[index] += 1;
                max_degrees[index] = max_degrees[index].max(pm.degree(polynomial, variable));
            }
        };
        for clause in self.clauses.iter().chain(&self.learned) {
            for &literal in &clause.literals {
                let Some(atom) = self.atoms.get_atom(literal) else {
                    continue;
                };
                match &**atom {
                    Atom::Ineq(ineq) => ineq.polynomials.iter().for_each(&mut collect),
                    Atom::Root(root) => collect(&root.polynomial),
                }
            }
        }
        // init_shuffle
        let mut shuffle: Vec<usize> = (0..count).collect();
        self.random_seed += 1;
        let mut random = RandomGen::new(self.random_seed);
        for index in (0..count).rev() {
            let other = random.next() as usize % (index + 1);
            shuffle.swap(index, other);
        }
        let mut order: Vec<usize> = (0..count).collect();
        order.sort_by(|&first, &second| {
            max_degrees[second]
                .cmp(&max_degrees[first])
                .then(occurrences[second].cmp(&occurrences[first]))
                .then(shuffle[first].cmp(&shuffle[second]))
        });
        let mut permutation: Vec<Var> = vec![0; count];
        for (position, &variable) in order.iter().enumerate() {
            permutation[variable] = position as Var;
        }
        self.reorder(&permutation);
    }

    // reorder: renames each variable x to permutation[x], in the polynomials, the assignment and
    // the watches.
    fn reorder(&mut self, permutation: &[Var]) {
        let learned = std::mem::take(&mut self.learned);
        let mut kept = Vec::new();
        for clause in learned {
            if clause.literals.iter().any(|&literal| {
                self.atoms
                    .get_atom(literal)
                    .is_some_and(|atom| matches!(**atom, Atom::Root(_)))
            }) {
                self.del_clause(&clause);
            } else {
                kept.push(clause);
            }
        }
        self.learned = kept;
        self.atoms.reinit_cache(&mut self.pm, &mut self.cache);
        self.reset_watches();
        let mut assignment: Vec<Option<Anum>> = Vec::new();
        for (variable, value) in self.assignment.iter().enumerate() {
            if let Some(value) = value {
                set_value(
                    &mut assignment,
                    permutation[variable] as usize,
                    Some(value.clone()),
                );
            }
        }
        self.undo_until_stage(NULL_VAR);
        self.cache.reset();
        let inv_perm: Vec<Var> = self
            .inv_perm
            .iter()
            .map(|&variable| permutation[variable as usize])
            .collect();
        for (external, &internal) in inv_perm.iter().enumerate() {
            self.perm[internal as usize] = external as Var;
        }
        let is_int = self.is_int.clone();
        for (variable, &flag) in is_int.iter().enumerate() {
            self.is_int[permutation[variable] as usize] = flag;
        }
        self.inv_perm = inv_perm;
        let mut polynomials: Vec<Polynomial> = Vec::new();
        let mut is_seen = HashSet::new();
        for atom in self.atoms.atoms.iter().flatten() {
            let atom_polynomials = match &**atom {
                Atom::Ineq(ineq) => &ineq.polynomials[..],
                Atom::Root(root) => std::slice::from_ref(&root.polynomial),
            };
            for polynomial in atom_polynomials {
                if is_seen.insert(Rc::as_ptr(polynomial)) {
                    polynomials.push(polynomial.clone());
                }
            }
        }
        self.pm.rename(permutation, &polynomials);
        self.atoms.reinit_cache(&mut self.pm, &mut self.cache);
        self.set_assignment(&assignment);
        let clauses = self.clauses.clone();
        self.reattach_arith_clauses(&clauses);
        let learned = self.learned.clone();
        self.reattach_arith_clauses(&learned);
    }

    // restore_order
    pub fn restore_order(&mut self) {
        let perm = self.perm.clone();
        self.reorder(&perm);
    }

    fn reset_watches(&mut self) {
        for watches in &mut self.watches {
            watches.clear();
        }
    }

    fn reattach_arith_clauses(&mut self, clauses: &[ClauseRef]) {
        for clause in clauses {
            let variable = self.get_max_var(clause);
            if variable != NULL_VAR {
                self.watches[variable as usize].push(clause.clone());
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::NlsatSolver;
    use crate::nlsat::algebraic::Anum;
    use crate::nlsat::test_util::{
        parse_polynomial, parse_rational, read_fixture, show_anum, show_polynomial,
    };
    use crate::nlsat::types::{Atom, IneqKind, RootKind};
    use crate::nlsat::{L_FALSE, L_TRUE};

    fn get_kind_name(atom: Option<&Atom>) -> &'static str {
        match atom {
            None => "undefined",
            Some(Atom::Ineq(ineq)) => match ineq.kind {
                IneqKind::Eq => "EQ",
                IneqKind::Lt => "LT",
                IneqKind::Gt => "GT",
            },
            Some(Atom::Root(root)) => match root.kind {
                RootKind::RootEq => "ROOT_EQ",
                RootKind::RootLt => "ROOT_LT",
                RootKind::RootGt => "ROOT_GT",
                RootKind::RootLe => "ROOT_LE",
                RootKind::RootGe => "ROOT_GE",
            },
        }
    }

    // The harness's constraint kinds: LE and GE as negated GT and LT.
    fn mk_harness_literal(solver: &mut NlsatSolver, kind: &str, text: &str) -> u32 {
        let polynomial = parse_polynomial(&mut solver.pm, text);
        match kind {
            "LE" => solver.mk_ineq_literal(IneqKind::Gt, &[polynomial], &[false]) ^ 1,
            "GE" => solver.mk_ineq_literal(IneqKind::Lt, &[polynomial], &[false]) ^ 1,
            _ => solver.mk_ineq_literal(
                match kind {
                    "EQ" => IneqKind::Eq,
                    "LT" => IneqKind::Lt,
                    _ => IneqKind::Gt,
                },
                &[polynomial],
                &[false],
            ),
        }
    }

    // The harness command: ca n, then int flags, one c KIND poly line per constraint, v x num den
    // per variable, and end. It prints each constraint's literal, then undef or the lemma.
    fn run_check_assignment(input: &str) -> String {
        let mut solver = NlsatSolver::new(None);
        let mut values: Vec<Option<Anum>> = Vec::new();
        let mut output: Vec<String> = Vec::new();
        let mut count = 0;
        for line in input.split('\n') {
            let words: Vec<&str> = line.split(' ').collect();
            if words[0] == "ca" {
                count = words[1].parse().expect("a count");
            }
            if words[0] == "int" {
                for variable in 0..count {
                    solver.mk_var(words.get(variable + 1) == Some(&"1"));
                }
            }
            if words[0] == "v" {
                let variable: usize = words[1].parse().expect("a variable");
                if variable >= values.len() {
                    values.resize(variable + 1, None);
                }
                values[variable] = Some(Anum::new(parse_rational(&format!(
                    "{}/{}",
                    words[2], words[3]
                ))));
            }
            if words[0] != "c" {
                continue;
            }
            let literal = mk_harness_literal(&mut solver, words[1], &words[2..].join(" "));
            solver.mk_external_clause(&[literal], None);
            output.push(format!("lit {literal}"));
        }
        let (result, clause) = solver
            .check_assignment(&values, None)
            .expect("check_assignment");
        let literals: Vec<String> = clause
            .iter()
            .map(|&literal| {
                let atom = solver.get_atom(literal);
                let sign = if literal & 1 == 1 { "!" } else { "+" };
                let polynomial = match atom.as_deref() {
                    Some(Atom::Ineq(ineq)) => show_polynomial(&solver.pm, &ineq.polynomials[0]),
                    _ => String::new(),
                };
                format!(
                    " {literal} {sign}{} {polynomial}",
                    get_kind_name(atom.as_deref())
                )
            })
            .collect();
        output.push(if result == L_FALSE {
            format!("lemma{}", literals.join(""))
        } else {
            "undef".to_string()
        });
        output.join("\n")
    }

    // The harness command: search n max_conflicts, then int flags, one a KIND poly line per atom,
    // and cl assumption refs per clause, a ref being a signed 1-based atom number. It prints each
    // clause's literals, the verdict, the nonzero statistics, and the model or the core.
    fn run_search(input: &str) -> String {
        let mut solver = NlsatSolver::new(None);
        let mut atoms: Vec<u32> = Vec::new();
        let mut output: Vec<String> = Vec::new();
        let header: Vec<&str> = input.split('\n').next().unwrap_or("").split(' ').collect();
        if header[2] != "0" {
            solver.max_conflicts = Some(header[2].parse().expect("max_conflicts"));
        }
        for line in input.split('\n') {
            let words: Vec<&str> = line.split(' ').collect();
            if words[0] == "int" {
                for flag in &words[1..] {
                    solver.mk_var(*flag == "1");
                }
            }
            if words[0] == "a" {
                atoms.push(mk_harness_literal(
                    &mut solver,
                    words[1],
                    &words[2..].join(" "),
                ));
            }
            if words[0] != "cl" {
                continue;
            }
            let literals: Vec<u32> = words[2..]
                .iter()
                .map(|word| {
                    let reference: i64 = word.parse().expect("a reference");
                    if reference > 0 {
                        atoms[(reference - 1) as usize]
                    } else {
                        atoms[(-reference - 1) as usize] ^ 1
                    }
                })
                .collect();
            let shown: Vec<String> = literals.iter().map(ToString::to_string).collect();
            output.push(format!("clause {}", shown.join(" ")));
            solver.mk_external_clause(
                &literals,
                if words[1] == "-1" {
                    None
                } else {
                    Some(words[1].parse().expect("an assumption"))
                },
            );
        }
        let result = solver.check(None).expect("check");
        output.push(
            if result == L_TRUE {
                "sat"
            } else if result == L_FALSE {
                "unsat"
            } else {
                "undef"
            }
            .to_string(),
        );
        let stats = &solver.stats;
        let counts = [
            ("conflicts", stats.conflicts),
            ("propagations", stats.propagations),
            ("decisions", stats.decisions),
            ("restarts", stats.restarts),
            ("stages", stats.stages),
            ("irrational_assignments", stats.irrational_assignments),
        ];
        let shown: String = counts
            .iter()
            .filter(|count| count.1 > 0)
            .map(|count| format!(" {}={}", count.0, count.1))
            .collect();
        output.push(format!("stats{shown}"));
        if result == L_TRUE {
            let count: i32 = header[1].parse().expect("a variable count");
            let mut model = String::new();
            for variable in 0..count {
                let value = solver.get_value(variable);
                model.push_str(&show_anum(&mut solver.am, &value));
            }
            output.push(format!("model{model}"));
        }
        if result == L_FALSE {
            let core: String = solver
                .get_core()
                .iter()
                .map(|assumption| format!(" {assumption}"))
                .collect();
            output.push(format!("core{core}"));
        }
        output.join("\n")
    }

    fn check_cases(name: &str, run: fn(&str) -> String) {
        let failures: Vec<String> = read_fixture(name)
            .into_iter()
            .filter_map(|(input, expected)| {
                let actual = run(&input);
                (actual != expected)
                    .then(|| format!("input:\n{input}\nexpected:\n{expected}\nactual:\n{actual}\n"))
            })
            .collect();
        assert!(failures.is_empty(), "{}", failures.join("\n"));
    }

    // Random constraints of degree 2 or less, with the lemmas that Z3's nlsat solver returns for
    // an assignment that violates them, literal numbering and monomial order included.
    #[test]
    fn check_assignment_matches_z3() {
        check_cases("check-assignment.json", run_check_assignment);
    }

    #[test]
    fn check_assignment_answers_undef_when_every_constraint_holds_because_of_the_clause_true() {
        assert_eq!(
            run_check_assignment("ca 1\nint 0\nc GT 1:0^1\nv 0 1 1\nend"),
            "lit 2\nundef"
        );
    }

    #[test]
    fn check_assignment_explains_with_a_polynomial_of_degree_2_by_factoring_it() {
        assert_eq!(
            run_check_assignment("ca 1\nint 0\nc LT 1:0^2 -4:\nv 0 3 1\nend"),
            "lit 2\nlemma 5 !GT [1:0^1 -2:] 3 !LT [1:0^2 -4:]"
        );
    }

    #[test]
    fn check_assignment_bounds_an_irrational_root_by_linear_polynomials_as_z3_does() {
        assert_eq!(
            run_check_assignment("ca 1\nint 0\nc EQ 1:0^2 -2:\nv 0 1 1\nend"),
            "lit 2\nlemma 5 !GT [1:0^1 1:] 7 !LT [4:0^1 -5:] 3 !EQ [1:0^2 -2:]"
        );
    }

    // Random clauses over atoms of degree 4 or less, with the verdict, statistics, model and core
    // of Z3's nlsat check.
    #[test]
    fn search_matches_z3() {
        check_cases("search.json", run_search);
    }
}
