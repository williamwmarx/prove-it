//! Ported from Z3 (src/smt/smt_conflict_resolution.cpp), MIT license, see z3-license.txt, through
//! `conflict-resolution.ts`. First-UIP conflict resolution with lemma minimization. Equalities in
//! a conflict are explained by walking the transitivity branches of the E-graph down to literals.
//!
//! `ConflictResolution` keeps the context, so its own fields are this struct, held by the context
//! as `conflict_resolution`, and its methods are `impl Context` methods here. A justification
//! explains itself through `Antecedents`, which `Explainer` implements over the context's fields.

use std::collections::HashSet;
use std::mem;

use crate::core::ast::{AstManager, Expr};
use crate::core::clause::BJustification;
use crate::core::context::Context;
use crate::core::enode::{Antecedents, EnodeId, Enodes, EqJustification, JustificationId};
use crate::core::literal::{BoolVar, FALSE_LITERAL, Literal, get_var, mk_literal, negate};
use crate::core::ref_vector::RefVector;
use crate::util::error::SmtError;
use crate::util::lbool::LBool;

#[derive(Clone, Debug, Default)]
pub struct ConflictResolution {
    antecedents: Vec<Literal>,
    todo_justifications: Vec<JustificationId>,
    todo_justifications_head: usize,
    todo_eqs: Vec<EnodeId>,
    processed_eqs: HashSet<(Expr, Expr)>,
    pub lemma: Vec<Literal>,
    /// m_lemma_atoms: the atoms of the lemma, which it holds until the lemma is a clause.
    pub lemma_atoms: RefVector,
    conflict_level: u32,
    pub new_scope_level: u32,
    pub lemma_iscope_level: u32,
    unmark: Vec<BoolVar>,
    /// m_lvl_set: a level_approx_set, whose bit level mod 32 stands for each level of the lemma,
    /// so other levels can pass for them.
    level_set: u32,
    minimization_stack: Vec<BoolVar>,
}

impl ConflictResolution {
    pub fn new() -> Self {
        Self::default()
    }
}

/// The conflict resolution's marking, over the context's fields that a justification reads while
/// the justifications' marks are written.
struct Explainer<'a> {
    resolution: &'a mut ConflictResolution,
    marks: &'a mut [bool],
    enodes: &'a Enodes,
    m: &'a AstManager,
    expr_to_bool_var: &'a [i32],
    assignment: &'a [LBool],
}

impl Explainer<'_> {
    fn eq_justification_to_literals(
        &mut self,
        lhs: EnodeId,
        rhs: EnodeId,
        justification: EqJustification,
    ) {
        match justification {
            EqJustification::Equation { literal } => self.resolution.antecedents.push(literal),
            EqJustification::Justification { justification } => {
                self.mark_justification(justification);
            }
            EqJustification::Congruence { is_commutative } => {
                let lhs_node = self.enodes.get(lhs);
                let rhs_node = self.enodes.get(rhs);
                if is_commutative {
                    self.mark_eq(lhs_node.get_arg(0), rhs_node.get_arg(1));
                    self.mark_eq(lhs_node.get_arg(1), rhs_node.get_arg(0));
                } else {
                    for index in 0..lhs_node.num_args() {
                        self.mark_eq(lhs_node.get_arg(index), rhs_node.get_arg(index));
                    }
                }
            }
            EqJustification::Axiom => {}
        }
    }

    fn eq_branch_to_literals(&mut self, start: EnodeId, ancestor: EnodeId) {
        let mut node = start;
        while node != ancestor {
            let Some(target) = self.enodes.get(node).trans_target else {
                break;
            };
            self.eq_justification_to_literals(
                node,
                target,
                self.enodes.get(node).trans_justification,
            );
            node = target;
        }
    }
}

impl Antecedents for Explainer<'_> {
    fn mark_literal(&mut self, literal: Literal) {
        self.resolution.antecedents.push(literal);
    }

    /// mark_eq: the pair starts with the node whose owner has the smaller id, which fixes the
    /// order in which eq2literals walks the two branches.
    fn mark_eq(&mut self, first: EnodeId, second: EnodeId) {
        if first == second {
            return;
        }
        let ids = &self.m.ids;
        let is_swapped = ids[self.enodes.get(first).owner as usize]
            > ids[self.enodes.get(second).owner as usize];
        let (lower, upper) = if is_swapped {
            (second, first)
        } else {
            (first, second)
        };
        let key = (self.enodes.get(lower).owner, self.enodes.get(upper).owner);
        if !self.resolution.processed_eqs.insert(key) {
            return;
        }
        self.resolution.todo_eqs.push(lower);
        self.resolution.todo_eqs.push(upper);
    }

    fn mark_justification(&mut self, justification: JustificationId) {
        if self.marks[justification as usize] {
            return;
        }
        self.marks[justification as usize] = true;
        self.resolution.todo_justifications.push(justification);
    }

    fn mark_justified_eq(
        &mut self,
        first: EnodeId,
        second: EnodeId,
        justification: EqJustification,
    ) {
        self.eq_justification_to_literals(first, second, justification);
    }

    fn get_root(&self, node: EnodeId) -> EnodeId {
        self.enodes.get(node).root
    }

    fn enode_to_literal(&self, node: EnodeId) -> Result<Literal, SmtError> {
        let owner = self.enodes.get(node).owner;
        let bool_var = match self.expr_to_bool_var.get(owner as usize) {
            Some(bool_var) if *bool_var != -1 => *bool_var as BoolVar,
            _ => {
                return Err(SmtError::Invariant(
                    "the formula has no Boolean variable".into(),
                ));
            }
        };
        Ok(mk_literal(
            bool_var,
            self.assignment[mk_literal(bool_var, false) as usize] == LBool::False,
        ))
    }
}

impl Context {
    fn explainer(&mut self) -> (&[crate::core::enode::Justification], Explainer<'_>) {
        let (entries, marks) = self.justification_arena.split_marks();
        (
            entries,
            Explainer {
                resolution: &mut self.conflict_resolution,
                marks,
                enodes: &self.enode_arena,
                m: &self.m,
                expr_to_bool_var: &self.expr_to_bool_var,
                assignment: &self.assignment,
            },
        )
    }

    fn mark_justification(&mut self, justification: JustificationId) {
        self.explainer().1.mark_justification(justification);
    }

    fn find_common_ancestor(&mut self, first: EnodeId, second: EnodeId) -> EnodeId {
        let mut node = Some(first);
        while let Some(current) = node {
            self.node_mut(current).set_is_marked2(true);
            node = self.node(current).trans_target;
        }
        let mut result = second;
        while !self.node(result).is_marked2() {
            let Some(target) = self.node(result).trans_target else {
                break;
            };
            result = target;
        }
        let mut node = Some(first);
        while let Some(current) = node {
            self.node_mut(current).set_is_marked2(false);
            node = self.node(current).trans_target;
        }
        result
    }

    fn process_justifications(&mut self) -> Result<(), SmtError> {
        loop {
            {
                let (entries, mut explainer) = self.explainer();
                while explainer.resolution.todo_justifications_head
                    < explainer.resolution.todo_justifications.len()
                {
                    let justification = explainer.resolution.todo_justifications
                        [explainer.resolution.todo_justifications_head];
                    explainer.resolution.todo_justifications_head += 1;
                    entries[justification as usize].get_antecedents(&mut explainer)?;
                }
            }
            while !self.conflict_resolution.todo_eqs.is_empty() {
                let second = self.conflict_resolution.todo_eqs.pop();
                let first = self.conflict_resolution.todo_eqs.pop();
                let (Some(first), Some(second)) = (first, second) else {
                    break;
                };
                let ancestor = self.find_common_ancestor(first, second);
                let mut explainer = self.explainer().1;
                explainer.eq_branch_to_literals(first, ancestor);
                explainer.eq_branch_to_literals(second, ancestor);
            }
            let resolution = &self.conflict_resolution;
            if resolution.todo_justifications_head == resolution.todo_justifications.len() {
                return Ok(());
            }
        }
    }

    fn unmark_justifications(&mut self, old_head: usize) {
        let resolution = &mut self.conflict_resolution;
        for index in old_head..resolution.todo_justifications.len() {
            self.justification_arena
                .set_marked(resolution.todo_justifications[index], false);
        }
        resolution.todo_justifications.truncate(old_head);
        resolution.todo_justifications_head = old_head;
        resolution.todo_eqs.clear();
        resolution.processed_eqs.clear();
    }

    fn justification_to_literals_core(
        &mut self,
        justification: JustificationId,
    ) -> Result<Vec<Literal>, SmtError> {
        let saved = mem::take(&mut self.conflict_resolution.antecedents);
        self.mark_justification(justification);
        let result = self.process_justifications();
        let literals = mem::replace(&mut self.conflict_resolution.antecedents, saved);
        result.map(|()| literals)
    }

    pub fn justification_to_literals(
        &mut self,
        justification: JustificationId,
    ) -> Result<Vec<Literal>, SmtError> {
        let result = self.justification_to_literals_core(justification)?;
        self.unmark_justifications(0);
        Ok(result)
    }

    fn get_justification_max_level(
        &mut self,
        justification: JustificationId,
    ) -> Result<u32, SmtError> {
        let mut result = 0;
        for literal in self.justification_to_literals(justification)? {
            result = result.max(self.get_assign_level(literal));
        }
        Ok(result)
    }

    fn get_max_level(
        &mut self,
        consequent: Literal,
        justification: BJustification,
    ) -> Result<u32, SmtError> {
        let mut result = if consequent != FALSE_LITERAL {
            self.get_assign_level(consequent)
        } else {
            0
        };
        let clause = match justification {
            BJustification::Justification(justification) => {
                return Ok(result.max(self.get_justification_max_level(justification)?));
            }
            BJustification::BinClause(literal) => {
                return Ok(result.max(self.get_assign_level(literal)));
            }
            BJustification::Decision | BJustification::Axiom => return Ok(result),
            BJustification::Clause(clause) => clause,
        };
        let num_literals = self.clauses.get_num_literals(clause);
        let mut start = 0;
        if consequent != FALSE_LITERAL {
            if self.clauses.get_literal(clause, 0) == consequent {
                start = 1;
            } else {
                result = result.max(self.get_assign_level(self.clauses.get_literal(clause, 0)));
                start = 2;
            }
        }
        for index in start..num_literals {
            result = result.max(self.get_assign_level(self.clauses.get_literal(clause, index)));
        }
        if let Some(clause_justification) = self.clauses.get_justification(clause) {
            result = result.max(self.get_justification_max_level(clause_justification)?);
        }
        Ok(result)
    }

    fn process_antecedent(&mut self, antecedent: Literal, marks: &mut i32) {
        let bool_var = get_var(antecedent);
        let level = self.get_level(bool_var);
        if self.is_marked(bool_var) || level <= self.base_level {
            return;
        }
        self.set_mark(bool_var, true);
        self.inc_bvar_activity(bool_var);
        if level == self.conflict_resolution.conflict_level {
            *marks += 1;
        } else {
            self.conflict_resolution.lemma.push(negate(antecedent));
            self.conflict_resolution
                .lemma_atoms
                .push(&mut self.m, self.bool_var2expr[bool_var as usize]);
        }
    }

    fn process_justification(
        &mut self,
        justification: JustificationId,
        marks: &mut i32,
    ) -> Result<(), SmtError> {
        for literal in self.justification_to_literals_core(justification)? {
            self.process_antecedent(literal, marks);
        }
        Ok(())
    }

    fn get_assigned_literal(&self, index: isize) -> Result<Literal, SmtError> {
        usize::try_from(index)
            .ok()
            .and_then(|index| self.assigned_literals.get(index).copied())
            .ok_or_else(|| SmtError::Invariant("the conflict has no implication point".into()))
    }

    /// Returns false when the conflict is at the search level, so the problem is unsat.
    pub fn resolve(
        &mut self,
        conflict: BJustification,
        not_literal: Option<Literal>,
    ) -> Result<bool, SmtError> {
        self.conflict_resolution.lemma = Vec::new();
        self.conflict_resolution.lemma_atoms.reset(&mut self.m)?;
        let mut justification = conflict;
        let mut consequent = not_literal.map_or(FALSE_LITERAL, negate);
        self.conflict_resolution.conflict_level = self.get_max_level(consequent, justification)?;
        if self.conflict_resolution.conflict_level <= self.search_level {
            return Ok(false);
        }
        let mut index = self.assigned_literals.len() as isize - 1;
        while index > 0
            && self.get_assign_level(self.get_assigned_literal(index)?)
                > self.conflict_resolution.conflict_level
        {
            index -= 1;
        }
        // The first slot holds the negated first unique implication point, found below.
        self.conflict_resolution.lemma.push(FALSE_LITERAL);
        self.conflict_resolution.lemma_atoms.push(&mut self.m, -1);
        let mut marks = 0;
        if let Some(not_literal) = not_literal {
            self.process_antecedent(not_literal, &mut marks);
        }
        loop {
            match justification {
                BJustification::Justification(justification) => {
                    self.process_justification(justification, &mut marks)?;
                }
                BJustification::BinClause(literal) => self.process_antecedent(literal, &mut marks),
                BJustification::Decision | BJustification::Axiom => {}
                BJustification::Clause(clause) => {
                    if self.clauses.is_lemma(clause) {
                        self.clauses.inc_activity(clause);
                    }
                    let num_literals = self.clauses.get_num_literals(clause);
                    let mut start = 0;
                    if consequent != FALSE_LITERAL {
                        if self.clauses.get_literal(clause, 0) == consequent {
                            start = 1;
                        } else {
                            self.process_antecedent(
                                negate(self.clauses.get_literal(clause, 0)),
                                &mut marks,
                            );
                            start = 2;
                        }
                    }
                    for literal_index in start..num_literals {
                        self.process_antecedent(
                            negate(self.clauses.get_literal(clause, literal_index)),
                            &mut marks,
                        );
                    }
                    if let Some(clause_justification) = self.clauses.get_justification(clause) {
                        self.process_justification(clause_justification, &mut marks)?;
                    }
                }
            }
            while !self.is_marked(get_var(self.get_assigned_literal(index)?)) {
                index -= 1;
            }
            consequent = self.get_assigned_literal(index)?;
            let consequent_var = get_var(consequent);
            justification = self.justifications[consequent_var as usize];
            index -= 1;
            marks -= 1;
            self.set_mark(consequent_var, false);
            if marks <= 0 {
                break;
            }
        }
        self.conflict_resolution.lemma[0] = negate(consequent);
        self.conflict_resolution.lemma_atoms.set(
            &mut self.m,
            0,
            self.bool_var2expr[get_var(consequent) as usize],
        )?;
        self.finalize_resolve()?;
        Ok(true)
    }

    fn finalize_resolve(&mut self) -> Result<(), SmtError> {
        self.unmark_justifications(0);
        self.minimize_lemma()?;
        self.conflict_resolution.new_scope_level = self.search_level;
        self.conflict_resolution.lemma_iscope_level =
            self.get_intern_level(get_var(self.conflict_resolution.lemma[0]));
        for index in 1..self.conflict_resolution.lemma.len() {
            let bool_var = get_var(self.conflict_resolution.lemma[index]);
            self.set_mark(bool_var, false);
            let level = self.get_level(bool_var);
            let intern_level = self.get_intern_level(bool_var);
            let resolution = &mut self.conflict_resolution;
            resolution.new_scope_level = resolution.new_scope_level.max(level);
            resolution.lemma_iscope_level = resolution.lemma_iscope_level.max(intern_level);
        }
        Ok(())
    }

    fn process_antecedent_for_minimization(&mut self, antecedent: Literal) -> bool {
        let bool_var = get_var(antecedent);
        let level = self.get_level(bool_var);
        if self.is_marked(bool_var) || level <= self.base_level {
            return true;
        }
        if self.conflict_resolution.level_set & (1 << (level & 31)) == 0 {
            return false;
        }
        self.set_mark(bool_var, true);
        self.conflict_resolution.unmark.push(bool_var);
        self.conflict_resolution.minimization_stack.push(bool_var);
        true
    }

    fn process_justification_for_minimization(
        &mut self,
        justification: JustificationId,
    ) -> Result<bool, SmtError> {
        for literal in self.justification_to_literals_core(justification)? {
            if !self.process_antecedent_for_minimization(literal) {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn reset_unmark(&mut self, old_size: usize, old_head: usize) {
        for index in old_size..self.conflict_resolution.unmark.len() {
            self.set_mark(self.conflict_resolution.unmark[index], false);
        }
        self.conflict_resolution.unmark.truncate(old_size);
        self.unmark_justifications(old_head);
    }

    fn is_implied_by_marked(&mut self, literal: Literal) -> Result<bool, SmtError> {
        self.conflict_resolution.minimization_stack = vec![get_var(literal)];
        let old_size = self.conflict_resolution.unmark.len();
        let old_head = self.conflict_resolution.todo_justifications_head;
        while let Some(bool_var) = self.conflict_resolution.minimization_stack.pop() {
            let mut is_implied = true;
            match self.justifications[bool_var as usize] {
                BJustification::Justification(justification) => {
                    is_implied = self.process_justification_for_minimization(justification)?;
                }
                BJustification::BinClause(literal) => {
                    is_implied = self.process_antecedent_for_minimization(literal);
                }
                BJustification::Decision | BJustification::Axiom => {
                    is_implied = self.get_level(bool_var) <= self.base_level;
                }
                BJustification::Clause(clause) => {
                    let num_literals = self.clauses.get_num_literals(clause);
                    let position = if get_var(self.clauses.get_literal(clause, 1)) == bool_var {
                        1
                    } else {
                        0
                    };
                    let mut index = 0;
                    while index < num_literals && is_implied {
                        if index != position {
                            is_implied = self.process_antecedent_for_minimization(negate(
                                self.clauses.get_literal(clause, index),
                            ));
                        }
                        index += 1;
                    }
                    if is_implied
                        && let Some(clause_justification) = self.clauses.get_justification(clause)
                    {
                        is_implied =
                            self.process_justification_for_minimization(clause_justification)?;
                    }
                }
            }
            if !is_implied {
                self.reset_unmark(old_size, old_head);
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn minimize_lemma(&mut self) -> Result<(), SmtError> {
        self.conflict_resolution.unmark = Vec::new();
        self.conflict_resolution.level_set = 0;
        for index in 0..self.conflict_resolution.lemma.len() {
            let level = self.get_level(get_var(self.conflict_resolution.lemma[index]));
            self.conflict_resolution.level_set |= 1 << (level & 31);
        }
        let mut kept = 1;
        for index in 1..self.conflict_resolution.lemma.len() {
            let literal = self.conflict_resolution.lemma[index];
            if self.is_implied_by_marked(literal)? {
                self.conflict_resolution.unmark.push(get_var(literal));
            } else {
                self.conflict_resolution.lemma[kept] = literal;
                if kept != index {
                    let atom = self.conflict_resolution.lemma_atoms.items[index];
                    self.conflict_resolution
                        .lemma_atoms
                        .set(&mut self.m, kept, atom)?;
                }
                kept += 1;
            }
        }
        self.reset_unmark(0, 0);
        self.conflict_resolution.lemma.truncate(kept);
        self.conflict_resolution
            .lemma_atoms
            .shrink(&mut self.m, kept)?;
        Ok(())
    }
}
