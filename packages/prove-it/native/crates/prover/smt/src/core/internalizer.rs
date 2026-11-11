//! Ported from Z3 (src/smt/smt_context.h, src/smt/smt_internalizer.cpp), MIT license, see
//! z3-license.txt, through `internalizer.ts`. The state of the SMT kernel and the translation of
//! formulas into it: Boolean variables, enodes, clauses and relevancy watches. The search lives in
//! `context.rs`, whose `Context` holds the fields of both TypeScript classes; this module is the
//! internalizer's methods.

use std::collections::HashMap;
use std::mem;

use crate::core::ast::{
    Decl, Expr, FAMILY_ARITH, FAMILY_BASIC, FAMILY_USER, KIND_APP, KIND_QUANTIFIER, OP_AND, OP_EQ,
    OP_IMPLIES, OP_ITE, OP_NOT, OP_OR, OP_XOR, SORT_BOOL, is_arith_sort,
};
use crate::core::cg_table::{CgTable, get_congruence_justification, is_congruent};
use crate::core::clause::{
    BJustification, CLS_AUX, CLS_LEARNED, CLS_TH_AXIOM, CLS_TH_LEMMA, Clause, DelEh,
};
use crate::core::context::{Context, NewEq, TrailClosure, next_random_value};
use crate::core::enode::{
    AXIOM_EQ_JUSTIFICATION, EnodeId, Enodes, EqJustification, Justification, JustificationId,
};
use crate::core::literal::{
    BoolVar, FALSE_LITERAL, Literal, TRUE_LITERAL, get_var, is_negated, mk_literal, negate,
};
use crate::core::relevancy::{RelevancyHandler, RelevancyPropagator};
use crate::core::sort::sort_numbers;
use crate::util::error::SmtError;
use crate::util::lbool::LBool;

/// DEEP_EXPR_THRESHOLD: the depth above which internalize_deep sorts an expression's subterms.
const DEEP_EXPR_THRESHOLD: i32 = 1024;
const WHITE: u8 = 0;
const GREY: u8 = 1;
const BLACK: u8 = 2;

// The kinds of undo trail entries. Z3 allocates its trail objects in a region. Here an entry is
// its kind on trail_kinds, with its operands on trail_nodes and trail_ints, so recording one
// allocates nothing. push_trail's closures are one more kind.
const UNDO_CLOSURE: u8 = 0;
const UNDO_MK_BOOL_VAR: u8 = 1;
const UNDO_MK_ENODE: u8 = 2;
const UNDO_VAR_THEORY: u8 = 3;
const UNDO_TRUE_FIRST: u8 = 4;
const UNDO_CGC_GENERATIONS: u8 = 5;
const UNDO_MERGE_TF: u8 = 6;
const UNDO_ENODE_FLAG: u8 = 7;
pub const UNDO_ADD_EQ: u8 = 8;
pub const UNDO_TH_VAR: u8 = 9;

// The first word of bool_var_data: the level of the assignment in the low 24 bits, then m_mark,
// m_phase_available, m_phase, m_eq, m_true_first, m_enode, m_quantifier and whether a theory is
// notified.
const LEVEL_MASK: u32 = 0xff_ffff;
const BV_MARK: u32 = 1 << 24;
pub const BV_PHASE_AVAILABLE: u32 = 1 << 25;
pub const BV_PHASE: u32 = 1 << 26;
pub const BV_EQ: u32 = 1 << 27;
pub const BV_TRUE_FIRST: u32 = 1 << 28;
pub const BV_ENODE: u32 = 1 << 29;
pub const BV_QUANTIFIER: u32 = 1 << 30;
pub const BV_THEORY: u32 = 1 << 31;

/// `array[index] = value` on a JavaScript array whose index is at most its length.
fn set_at<T: Clone>(values: &mut Vec<T>, index: usize, value: T, fill: T) {
    if index >= values.len() {
        values.resize(index + 1, fill);
    }
    values[index] = value;
}

/// get_cg_root: a node's cg can be stale, so a node that is not a congruence root looks the root
/// up.
fn get_cg_root(enodes: &Enodes, cg_table: &CgTable, node: EnodeId) -> EnodeId {
    if !enodes.uses_cg_table(node) || enodes.is_cgr(node) {
        return node;
    }
    cg_table.find_congruent(enodes, node).unwrap_or(node)
}

fn set_generation(enodes: &mut Enodes, cg_table: &CgTable, node: EnodeId, generation: u32) {
    if !enodes.get(node).is_eq() {
        let root = get_cg_root(enodes, cg_table, node);
        enodes.get_mut(root).generation = generation;
    }
}

fn to_b_justification(justification: Option<JustificationId>) -> BJustification {
    justification.map_or(BJustification::Axiom, BJustification::Justification)
}

impl Context {
    pub fn set_conflict(&mut self, justification: BJustification, not_literal: Option<Literal>) {
        if self.conflict.is_some() {
            return;
        }
        self.conflict = Some(crate::core::context::Conflict {
            justification,
            not_literal,
        });
    }

    pub fn push_eq(&mut self, lhs: EnodeId, rhs: EnodeId, justification: EqJustification) {
        self.eq_propagation_queue.push(NewEq {
            lhs,
            rhs,
            justification,
        });
    }

    /// random_gen from Z3's util/util.h with the default seed 0.
    pub fn get_random_value(&mut self) -> u32 {
        next_random_value(&mut self.random_seed)
    }

    pub fn push_trail(&mut self, undo: TrailClosure) {
        self.trail_closures.push(undo);
        self.trail_kinds.push(UNDO_CLOSURE);
    }

    pub(crate) fn pop_trail(&mut self, limit: usize) -> Result<(), SmtError> {
        for index in (limit..self.trail_kinds.len()).rev() {
            self.undo_trail_entry(self.trail_kinds[index])?;
        }
        self.trail_kinds.truncate(limit);
        Ok(())
    }

    fn pop_trail_node(&mut self) -> Result<EnodeId, SmtError> {
        self.trail_nodes
            .pop()
            .ok_or_else(|| SmtError::Invariant("the trail has no node".into()))
    }

    fn pop_trail_int(&mut self) -> Result<u32, SmtError> {
        self.trail_ints
            .pop()
            .ok_or_else(|| SmtError::Invariant("the trail has no number".into()))
    }

    fn undo_trail_entry(&mut self, kind: u8) -> Result<(), SmtError> {
        match kind {
            UNDO_CLOSURE => {
                if let Some(closure) = self.trail_closures.pop() {
                    self.undo_trail_closure(closure);
                }
            }
            UNDO_MK_BOOL_VAR => self.undo_mk_bool_var()?,
            UNDO_MK_ENODE => self.undo_mk_enode()?,
            UNDO_VAR_THEORY => {
                let bool_var = self.pop_trail_int()?;
                self.set_bool_var_flag(bool_var, BV_THEORY, false);
            }
            UNDO_TRUE_FIRST => {
                let bool_var = self.pop_trail_int()?;
                self.set_bool_var_flag(bool_var, BV_TRUE_FIRST, false);
            }
            UNDO_CGC_GENERATIONS => {
                let second = self.pop_trail_node()?;
                let first = self.pop_trail_node()?;
                let second_generation = self.pop_trail_int()?;
                let first_generation = self.pop_trail_int()?;
                self.undo_merge_cgc_generations(first, first_generation, second, second_generation);
            }
            UNDO_MERGE_TF => {
                let node = self.pop_trail_node()?;
                self.node_mut(node).set_is_merge_tf(false);
            }
            UNDO_ENODE_FLAG => {
                let bool_var = self.pop_trail_int()?;
                self.set_bool_var_flag(bool_var, BV_ENODE, false);
            }
            // context.ts's undoTrailEntry.
            UNDO_ADD_EQ => {
                let n1 = self.pop_trail_node()?;
                let r1 = self.pop_trail_node()?;
                let r2_num_parents = self.pop_trail_int()?;
                self.undo_add_eq(r1, n1, r2_num_parents as usize);
            }
            UNDO_TH_VAR => {
                let node = self.pop_trail_node()?;
                let th_var = self.pop_trail_int()? as i32;
                self.node_mut(node).th_var = -1;
                let root = self.root(node);
                if root != node && self.node(root).th_var == th_var {
                    self.node_mut(root).th_var = -1;
                }
            }
            _ => {}
        }
        Ok(())
    }

    // Assignment queries.

    pub fn get_assignment(&self, literal: Literal) -> LBool {
        self.assignment[literal as usize]
    }

    pub fn get_bool_var_assignment(&self, bool_var: BoolVar) -> LBool {
        self.assignment[mk_literal(bool_var, false) as usize]
    }

    pub fn get_assign_level(&self, literal: Literal) -> u32 {
        self.get_level(get_var(literal))
    }

    pub fn is_b_internalized(&self, expr: Expr) -> bool {
        self.find_bool_var(expr).is_some()
    }

    pub fn find_bool_var(&self, expr: Expr) -> Option<BoolVar> {
        match self.expr_to_bool_var.get(expr as usize) {
            Some(bool_var) if *bool_var != -1 => Some(*bool_var as BoolVar),
            _ => None,
        }
    }

    pub(crate) fn set_expr_bool_var(&mut self, expr: Expr, bool_var: i32) {
        if expr as usize >= self.expr_to_bool_var.len() {
            let length = (2 * self.expr_to_bool_var.len()).max(expr as usize + 1);
            self.expr_to_bool_var.resize(length, -1);
        }
        self.expr_to_bool_var[expr as usize] = bool_var;
    }

    pub fn get_bool_var(&self, expr: Expr) -> Result<BoolVar, SmtError> {
        self.find_bool_var(expr)
            .ok_or_else(|| SmtError::Invariant("the formula has no Boolean variable".into()))
    }

    pub fn get_enode(&self, expr: Expr) -> Option<EnodeId> {
        self.expr_to_enode.get(expr as usize).copied().flatten()
    }

    pub fn is_e_internalized(&self, expr: Expr) -> bool {
        self.get_enode(expr).is_some()
    }

    pub fn find_congruent(&self, decl: Decl, args: &[EnodeId]) -> Option<EnodeId> {
        self.cg_table
            .find_for(&self.enode_arena, decl, args, decl == OP_EQ)
    }

    /// is_diseq_core: the roots are distinct values, or an equality between the two classes is
    /// false. The congruence table is searched with m_is_diseq_tmp, an equality of the sort, which
    /// holds a reference until an equality of another sort replaces it.
    pub fn is_diseq(&mut self, first: EnodeId, second: EnodeId) -> Result<bool, SmtError> {
        let first_owner = self.node(first).owner;
        let second_owner = self.node(second).owner;
        if self.m.are_distinct(
            self.node(self.root(first)).owner,
            self.node(self.root(second)).owner,
        ) {
            return Ok(true);
        }
        let tmp = self.is_diseq_tmp;
        if tmp == -1
            || self.m.sorts[self.m.get_arg(tmp, 0) as usize] != self.m.sorts[first_owner as usize]
        {
            if tmp != -1 {
                self.m.dec_ref(tmp)?;
            }
            self.is_diseq_tmp = self.m.mk_eq(first_owner, second_owner)?;
            self.m.inc_ref(self.is_diseq_tmp);
        }
        let Some(found) = self
            .cg_table
            .find_for(&self.enode_arena, OP_EQ, &[first, second], true)
        else {
            return Ok(false);
        };
        let root = self.root(found);
        if root == self.true_enode {
            return Ok(false);
        }
        let root_owner = self.node(root).owner;
        Ok(root == self.false_enode
            || (self.is_relevant(root_owner)
                && self.get_assignment_of_expr(root_owner)? == LBool::False))
    }

    pub fn enodes_of(&self, decl: Decl) -> &[EnodeId] {
        self.decl2enodes.get(&decl).map_or(&[], Vec::as_slice)
    }

    pub fn get_literal(&self, expr: Expr) -> Result<Literal, SmtError> {
        if self.m.is_not(expr) {
            return Ok(negate(self.get_literal(self.m.get_arg(expr, 0))?));
        }
        if expr == self.m.true_expr {
            return Ok(TRUE_LITERAL);
        }
        if expr == self.m.false_expr {
            return Ok(FALSE_LITERAL);
        }
        Ok(mk_literal(self.get_bool_var(expr)?, false))
    }

    fn get_assignment_of_expr(&self, expr: Expr) -> Result<LBool, SmtError> {
        Ok(self.assignment[mk_literal(self.get_bool_var(expr)?, false) as usize])
    }

    /// The value of an expression, or its negation's negated, or of true and false.
    pub fn find_assignment(&self, expr: Expr) -> LBool {
        let m = &self.m;
        let value_of = |bool_var: BoolVar| self.assignment[mk_literal(bool_var, false) as usize];
        if m.is_not(expr) {
            let arg = m.get_arg(expr, 0);
            if let Some(bool_var) = self.find_bool_var(arg) {
                return !value_of(bool_var);
            }
            if arg == m.false_expr {
                return LBool::True;
            }
            if arg == m.true_expr {
                return LBool::False;
            }
            return LBool::Undef;
        }
        // get_assignment(expr) answers false for false before it reads the Boolean variable that
        // false shares with true (smt_context.cpp:1646-1648).
        if expr == m.false_expr {
            return LBool::False;
        }
        if let Some(bool_var) = self.find_bool_var(expr) {
            return value_of(bool_var);
        }
        if expr == m.true_expr {
            return LBool::True;
        }
        LBool::Undef
    }

    pub fn enode_to_literal(&self, node: EnodeId) -> Result<Literal, SmtError> {
        let bool_var = self.get_bool_var(self.node(node).owner)?;
        Ok(mk_literal(
            bool_var,
            self.assignment[mk_literal(bool_var, false) as usize] == LBool::False,
        ))
    }

    pub fn is_relevant(&self, expr: Expr) -> bool {
        self.relevancy.is_relevant(expr)
    }

    /// context::mark_as_relevant, which propagates the relevancy at once.
    pub fn mark_as_relevant(&mut self, expr: Expr) -> Result<(), SmtError> {
        RelevancyPropagator::mark_as_relevant(self, expr)?;
        RelevancyPropagator::propagate(self)
    }

    pub fn mark_literal_as_relevant(&mut self, literal: Literal) -> Result<(), SmtError> {
        self.mark_as_relevant(self.bool_var2expr[get_var(literal) as usize])
    }

    pub fn is_inconsistent(&self) -> bool {
        self.conflict.is_some()
    }

    /// get_generation: the generation of the congruence root. Equalities have generation 0, since
    /// patterns have no equalities.
    pub fn get_generation(&self, node: EnodeId) -> u32 {
        if self.node(node).is_eq() {
            return 0;
        }
        self.node(get_cg_root(&self.enode_arena, &self.cg_table, node))
            .generation
    }

    fn undo_merge_cgc_generations(
        &mut self,
        first: EnodeId,
        first_generation: u32,
        second: EnodeId,
        second_generation: u32,
    ) {
        set_generation(
            &mut self.enode_arena,
            &self.cg_table,
            first,
            first_generation,
        );
        set_generation(
            &mut self.enode_arena,
            &self.cg_table,
            second,
            second_generation,
        );
        // apply_sticky_updates: a lowered generation outlives the merge that it was made under.
        // Only the updates of the two nodes' declarations can be congruent to them, and a node
        // with an update uses the congruence table, so it has arguments and is no equality.
        self.apply_sticky_updates(first, first_generation, Some(second), second_generation);
        if self.node(second).decl != self.node(first).decl {
            self.apply_sticky_updates(second, second_generation, None, 0);
        }
    }

    fn apply_sticky_updates(
        &mut self,
        first: EnodeId,
        first_generation: u32,
        second: Option<EnodeId>,
        second_generation: u32,
    ) {
        let enodes = &mut self.enode_arena;
        let first_decl = enodes.get(first).decl;
        let Some(group) = self.sticky_generations.get_group(first_decl) else {
            return;
        };
        let first_root = enodes.get_arg_root(first, 0);
        let second_root = second
            .filter(|second| enodes.get(*second).decl == first_decl)
            .map(|second| enodes.get_arg_root(second, 0));
        for index in 0..group.nodes.len() {
            let Some(node) = group.nodes[index] else {
                continue;
            };
            let generation = group.generations[index];
            let root = enodes.get_arg_root(node, 0);
            if generation < first_generation
                && root == first_root
                && is_congruent(enodes, node, first)
            {
                set_generation(enodes, &self.cg_table, first, generation);
            } else if let Some(second) = second
                && generation < second_generation
                && Some(root) == second_root
                && is_congruent(enodes, node, second)
            {
                set_generation(enodes, &self.cg_table, second, generation);
            }
        }
    }

    // Boolean variables and enodes.

    /// mk_bool_var: m_b_internalized_stack holds a reference to the expression until the variable
    /// is deleted.
    pub fn mk_bool_var(&mut self, expr: Expr) -> BoolVar {
        let bool_var = self.num_bool_vars;
        self.num_bool_vars += 1;
        let literal = mk_literal(bool_var, false);
        self.m.inc_ref(expr);
        self.set_expr_bool_var(expr, bool_var as i32);
        set_at(&mut self.bool_var2expr, bool_var as usize, expr, -1);
        if 2 * bool_var as usize + 1 >= self.bool_var_data.len() {
            let length = 2 * self.bool_var_data.len();
            self.bool_var_data.resize(length, 0);
        }
        self.bool_var_data[2 * bool_var as usize] = 0;
        self.bool_var_data[2 * bool_var as usize + 1] = self.scope_level;
        set_at(
            &mut self.justifications,
            bool_var as usize,
            BJustification::Decision,
            BJustification::Decision,
        );
        let activity = if self.is_searching {
            -(f64::from(self.get_random_value() % 1000) / 1000.0)
        } else {
            0.0
        };
        set_at(&mut self.activity, bool_var as usize, activity, 0.0);
        set_at(
            &mut self.assignment,
            literal as usize,
            LBool::Undef,
            LBool::Undef,
        );
        set_at(
            &mut self.assignment,
            literal as usize + 1,
            LBool::Undef,
            LBool::Undef,
        );
        self.reset_watches(literal);
        self.reset_watches(literal + 1);
        let (queue, view) = self.split_case_split_queue();
        queue.mk_var(&view, bool_var);
        self.trail_kinds.push(UNDO_MK_BOOL_VAR);
        bool_var
    }

    /// The arrays keep the deleted variable's entries, which mk_bool_var overwrites.
    fn undo_mk_bool_var(&mut self) -> Result<(), SmtError> {
        self.num_bool_vars -= 1;
        let bool_var = self.num_bool_vars;
        let expr = self.bool_var2expr[bool_var as usize];
        let (queue, view) = self.split_case_split_queue();
        queue.del_var(&view, bool_var);
        if self.has_bool_var_flag(bool_var, BV_QUANTIFIER) {
            self.qmanager.del(expr);
        }
        self.expr_to_bool_var[expr as usize] = -1;
        self.justifications[bool_var as usize] = BJustification::Decision;
        self.m.dec_ref(expr)
    }

    /// The level of the variable's assignment.
    pub fn get_level(&self, bool_var: BoolVar) -> u32 {
        self.bool_var_data[2 * bool_var as usize] & LEVEL_MASK
    }

    pub(crate) fn set_level(&mut self, bool_var: BoolVar, level: u32) {
        let index = 2 * bool_var as usize;
        self.bool_var_data[index] = (self.bool_var_data[index] & !LEVEL_MASK) | level;
    }

    /// The scope level at which the variable was internalized.
    pub fn get_intern_level(&self, bool_var: BoolVar) -> u32 {
        self.bool_var_data[2 * bool_var as usize + 1]
    }

    pub(crate) fn has_bool_var_flag(&self, bool_var: BoolVar, flag: u32) -> bool {
        self.bool_var_data[2 * bool_var as usize] & flag != 0
    }

    pub(crate) fn set_bool_var_flag(&mut self, bool_var: BoolVar, flag: u32, value: bool) {
        let index = 2 * bool_var as usize;
        self.bool_var_data[index] = if value {
            self.bool_var_data[index] | flag
        } else {
            self.bool_var_data[index] & !flag
        };
    }

    pub fn is_marked(&self, bool_var: BoolVar) -> bool {
        self.has_bool_var_flag(bool_var, BV_MARK)
    }

    pub fn set_mark(&mut self, bool_var: BoolVar, value: bool) {
        self.set_bool_var_flag(bool_var, BV_MARK, value);
    }

    /// watch_list::reset: a new variable's lists keep the room of a deleted one's.
    fn reset_watches(&mut self, literal: Literal) {
        let index = literal as usize;
        if index >= self.watches.len() {
            self.watches.resize_with(index + 1, Vec::new);
        }
        self.watches[index].clear();
        if index >= self.binary_watches.len() {
            self.binary_watches.resize_with(index + 1, Vec::new);
        }
        self.binary_watches[index].clear();
    }

    pub(crate) fn is_atom(&self, bool_var: BoolVar) -> bool {
        self.has_bool_var_flag(bool_var, BV_EQ | BV_ENODE | BV_THEORY | BV_QUANTIFIER)
    }

    pub fn set_var_theory(&mut self, bool_var: BoolVar) {
        if self.scope_level > self.get_intern_level(bool_var) {
            self.trail_ints.push(bool_var);
            self.trail_kinds.push(UNDO_VAR_THEORY);
        }
        self.set_bool_var_flag(bool_var, BV_THEORY, true);
    }

    pub fn set_true_first_flag(&mut self, bool_var: BoolVar) {
        self.trail_ints.push(bool_var);
        self.trail_kinds.push(UNDO_TRUE_FIRST);
        self.set_bool_var_flag(bool_var, BV_TRUE_FIRST, true);
    }

    pub fn is_true_first(&self, bool_var: BoolVar) -> bool {
        self.has_bool_var_flag(bool_var, BV_TRUE_FIRST)
    }

    pub fn mk_enode(
        &mut self,
        expr: Expr,
        is_suppressing_args: bool,
        is_merge_tf: bool,
        is_cgc_enabled: bool,
    ) -> Result<EnodeId, SmtError> {
        let generation = self
            .cached_generation
            .get(&expr)
            .copied()
            .unwrap_or(self.generation);
        let num_args = if is_suppressing_args {
            0
        } else {
            self.m.get_num_args(expr)
        };
        let mut more_args = Vec::new();
        for index in 2..num_args {
            more_args.push(self.get_arg_enode(expr, index)?);
        }
        let is_eq = !is_suppressing_args && self.m.get_op(expr) == OP_EQ;
        let arg0 = if num_args > 0 {
            Some(self.get_arg_enode(expr, 0)?)
        } else {
            None
        };
        let arg1 = if num_args > 1 {
            Some(self.get_arg_enode(expr, 1)?)
        } else {
            None
        };
        let node = self.enode_arena.mk(
            expr,
            self.m.decls[expr as usize],
            num_args as u32,
            arg0,
            arg1,
            more_args,
            generation,
            is_eq,
            self.m.sorts[expr as usize] == SORT_BOOL,
            is_merge_tf,
            is_cgc_enabled,
            self.scope_level,
        );
        for index in 0..num_args as u32 {
            let root = self.enode_arena.get_arg_root(node, index);
            self.node_mut(root).set_is_shared(None);
            self.node_mut(root).add_parent(node);
        }
        if self.m.is_unique_value(expr) {
            self.node_mut(node).set_is_interpreted(true);
        }
        set_at(&mut self.expr_to_enode, expr as usize, Some(node), None);
        // m_e_internalized_stack holds a reference to the expression until the enode is deleted.
        self.m.inc_ref(expr);
        self.trail_kinds.push(UNDO_MK_ENODE);
        self.enodes.push(node);
        if num_args > 0 {
            if self.enode_arena.is_true_eq(node) {
                let literal = mk_literal(self.get_bool_var(expr)?, false);
                let justification = self.justification_arena.mk(Justification::EqPropagation {
                    first: self.node(node).get_arg(0),
                    second: self.node(node).get_arg(1),
                });
                self.assign(literal, BJustification::Justification(justification), false);
                self.push_eq(node, self.true_enode, AXIOM_EQ_JUSTIFICATION);
            } else if is_cgc_enabled {
                let congruent = self.cg_table.insert(&self.enode_arena, node);
                if congruent != node {
                    self.node_mut(node).cg = congruent;
                    if !is_eq {
                        self.merge_cgc_generations(node, generation, congruent);
                    }
                    let justification =
                        get_congruence_justification(&self.enode_arena, node, congruent);
                    self.push_eq(node, congruent, justification);
                }
            }
            if !is_eq {
                let decl = self.node(node).decl;
                self.decl2enodes.entry(decl).or_default().push(node);
            }
        }
        Ok(node)
    }

    /// The enode of an argument of expr, which is internalized before expr.
    fn get_arg_enode(&self, expr: Expr, index: usize) -> Result<EnodeId, SmtError> {
        self.get_enode(self.m.get_arg(expr, index))
            .ok_or_else(|| SmtError::Invariant("an argument was not internalized".into()))
    }

    fn undo_mk_enode(&mut self) -> Result<(), SmtError> {
        let Some(node) = self.enodes.pop() else {
            return Ok(());
        };
        let owner = self.node(node).owner;
        self.expr_to_enode[owner as usize] = None;
        if self.enode_arena.is_cgr(node) && self.enode_arena.uses_cg_table(node) {
            self.cg_table.erase(&self.enode_arena, node);
        }
        let num_args = self.node(node).num_args();
        if num_args > 0
            && !self.node(node).is_eq()
            && let Some(list) = self.decl2enodes.get_mut(&self.enode_arena.get(node).decl)
        {
            list.pop();
        }
        for index in 0..num_args {
            let root = self.enode_arena.get_arg_root(node, index);
            self.node_mut(root).parents.pop();
        }
        self.m.dec_ref(owner)?;
        self.sticky_generations.delete(&self.enode_arena, node);
        Ok(())
    }

    pub(crate) fn merge_cgc_generations(
        &mut self,
        first: EnodeId,
        first_generation: u32,
        second: EnodeId,
    ) {
        self.trail_ints.push(first_generation);
        self.trail_ints.push(self.node(second).generation);
        self.trail_nodes.push(first);
        self.trail_nodes.push(second);
        self.trail_kinds.push(UNDO_CGC_GENERATIONS);
        if first_generation < self.node(second).generation {
            self.node_mut(second).generation = first_generation;
        }
    }

    fn set_merge_tf(&mut self, node: EnodeId, bool_var: BoolVar, is_new_var: bool) {
        if self.node(node).is_merge_tf() {
            return;
        }
        if !is_new_var {
            self.trail_nodes.push(node);
            self.trail_kinds.push(UNDO_MERGE_TF);
        }
        self.node_mut(node).set_is_merge_tf(true);
        let value = self.assignment[mk_literal(bool_var, false) as usize];
        if value == LBool::True && self.root(node) != self.root(self.true_enode) {
            self.push_eq(
                node,
                self.true_enode,
                EqJustification::Equation {
                    literal: mk_literal(bool_var, false),
                },
            );
        } else if value == LBool::False && self.root(node) != self.root(self.false_enode) {
            self.push_eq(
                node,
                self.false_enode,
                EqJustification::Equation {
                    literal: mk_literal(bool_var, true),
                },
            );
        }
    }

    fn set_enode_flag(&mut self, bool_var: BoolVar, is_new_var: bool) {
        if self.has_bool_var_flag(bool_var, BV_ENODE) {
            return;
        }
        if !is_new_var {
            self.trail_ints.push(bool_var);
            self.trail_kinds.push(UNDO_ENODE_FLAG);
        }
        self.set_bool_var_flag(bool_var, BV_ENODE, true);
    }

    /// update_generation: a node of a congruence class records its lower generation as sticky, so
    /// undoing a merge of the class keeps it.
    fn update_generation(&mut self, node: EnodeId) {
        if self.node(node).is_eq() {
            return;
        }
        if self.generation > 0 && self.generation < self.get_generation(node) {
            set_generation(&mut self.enode_arena, &self.cg_table, node, self.generation);
            if self.enode_arena.uses_cg_table(node) {
                self.sticky_generations
                    .set(&self.enode_arena, node, self.generation);
            }
        }
    }

    // Internalization.

    fn is_gate(&self, expr: Expr) -> bool {
        let op = self.m.get_op(expr);
        if op == OP_AND || op == OP_OR || op == OP_ITE {
            return true;
        }
        op == OP_EQ && self.m.is_bool(self.m.get_arg(expr, 0))
    }

    /// should_internalize_rec: a term, or a Boolean application of the basic family or an
    /// uninterpreted declaration.
    fn should_internalize_rec(&self, expr: Expr) -> bool {
        if self.m.kinds[expr as usize] != KIND_APP || self.m.sorts[expr as usize] != SORT_BOOL {
            return true;
        }
        let family = self.m.get_family(expr);
        family == FAMILY_BASIC || family == FAMILY_USER
    }

    /// internalize_deep: internalizes the subterms of a deep expression bottom up, in the order of
    /// a topological sort, so the recursion of internalize_rec stays shallow.
    fn internalize_deep(&mut self, expr: Expr) -> Result<(), SmtError> {
        if self.is_e_internalized(expr)
            || self.m.depths[expr as usize] <= DEEP_EXPR_THRESHOLD
            || !self.should_internalize_rec(expr)
        {
            return Ok(());
        }
        // The color of each expression in a gate context and outside one: white while unvisited,
        // grey while its children are visited, and black once it is sorted.
        let mut colors: HashMap<(Expr, bool), u8> = HashMap::new();
        let mut todo = vec![(expr, true)];
        let mut sorted = Vec::new();
        while let Some(&top) = todo.last() {
            let color = colors.get(&top).copied().unwrap_or(WHITE);
            if color == BLACK {
                todo.pop();
            } else if color == WHITE {
                colors.insert(top, GREY);
                self.visit_children(top.0, &mut todo, &colors);
            } else {
                colors.insert(top, BLACK);
                if top.0 != expr && !self.m.is_not(top.0) && self.should_internalize_rec(top.0) {
                    sorted.push(top);
                }
            }
        }
        for entry in sorted {
            self.internalize_rec(entry.0, entry.1)?;
        }
        Ok(())
    }

    /// ts_visit_children, which Z3 calls again on grey expressions only in its assertions.
    fn visit_children(
        &mut self,
        current: Expr,
        todo: &mut Vec<(Expr, bool)>,
        colors: &HashMap<(Expr, bool), u8>,
    ) {
        let mut visit_child = |child: Expr, is_gate: bool| {
            if colors.get(&(child, is_gate)).copied().unwrap_or(WHITE) == WHITE {
                todo.push((child, is_gate));
            }
        };
        if self.m.kinds[current as usize] == KIND_QUANTIFIER
            || !self.should_internalize_rec(current)
        {
            return;
        }
        let node = self.get_enode(current);
        if let Some(node) = node {
            self.update_generation(node);
        }
        let is_bool = self.m.sorts[current as usize] == SORT_BOOL;
        if if is_bool {
            self.is_b_internalized(current)
        } else {
            node.is_some()
        } {
            return;
        }
        if self.m.get_op(current) == OP_ITE && !is_bool {
            visit_child(self.m.get_arg(current, 0), true);
            visit_child(self.m.get_arg(current, 1), false);
            visit_child(self.m.get_arg(current, 2), false);
            return;
        }
        let is_new_gate = is_bool && (self.is_gate(current) || self.m.is_not(current));
        for index in (0..self.m.get_num_args(current)).rev() {
            visit_child(self.m.get_arg(current, index), is_new_gate);
        }
    }

    pub fn internalize_assertion(&mut self, expr: Expr, generation: u32) -> Result<(), SmtError> {
        let saved_generation = self.generation;
        self.generation = generation;
        self.internalize_deep(expr)?;
        if self.is_gate(expr) {
            match self.m.get_op(expr) {
                OP_AND => {
                    for index in 0..self.m.get_num_args(expr) {
                        let arg = self.m.get_arg(expr, index);
                        self.internalize_rec(arg, true)?;
                        self.mk_clause(&mut vec![self.get_literal(arg)?], None, CLS_AUX, None)?;
                    }
                }
                OP_OR => {
                    for index in 0..self.m.get_num_args(expr) {
                        let arg = self.m.get_arg(expr, index);
                        self.internalize_rec(arg, true)?;
                    }
                    let mut literals = Vec::new();
                    for index in 0..self.m.get_num_args(expr) {
                        literals.push(self.get_literal(self.m.get_arg(expr, index))?);
                    }
                    self.mk_clause(&mut literals, None, CLS_AUX, None)?;
                    self.add_or_rel_watches(expr)?;
                }
                OP_EQ => {
                    self.internalize_rec(self.m.get_arg(expr, 0), true)?;
                    self.internalize_rec(self.m.get_arg(expr, 1), true)?;
                    let first = self.get_literal(self.m.get_arg(expr, 0))?;
                    let second = self.get_literal(self.m.get_arg(expr, 1))?;
                    self.mk_clause(&mut vec![first, negate(second)], None, CLS_AUX, None)?;
                    self.mk_clause(&mut vec![negate(first), second], None, CLS_AUX, None)?;
                }
                _ => {
                    for index in 0..self.m.get_num_args(expr) {
                        let arg = self.m.get_arg(expr, index);
                        self.internalize_rec(arg, true)?;
                    }
                    let condition = self.get_literal(self.m.get_arg(expr, 0))?;
                    let then_literal = self.get_literal(self.m.get_arg(expr, 1))?;
                    self.mk_clause(
                        &mut vec![negate(condition), then_literal],
                        None,
                        CLS_AUX,
                        None,
                    )?;
                    let else_literal = self.get_literal(self.m.get_arg(expr, 2))?;
                    self.mk_clause(&mut vec![condition, else_literal], None, CLS_AUX, None)?;
                    self.add_ite_rel_watches(expr)?;
                }
            }
            self.mark_as_relevant(expr)?;
        } else {
            self.internalize_rec(expr, true)?;
            let literal = self.get_literal(expr)?;
            if literal == FALSE_LITERAL {
                self.set_conflict(BJustification::Axiom, None);
            } else if literal != TRUE_LITERAL {
                self.assign(literal, BJustification::Axiom, false);
                self.mark_literal_as_relevant(literal)?;
            }
        }
        self.generation = saved_generation;
        Ok(())
    }

    /// internalize with the context's generation.
    pub fn internalize(&mut self, expr: Expr, is_gate_context: bool) -> Result<(), SmtError> {
        self.internalize_with_generation(expr, is_gate_context, self.generation)
    }

    pub fn internalize_with_generation(
        &mut self,
        expr: Expr,
        is_gate_context: bool,
        generation: u32,
    ) -> Result<(), SmtError> {
        let saved_generation = self.generation;
        self.generation = generation;
        self.internalize_deep(expr)?;
        self.internalize_rec(expr, is_gate_context)?;
        self.generation = saved_generation;
        Ok(())
    }

    fn internalize_rec(&mut self, expr: Expr, is_gate_context: bool) -> Result<(), SmtError> {
        if self.m.sorts[expr as usize] == SORT_BOOL {
            self.internalize_formula(expr, is_gate_context)
        } else {
            self.internalize_term(expr)
        }
    }

    fn internalize_formula(&mut self, expr: Expr, is_gate_context: bool) -> Result<(), SmtError> {
        if expr == self.m.true_expr || expr == self.m.false_expr {
            return Ok(());
        }
        if self.m.is_not(expr) && is_gate_context {
            return self.internalize_rec(self.m.get_arg(expr, 0), true);
        }
        if let Some(bool_var) = self.find_bool_var(expr) {
            let node = self.get_enode(expr);
            if let Some(node) = node {
                self.update_generation(node);
            }
            if !is_gate_context && self.m.kinds[expr as usize] == KIND_APP {
                if let Some(node) = node {
                    self.set_merge_tf(node, bool_var, false);
                } else {
                    self.mk_enode(expr, true, true, false)?;
                    self.set_enode_flag(bool_var, false);
                    if self.assignment[mk_literal(bool_var, false) as usize] != LBool::Undef {
                        self.propagate_bool_var_enode(bool_var)?;
                    }
                }
            }
            return Ok(());
        }
        let op = self.m.get_op(expr);
        let kind = self.m.kinds[expr as usize];
        if op == OP_EQ && !self.m.is_bool(self.m.get_arg(expr, 0)) {
            self.internalize_eq(expr, is_gate_context)
        } else if kind == KIND_APP && self.internalize_theory_atom(expr, is_gate_context)? {
            Ok(())
        } else if kind == KIND_QUANTIFIER {
            self.internalize_quantifier(expr)
        } else {
            self.internalize_formula_core(expr, is_gate_context)
        }
    }

    fn internalize_eq(&mut self, expr: Expr, is_gate_context: bool) -> Result<(), SmtError> {
        self.internalize_formula_core(expr, is_gate_context)?;
        let bool_var = self.get_bool_var(expr)?;
        self.set_bool_var_flag(bool_var, BV_EQ, true);
        if self.m.sorts[self.m.get_arg(expr, 0) as usize] != SORT_BOOL && self.is_arith_sort(expr) {
            self.theory_internalize_eq_eh(expr)?;
        }
        Ok(())
    }

    fn is_arith_sort(&self, eq: Expr) -> bool {
        is_arith_sort(self.m.sorts[self.m.get_arg(eq, 0) as usize])
    }

    fn internalize_theory_atom(
        &mut self,
        expr: Expr,
        is_gate_context: bool,
    ) -> Result<bool, SmtError> {
        if self.m.get_family(expr) != FAMILY_ARITH || !self.theory_internalize_atom(expr)? {
            return Ok(false);
        }
        let bool_var = self.get_bool_var(expr)?;
        if !is_gate_context {
            match self.get_enode(expr) {
                None => {
                    self.mk_enode(expr, true, true, false)?;
                }
                Some(node) => {
                    self.set_enode_flag(bool_var, true);
                    self.set_merge_tf(node, bool_var, true);
                }
            }
        }
        if self.get_enode(expr).is_some() {
            self.set_enode_flag(bool_var, true);
            if self.assignment[mk_literal(bool_var, false) as usize] != LBool::Undef {
                self.propagate_bool_var_enode(bool_var)?;
            }
        }
        Ok(true)
    }

    fn internalize_quantifier(&mut self, expr: Expr) -> Result<(), SmtError> {
        let bool_var = self.mk_bool_var(expr);
        let generation = self
            .cached_generation
            .get(&expr)
            .copied()
            .unwrap_or(self.generation);
        self.set_bool_var_flag(bool_var, BV_QUANTIFIER, true);
        self.qmanager_add(expr, generation)
    }

    pub(crate) fn internalize_formula_core(
        &mut self,
        expr: Expr,
        is_gate_context: bool,
    ) -> Result<(), SmtError> {
        let op = self.m.get_op(expr);
        let is_gate_node = self.is_gate(expr) || op == OP_NOT;
        for index in 0..self.m.get_num_args(expr) {
            let arg = self.m.get_arg(expr, index);
            self.internalize_rec(arg, is_gate_node)?;
        }
        let is_new_var = !self.is_b_internalized(expr);
        let bool_var = if is_new_var {
            self.mk_bool_var(expr)
        } else {
            self.get_bool_var(expr)?
        };
        let node = self.get_enode(expr);
        if node.is_none() && (!is_gate_context || (!is_gate_node && self.m.get_num_args(expr) > 0))
        {
            self.mk_enode(expr, is_gate_node, !is_gate_context, true)?;
            self.set_enode_flag(bool_var, is_new_var);
        } else if let Some(node) = node
            && !is_gate_context
        {
            self.set_merge_tf(node, bool_var, is_new_var);
        }
        if !is_new_var || self.m.get_family(expr) != FAMILY_BASIC {
            return Ok(());
        }
        let literal = mk_literal(bool_var, false);
        match op {
            OP_NOT => {
                let child = self.get_literal(self.m.get_arg(expr, 0))?;
                self.mk_gate_clause(negate(literal), negate(child), None)?;
                self.mk_gate_clause(literal, child, None)?;
            }
            OP_AND => {
                let mut buffer = mem::take(&mut self.gate_buffer);
                buffer.clear();
                buffer.push(literal);
                let result = self.mk_and_cnstr(expr, literal, &mut buffer);
                self.gate_buffer = buffer;
                result?;
                self.add_and_rel_watches(expr)?;
            }
            OP_OR => {
                let mut buffer = mem::take(&mut self.gate_buffer);
                buffer.clear();
                buffer.push(negate(literal));
                let result = self.mk_or_cnstr(expr, literal, &mut buffer);
                self.gate_buffer = buffer;
                result?;
                self.add_or_rel_watches(expr)?;
            }
            OP_IMPLIES => {
                let first = self.get_literal(self.m.get_arg(expr, 0))?;
                let second = self.get_literal(self.m.get_arg(expr, 1))?;
                self.mk_gate_clause(literal, first, None)?;
                self.mk_gate_clause(literal, negate(second), None)?;
                self.mk_gate_clause(negate(literal), negate(first), Some(second))?;
            }
            OP_EQ | OP_XOR => {
                if op == OP_EQ && !self.m.is_bool(self.m.get_arg(expr, 0)) {
                    return Ok(());
                }
                let gate = if op == OP_XOR {
                    negate(literal)
                } else {
                    literal
                };
                let first = self.get_literal(self.m.get_arg(expr, 0))?;
                let second = self.get_literal(self.m.get_arg(expr, 1))?;
                self.mk_gate_clause(negate(gate), first, Some(negate(second)))?;
                self.mk_gate_clause(negate(gate), negate(first), Some(second))?;
                self.mk_gate_clause(gate, first, Some(second))?;
                self.mk_gate_clause(gate, negate(first), Some(negate(second)))?;
            }
            OP_ITE => {
                let condition = self.get_literal(self.m.get_arg(expr, 0))?;
                let then_literal = self.get_literal(self.m.get_arg(expr, 1))?;
                let else_literal = self.get_literal(self.m.get_arg(expr, 2))?;
                self.mk_gate_clause(negate(literal), negate(condition), Some(then_literal))?;
                self.mk_gate_clause(negate(literal), condition, Some(else_literal))?;
                self.mk_gate_clause(literal, negate(condition), Some(negate(then_literal)))?;
                self.mk_gate_clause(literal, condition, Some(negate(else_literal)))?;
                self.add_ite_rel_watches(expr)?;
            }
            _ => {}
        }
        Ok(())
    }

    /// The clauses of mk_and_cnstr, with the literal_buffer the context reuses.
    fn mk_and_cnstr(
        &mut self,
        expr: Expr,
        literal: Literal,
        buffer: &mut Vec<Literal>,
    ) -> Result<(), SmtError> {
        for index in 0..self.m.get_num_args(expr) {
            let arg = self.m.get_arg(expr, index);
            let arg_literal = self.get_literal(arg)?;
            self.mk_gate_clause(negate(literal), arg_literal, None)?;
            buffer.push(negate(arg_literal));
        }
        self.mk_clause(buffer, None, CLS_AUX, None)?;
        Ok(())
    }

    /// The clauses of mk_or_cnstr, with the literal_buffer the context reuses.
    fn mk_or_cnstr(
        &mut self,
        expr: Expr,
        literal: Literal,
        buffer: &mut Vec<Literal>,
    ) -> Result<(), SmtError> {
        for index in 0..self.m.get_num_args(expr) {
            let arg = self.m.get_arg(expr, index);
            let arg_literal = self.get_literal(arg)?;
            self.mk_gate_clause(literal, negate(arg_literal), None)?;
            buffer.push(arg_literal);
        }
        self.mk_clause(buffer, None, CLS_AUX, None)?;
        Ok(())
    }

    /// mk_gate_clause with two or three literals.
    fn mk_gate_clause(
        &mut self,
        first: Literal,
        second: Literal,
        third: Option<Literal>,
    ) -> Result<(), SmtError> {
        let mut literals = mem::take(&mut self.gate_literals);
        literals.clear();
        literals.push(first);
        literals.push(second);
        if let Some(third) = third {
            literals.push(third);
        }
        let result = self.mk_clause(&mut literals, None, CLS_AUX, None);
        self.gate_literals = literals;
        result.map(|_| ())
    }

    pub fn internalize_term(&mut self, expr: Expr) -> Result<(), SmtError> {
        if let Some(existing) = self.get_enode(expr) {
            self.update_generation(existing);
            // The theory may have made a nested term, such as the 2 of (* 2 x), without a
            // variable, which it needs once the term occurs elsewhere.
            if self.m.get_family(expr) == FAMILY_ARITH && !self.theory_is_attached_to_var(existing)
            {
                self.theory_internalize_term(expr)?;
            }
            return Ok(());
        }
        if self.m.get_op(expr) == OP_ITE {
            return self.internalize_ite_term(expr);
        }
        if self.m.get_family(expr) == FAMILY_ARITH && self.theory_internalize_term(expr)? {
            return Ok(());
        }
        for index in 0..self.m.get_num_args(expr) {
            let arg = self.m.get_arg(expr, index);
            self.internalize_rec(arg, false)?;
        }
        if self.get_enode(expr).is_some() {
            return Ok(());
        }
        self.mk_enode(expr, false, false, true)?;
        Ok(())
    }

    /// mk_eq_atom: the side with the smaller id goes first.
    pub fn mk_eq_atom(&mut self, lhs: Expr, rhs: Expr) -> Result<Expr, SmtError> {
        if self.m.ids[lhs as usize] < self.m.ids[rhs as usize] {
            self.m.mk_eq(lhs, rhs)
        } else {
            self.m.mk_eq(rhs, lhs)
        }
    }

    fn internalize_ite_term(&mut self, expr: Expr) -> Result<(), SmtError> {
        let then_eq = self.mk_eq_atom(expr, self.m.get_arg(expr, 1))?;
        let else_eq = self.mk_eq_atom(expr, self.m.get_arg(expr, 2))?;
        self.mk_enode(expr, true, false, false)?;
        self.internalize_rec(self.m.get_arg(expr, 0), true)?;
        self.internalize_rec(self.m.get_arg(expr, 1), false)?;
        self.internalize_rec(self.m.get_arg(expr, 2), false)?;
        self.internalize_rec(then_eq, true)?;
        self.internalize_rec(else_eq, true)?;
        let condition = self.get_literal(self.m.get_arg(expr, 0))?;
        self.mk_clause(
            &mut vec![negate(condition), self.get_literal(then_eq)?],
            None,
            CLS_AUX,
            None,
        )?;
        self.mk_clause(
            &mut vec![condition, self.get_literal(else_eq)?],
            None,
            CLS_AUX,
            None,
        )?;
        // ite_term_relevancy_eh: it marks the terms for the propagator, which propagates them
        // later.
        let handler = RelevancyHandler::IteTerm {
            expr,
            then_eq,
            else_eq,
        };
        self.add_rel_watch(condition, handler)?;
        self.add_rel_watch(negate(condition), handler)?;
        RelevancyPropagator::add_handler(self, expr, handler)
    }

    fn add_rel_watch(
        &mut self,
        literal: Literal,
        handler: RelevancyHandler,
    ) -> Result<(), SmtError> {
        let expr = self.bool_var2expr[get_var(literal) as usize];
        RelevancyPropagator::add_watch(self, expr, !is_negated(literal), handler)
    }

    fn add_and_rel_watches(&mut self, expr: Expr) -> Result<(), SmtError> {
        let handler = RelevancyHandler::And { expr };
        for index in 0..self.m.get_num_args(expr) {
            let literal = self.get_literal(self.m.get_arg(expr, index))?;
            if literal > 1 {
                self.add_rel_watch(negate(literal), handler)?;
            }
        }
        Ok(())
    }

    fn add_or_rel_watches(&mut self, expr: Expr) -> Result<(), SmtError> {
        let handler = RelevancyHandler::Or { expr };
        for index in 0..self.m.get_num_args(expr) {
            let literal = self.get_literal(self.m.get_arg(expr, index))?;
            if literal > 1 {
                self.add_rel_watch(literal, handler)?;
            }
        }
        Ok(())
    }

    fn add_ite_rel_watches(&mut self, expr: Expr) -> Result<(), SmtError> {
        let handler = RelevancyHandler::Ite { expr };
        let literal = self.get_literal(self.m.get_arg(expr, 0))?;
        if literal <= 1 {
            return Ok(());
        }
        self.add_rel_watch(literal, handler)?;
        self.add_rel_watch(negate(literal), handler)
    }

    // Clauses.

    pub fn mk_th_axiom(&mut self, literals: &mut Vec<Literal>) -> Result<(), SmtError> {
        self.mk_clause(literals, None, CLS_TH_AXIOM, None)?;
        Ok(())
    }

    fn simplify_aux_clause_literals(
        &self,
        literals: &mut Vec<Literal>,
        removed: &mut Vec<Literal>,
    ) -> bool {
        sort_numbers(literals);
        let mut previous: Option<Literal> = None;
        let mut kept = 0;
        for index in 0..literals.len() {
            let literal = literals[index];
            let value = self.assignment[literal as usize];
            if value == LBool::False {
                if Some(literal) != previous {
                    previous = Some(literal);
                    removed.push(negate(literal));
                }
            } else if value == LBool::Undef {
                if previous.is_some_and(|previous| literal == negate(previous)) {
                    return false;
                }
                if Some(literal) != previous {
                    previous = Some(literal);
                    literals[kept] = literal;
                    kept += 1;
                }
            } else {
                return false;
            }
        }
        literals.truncate(kept);
        true
    }

    /// simplify_aux_lemma_literals: unlike an aux clause, a theory lemma keeps its false literals,
    /// so it needs no unit resolution justification.
    fn simplify_aux_lemma_literals(&self, literals: &mut Vec<Literal>) -> bool {
        sort_numbers(literals);
        let mut previous: Option<Literal> = None;
        let mut kept = 0;
        for index in 0..literals.len() {
            let literal = literals[index];
            if self.get_level(get_var(literal)) <= self.base_level
                && self.assignment[literal as usize] == LBool::True
            {
                return false;
            }
            if previous.is_some_and(|previous| literal == negate(previous)) {
                return false;
            }
            if Some(literal) != previous {
                previous = Some(literal);
                literals[kept] = literal;
                kept += 1;
            }
        }
        literals.truncate(kept);
        true
    }

    pub(crate) fn select_watch_literal(&self, clause: Clause, starting_at: u32) -> u32 {
        let clauses = &self.clauses;
        let mut min_true: Option<u32> = None;
        let mut max_false: Option<u32> = None;
        let mut unknown: Option<u32> = None;
        for index in starting_at..clauses.get_num_literals(clause) {
            let literal = clauses.get_literal(clause, index);
            let value = self.assignment[literal as usize];
            let level = self.get_level(get_var(literal));
            if value == LBool::False {
                if max_false.is_none_or(|max_false| {
                    level > self.get_level(get_var(clauses.get_literal(clause, max_false)))
                }) {
                    max_false = Some(index);
                }
            } else if value == LBool::Undef {
                unknown = Some(index);
            } else if min_true.is_none_or(|min_true| {
                level < self.get_level(get_var(clauses.get_literal(clause, min_true)))
            }) {
                min_true = Some(index);
            }
        }
        min_true.or(unknown).or(max_false).unwrap_or(starting_at)
    }

    fn select_learned_watch_literal(&self, clause: Clause) -> u32 {
        let clauses = &self.clauses;
        let mut max_false: Option<u32> = None;
        let mut max_level = 0;
        for index in 1..clauses.get_num_literals(clause) {
            let literal = clauses.get_literal(clause, index);
            let level = if self.assignment[literal as usize] == LBool::False {
                self.get_level(get_var(literal))
            } else {
                self.scope_level
            };
            if max_false.is_none() || level > max_level {
                max_false = Some(index);
                max_level = level;
            }
        }
        max_false.unwrap_or(1)
    }

    pub(crate) fn add_watch_literal(&mut self, clause: Clause, index: u32) {
        self.add_watch(negate(self.clauses.get_literal(clause, index)), clause);
    }

    pub(crate) fn add_watch(&mut self, literal: Literal, clause: Clause) {
        if literal as usize >= self.watches.len() {
            self.watches.resize_with(literal as usize + 1, Vec::new);
        }
        self.watches[literal as usize].push(clause);
    }

    pub(crate) fn remove_watch_literal(&mut self, clause: Clause, index: u32) {
        let literal = negate(self.clauses.get_literal(clause, index));
        let Some(list) = self.watches.get_mut(literal as usize) else {
            return;
        };
        // A clause is deleted when its scope is popped, so it is most often near the end.
        if let Some(position) = list.iter().rposition(|watched| *watched == clause) {
            list.remove(position);
        }
    }

    /// A binary justification holds only its literal.
    pub(crate) fn get_bin_justification(&self, literal: Literal) -> BJustification {
        BJustification::BinClause(literal)
    }

    /// use_binary_clause_opt: a clause of two literals at the base level of the first scope, over
    /// variables created there, becomes a pair of binary watches. With relevancy, lemmas stay
    /// clauses so their propagations can mark literals as relevant.
    fn is_using_binary_clause_opt(&self, first: Literal, second: Literal, is_lemma: bool) -> bool {
        if is_lemma && self.relevancy.is_enabled {
            return false;
        }
        if self.base_level > 0 {
            return false;
        }
        if !is_lemma && self.scope_level > 0 {
            return false;
        }
        self.get_intern_level(get_var(first)) == 0 && self.get_intern_level(get_var(second)) == 0
    }

    fn get_max_iscope_level(&self, literals: &[Literal]) -> u32 {
        literals
            .iter()
            .map(|literal| self.get_intern_level(get_var(*literal)))
            .fold(0, u32::max)
    }

    fn mark_for_reinit(&mut self, clause: Clause, level: u32, is_reinternalizing_atoms: bool) {
        self.clauses.set_reinit(clause, true);
        self.clauses
            .set_reinternalize_atoms(clause, is_reinternalizing_atoms);
        while self.clauses_to_reinit.len() <= level as usize {
            self.clauses_to_reinit.push(Vec::new());
        }
        self.clauses_to_reinit[level as usize].push(clause);
    }

    /// mk_clause: like Z3's, it simplifies the literals in the array it is given.
    pub fn mk_clause(
        &mut self,
        literals: &mut Vec<Literal>,
        input_justification: Option<JustificationId>,
        kind: u32,
        del_eh: Option<DelEh>,
    ) -> Result<Option<Clause>, SmtError> {
        let mut justification = input_justification;
        if kind == CLS_TH_LEMMA {
            if !self.simplify_aux_lemma_literals(literals) {
                return Ok(None);
            }
        } else if kind != CLS_LEARNED {
            let mut removed = mem::take(&mut self.removed_literals);
            removed.clear();
            let is_kept = self.simplify_aux_clause_literals(literals, &mut removed);
            if is_kept && !removed.is_empty() {
                justification = Some(self.justification_arena.mk(Justification::UnitResolution {
                    justification,
                    literals: removed.clone(),
                }));
            }
            self.removed_literals = removed;
            if !is_kept {
                return Ok(None);
            }
        }
        if literals.is_empty() {
            self.set_conflict(to_b_justification(justification), None);
            return Ok(None);
        }
        if literals.len() == 1 {
            self.assign(literals[0], to_b_justification(justification), false);
            return Ok(None);
        }
        let is_lemma = kind == CLS_LEARNED || kind == CLS_TH_LEMMA;
        if literals.len() == 2
            && self.is_using_binary_clause_opt(literals[0], literals[1], is_lemma)
        {
            let first = literals[0];
            let second = literals[1];
            for (watched, propagated) in [(negate(first), second), (negate(second), first)] {
                if watched as usize >= self.binary_watches.len() {
                    self.binary_watches
                        .resize_with(watched as usize + 1, Vec::new);
                }
                self.binary_watches[watched as usize].push(propagated);
            }
            if self.assignment[first as usize] == LBool::False {
                let justification = self.get_bin_justification(negate(first));
                self.assign(second, justification, false);
            } else if self.assignment[second as usize] == LBool::False {
                let justification = self.get_bin_justification(negate(second));
                self.assign(first, justification, false);
            }
            return Ok(None);
        }
        let iscope_level = if is_lemma {
            self.get_max_iscope_level(literals)
        } else {
            0
        };
        let is_saving_atoms = is_lemma && iscope_level > self.base_level;
        let atoms: Option<Vec<u32>> = is_saving_atoms.then(|| {
            literals
                .iter()
                .map(|literal| self.bool_var2expr[get_var(*literal) as usize] as u32)
                .collect()
        });
        for atom in atoms.iter().flatten() {
            self.m.inc_ref(*atom as Expr);
        }
        let clause = self
            .clauses
            .mk(literals, kind, justification, del_eh, atoms.as_deref());
        if is_lemma {
            if kind == CLS_LEARNED {
                let watch = self.select_learned_watch_literal(clause);
                self.clauses.swap_literals(clause, 1, watch);
            } else {
                let first_watch = self.select_watch_literal(clause, 0);
                self.clauses.swap_literals(clause, 0, first_watch);
                let second_watch = self.select_watch_literal(clause, 1);
                self.clauses.swap_literals(clause, 1, second_watch);
            }
            self.lemmas.push(clause);
            self.add_watch_literal(clause, 0);
            self.add_watch_literal(clause, 1);
            let first = self.clauses.get_literal(clause, 0);
            let second = self.clauses.get_literal(clause, 1);
            // A theory lemma that conflicts or propagates above the base level is checked again
            // when the level is backtracked.
            let is_propagating = self.assignment[first as usize] == LBool::False
                || self.assignment[second as usize] == LBool::False;
            if self.assignment[first as usize] == LBool::False {
                self.set_conflict(BJustification::Clause(clause), None);
            } else if self.assignment[second as usize] == LBool::False {
                self.assign(first, BJustification::Clause(clause), false);
            }
            let is_reinit =
                kind == CLS_TH_LEMMA && is_propagating && self.scope_level > self.base_level;
            if is_saving_atoms || is_reinit {
                let level = if is_reinit {
                    self.scope_level
                } else {
                    iscope_level
                };
                self.mark_for_reinit(clause, level, is_saving_atoms);
            }
            return Ok(Some(clause));
        }
        self.aux_clauses.push(clause);
        self.add_watch_literal(clause, 0);
        self.add_watch_literal(clause, 1);
        if self.assignment[literals[0] as usize] == LBool::False {
            self.set_conflict(BJustification::Clause(clause), None);
        } else if self.assignment[literals[1] as usize] == LBool::False {
            self.assign(literals[0], BJustification::Clause(clause), false);
        }
        Ok(Some(clause))
    }

    /// The deletion handlers a clause keeps, applied where the TypeScript calls them.
    fn apply_del_eh(&mut self, del_eh: DelEh) {
        match del_eh {
            DelEh::DynAckInstantiated { first, second } => self
                .dyn_ack
                .remove_instantiated(first as Expr, second as Expr),
        }
    }

    /// del_clause. A clause in the reinit stack is only marked deleted, and reinit_clauses frees
    /// it.
    pub(crate) fn delete_clause(&mut self, clause: Clause) -> Result<(), SmtError> {
        if self.clauses.is_deleted(clause) {
            return Ok(());
        }
        self.remove_watch_literal(clause, 0);
        self.remove_watch_literal(clause, 1);
        self.clauses.mark_as_deleted(clause);
        if let Some(del_eh) = self.clauses.get_del_eh(clause) {
            self.apply_del_eh(del_eh);
        }
        if self.clauses.is_reinternalize_atoms(clause) {
            self.release_atoms(clause)?;
        }
        if !self.clauses.is_reinit(clause) {
            self.clauses.free(clause);
        }
        Ok(())
    }

    /// release_atoms: the clause no longer holds its atoms.
    pub(crate) fn release_atoms(&mut self, clause: Clause) -> Result<(), SmtError> {
        for atom in self.clauses.get_atoms(clause) {
            self.m.dec_ref(atom as Expr)?;
        }
        self.clauses.clear_atoms(clause);
        Ok(())
    }

    /// del_clauses: past 1,000 clauses, mark each deleted, filter each of their watch lists once,
    /// then release their atoms, instead of searching a watch list per clause.
    pub(crate) fn delete_clauses(
        &mut self,
        clauses: &mut Vec<Clause>,
        old_size: usize,
    ) -> Result<(), SmtError> {
        if clauses.len() - old_size <= 1000 {
            for index in (old_size..clauses.len()).rev() {
                self.delete_clause(clauses[index])?;
            }
            clauses.truncate(old_size);
            return Ok(());
        }
        if self.watch_marks.len() < self.watches.len() {
            self.watch_marks = vec![0; (2 * self.watch_marks.len()).max(self.watches.len())];
        }
        let mut watched = Vec::new();
        for index in (old_size..clauses.len()).rev() {
            let clause = clauses[index];
            if !self.clauses.is_deleted(clause) {
                self.clauses.mark_as_deleted(clause);
                if let Some(del_eh) = self.clauses.get_del_eh(clause) {
                    self.apply_del_eh(del_eh);
                }
            }
            for position in 0..2 {
                let literal = negate(self.clauses.get_literal(clause, position));
                if self.watch_marks[literal as usize] == 1 {
                    continue;
                }
                self.watch_marks[literal as usize] = 1;
                watched.push(literal);
            }
        }
        for literal in watched {
            self.watch_marks[literal as usize] = 0;
            let store = &self.clauses;
            if let Some(list) = self.watches.get_mut(literal as usize) {
                list.retain(|clause| !store.is_deleted(*clause));
            }
        }
        for index in (old_size..clauses.len()).rev() {
            let clause = clauses[index];
            if self.clauses.is_reinternalize_atoms(clause) {
                self.release_atoms(clause)?;
            }
            if !self.clauses.is_reinit(clause) {
                self.clauses.free(clause);
            }
        }
        clauses.truncate(old_size);
        Ok(())
    }
}
