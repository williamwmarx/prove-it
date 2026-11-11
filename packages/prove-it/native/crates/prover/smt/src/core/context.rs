//! Ported from Z3 (src/smt/smt_context.cpp), MIT license, see z3-license.txt, through
//! `context.ts`. The SMT kernel's search: a CDCL loop over Boolean variables combined with an
//! E-graph for congruence closure, relevancy propagation, the arithmetic theory and quantifier
//! instantiation, with Z3's default parameters for UFNIA.
//!
//! `Context extends Internalizer` in the TypeScript: here one struct with the fields of both
//! classes, whose internalizer methods are in `internalizer.rs` (design/smt-core.md, "The
//! context"). The nodes and justifications are the arenas `enode_arena` and `justification_arena`,
//! and the classes that keep the context (`ConflictResolution`, `DynAckManager`,
//! `DefaultQuantifierManager`, `TheoryLra`) are fields whose methods that reach the context are
//! `impl Context` methods in their modules.

use std::collections::{HashMap, HashSet};
use std::mem;
use std::rc::Rc;

use crate::core::asserted_formulas::AssertedFormulas;
use crate::core::ast::{AstManager, Decl, Expr, FAMILY_ARITH, KIND_APP, KIND_QUANTIFIER, KIND_VAR};
use crate::core::case_split_queue::{CaseSplitContext, CaseSplitQueue};
use crate::core::cg_table::{CgTable, get_congruence_justification, is_congruent};
use crate::core::clause::{
    BJustification, CLS_LEARNED, CLS_TH_LEMMA, Clause, ClauseStore, HEADER_SIZE,
};
use crate::core::conflict_resolution::ConflictResolution;
use crate::core::dyn_ack::DynAckManager;
use crate::core::e_matching::MamClosure;
use crate::core::enode::{Enode, EnodeId, Enodes, EqJustification, Justification, Justifications};
use crate::core::internalizer::{
    BV_ENODE, BV_EQ, BV_PHASE, BV_PHASE_AVAILABLE, BV_QUANTIFIER, BV_THEORY, BV_TRUE_FIRST,
    UNDO_ADD_EQ, UNDO_TH_VAR,
};
use crate::core::literal::{
    BoolVar, Literal, TRUE_BOOL_VAR, get_var, is_negated, mk_literal, negate,
};
use crate::core::model_generator::{GeneratedModel, mk_model};
use crate::core::proto_model::ProtoModelRef;
use crate::core::quantifier_manager::DefaultQuantifierManager;
use crate::core::relevancy::{RelevancyContext, RelevancyHandler, RelevancyPropagator};
use crate::core::rewriter::{KERNEL_REWRITER_OPTIONS, Rewriter};
use crate::core::sticky_generations::StickyGenerations;
use crate::core::theory_lra::TheoryLra;
use crate::core::theory_lra_state::TheoryClosure;
use crate::util::error::SmtError;
use crate::util::lbool::LBool;

pub const FC_DONE: u8 = 0;
pub const FC_CONTINUE: u8 = 1;
pub const FC_GIVEUP: u8 = 2;

const ACTIVITY_LIMIT: f64 = 1e100;
const INV_ACTIVITY_LIMIT: f64 = 1e-100;
const INV_DECAY: f64 = 1.052;
const RESTART_INITIAL: u32 = 100;
const RESTART_FACTOR: f64 = 1.1;
// phase_caching_on and phase_caching_off: the numbers of conflicts while phase caching is on and
// off.
const PHASE_CACHING_ON: u32 = 400;
const PHASE_CACHING_OFF: u32 = 100;
const AGILITY_FACTOR: f64 = 0.9999;
// The LGC_FIXED lemma garbage collection: lemma_gc_initial conflicts between collections, and the
// activity and unassigned literal thresholds of del_inactive_lemmas2.
const LEMMA_GC_INITIAL: u32 = 5000;
// theory_lra::num_final_check_levels: level 2 also runs nlsat's full check.
const NUM_ARITH_FINAL_CHECK_LEVELS: u32 = 2;
const NEW_OLD_RATIO: usize = 16;
const OLD_CLAUSE_ACTIVITY: i32 = 500;
const NEW_CLAUSE_RELEVANCY: u32 = 45;
const OLD_CLAUSE_RELEVANCY: u32 = 6;
const RESTART_AGILITY_THRESHOLD: f64 = 0.18;

pub const CHECK_MODEL_SAT: u8 = 0;
pub const CHECK_MODEL_UNKNOWN: u8 = 1;
pub const CHECK_MODEL_RESTART: u8 = 2;

/// The reasons a search may stop without an answer that MBQI cares about.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum SearchFailure {
    Ok,
    Theory,
    Quantifiers,
    Canceled,
}

/// m_model_generator's model, m_proto_model and m_model. The model generator holds the last model
/// it made. From mk_proto_model to reset_model the context holds that model too as its proto
/// model, and get_model adds the model the proto model makes.
enum ModelState {
    None,
    Generated(Rc<GeneratedModel>),
    Proto(Rc<GeneratedModel>),
    Final {
        generated: Rc<GeneratedModel>,
        model: ProtoModelRef,
    },
}

/// smt_params: the kernel runs model-based quantifier instantiation with relevancy level 2 and the
/// CS_ACTIVITY_DELAY_NEW case split queue. The model checker's auxiliary context runs neither, as
/// Z3 sets its relevancy level to 0 and its case split strategy to CS_ACTIVITY.
#[derive(Clone, Copy, Debug)]
pub struct SmtParams {
    pub is_mbqi: bool,
    /// 0 or 2.
    pub relevancy_level: u32,
}

/// An equality the E-graph merges at the next propagation.
#[derive(Clone, Copy, Debug)]
pub(crate) struct NewEq {
    pub(crate) lhs: EnodeId,
    pub(crate) rhs: EnodeId,
    pub(crate) justification: EqJustification,
}

/// m_conflict and m_not_l: the justification of the conflict, and the literal it falsifies, if
/// any.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Conflict {
    pub(crate) justification: BJustification,
    pub(crate) not_literal: Option<Literal>,
}

/// The closures the TypeScript pushes with `pushTrail`, with what each captures, undone by
/// `undo_trail_closure`. A module that pushes another one adds its variant here.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TrailClosure {
    /// context.ts attachThVar: `() => { node.thVar = oldVar; }`.
    ThVar { node: EnodeId, old_var: i32 },
    /// quantifier-manager.ts finalCheckEh: `() => { this.lazyMatchingIndex = saved; }`.
    LazyMatchingIndex { saved: u32 },
    /// The closures of the matchers and their compilers (`e_matching.rs`).
    Mam(MamClosure),
    /// The closures of the arithmetic theory (`theory_lra_state.rs`).
    Theory(TheoryClosure),
}

/// The CaseSplitContext of `internalizer.ts`'s constructor, over the context's fields.
pub(crate) struct CaseSplitView<'a> {
    activity: &'a [f64],
    is_searching: bool,
    random_seed: &'a mut u32,
    num_bool_vars: u32,
    assignment: &'a [LBool],
}

/// random_gen from Z3's util/util.h with the default seed 0.
pub(crate) fn next_random_value(seed: &mut u32) -> u32 {
    *seed = seed.wrapping_mul(214013).wrapping_add(2531011);
    (*seed >> 16) & 0x7fff
}

impl CaseSplitContext for CaseSplitView<'_> {
    fn activity(&self) -> &[f64] {
        self.activity
    }

    fn get_is_searching(&self) -> bool {
        self.is_searching
    }

    fn get_random_value(&mut self) -> u32 {
        next_random_value(self.random_seed)
    }

    fn get_num_bool_vars(&self) -> u32 {
        self.num_bool_vars
    }

    fn is_unassigned(&self, bool_var: BoolVar) -> bool {
        self.assignment[mk_literal(bool_var, false) as usize] == LBool::Undef
    }
}

pub struct Context {
    // Internalizer's fields.
    pub m: AstManager,
    pub rewriter: Rewriter,
    pub relevancy: RelevancyPropagator,
    pub case_split_queue: CaseSplitQueue,
    pub cg_table: CgTable,
    pub(crate) sticky_generations: StickyGenerations,
    /// The nodes, which the TypeScript makes with `new Enode`. A slot is never reused, so a node
    /// that `undo_mk_enode` drops stays in the arena unreachable.
    pub enode_arena: Enodes,
    /// The justifications, which the TypeScript makes with `new …Justification`.
    pub justification_arena: Justifications,
    // Per Boolean variable. Like Z3's vectors, the arrays keep their size when a variable is
    // deleted. Only the first num_bool_vars entries are live.
    pub num_bool_vars: u32,
    pub bool_var2expr: Vec<Expr>,
    /// bool_var_data: two words per variable. The first holds the level of its assignment and the
    /// BV_ flags, the second the level of its internalization.
    pub(crate) bool_var_data: Vec<u32>,
    /// The reason of each variable's assignment; `Decision` (the TypeScript's `null`) while it is
    /// unassigned.
    pub justifications: Vec<BJustification>,
    pub activity: Vec<f64>,
    // Per literal.
    pub(crate) assignment: Vec<LBool>,
    pub clauses: ClauseStore,
    /// The watch lists of each literal. An empty list stands for the TypeScript's `undefined`.
    pub(crate) watches: Vec<Vec<Clause>>,
    /// del_clauses' uint_set of the watch lists to filter, by literal, all 0 between calls.
    pub(crate) watch_marks: Vec<u8>,
    /// The false literals that simplify_aux_clause_literals removes from the clause mk_clause
    /// makes.
    pub(crate) removed_literals: Vec<Literal>,
    /// The literal_buffer of mk_and_cnstr and mk_or_cnstr, and the array that mk_gate_clause keeps
    /// on the stack.
    pub(crate) gate_buffer: Vec<Literal>,
    pub(crate) gate_literals: Vec<Literal>,
    /// The binary clauses of the binary clause optimization: the literals each literal propagates
    /// when it becomes true, which Z3 visits newest first and before the clauses.
    pub(crate) binary_watches: Vec<Vec<Literal>>,
    // Per expression.
    /// The Boolean variable of each expression, or -1.
    pub(crate) expr_to_bool_var: Vec<i32>,
    pub(crate) expr_to_enode: Vec<Option<EnodeId>>,
    pub assigned_literals: Vec<Literal>,
    pub scope_level: u32,
    pub base_level: u32,
    pub search_level: u32,
    pub(crate) trail_kinds: Vec<u8>,
    pub(crate) trail_nodes: Vec<EnodeId>,
    pub(crate) trail_ints: Vec<u32>,
    pub(crate) trail_closures: Vec<TrailClosure>,
    pub(crate) aux_clauses: Vec<Clause>,
    pub(crate) lemmas: Vec<Clause>,
    pub(crate) clauses_to_reinit: Vec<Vec<Clause>>,
    pub(crate) conflict: Option<Conflict>,
    pub(crate) eq_propagation_queue: Vec<NewEq>,
    /// The context's live nodes, in the order they were made.
    pub enodes: Vec<EnodeId>,
    pub(crate) decl2enodes: HashMap<Decl, Vec<EnodeId>>,
    pub true_enode: EnodeId,
    pub(crate) is_diseq_tmp: Expr,
    pub false_enode: EnodeId,
    pub(crate) generation: u32,
    pub(crate) cached_generation: HashMap<Expr, u32>,
    pub(crate) random_seed: u32,
    pub is_searching: bool,
    // Context's fields.
    /// setup_context makes the theories after the first formulas are asserted, so the field starts
    /// unassigned.
    pub theory: Option<TheoryLra>,
    pub qmanager: DefaultQuantifierManager,
    pub conflict_resolution: ConflictResolution,
    pub(crate) dyn_ack: DynAckManager,
    qhead: usize,
    pub(crate) scope_assigned_limits: Vec<usize>,
    scope_aux_clause_limits: Vec<usize>,
    scope_trail_limits: Vec<usize>,
    /// The number of lemmas when each user scope began.
    base_scope_lemma_limits: Vec<usize>,
    pub(crate) atom_propagation_queue: Vec<Literal>,
    th_eq_queue: Vec<i32>,
    th_diseq_queue: Vec<i32>,
    pub(crate) bvar_inc: f64,
    agility: f64,
    num_conflicts: u32,
    num_conflicts_since_restart: u32,
    num_conflicts_since_lemma_gc: u32,
    restart_threshold: u32,
    restart_outer_threshold: u32,
    is_phase_cache_on: bool,
    phase_counter: u32,
    final_check_index: u32,
    r1_parent_generations: HashMap<EnodeId, u32>,
    erased_generations: HashMap<EnodeId, u32>,
    last_search_failure: SearchFailure,
    model_state: ModelState,
}

impl RelevancyContext for Context {
    fn relevancy(&self) -> &RelevancyPropagator {
        &self.relevancy
    }

    fn relevancy_mut(&mut self) -> &mut RelevancyPropagator {
        &mut self.relevancy
    }

    fn manager(&self) -> &AstManager {
        &self.m
    }

    fn manager_mut(&mut self) -> &mut AstManager {
        &mut self.m
    }

    fn find_assignment(&self, expr: Expr) -> LBool {
        Context::find_assignment(self, expr)
    }

    fn find_enode(&self, expr: Expr) -> Option<EnodeId> {
        self.get_enode(expr)
    }

    fn enodes(&self) -> &Enodes {
        &self.enode_arena
    }

    fn relevant_eh(&mut self, expr: Expr) -> Result<(), SmtError> {
        Context::relevant_eh(self, expr)
    }

    fn run_relevancy_handler(&mut self, handler: RelevancyHandler) -> Result<(), SmtError> {
        match handler {
            RelevancyHandler::IteTerm {
                expr,
                then_eq,
                else_eq,
            } => {
                if !self.is_relevant(expr) {
                    return Ok(());
                }
                let condition = self.m.get_arg(expr, 0);
                RelevancyPropagator::mark_as_relevant(self, condition)?;
                let value = Context::find_assignment(self, condition);
                if value == LBool::False {
                    RelevancyPropagator::mark_as_relevant(self, else_eq)?;
                } else if value == LBool::True {
                    RelevancyPropagator::mark_as_relevant(self, then_eq)?;
                }
                Ok(())
            }
            RelevancyHandler::And { expr } => {
                if self.is_relevant(expr) {
                    RelevancyPropagator::propagate_and(self, expr)?;
                }
                Ok(())
            }
            RelevancyHandler::Or { expr } => {
                if self.is_relevant(expr) {
                    RelevancyPropagator::propagate_or(self, expr)?;
                }
                Ok(())
            }
            RelevancyHandler::Ite { expr } => {
                if self.is_relevant(expr) {
                    RelevancyPropagator::propagate_ite(self, expr)?;
                }
                Ok(())
            }
            RelevancyHandler::MarkAsRelevant { target } => {
                RelevancyPropagator::mark_as_relevant(self, target)
            }
            RelevancyHandler::EqAxioms {
                first,
                second,
                eq,
                le,
                ge,
            } => {
                if !self.is_relevant(first) || !self.is_relevant(second) {
                    return Ok(());
                }
                RelevancyPropagator::mark_as_relevant(self, eq)?;
                RelevancyPropagator::mark_as_relevant(self, le)?;
                RelevancyPropagator::mark_as_relevant(self, ge)
            }
        }
    }
}

impl Context {
    pub fn new(mut m: AstManager, params: SmtParams) -> Result<Context, SmtError> {
        let is_relevancy_enabled = params.relevancy_level > 0;
        let is_delaying_new_case_splits = params.relevancy_level > 0;
        let rewriter = Rewriter::new(&m, KERNEL_REWRITER_OPTIONS, false);
        // The TypeScript makes the quantifier manager after the internalizer's constructor made
        // the variable and the nodes of true and false, which only count references, so it is the
        // same to make it first.
        let qmanager = DefaultQuantifierManager::new(&mut m, params.is_mbqi);
        let mut context = Context {
            m,
            rewriter,
            relevancy: RelevancyPropagator::new(is_relevancy_enabled),
            case_split_queue: CaseSplitQueue::new(is_delaying_new_case_splits),
            cg_table: CgTable::new(),
            sticky_generations: StickyGenerations::new(),
            enode_arena: Enodes::new(),
            justification_arena: Justifications::new(),
            num_bool_vars: 0,
            bool_var2expr: Vec::new(),
            bool_var_data: vec![0; 2048],
            justifications: Vec::new(),
            activity: Vec::new(),
            assignment: Vec::new(),
            clauses: ClauseStore::new(),
            watches: Vec::new(),
            watch_marks: vec![0; 1024],
            removed_literals: Vec::new(),
            gate_buffer: Vec::new(),
            gate_literals: Vec::new(),
            binary_watches: Vec::new(),
            expr_to_bool_var: vec![-1; 1024],
            expr_to_enode: Vec::new(),
            assigned_literals: Vec::new(),
            scope_level: 0,
            base_level: 0,
            search_level: 0,
            trail_kinds: Vec::new(),
            trail_nodes: Vec::new(),
            trail_ints: Vec::new(),
            trail_closures: Vec::new(),
            aux_clauses: Vec::new(),
            lemmas: Vec::new(),
            clauses_to_reinit: Vec::new(),
            conflict: None,
            eq_propagation_queue: Vec::new(),
            enodes: Vec::new(),
            decl2enodes: HashMap::new(),
            true_enode: 0,
            is_diseq_tmp: -1,
            false_enode: 0,
            generation: 0,
            cached_generation: HashMap::new(),
            random_seed: 0,
            is_searching: false,
            theory: None,
            qmanager,
            conflict_resolution: ConflictResolution::new(),
            dyn_ack: DynAckManager::new(),
            qhead: 0,
            scope_assigned_limits: Vec::new(),
            scope_aux_clause_limits: Vec::new(),
            scope_trail_limits: Vec::new(),
            base_scope_lemma_limits: Vec::new(),
            atom_propagation_queue: Vec::new(),
            th_eq_queue: Vec::new(),
            th_diseq_queue: Vec::new(),
            bvar_inc: 1.0,
            agility: 0.0,
            num_conflicts: 0,
            num_conflicts_since_restart: 0,
            num_conflicts_since_lemma_gc: 0,
            restart_threshold: RESTART_INITIAL,
            restart_outer_threshold: RESTART_INITIAL,
            is_phase_cache_on: true,
            phase_counter: 0,
            final_check_index: 0,
            r1_parent_generations: HashMap::new(),
            erased_generations: HashMap::new(),
            last_search_failure: SearchFailure::Ok,
            model_state: ModelState::None,
        };
        let true_expr = context.m.true_expr;
        let false_expr = context.m.false_expr;
        context.mk_bool_var(true_expr);
        context.assignment[0] = LBool::True;
        context.assignment[1] = LBool::False;
        context.justifications[0] = BJustification::Axiom;
        context.true_enode = context.mk_enode(true_expr, true, true, false)?;
        context.set_expr_bool_var(false_expr, TRUE_BOOL_VAR as i32);
        context.false_enode = context.mk_enode(false_expr, true, true, false)?;
        Ok(context)
    }

    pub(crate) fn node(&self, node: EnodeId) -> &Enode {
        self.enode_arena.get(node)
    }

    pub(crate) fn node_mut(&mut self, node: EnodeId) -> &mut Enode {
        self.enode_arena.get_mut(node)
    }

    pub(crate) fn root(&self, node: EnodeId) -> EnodeId {
        self.enode_arena.get(node).root
    }

    /// The case split queue and the view of the context it reads.
    pub(crate) fn split_case_split_queue(&mut self) -> (&mut CaseSplitQueue, CaseSplitView<'_>) {
        (
            &mut self.case_split_queue,
            CaseSplitView {
                activity: &self.activity,
                is_searching: self.is_searching,
                random_seed: &mut self.random_seed,
                num_bool_vars: self.num_bool_vars,
                assignment: &self.assignment,
            },
        )
    }

    /// register_plugin initializes each theory it registers.
    pub fn setup_context(&mut self) -> Result<(), SmtError> {
        self.theory = Some(TheoryLra::new(&mut self.m));
        self.theory_init()
    }

    /// The search stops with unknown when the manager's resource limit cancels it.
    pub fn check_canceled(&self) -> bool {
        !self.m.limit.inc()
    }

    pub(crate) fn undo_trail_closure(&mut self, closure: TrailClosure) {
        match closure {
            TrailClosure::ThVar { node, old_var } => self.node_mut(node).th_var = old_var,
            TrailClosure::LazyMatchingIndex { saved } => self.qmanager.lazy_matching_index = saved,
            TrailClosure::Mam(closure) => self.mam_undo_closure(closure),
            TrailClosure::Theory(closure) => self.lra_undo_closure(closure),
        }
    }

    // Assignment and propagation.

    pub fn assign(&mut self, literal: Literal, justification: BJustification, is_decision: bool) {
        let value = self.assignment[literal as usize];
        if value == LBool::False {
            self.set_conflict(justification, Some(negate(literal)));
        } else if value == LBool::Undef {
            self.assign_core(literal, justification, is_decision);
        }
    }

    fn assign_core(&mut self, literal: Literal, justification: BJustification, is_decision: bool) {
        let bool_var = get_var(literal);
        self.assigned_literals.push(literal);
        self.assignment[literal as usize] = LBool::True;
        self.assignment[negate(literal) as usize] = LBool::False;
        self.justifications[bool_var as usize] = justification;
        self.set_level(bool_var, self.scope_level);
        let is_negative = is_negated(literal);
        if self.has_bool_var_flag(bool_var, BV_PHASE_AVAILABLE) {
            self.agility *= AGILITY_FACTOR;
            if !is_decision && self.has_bool_var_flag(bool_var, BV_PHASE) == is_negative {
                self.agility += 1.0 - AGILITY_FACTOR;
            }
        }
        self.set_bool_var_flag(bool_var, BV_PHASE_AVAILABLE, true);
        self.set_bool_var_flag(bool_var, BV_PHASE, !is_negative);
        if self.is_atom(bool_var) && self.is_relevant(self.bool_var2expr[bool_var as usize]) {
            self.atom_propagation_queue.push(literal);
        }
    }

    fn bcp(&mut self) -> bool {
        while self.qhead < self.assigned_literals.len() {
            if self.check_canceled() {
                return true;
            }
            let literal = self.assigned_literals[self.qhead];
            self.qhead += 1;
            let not_literal = negate(literal);
            let num_binary = self
                .binary_watches
                .get(literal as usize)
                .map_or(0, Vec::len);
            if num_binary > 0 {
                let justification = self.get_bin_justification(literal);
                for index in (0..num_binary).rev() {
                    let other = self.binary_watches[literal as usize][index];
                    let value = self.assignment[other as usize];
                    if value == LBool::False {
                        self.set_conflict(justification, Some(negate(other)));
                        return false;
                    }
                    if value == LBool::Undef {
                        self.assign_core(other, justification, false);
                    }
                }
            }
            let Some(slot) = self.watches.get_mut(literal as usize) else {
                continue;
            };
            // Nothing below adds a watch on this literal (a candidate is never false, and the
            // negated literal is), so the list is taken out while it is filtered.
            let mut list = mem::take(slot);
            let mut kept = 0;
            let mut index = 0;
            while index < list.len() {
                let clause = list[index];
                let first = (clause + HEADER_SIZE) as usize;
                let data = &mut self.clauses.data;
                if data[first] as Literal == not_literal {
                    data[first] = data[first + 1];
                    data[first + 1] = not_literal as i32;
                }
                let first_literal = data[first] as Literal;
                let first_value = self.assignment[first_literal as usize];
                if first_value == LBool::True {
                    list[kept] = clause;
                    kept += 1;
                    index += 1;
                    continue;
                }
                let mut is_found = false;
                let end = first + self.clauses.data[clause as usize] as usize;
                for position in first + 2..end {
                    let candidate = self.clauses.data[position] as Literal;
                    if self.assignment[candidate as usize] != LBool::False {
                        self.add_watch(negate(candidate), clause);
                        self.clauses.data[first + 1] = candidate as i32;
                        self.clauses.data[position] = not_literal as i32;
                        is_found = true;
                        break;
                    }
                }
                index += 1;
                if is_found {
                    continue;
                }
                list[kept] = clause;
                kept += 1;
                if first_value == LBool::False {
                    while index < list.len() {
                        list[kept] = list[index];
                        kept += 1;
                        index += 1;
                    }
                    list.truncate(kept);
                    self.watches[literal as usize] = list;
                    self.set_conflict(BJustification::Clause(clause), None);
                    return false;
                }
                self.assign_core(first_literal, BJustification::Clause(clause), false);
            }
            list.truncate(kept);
            self.watches[literal as usize] = list;
        }
        true
    }

    fn propagate_eqs(&mut self) -> Result<bool, SmtError> {
        let mut index = 0;
        while index < self.eq_propagation_queue.len() && !self.check_canceled() {
            let entry = self.eq_propagation_queue[index];
            self.add_eq(entry.lhs, entry.rhs, entry.justification)?;
            if self.is_inconsistent() {
                self.eq_propagation_queue.clear();
                return Ok(false);
            }
            index += 1;
        }
        self.eq_propagation_queue.clear();
        Ok(true)
    }

    fn propagate_atoms(&mut self) -> Result<bool, SmtError> {
        let mut index = 0;
        while index < self.atom_propagation_queue.len() && !self.check_canceled() {
            let literal = self.atom_propagation_queue[index];
            let bool_var = get_var(literal);
            let value = self.assignment[mk_literal(bool_var, false) as usize];
            if self.has_bool_var_flag(bool_var, BV_ENODE) {
                self.propagate_bool_var_enode(bool_var)?;
            }
            if self.is_inconsistent() {
                return Ok(false);
            }
            if self.has_bool_var_flag(bool_var, BV_EQ) {
                let eq = self.bool_var2expr[bool_var as usize];
                if !self.m.is_bool(self.m.get_arg(eq, 0)) {
                    let lhs = self.get_enode(self.m.get_arg(eq, 0));
                    let rhs = self.get_enode(self.m.get_arg(eq, 1));
                    if let (Some(lhs), Some(rhs)) = (lhs, rhs) {
                        if value == LBool::True {
                            self.add_eq(lhs, rhs, EqJustification::Equation { literal })?;
                        } else if !self.add_diseq(lhs, rhs) && !self.is_inconsistent() {
                            let justification =
                                self.justification_arena.mk(Justification::EqPropagation {
                                    first: lhs,
                                    second: rhs,
                                });
                            self.set_conflict(
                                BJustification::Justification(justification),
                                Some(mk_literal(bool_var, true)),
                            );
                        }
                    }
                }
            } else if self.has_bool_var_flag(bool_var, BV_THEORY) {
                self.theory_assign_eh(bool_var, value == LBool::True)?;
            } else if self.has_bool_var_flag(bool_var, BV_QUANTIFIER) && value == LBool::True {
                self.qmanager_assign_eh(self.bool_var2expr[bool_var as usize])?;
            }
            if self.is_inconsistent() {
                return Ok(false);
            }
            index += 1;
        }
        self.atom_propagation_queue.clear();
        Ok(true)
    }

    pub(crate) fn propagate_bool_var_enode(&mut self, bool_var: BoolVar) -> Result<(), SmtError> {
        let value = self.assignment[mk_literal(bool_var, false) as usize];
        let Some(start) = self.get_enode(self.bool_var2expr[bool_var as usize]) else {
            return Ok(());
        };
        let is_negative = value == LBool::False;
        if self.node(start).is_merge_tf() {
            let target = if is_negative {
                self.false_enode
            } else {
                self.true_enode
            };
            self.add_eq(
                start,
                target,
                EqJustification::Equation {
                    literal: mk_literal(bool_var, is_negative),
                },
            )?;
        }
        let root = self.root(start);
        if root == self.true_enode || root == self.false_enode {
            return Ok(());
        }
        let root_owner = self.node(root).owner;
        if start == root
            || !self.is_relevant(root_owner)
            || self.assignment[mk_literal(self.get_bool_var(root_owner)?, false) as usize] != value
        {
            let first = start;
            let mut node = self.node(start).next;
            while node != first {
                let other_var = self.get_bool_var(self.node(node).owner)?;
                if self.assignment[mk_literal(other_var, false) as usize] != value {
                    let justification = self.mk_mp_iff(first, node);
                    self.assign(mk_literal(other_var, is_negative), justification, false);
                }
                node = self.node(node).next;
            }
        }
        Ok(())
    }

    fn mk_mp_iff(&mut self, first: EnodeId, second: EnodeId) -> BJustification {
        BJustification::Justification(
            self.justification_arena
                .mk(Justification::MpIff { first, second }),
        )
    }

    pub fn relevant_eh(&mut self, expr: Expr) -> Result<(), SmtError> {
        if let Some(bool_var) = self.find_bool_var(expr)
            && self.is_atom(bool_var)
        {
            let value = self.assignment[mk_literal(bool_var, false) as usize];
            if value != LBool::Undef {
                self.atom_propagation_queue
                    .push(mk_literal(bool_var, value == LBool::False));
            }
        }
        if self.m.kinds[expr as usize] != KIND_APP {
            return Ok(());
        }
        let node = self.get_enode(expr);
        if let Some(node) = node {
            self.qmanager_relevant_eh(node)?;
        }
        if self.m.get_family(expr) == FAMILY_ARITH
            || node.is_some_and(|node| self.node(node).th_var >= 0)
        {
            self.theory_relevant_eh(expr)?;
        }
        Ok(())
    }

    fn propagate_relevancy(&mut self, qhead: usize) -> Result<(), SmtError> {
        let mut index = qhead;
        while index < self.assigned_literals.len() {
            let literal = self.assigned_literals[index];
            let expr = self.bool_var2expr[get_var(literal) as usize];
            RelevancyPropagator::assign_eh(self, expr, !is_negated(literal))?;
            index += 1;
        }
        RelevancyPropagator::propagate(self)
    }

    fn propagate_th_eqs(&mut self) -> Result<(), SmtError> {
        let mut index = 0;
        while index < self.th_eq_queue.len() && !self.is_inconsistent() {
            self.theory_new_eq_eh(self.th_eq_queue[index], self.th_eq_queue[index + 1])?;
            index += 2;
        }
        self.th_eq_queue.clear();
        Ok(())
    }

    fn propagate_th_diseqs(&mut self) -> Result<(), SmtError> {
        let mut index = 0;
        while index < self.th_diseq_queue.len() && !self.is_inconsistent() {
            self.theory_new_diseq_eh(self.th_diseq_queue[index], self.th_diseq_queue[index + 1])?;
            index += 2;
        }
        self.th_diseq_queue.clear();
        Ok(())
    }

    pub fn can_propagate(&self) -> bool {
        self.qhead != self.assigned_literals.len()
            || self.relevancy.can_propagate()
            || !self.atom_propagation_queue.is_empty()
            || self.qmanager_can_propagate()
            || self.theory_can_propagate()
            || !self.eq_propagation_queue.is_empty()
            || !self.th_eq_queue.is_empty()
            || !self.th_diseq_queue.is_empty()
    }

    pub fn propagate(&mut self) -> Result<bool, SmtError> {
        loop {
            if self.is_inconsistent() {
                return Ok(false);
            }
            let qhead = self.qhead;
            if !self.bcp() {
                return Ok(false);
            }
            self.propagate_relevancy(qhead)?;
            if self.is_inconsistent() {
                return Ok(false);
            }
            if !self.propagate_atoms()? {
                return Ok(false);
            }
            if !self.propagate_eqs()? {
                return Ok(false);
            }
            self.propagate_th_eqs()?;
            self.propagate_th_diseqs()?;
            if self.is_inconsistent() {
                return Ok(false);
            }
            self.theory_propagate()?;
            if self.is_inconsistent() {
                return Ok(false);
            }
            if !self.check_canceled() {
                self.qmanager_propagate()?;
            }
            if self.is_inconsistent() {
                return Ok(false);
            }
            if self.is_resource_limit_exceeded() {
                self.qhead = qhead;
                return Ok(true);
            }
            if !self.can_propagate() {
                return Ok(true);
            }
        }
    }

    // Equalities.

    fn get_closest_var(&self, start: EnodeId) -> i32 {
        let mut node = Some(start);
        while let Some(current) = node {
            if self.node(current).th_var >= 0 {
                return self.node(current).th_var;
            }
            node = self.node(current).trans_target;
        }
        -1
    }

    pub(crate) fn invert_trans(&mut self, start: EnodeId) {
        let mut current = self.node(start).trans_target;
        let mut justification = self.node(start).trans_justification;
        let mut previous = start;
        self.node_mut(start).trans_target = None;
        while let Some(node) = current {
            let next = self.node(node).trans_target;
            let next_justification = self.node(node).trans_justification;
            let enode = self.node_mut(node);
            enode.trans_target = Some(previous);
            enode.trans_justification = justification;
            previous = node;
            current = next;
            justification = next_justification;
        }
    }

    fn push_new_th_eq(&mut self, first: i32, second: i32) {
        self.th_eq_queue.push(first);
        self.th_eq_queue.push(second);
    }

    fn push_new_th_diseq(&mut self, first: i32, second: i32) {
        if self.node(self.theory_get_enode(first)).is_interpreted()
            && self.node(self.theory_get_enode(second)).is_interpreted()
        {
            return;
        }
        self.th_diseq_queue.push(first);
        self.th_diseq_queue.push(second);
    }

    fn push_new_th_diseqs(&mut self, root: EnodeId, th_var: i32) -> Result<(), SmtError> {
        let mut index = 0;
        while index < self.node(root).parents.len() {
            let parent = self.node(root).parents[index];
            index += 1;
            if !self.node(parent).is_eq() {
                continue;
            }
            let literal = mk_literal(self.get_bool_var(self.node(parent).owner)?, false);
            if self.assignment[literal as usize] != LBool::False {
                continue;
            }
            let mut lhs = self.node(parent).get_arg(0);
            let mut rhs = self.node(parent).get_arg(1);
            if self.root(rhs) == self.root(root) {
                mem::swap(&mut lhs, &mut rhs);
            }
            let rhs_var = self.get_closest_var(rhs);
            let lhs_var = self.get_closest_var(lhs);
            let final_var = if lhs_var >= 0 { lhs_var } else { th_var };
            if rhs_var >= 0 && final_var != rhs_var {
                self.push_new_th_diseq(final_var, rhs_var);
            }
        }
        Ok(())
    }

    fn merge_theory_vars(
        &mut self,
        n2: EnodeId,
        n1: EnodeId,
        justification: EqJustification,
    ) -> Result<(), SmtError> {
        let r2 = self.root(n2);
        let r1 = self.root(n1);
        if self.node(r1).th_var < 0 && self.node(r2).th_var < 0 {
            return Ok(());
        }
        let is_from_theory = matches!(justification, EqJustification::Justification { .. });
        let v2 = self.get_closest_var(n2);
        let v1 = self.get_closest_var(n1);
        if v2 >= 0 && v1 >= 0 {
            if !is_from_theory {
                self.push_new_th_eq(v2, v1);
            }
        } else if v1 < 0 && v2 >= 0 {
            self.push_new_th_diseqs(r1, v2)?;
        } else if v1 >= 0 && v2 < 0 {
            self.node_mut(r2).th_var = v1;
            self.push_new_th_diseqs(r2, v1)?;
        }
        Ok(())
    }

    pub fn attach_th_var(&mut self, node: EnodeId, th_var: i32) -> Result<(), SmtError> {
        let old_var = self.node(node).th_var;
        // A variable that an equality moved to the node's list, which the node's own replaces.
        if old_var >= 0 {
            self.node_mut(node).th_var = th_var;
            self.push_trail(TrailClosure::ThVar { node, old_var });
            self.push_new_th_eq(th_var, old_var);
            return Ok(());
        }
        let root = self.root(node);
        let root_var = self.node(root).th_var;
        self.node_mut(node).th_var = th_var;
        self.trail_ints.push(th_var as u32);
        self.trail_nodes.push(node);
        self.trail_kinds.push(UNDO_TH_VAR);
        if root_var < 0 {
            if root != node {
                self.node_mut(root).th_var = th_var;
            }
            self.push_new_th_diseqs(root, th_var)?;
        } else if root != node {
            self.push_new_th_eq(root_var, th_var);
        }
        Ok(())
    }

    pub fn add_eq(
        &mut self,
        input_n1: EnodeId,
        input_n2: EnodeId,
        justification: EqJustification,
    ) -> Result<(), SmtError> {
        let mut n1 = input_n1;
        let mut n2 = input_n2;
        let mut r1 = self.root(n1);
        let mut r2 = self.root(n2);
        if r1 == r2 {
            return Ok(());
        }
        if self.node(r1).is_interpreted() && self.node(r2).is_interpreted() {
            let conflict = self.justification_arena.mk(Justification::EqConflict {
                first: n1,
                second: n2,
                justification,
            });
            self.set_conflict(BJustification::Justification(conflict), None);
            return Ok(());
        }
        if (self.node(r1).class_size > self.node(r2).class_size && !self.node(r2).is_interpreted())
            || self.node(r1).is_interpreted()
        {
            mem::swap(&mut n1, &mut n2);
            mem::swap(&mut r1, &mut r2);
        }
        let r1_owner = self.node(r1).owner;
        let r2_owner = self.node(r2).owner;
        if self.is_relevant(r1_owner) {
            self.mark_as_relevant(r2_owner)?;
        } else if self.is_relevant(r2_owner) {
            self.mark_as_relevant(r1_owner)?;
        }
        let r2_num_parents = self.node(r2).parents.len();
        self.qmanager_add_eq_eh(r1, r2)?;
        self.merge_theory_vars(n2, n1, justification)?;
        self.invert_trans(n1);
        let node = self.node_mut(n1);
        node.trans_target = Some(n2);
        node.trans_justification = justification;
        self.remove_parents_from_cg_table(r1);
        let mut current = r1;
        loop {
            self.node_mut(current).root = r2;
            current = self.node(current).next;
            if current == r1 {
                break;
            }
        }
        self.reinsert_parents_into_cg_table(r1, r2, n1, n2, justification)?;
        self.trail_ints.push(r2_num_parents as u32);
        self.trail_nodes.push(r1);
        self.trail_nodes.push(n1);
        self.trail_kinds.push(UNDO_ADD_EQ);
        if self.node(n2).is_bool() {
            self.propagate_bool_enode_assignment(r1, r2, n1, n2)?;
        }
        let saved_next = self.node(r1).next;
        let r2_next = self.node(r2).next;
        self.node_mut(r1).next = r2_next;
        self.node_mut(r2).next = saved_next;
        let r1_class_size = self.node(r1).class_size;
        self.node_mut(r2).class_size += r1_class_size;
        Ok(())
    }

    fn remove_parents_from_cg_table(&mut self, r1: EnodeId) {
        let mut index = 0;
        while index < self.node(r1).parents.len() {
            let parent = self.node(r1).parents[index];
            index += 1;
            if self.node(parent).is_marked()
                || !self.enode_arena.is_cgr(parent)
                || self.enode_arena.is_true_eq(parent)
            {
                continue;
            }
            self.node_mut(parent).set_is_marked(true);
            if self.node(parent).is_cgc_enabled() {
                if !self.node(parent).is_eq() {
                    self.r1_parent_generations
                        .insert(parent, self.node(parent).generation);
                }
                self.cg_table.erase(&self.enode_arena, parent);
            }
        }
    }

    /// n1 = n2, justified by the justification, implied r1 = r2. A congruence that makes a false
    /// equality true is the root of a conflict, which dynamic Ackermannization counts.
    fn reinsert_parents_into_cg_table(
        &mut self,
        r1: EnodeId,
        r2: EnodeId,
        n1: EnodeId,
        n2: EnodeId,
        justification: EqJustification,
    ) -> Result<(), SmtError> {
        let mut index = 0;
        while index < self.node(r1).parents.len() {
            let parent = self.node(r1).parents[index];
            index += 1;
            if !self.node(parent).is_marked() {
                continue;
            }
            self.node_mut(parent).set_is_marked(false);
            if self.node(parent).is_eq() {
                let lhs = self.node(parent).get_arg(0);
                let rhs = self.node(parent).get_arg(1);
                if self.root(lhs) == self.root(rhs) {
                    let literal = mk_literal(self.get_bool_var(self.node(parent).owner)?, false);
                    let value = self.assignment[literal as usize];
                    if value != LBool::True {
                        if value == LBool::False
                            && matches!(justification, EqJustification::Congruence { .. })
                        {
                            self.dyn_ack_cg_conflict_eh(self.node(n1).owner, self.node(n2).owner);
                        }
                        let propagation =
                            self.justification_arena.mk(Justification::EqPropagation {
                                first: lhs,
                                second: rhs,
                            });
                        self.assign(literal, BJustification::Justification(propagation), false);
                    }
                    continue;
                }
            }
            if !self.node(parent).is_cgc_enabled() {
                self.node_mut(r2).add_parent(parent);
                continue;
            }
            let parent_generation = if self.node(parent).is_eq() {
                0
            } else {
                match self.r1_parent_generations.get(&parent) {
                    Some(generation) => *generation,
                    None => self.get_generation(parent),
                }
            };
            let congruent = self.cg_table.insert(&self.enode_arena, parent);
            if congruent == parent {
                self.node_mut(parent).generation = parent_generation;
                self.node_mut(r2).add_parent(parent);
                continue;
            }
            self.node_mut(parent).cg = congruent;
            self.merge_cgc_generations(parent, parent_generation, congruent);
            if self.root(congruent) != self.root(parent) {
                let congruence = get_congruence_justification(&self.enode_arena, parent, congruent);
                self.push_eq(parent, congruent, congruence);
            }
        }
        self.r1_parent_generations.clear();
        Ok(())
    }

    pub(crate) fn undo_add_eq(&mut self, r1: EnodeId, n1: EnodeId, r2_num_parents: usize) {
        let r2 = self.root(r1);
        let r1_class_size = self.node(r1).class_size;
        self.node_mut(r2).class_size -= r1_class_size;
        let saved_next = self.node(r1).next;
        let r2_next = self.node(r2).next;
        self.node_mut(r1).next = r2_next;
        self.node_mut(r2).next = saved_next;
        self.erased_generations.clear();
        for index in r2_num_parents..self.node(r2).parents.len() {
            let parent = self.node(r2).parents[index];
            if self.node(parent).is_cgc_enabled() {
                if !self.node(parent).is_eq() {
                    self.erased_generations
                        .insert(parent, self.node(parent).generation);
                }
                self.cg_table.erase(&self.enode_arena, parent);
            }
        }
        let mut current = r1;
        loop {
            self.node_mut(current).root = r1;
            current = self.node(current).next;
            if current == r1 {
                break;
            }
        }
        self.node_mut(r2).parents.truncate(r2_num_parents);
        for index in 0..self.node(r1).parents.len() {
            let parent = self.node(r1).parents[index];
            if !self.node(parent).is_cgc_enabled() {
                continue;
            }
            let cg = self.node(parent).cg;
            if self.enode_arena.is_true_eq(parent)
                || (parent != cg && is_congruent(&self.enode_arena, parent, cg))
            {
                continue;
            }
            let generation = if self.node(parent).is_eq() {
                0
            } else if parent == cg {
                let Some(cached) = self.erased_generations.get(&parent) else {
                    continue;
                };
                *cached
            } else {
                100000
            };
            let congruent = self.cg_table.insert(&self.enode_arena, parent);
            self.node_mut(parent).cg = congruent;
            if congruent == parent {
                self.node_mut(parent).generation = generation;
            }
        }
        let r2_var = self.node(r2).th_var;
        if r2_var >= 0 && self.root(self.theory_get_enode(r2_var)) != r2 {
            self.node_mut(r2).th_var = -1;
        }
        self.node_mut(n1).trans_target = None;
        self.invert_trans(r1);
    }

    fn propagate_bool_enode_assignment(
        &mut self,
        r1: EnodeId,
        r2: EnodeId,
        n1: EnodeId,
        n2: EnodeId,
    ) -> Result<(), SmtError> {
        if r2 == self.false_enode || r2 == self.true_enode {
            let is_false = r2 == self.false_enode;
            let mut current = r1;
            loop {
                let literal = mk_literal(self.get_bool_var(self.node(current).owner)?, is_false);
                if self.assignment[literal as usize] != LBool::True {
                    let justification = self
                        .justification_arena
                        .mk(Justification::EqRootPropagation { node: current });
                    self.assign(literal, BJustification::Justification(justification), false);
                }
                current = self.node(current).next;
                if current == r1 {
                    return Ok(());
                }
            }
        }
        let first =
            self.assignment[mk_literal(self.get_bool_var(self.node(n1).owner)?, false) as usize];
        let second =
            self.assignment[mk_literal(self.get_bool_var(self.node(n2).owner)?, false) as usize];
        if first == second {
            return Ok(());
        }
        if second == LBool::Undef {
            self.propagate_bool_enode_assignment_core(n1, n2)
        } else {
            self.propagate_bool_enode_assignment_core(n2, n1)
        }
    }

    fn propagate_bool_enode_assignment_core(
        &mut self,
        source: EnodeId,
        start: EnodeId,
    ) -> Result<(), SmtError> {
        let value = self.assignment
            [mk_literal(self.get_bool_var(self.node(source).owner)?, false) as usize];
        let mut target = start;
        loop {
            let bool_var = self.get_bool_var(self.node(target).owner)?;
            let target_value = self.assignment[mk_literal(bool_var, false) as usize];
            if target_value != value {
                if target_value != LBool::Undef
                    && is_congruent(&self.enode_arena, source, target)
                    && self.node(source).num_args() > 0
                {
                    self.dyn_ack_cg_conflict_eh(self.node(source).owner, self.node(target).owner);
                }
                let justification = self.mk_mp_iff(source, target);
                self.assign(
                    mk_literal(bool_var, value == LBool::False),
                    justification,
                    false,
                );
            }
            target = self.node(target).next;
            if target == start {
                return Ok(());
            }
        }
    }

    fn add_diseq(&mut self, n1: EnodeId, n2: EnodeId) -> bool {
        let r1 = self.root(n1);
        let r2 = self.root(n2);
        if r1 == r2 {
            return self.node(r1).th_var >= 0;
        }
        let v1 = self.get_closest_var(n1);
        let v2 = self.get_closest_var(n2);
        if v1 >= 0 && v2 >= 0 {
            self.push_new_th_diseq(v1, v2);
        }
        true
    }

    /// Theory combination: assume that two shared terms are equal.
    pub fn assume_eq(&mut self, lhs: EnodeId, rhs: EnodeId) -> Result<bool, SmtError> {
        if self.root(lhs) == self.root(rhs) {
            return Ok(false);
        }
        let eq = self.mk_eq_atom(self.node(lhs).owner, self.node(rhs).owner)?;
        let mut is_new = false;
        if !self.is_b_internalized(eq) {
            self.internalize_formula_core(eq, true)?;
            let bool_var = self.get_bool_var(eq)?;
            self.set_bool_var_flag(bool_var, BV_EQ, true);
            self.set_true_first_flag(bool_var);
            self.theory_internalize_eq_eh(eq)?;
            is_new = true;
        }
        let bool_var = self.get_bool_var(eq)?;
        if !self.has_bool_var_flag(bool_var, BV_TRUE_FIRST) {
            self.set_true_first_flag(bool_var);
            is_new = true;
        }
        if self.assignment[mk_literal(bool_var, false) as usize] == LBool::Undef {
            is_new = true;
        }
        if !self.is_relevant(eq) {
            self.mark_as_relevant(eq)?;
            is_new = true;
        }
        Ok(is_new)
    }

    // Search.

    pub fn inc_bvar_activity(&mut self, bool_var: BoolVar) {
        self.activity[bool_var as usize] += self.bvar_inc;
        if self.activity[bool_var as usize] > ACTIVITY_LIMIT {
            for index in 0..self.num_bool_vars as usize {
                self.activity[index] *= INV_ACTIVITY_LIMIT;
            }
            self.bvar_inc *= INV_ACTIVITY_LIMIT;
        }
        let (queue, view) = self.split_case_split_queue();
        queue.activity_increased(&view, bool_var);
    }

    fn push_scope(&mut self) -> Result<(), SmtError> {
        self.scope_level += 1;
        self.scope_assigned_limits
            .push(self.assigned_literals.len());
        self.scope_aux_clause_limits.push(self.aux_clauses.len());
        self.scope_trail_limits.push(self.trail_kinds.len());
        self.relevancy.push();
        self.qmanager_push()?;
        self.theory_push_scope_eh()
    }

    fn cache_generation_of_expr(
        &mut self,
        expr: Expr,
        new_level: u32,
        visited: &mut HashSet<Expr>,
    ) -> Result<(), SmtError> {
        let mut todo = vec![expr];
        while let Some(current) = todo.pop() {
            if !visited.insert(current) {
                continue;
            }
            let kind = self.m.kinds[current as usize];
            if kind == KIND_APP {
                if let Some(node) = self.get_enode(current) {
                    if self.node(node).iscope_level <= new_level {
                        continue;
                    }
                    let generation = self.get_generation(node);
                    self.cached_generation.insert(current, generation);
                }
                for index in 0..self.m.get_num_args(current) {
                    let arg = self.m.get_arg(current, index);
                    if self.m.kinds[arg as usize] != KIND_VAR {
                        todo.push(arg);
                    }
                }
            } else if kind == KIND_QUANTIFIER && self.is_b_internalized(current) {
                self.cached_generation
                    .insert(current, self.qmanager.get_generation(current));
                todo.push(self.m.get_quantifier(current)?.body);
            }
        }
        Ok(())
    }

    fn cache_generation_of_literals(
        &mut self,
        literals: &[Literal],
        new_level: u32,
        visited: &mut HashSet<Expr>,
    ) -> Result<(), SmtError> {
        for literal in literals {
            let bool_var = get_var(*literal);
            if self.get_intern_level(bool_var) > new_level {
                self.cache_generation_of_expr(
                    self.bool_var2expr[bool_var as usize],
                    new_level,
                    visited,
                )?;
            }
        }
        Ok(())
    }

    fn cache_generation(
        &mut self,
        new_level: u32,
        visited: &mut HashSet<Expr>,
    ) -> Result<(), SmtError> {
        let limit = i64::from(self.scope_level).min(self.clauses_to_reinit.len() as i64 - 1);
        let mut level = i64::from(new_level);
        while level <= limit {
            for index in 0..self.clauses_to_reinit[level as usize].len() {
                let clause = self.clauses_to_reinit[level as usize][index];
                let literals = self.clauses.get_literals(clause);
                self.cache_generation_of_literals(&literals, new_level, visited)?;
            }
            level += 1;
        }
        Ok(())
    }

    fn unassign_vars(&mut self, old_limit: usize) {
        for index in (old_limit..self.assigned_literals.len()).rev() {
            let literal = self.assigned_literals[index];
            self.assignment[literal as usize] = LBool::Undef;
            self.assignment[negate(literal) as usize] = LBool::Undef;
            self.justifications[get_var(literal) as usize] = BJustification::Decision;
            let (queue, view) = self.split_case_split_queue();
            queue.unassign_var(&view, get_var(literal));
        }
        self.assigned_literals.truncate(old_limit);
        self.qhead = old_limit;
    }

    fn pop_scope_core(
        &mut self,
        num_scopes: u32,
        visited: &mut HashSet<Expr>,
    ) -> Result<u32, SmtError> {
        let new_level = self.scope_level - num_scopes;
        self.cache_generation(new_level, visited)?;
        self.qmanager_pop(num_scopes)?;
        if new_level < self.base_level {
            let mut lemmas = mem::take(&mut self.lemmas);
            let result = self.delete_clauses(
                &mut lemmas,
                self.base_scope_lemma_limits[new_level as usize],
            );
            self.lemmas = lemmas;
            result?;
            self.base_scope_lemma_limits.truncate(new_level as usize);
        }
        self.conflict = None;
        let mut aux_clauses = mem::take(&mut self.aux_clauses);
        let result = self.delete_clauses(
            &mut aux_clauses,
            self.scope_aux_clause_limits[new_level as usize],
        );
        self.aux_clauses = aux_clauses;
        result?;
        self.relevancy.pop(&mut self.m, num_scopes as usize)?;
        self.unassign_vars(self.scope_assigned_limits[new_level as usize]);
        self.pop_trail(self.scope_trail_limits[new_level as usize])?;
        self.theory_pop_scope_eh(num_scopes)?;
        self.eq_propagation_queue.clear();
        self.th_eq_queue.clear();
        self.th_diseq_queue.clear();
        self.atom_propagation_queue.clear();
        self.scope_assigned_limits.truncate(new_level as usize);
        self.scope_aux_clause_limits.truncate(new_level as usize);
        self.scope_trail_limits.truncate(new_level as usize);
        self.scope_level = new_level;
        if new_level < self.base_level {
            self.base_level = new_level;
            self.search_level = new_level;
        }
        let num_bool_vars = self.num_bool_vars;
        self.reinit_clauses(num_scopes, num_bool_vars)?;
        Ok(num_bool_vars)
    }

    fn pop_scope(&mut self, num_scopes: u32) -> Result<(), SmtError> {
        self.pop_scope_core(num_scopes, &mut HashSet::new())?;
        self.cached_generation.clear();
        Ok(())
    }

    fn reinit_clauses(&mut self, num_scopes: u32, num_bool_vars: u32) -> Result<(), SmtError> {
        if self.clauses_to_reinit.is_empty() {
            return Ok(());
        }
        let limit = (self.scope_level + num_scopes).min(self.clauses_to_reinit.len() as u32 - 1);
        for level in self.scope_level + 1..=limit {
            let clauses = mem::take(&mut self.clauses_to_reinit[level as usize]);
            for clause in clauses {
                self.clauses.check_live(clause)?;
                if self.clauses.is_deleted(clause) {
                    self.clauses.set_reinit(clause, false);
                    self.clauses.set_reinternalize_atoms(clause, false);
                    self.clauses.free(clause);
                    continue;
                }
                let mut is_kept = false;
                let atoms = self.clauses.get_atoms(clause);
                if self.clauses.is_reinternalize_atoms(clause) && !atoms.is_empty() {
                    for index in 0..2 {
                        if get_var(self.clauses.get_literal(clause, index)) < num_bool_vars {
                            self.remove_watch_literal(clause, index);
                        }
                    }
                    let is_th_lemma = self.clauses.get_kind(clause) == CLS_TH_LEMMA;
                    for (index, atom) in atoms.iter().enumerate() {
                        let atom = *atom as Expr;
                        self.internalize(atom, !self.m.is_not(atom))?;
                        let literal = mk_literal(
                            self.get_bool_var(atom)?,
                            self.clauses.get_atom_sign(clause, index as u32),
                        );
                        self.clauses.set_literal(clause, index as u32, literal);
                        if is_th_lemma {
                            self.mark_literal_as_relevant(literal)?;
                        }
                    }
                    let first_watch = self.select_watch_literal(clause, 0);
                    self.clauses.swap_literals(clause, 0, first_watch);
                    let second_watch = self.select_watch_literal(clause, 1);
                    self.clauses.swap_literals(clause, 1, second_watch);
                    self.add_watch_literal(clause, 0);
                    self.add_watch_literal(clause, 1);
                    let first = self.clauses.get_literal(clause, 0);
                    if self.assignment[first as usize] == LBool::False {
                        self.set_conflict(BJustification::Clause(clause), None);
                    } else if self.assignment[self.clauses.get_literal(clause, 1) as usize]
                        == LBool::False
                    {
                        self.assign(first, BJustification::Clause(clause), false);
                    }
                    is_kept = true;
                } else {
                    let first = self.clauses.get_literal(clause, 0);
                    let second = self.clauses.get_literal(clause, 1);
                    if self.clauses.get_kind(clause) == CLS_TH_LEMMA {
                        self.mark_literal_as_relevant(first)?;
                        self.mark_literal_as_relevant(second)?;
                    }
                    if self.assignment[first as usize] == LBool::False
                        && self.is_empty_clause(clause)
                    {
                        self.set_conflict(BJustification::Clause(clause), None);
                        is_kept = true;
                    } else if self.assignment[second as usize] == LBool::False
                        && self.assignment[first as usize] == LBool::Undef
                        && self.is_unit_clause(clause)
                    {
                        self.assign(first, BJustification::Clause(clause), false);
                        is_kept = true;
                    }
                }
                if is_kept && self.scope_level > self.base_level {
                    while self.clauses_to_reinit.len() <= self.scope_level as usize {
                        self.clauses_to_reinit.push(Vec::new());
                    }
                    self.clauses_to_reinit[self.scope_level as usize].push(clause);
                } else {
                    if self.clauses.is_reinternalize_atoms(clause) {
                        self.release_atoms(clause)?;
                    }
                    self.clauses.set_reinit(clause, false);
                    self.clauses.set_reinternalize_atoms(clause, false);
                }
            }
        }
        Ok(())
    }

    fn is_empty_clause(&self, clause: Clause) -> bool {
        (0..self.clauses.get_num_literals(clause)).all(|index| {
            self.assignment[self.clauses.get_literal(clause, index) as usize] == LBool::False
        })
    }

    /// is_unit_clause: exactly one literal is unassigned and the rest are false.
    fn is_unit_clause(&self, clause: Clause) -> bool {
        let mut is_found = false;
        for index in 0..self.clauses.get_num_literals(clause) {
            let value = self.assignment[self.clauses.get_literal(clause, index) as usize];
            if value == LBool::True {
                return false;
            }
            if value == LBool::Undef {
                if is_found {
                    return false;
                }
                is_found = true;
            }
        }
        is_found
    }

    /// guess with PS_CACHING_CONSERVATIVE: the cached phase while phase caching is on, else false.
    fn guess(&self, bool_var: BoolVar) -> bool {
        if self.m.kinds[self.bool_var2expr[bool_var as usize] as usize] == KIND_QUANTIFIER {
            return false;
        }
        if self.has_bool_var_flag(bool_var, BV_TRUE_FIRST) {
            return true;
        }
        self.is_phase_cache_on
            && self.has_bool_var_flag(bool_var, BV_PHASE_AVAILABLE)
            && self.has_bool_var_flag(bool_var, BV_PHASE)
    }

    fn update_phase_cache_counter(&mut self) {
        self.phase_counter += 1;
        let limit = if self.is_phase_cache_on {
            PHASE_CACHING_ON
        } else {
            PHASE_CACHING_OFF
        };
        if self.phase_counter < limit {
            return;
        }
        self.phase_counter = 0;
        self.is_phase_cache_on = !self.is_phase_cache_on;
    }

    fn decide(&mut self) -> Result<bool, SmtError> {
        let (queue, mut view) = self.split_case_split_queue();
        let Some(bool_var) = queue.next_case_split(&mut view) else {
            return Ok(false);
        };
        let is_positive = self.guess(bool_var);
        self.push_scope()?;
        self.assign(
            mk_literal(bool_var, !is_positive),
            BJustification::Axiom,
            true,
        );
        Ok(true)
    }

    fn resolve_conflict(&mut self) -> Result<bool, SmtError> {
        self.num_conflicts += 1;
        self.num_conflicts_since_restart += 1;
        self.num_conflicts_since_lemma_gc += 1;
        self.atom_propagation_queue.clear();
        self.eq_propagation_queue.clear();
        self.th_eq_queue.clear();
        self.th_diseq_queue.clear();
        let head = if self.scope_level == 0 {
            0
        } else {
            self.scope_assigned_limits[self.scope_level as usize - 1]
        };
        for index in head..self.assigned_literals.len() {
            let bool_var = get_var(self.assigned_literals[index]);
            self.set_bool_var_flag(bool_var, BV_PHASE_AVAILABLE, false);
        }
        let Some(conflict) = self.conflict else {
            return Ok(false);
        };
        if !self.resolve(conflict.justification, conflict.not_literal)? {
            return Ok(false);
        }
        let new_level = self.conflict_resolution.new_scope_level;
        let mut literals = mem::take(&mut self.conflict_resolution.lemma);
        let atoms = self.conflict_resolution.lemma_atoms.items.clone();
        let mut visited = HashSet::new();
        if self.conflict_resolution.lemma_iscope_level > new_level {
            self.cache_generation_of_literals(&literals, new_level, &mut visited)?;
        }
        let was_relevant: Vec<bool> = literals
            .iter()
            .map(|literal| self.is_relevant(self.bool_var2expr[get_var(*literal) as usize]))
            .collect();
        let num_bool_vars = self.pop_scope_core(self.scope_level - new_level, &mut visited)?;
        if self.conflict_resolution.lemma_iscope_level > self.scope_level {
            for index in 0..literals.len() {
                let literal = literals[index];
                if get_var(literal) < num_bool_vars {
                    continue;
                }
                self.internalize(atoms[index], true)?;
                let atom_literal = self.get_literal(atoms[index])?;
                literals[index] = if is_negated(literal) {
                    negate(atom_literal)
                } else {
                    atom_literal
                };
            }
        }
        // restore_relevancy: marking propagates, so it only marks the literals that lost
        // relevancy.
        for index in 0..literals.len() {
            if was_relevant[index]
                && !self.is_relevant(self.bool_var2expr[get_var(literals[index]) as usize])
            {
                self.mark_literal_as_relevant(literals[index])?;
            }
        }
        self.cached_generation.clear();
        let mut lemma = literals.clone();
        self.conflict_resolution.lemma = literals;
        self.mk_clause(&mut lemma, None, CLS_LEARNED, None)?;
        self.conflict_resolution.lemma_atoms.reset(&mut self.m)?;
        self.bvar_inc *= INV_DECAY;
        self.update_phase_cache_counter();
        Ok(true)
    }

    fn final_check(&mut self) -> Result<u8, SmtError> {
        let status = self.qmanager_final_check_eh(false)?;
        if status != FC_DONE {
            return Ok(status);
        }
        let old_index = self.final_check_index;
        let mut result = FC_DONE;
        let mut failure = SearchFailure::Ok;
        let mut level = 1;
        let mut max_level = 1;
        loop {
            let is_theory = self.final_check_index == 0;
            // Z3 registers every theory for UFNIA, and only arithmetic acts on tlapm's
            // obligations. Of the theories between arithmetic and the quantifiers,
            // theory_finite_set makes a set.range declaration, and its assume_eqs draws a random
            // value.
            if !is_theory {
                self.m.init_finite_set_plugin();
                self.get_random_value();
            }
            let check = if is_theory {
                self.theory_final_check_eh(level)?
            } else {
                self.qmanager_final_check_eh(true)?
            };
            if is_theory {
                max_level = max_level.max(NUM_ARITH_FINAL_CHECK_LEVELS);
            }
            // Z3 reads the cancel flag after each theory's final check, and a canceled check gives
            // up.
            let is_canceled = is_theory && self.check_canceled();
            if is_canceled {
                failure = SearchFailure::Canceled;
            } else if is_theory && check == FC_GIVEUP {
                failure = SearchFailure::Theory;
            }
            self.final_check_index = (self.final_check_index + 1) % 2;
            if check == FC_CONTINUE {
                return Ok(FC_CONTINUE);
            }
            if check == FC_GIVEUP || is_canceled {
                result = FC_GIVEUP;
            }
            if self.final_check_index != old_index {
                continue;
            }
            if level >= max_level || result == FC_DONE || self.can_propagate() {
                break;
            }
            // A higher level reruns every check with the give-up state of the lower one cleared.
            level += 1;
            result = FC_DONE;
            failure = SearchFailure::Ok;
        }
        if self.can_propagate() {
            return Ok(FC_CONTINUE);
        }
        if result == FC_GIVEUP && failure != SearchFailure::Ok {
            self.last_search_failure = failure;
        }
        Ok(result)
    }

    fn bounded_search(&mut self) -> Result<LBool, SmtError> {
        loop {
            while !self.propagate()? {
                if !self.resolve_conflict()? {
                    return Ok(LBool::False);
                }
                if !self.is_inconsistent() {
                    if self.is_resource_limit_exceeded() || self.check_canceled() {
                        return Ok(LBool::Undef);
                    }
                    if self.num_conflicts_since_restart > self.restart_threshold
                        && self.scope_level - self.base_level > 2
                    {
                        return Ok(LBool::Undef);
                    }
                }
                if self.num_conflicts_since_lemma_gc > LEMMA_GC_INITIAL {
                    self.del_inactive_lemmas()?;
                }
                self.dyn_ack_propagate_eh()?;
            }
            if self.is_resource_limit_exceeded() && !self.is_inconsistent() {
                return Ok(LBool::Undef);
            }
            if self.check_canceled() {
                return Ok(LBool::Undef);
            }
            if !self.decide()? {
                if self.is_inconsistent() {
                    return Ok(LBool::False);
                }
                let status = self.final_check()?;
                if status == FC_DONE {
                    return Ok(LBool::True);
                }
                if status == FC_GIVEUP {
                    return Ok(LBool::Undef);
                }
            }
            if self.is_resource_limit_exceeded() && !self.is_inconsistent() {
                return Ok(LBool::Undef);
            }
        }
    }

    /// resource_limits_exceeded: while searching, a failure stops the search, and the cancel flag
    /// is read twice.
    fn is_resource_limit_exceeded(&self) -> bool {
        if self.is_searching
            && (self.last_search_failure != SearchFailure::Ok || self.check_canceled())
        {
            return true;
        }
        self.check_canceled()
    }

    /// reset_model: the model generator still holds the proto model.
    fn reset_model(&mut self) -> Result<(), SmtError> {
        match mem::replace(&mut self.model_state, ModelState::None) {
            ModelState::None => Ok(()),
            ModelState::Generated(generated) => {
                self.model_state = ModelState::Generated(generated);
                Ok(())
            }
            ModelState::Proto(generated) => {
                generated.model.borrow_mut().dec_ref(&mut self.m)?;
                self.model_state = ModelState::Generated(generated);
                Ok(())
            }
            ModelState::Final { generated, model } => {
                model.borrow_mut().dec_ref(&mut self.m)?;
                generated.model.borrow_mut().dec_ref(&mut self.m)?;
                self.model_state = ModelState::Generated(generated);
                Ok(())
            }
        }
    }

    /// mk_proto_model: the model of the current assignment, which the quantifier manager adjusts.
    /// The model generator releases the last model first.
    fn mk_proto_model(&mut self) -> Result<Rc<GeneratedModel>, SmtError> {
        match &self.model_state {
            ModelState::None => {}
            ModelState::Generated(generated)
            | ModelState::Proto(generated)
            | ModelState::Final { generated, .. } => {
                generated.model.borrow_mut().dec_ref(&mut self.m)?;
            }
        }
        let generated = Rc::new(mk_model(self)?);
        generated.model.borrow_mut().inc_ref();
        self.model_state = ModelState::Generated(generated.clone());
        self.qmanager_adjust_model(&generated.model)?;
        generated
            .model
            .borrow_mut()
            .complete_partial_funcs(&mut self.m, false)?;
        generated.model.borrow_mut().cleanup(&mut self.m)?;
        generated.model.borrow_mut().inc_ref();
        self.model_state = ModelState::Proto(generated.clone());
        Ok(generated)
    }

    /// get_model: the model that the proto model makes, which the caller holds too. add_rec_funs
    /// gives each named expression without an interpretation its expression.
    pub fn get_model(&mut self) -> Result<ProtoModelRef, SmtError> {
        let generated = match &self.model_state {
            ModelState::Final { model, .. } => return Ok(model.clone()),
            ModelState::Proto(generated) => generated.clone(),
            ModelState::None | ModelState::Generated(_) => self.mk_proto_model()?,
        };
        let model = generated.model.borrow_mut().mk_model(&mut self.m)?;
        let model = Rc::new(std::cell::RefCell::new(model));
        let macros: Vec<(Decl, Expr)> = self
            .m
            .macros
            .iter()
            .map(|(decl, expr)| (decl as Decl, *expr))
            .collect();
        for (decl, expr) in macros {
            let hash = self.m.get_decl_hash(decl);
            if !model.borrow().const_interps.contains_key(decl as u32, hash) {
                model.borrow_mut().register_const(&mut self.m, decl, expr)?;
            }
        }
        model.borrow_mut().inc_ref();
        self.model_state = ModelState::Final {
            generated,
            model: model.clone(),
        };
        Ok(model)
    }

    /// The model generator's last model, for the tests.
    #[cfg(test)]
    pub(crate) fn get_generated_model(&self) -> Option<Rc<GeneratedModel>> {
        match &self.model_state {
            ModelState::None => None,
            ModelState::Generated(generated)
            | ModelState::Proto(generated)
            | ModelState::Final { generated, .. } => Some(generated.clone()),
        }
    }

    /// validate_model: every relevant ground literal of the assignment holds in the model.
    pub fn validate_model(&mut self, model: &ProtoModelRef) -> Result<bool, SmtError> {
        for index in 0..self.assigned_literals.len() {
            let literal = self.assigned_literals[index];
            let atom = self.bool_var2expr[get_var(literal) as usize];
            if !self.is_relevant(atom) {
                continue;
            }
            // n and res of Z3's loop hold the literal and its value.
            let expr = if is_negated(literal) {
                self.m.mk_not(atom)?
            } else {
                atom
            };
            self.m.inc_ref(expr);
            let value = if self.m.is_ground(expr) {
                model.borrow_mut().eval(&mut self.m, expr, false)?
            } else {
                -1
            };
            if value != -1 {
                self.m.dec_ref(value)?;
            }
            self.m.dec_ref(expr)?;
            if value == self.m.false_expr {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// restart: decides whether the search goes on after a bounded search. A candidate model of a
    /// problem with quantifiers goes to model-based quantifier instantiation, which may add
    /// instances and force a restart.
    fn restart(
        &mut self,
        input_status: LBool,
        current_level: u32,
    ) -> Result<Option<LBool>, SmtError> {
        let mut status = input_status;
        self.reset_model()?;
        let mut is_forced_restart = false;
        if self.last_search_failure != SearchFailure::Ok {
            if self.last_search_failure != SearchFailure::Theory
                || status == LBool::False
                || self.is_inconsistent()
                || !self.qmanager.has_quantifiers()
                || !self.qmanager.is_model_based()
            {
                return Ok(Some(status));
            }
            let generated = self.mk_proto_model()?;
            if self.qmanager_check_model(&generated.model, &generated.root2value)?
                != CHECK_MODEL_RESTART
            {
                return Ok(Some(status));
            }
            self.last_search_failure = SearchFailure::Ok;
            status = LBool::Undef;
            is_forced_restart = true;
        }
        if status == LBool::False {
            return Ok(Some(LBool::False));
        }
        if status == LBool::True && !self.qmanager.has_quantifiers() {
            return Ok(Some(LBool::True));
        }
        if status == LBool::True {
            let generated = self.mk_proto_model()?;
            let result = if self.qmanager.is_model_based() {
                self.qmanager_check_model(&generated.model, &generated.root2value)?
            } else {
                CHECK_MODEL_UNKNOWN
            };
            if result == CHECK_MODEL_SAT {
                return Ok(Some(LBool::True));
            }
            if result == CHECK_MODEL_UNKNOWN {
                self.last_search_failure = SearchFailure::Quantifiers;
                return Ok(Some(LBool::Undef));
            }
        }
        // inc_limits with RS_IN_OUT_GEOMETRIC.
        if self.num_conflicts_since_restart >= self.restart_threshold {
            self.restart_threshold =
                (f64::from(self.restart_threshold) * RESTART_FACTOR).trunc() as u32;
            if self.restart_threshold > self.restart_outer_threshold {
                self.restart_threshold = RESTART_INITIAL;
                self.restart_outer_threshold =
                    (f64::from(self.restart_outer_threshold) * RESTART_FACTOR).trunc() as u32;
            }
        }
        self.num_conflicts_since_restart = 0;
        if is_forced_restart || status == LBool::True || self.agility < RESTART_AGILITY_THRESHOLD {
            if self.scope_level > current_level {
                self.pop_scope(self.scope_level - current_level)?;
            }
            if !self.is_inconsistent() {
                self.theory_restart_eh()?;
            }
            if !self.is_inconsistent() {
                self.qmanager_restart_eh()?;
            }
            if self.is_inconsistent() {
                self.resolve_conflict()?;
                return Ok(Some(LBool::False));
            }
        }
        Ok(None)
    }

    /// can_delete: a lemma that justifies neither of its watched literals.
    fn is_deletable(&self, clause: Clause) -> bool {
        if self.clauses.is_reinit(clause) {
            return false;
        }
        let justification = BJustification::Clause(clause);
        self.justifications[get_var(self.clauses.get_literal(clause, 0)) as usize] != justification
            && self.justifications[get_var(self.clauses.get_literal(clause, 1)) as usize]
                != justification
    }

    fn has_more_than_k_unassigned_literals(&self, clause: Clause, limit: u32) -> bool {
        let mut remaining = limit;
        for index in 0..self.clauses.get_num_literals(clause) {
            if self.assignment[self.clauses.get_literal(clause, index) as usize] == LBool::Undef {
                remaining -= 1;
                if remaining == 0 {
                    return true;
                }
            }
        }
        false
    }

    /// del_inactive_lemmas2: deletes the lemmas of the current user scope with low activity and
    /// many unassigned literals. The newest sixteenth of them tolerates more unassigned literals.
    fn del_inactive_lemmas(&mut self) -> Result<(), SmtError> {
        let mut lemmas = mem::take(&mut self.lemmas);
        let result = self.del_inactive_lemmas_of(&mut lemmas);
        self.lemmas = lemmas;
        result?;
        self.num_conflicts_since_lemma_gc = 0;
        Ok(())
    }

    fn del_inactive_lemmas_of(&mut self, lemmas: &mut Vec<Clause>) -> Result<(), SmtError> {
        let start_at = if self.base_level == 0 {
            0
        } else {
            self.base_scope_lemma_limits[self.base_level as usize - 1]
        };
        let real_size = lemmas.len() - start_at;
        let new_first_index = start_at + real_size / NEW_OLD_RATIO * (NEW_OLD_RATIO - 1);
        let mut kept = start_at;
        for index in start_at..lemmas.len() {
            let clause = lemmas[index];
            self.clauses.check_live(clause)?;
            if self.is_deletable(clause)
                && (self.clauses.is_deleted(clause)
                    || (self.clauses.get_activity(clause) < OLD_CLAUSE_ACTIVITY
                        && self.has_more_than_k_unassigned_literals(
                            clause,
                            if index >= new_first_index {
                                NEW_CLAUSE_RELEVANCY
                            } else {
                                OLD_CLAUSE_RELEVANCY
                            },
                        )))
            {
                self.delete_clause(clause)?;
                continue;
            }
            lemmas[kept] = clause;
            kept += 1;
        }
        lemmas.truncate(kept);
        Ok(())
    }

    /// push: a user scope, which pop removes with everything asserted in it.
    pub fn push(&mut self) -> Result<(), SmtError> {
        self.pop_to_base_level()?;
        self.push_scope()?;
        self.base_scope_lemma_limits.push(self.lemmas.len());
        self.base_level += 1;
        self.search_level += 1;
        Ok(())
    }

    pub fn pop(&mut self, num_scopes: u32) -> Result<(), SmtError> {
        self.pop_to_base_level()?;
        self.pop_scope(num_scopes)
    }

    /// pop_to_base_lvl: undoes the decisions of the last search, before new assertions.
    pub fn pop_to_base_level(&mut self) -> Result<(), SmtError> {
        if self.scope_level > self.base_level {
            self.pop_scope(self.scope_level - self.base_level)?;
        }
        Ok(())
    }

    /// internalize_assertions: the formulas of the asserted formulas, after preprocessing. When
    /// they are inconsistent, none is internalized and the context has an axiom conflict.
    pub fn internalize_assertions(
        &mut self,
        asserted: &mut AssertedFormulas,
    ) -> Result<(), SmtError> {
        let formulas = asserted.reduce(&mut self.m)?;
        if asserted.is_inconsistent {
            self.set_conflict(BJustification::Axiom, None);
            return Ok(());
        }
        for formula in formulas {
            if self.is_inconsistent() {
                break;
            }
            self.internalize_assertion(formula, 0)?;
        }
        Ok(())
    }

    /// init_assumptions: the search runs above a scope where the assumptions hold.
    pub fn init_assumptions(&mut self, assumptions: &[Expr]) -> Result<(), SmtError> {
        if !assumptions.is_empty() {
            self.propagate()?;
            if self.is_inconsistent() {
                return Ok(());
            }
            self.del_inactive_lemmas()?;
            self.push_scope()?;
            for assumption in assumptions {
                if self.is_inconsistent() {
                    break;
                }
                self.internalize_assertion(*assumption, 0)?;
            }
        }
        self.search_level = self.scope_level;
        Ok(())
    }

    pub fn search(&mut self) -> Result<LBool, SmtError> {
        if self.is_inconsistent() {
            return Ok(LBool::False);
        }
        self.reset_model()?;
        self.theory_init_search_eh()?;
        self.qmanager_init_search_eh()?;
        self.dyn_ack_init_search_eh()?;
        self.num_conflicts = 0;
        self.num_conflicts_since_restart = 0;
        self.num_conflicts_since_lemma_gc = 0;
        self.restart_threshold = RESTART_INITIAL;
        self.restart_outer_threshold = RESTART_INITIAL;
        self.agility = 0.0;
        self.final_check_index = 0;
        self.last_search_failure = SearchFailure::Ok;
        self.is_searching = true;
        let current_level = self.scope_level;
        let mut result = None;
        while result.is_none() {
            let status = self.bounded_search()?;
            result = if status != LBool::False && self.check_canceled() {
                Some(LBool::Undef)
            } else {
                self.restart(status, current_level)?
            };
        }
        self.is_searching = false;
        Ok(result.unwrap_or(LBool::Undef))
    }

    pub fn get_num_conflicts(&self) -> u32 {
        self.num_conflicts
    }
}

#[cfg(test)]
mod tests {
    //! Ground propositional and EUF problems, internalized from hand-built expressions and
    //! searched. The expected results and conflict counts are those of the TypeScript kernel on the
    //! same expressions, made in the same order (a script that builds each problem with
    //! `ast.ts`'s manager and `context.ts`'s `Context`, after `setupContext`).

    use prove_decide::Limits;

    use super::{Context, SmtParams};
    use crate::core::ast::{AstManager, Decl, Expr, OP_ITE, SORT_BOOL, SmtSymbol, Sort};
    use crate::core::clause::BJustification;
    use crate::core::literal::{get_var, negate};
    use crate::util::error::SmtError;
    use crate::util::lbool::LBool;
    use crate::util::rlimit::ResourceLimit;

    fn mk(relevancy_level: u32) -> Context {
        let limits = Limits::new(f64::INFINITY, None, None);
        let m = AstManager::new(ResourceLimit::new(&limits));
        let mut context = Context::new(
            m,
            SmtParams {
                is_mbqi: true,
                relevancy_level,
            },
        )
        .unwrap();
        context.setup_context().unwrap();
        context
    }

    fn mk_const(context: &mut Context, name: &str, sort: Sort) -> Expr {
        let decl = context
            .m
            .mk_func_decl(SmtSymbol::Name(name.into()), &[], sort, false);
        context.m.mk_app(decl, &[], sort).unwrap()
    }

    fn not(context: &mut Context, expr: Expr) -> Expr {
        context.m.mk_not(expr).unwrap()
    }

    fn or(context: &mut Context, args: &[Expr]) -> Expr {
        context.m.mk_or(args).unwrap()
    }

    fn eq(context: &mut Context, lhs: Expr, rhs: Expr) -> Expr {
        context.m.mk_eq(lhs, rhs).unwrap()
    }

    fn assert(context: &mut Context, expr: Expr) {
        context.internalize_assertion(expr, 0).unwrap();
    }

    /// The result, the conflicts and the steps of a search, which the TypeScript prints.
    fn search(context: &mut Context) -> (LBool, u32, u64) {
        let result = context.search().unwrap();
        (result, context.get_num_conflicts(), context.m.limit.count())
    }

    struct Euf {
        context: Context,
        sort: Sort,
        f: Decl,
        a: Expr,
        b: Expr,
        c: Expr,
    }

    impl Euf {
        fn new() -> Euf {
            let mut context = mk(2);
            let sort = context.m.mk_sort("U");
            let f = context
                .m
                .mk_func_decl(SmtSymbol::Name("f".into()), &[sort], sort, false);
            let a = mk_const(&mut context, "a", sort);
            let b = mk_const(&mut context, "b", sort);
            let c = mk_const(&mut context, "c", sort);
            Euf {
                context,
                sort,
                f,
                a,
                b,
                c,
            }
        }

        fn app(&mut self, arg: Expr) -> Expr {
            self.context.m.mk_app(self.f, &[arg], self.sort).unwrap()
        }
    }

    #[test]
    fn refutes_the_four_clauses_over_two_atoms() {
        for level in [2, 0] {
            let mut context = mk(level);
            let p = mk_const(&mut context, "p", SORT_BOOL);
            let q = mk_const(&mut context, "q", SORT_BOOL);
            let not_p = not(&mut context, p);
            let not_q = not(&mut context, q);
            for (first, second) in [(p, q), (not_p, q), (p, not_q), (not_p, not_q)] {
                let clause = or(&mut context, &[first, second]);
                assert(&mut context, clause);
            }
            assert_eq!(search(&mut context), (LBool::False, 2, 16), "level {level}");
        }
    }

    #[test]
    fn merges_by_transitivity_and_congruence() {
        let mut euf = Euf::new();
        let (a, b, c) = (euf.a, euf.b, euf.c);
        let ab = eq(&mut euf.context, a, b);
        let bc = eq(&mut euf.context, b, c);
        assert(&mut euf.context, ab);
        assert(&mut euf.context, bc);
        let fa = euf.app(a);
        let fc = euf.app(c);
        let fa_fc = eq(&mut euf.context, fa, fc);
        let diseq = not(&mut euf.context, fa_fc);
        assert(&mut euf.context, diseq);
        assert_eq!(search(&mut euf.context), (LBool::False, 1, 8));
    }

    #[test]
    fn learns_from_congruence_conflicts_in_a_case_split() {
        let mut euf = Euf::new();
        let (a, b, c) = (euf.a, euf.b, euf.c);
        let ab = eq(&mut euf.context, a, b);
        let ac = eq(&mut euf.context, a, c);
        let either = or(&mut euf.context, &[ab, ac]);
        assert(&mut euf.context, either);
        let fa = euf.app(a);
        let fb = euf.app(b);
        let fc = euf.app(c);
        for other in [fb, fc] {
            let fa_other = eq(&mut euf.context, fa, other);
            let diseq = not(&mut euf.context, fa_other);
            assert(&mut euf.context, diseq);
        }
        assert_eq!(search(&mut euf.context), (LBool::False, 2, 27));
    }

    #[test]
    fn finds_the_branch_that_congruence_allows() {
        let mut euf = Euf::new();
        let (a, b, c) = (euf.a, euf.b, euf.c);
        let ab = eq(&mut euf.context, a, b);
        let ac = eq(&mut euf.context, a, c);
        let either = or(&mut euf.context, &[ab, ac]);
        assert(&mut euf.context, either);
        let fa = euf.app(a);
        let fb = euf.app(b);
        let fa_fb = eq(&mut euf.context, fa, fb);
        let diseq = not(&mut euf.context, fa_fb);
        assert(&mut euf.context, diseq);
        assert_eq!(search(&mut euf.context), (LBool::True, 1, 34));
        let context = &euf.context;
        assert_eq!(context.find_assignment(ab), LBool::False);
        assert_eq!(context.find_assignment(ac), LBool::True);
        let (a, c) = (context.get_enode(a).unwrap(), context.get_enode(c).unwrap());
        assert_eq!(context.root(a), context.root(c));
        assert!(context.is_relevant(ac));
    }

    #[test]
    fn closes_cycles_of_function_applications() {
        let mut euf = Euf::new();
        let a = euf.a;
        let fa = euf.app(a);
        let f2 = euf.app(fa);
        let f3 = euf.app(f2);
        let f4 = euf.app(f3);
        let f5 = euf.app(f4);
        for (lhs, rhs) in [(f3, a), (f5, a)] {
            let equality = eq(&mut euf.context, lhs, rhs);
            assert(&mut euf.context, equality);
        }
        let fa_a = eq(&mut euf.context, fa, a);
        let diseq = not(&mut euf.context, fa_a);
        assert(&mut euf.context, diseq);
        assert_eq!(search(&mut euf.context), (LBool::False, 1, 10));
    }

    #[test]
    fn splits_on_the_condition_of_an_ite_term() {
        let mut euf = Euf::new();
        let (a, b, c, sort) = (euf.a, euf.b, euf.c, euf.sort);
        let context = &mut euf.context;
        let p = mk_const(context, "p", SORT_BOOL);
        let ite = context.m.mk_app(OP_ITE, &[p, a, b], sort).unwrap();
        let c_ite = eq(context, c, ite);
        assert(context, c_ite);
        for other in [a, b] {
            let equality = eq(context, c, other);
            let diseq = not(context, equality);
            assert(context, diseq);
        }
        assert_eq!(search(context), (LBool::False, 1, 16));
    }

    #[test]
    fn explains_chains_of_equalities_through_conjunctions() {
        let mut euf = Euf::new();
        let sort = euf.sort;
        let xs: Vec<Expr> = (0..6)
            .map(|index| mk_const(&mut euf.context, &format!("x{index}"), sort))
            .collect();
        let ys: Vec<Expr> = (0..6)
            .map(|index| mk_const(&mut euf.context, &format!("y{index}"), sort))
            .collect();
        for index in 0..5 {
            let context = &mut euf.context;
            let xy = eq(context, xs[index], ys[index]);
            let yx = eq(context, ys[index], xs[index + 1]);
            let both = context.m.mk_and(&[xy, yx]).unwrap();
            let xx = eq(context, xs[index], xs[index + 1]);
            let either = or(context, &[both, xx]);
            assert(context, either);
        }
        let first = euf.app(xs[0]);
        let last = euf.app(xs[5]);
        let ends = eq(&mut euf.context, first, last);
        let diseq = not(&mut euf.context, ends);
        assert(&mut euf.context, diseq);
        assert_eq!(search(&mut euf.context), (LBool::False, 6, 290));
    }

    #[test]
    fn pops_what_a_user_scope_asserted() {
        let mut context = mk(2);
        let p = mk_const(&mut context, "p", SORT_BOOL);
        assert(&mut context, p);
        context.push().unwrap();
        let not_p = not(&mut context, p);
        assert(&mut context, not_p);
        assert_eq!(context.search().unwrap(), LBool::False);
        context.pop(1).unwrap();
        assert_eq!(context.search().unwrap(), LBool::True);
        assert_eq!(context.find_assignment(p), LBool::True);
    }

    fn assert_pigeonhole(context: &mut Context, holes: usize) {
        let x: Vec<Vec<Expr>> = (0..=holes)
            .map(|i| {
                (0..holes)
                    .map(|j| mk_const(context, &format!("x{i}_{j}"), SORT_BOOL))
                    .collect()
            })
            .collect();
        for row in &x {
            let clause = or(context, row);
            assert(context, clause);
        }
        for j in 0..holes {
            for (i, row) in x.iter().enumerate() {
                for other in &x[i + 1..] {
                    let first = not(context, row[j]);
                    let second = not(context, other[j]);
                    let clause = or(context, &[first, second]);
                    assert(context, clause);
                }
            }
        }
    }

    /// Eight holes take more than LEMMA_GC_INITIAL conflicts, so the lemmas are collected.
    #[test]
    fn refutes_the_pigeonhole_principle() {
        let cases = [
            (2, 2, 24),
            (4, 26, 615),
            (5, 124, 3243),
            (6, 586, 14480),
            (7, 3372, 91422),
            (8, 23968, 647219),
        ];
        for (holes, conflicts, steps) in cases {
            let mut context = mk(2);
            assert_pigeonhole(&mut context, holes);
            assert_eq!(
                search(&mut context),
                (LBool::False, conflicts, steps),
                "{holes} holes"
            );
        }
    }

    /// 3-SAT clauses from a linear congruential generator.
    fn lcg_clauses(num_vars: u32, num_clauses: u32, seed: u32) -> Vec<Vec<(usize, bool)>> {
        let mut state = seed;
        let mut next = || {
            state = state.wrapping_mul(1103515245).wrapping_add(12345);
            state >> 8
        };
        (0..num_clauses)
            .map(|_| {
                (0..3)
                    .map(|_| ((next() % num_vars) as usize, next() % 2 == 0))
                    .collect()
            })
            .collect()
    }

    #[test]
    fn decides_random_three_sat() {
        let model = "0100010100001000001000111110000000001011";
        let other_model = "0111100110010111000001001101010001011110";
        let cases = [
            (40, 170, 1, LBool::True, 36, [1047, 1047], model),
            (40, 170, 2, LBool::True, 10, [298, 298], other_model),
            (60, 255, 3, LBool::False, 102, [2672, 2674], ""),
            (80, 340, 4, LBool::False, 151, [4903, 4903], ""),
        ];
        for (num_vars, num_clauses, seed, expected, conflicts, steps, model) in cases {
            for (level, steps) in [2, 0].into_iter().zip(steps) {
                let mut context = mk(level);
                let vars: Vec<Expr> = (0..num_vars)
                    .map(|index| mk_const(&mut context, &format!("v{index}"), SORT_BOOL))
                    .collect();
                for clause in lcg_clauses(num_vars, num_clauses, seed) {
                    let literals: Vec<Expr> = clause
                        .iter()
                        .map(|(index, is_positive)| {
                            if *is_positive {
                                vars[*index]
                            } else {
                                not(&mut context, vars[*index])
                            }
                        })
                        .collect();
                    let disjunction = or(&mut context, &literals);
                    assert(&mut context, disjunction);
                }
                let case = format!("{num_vars} {seed} {level}");
                assert_eq!(search(&mut context), (expected, conflicts, steps), "{case}");
                if expected == LBool::True {
                    let found: String = vars
                        .iter()
                        .map(|var| {
                            if context.find_assignment(*var) == LBool::True {
                                '1'
                            } else {
                                '0'
                            }
                        })
                        .collect();
                    assert_eq!(found, model, "{case}");
                }
            }
        }
    }

    /// Pigeons equal to holes, told apart by f: from five holes on, pairs of applications are the
    /// roots of enough conflicts to get Ackermann lemmas.
    #[test]
    fn counts_congruence_conflicts_for_dynamic_ackermannization() {
        let cases = [
            (3, 23, 721, 0),
            (4, 70, 2447, 0),
            (5, 216, 8634, 3),
            (6, 982, 37936, 5),
        ];
        for (holes, conflicts, steps, instances) in cases {
            let mut euf = Euf::new();
            let sort = euf.sort;
            let hs: Vec<Expr> = (0..holes)
                .map(|j| mk_const(&mut euf.context, &format!("h{j}"), sort))
                .collect();
            let ps: Vec<Expr> = (0..=holes)
                .map(|i| mk_const(&mut euf.context, &format!("p{i}"), sort))
                .collect();
            for p in &ps {
                let eqs: Vec<Expr> = hs.iter().map(|h| eq(&mut euf.context, *p, *h)).collect();
                let either = or(&mut euf.context, &eqs);
                assert(&mut euf.context, either);
            }
            for i in 0..=holes {
                for k in i + 1..=holes {
                    let first = euf.app(ps[i]);
                    let second = euf.app(ps[k]);
                    let equality = eq(&mut euf.context, first, second);
                    let diseq = not(&mut euf.context, equality);
                    assert(&mut euf.context, diseq);
                }
            }
            assert_eq!(
                search(&mut euf.context),
                (LBool::False, conflicts, steps),
                "{holes} holes"
            );
            assert_eq!(
                euf.context.dyn_ack.get_num_instances(),
                instances,
                "{holes} holes"
            );
        }
    }

    #[test]
    fn propagates_unit_clauses_and_conflicts_at_the_base_level() {
        let mut context = mk(0);
        let p = mk_const(&mut context, "p", SORT_BOOL);
        let q = mk_const(&mut context, "q", SORT_BOOL);
        let not_p = not(&mut context, p);
        let clause = or(&mut context, &[not_p, q]);
        assert(&mut context, clause);
        assert(&mut context, p);
        assert!(context.propagate().unwrap());
        let q_literal = context.get_literal(q).unwrap();
        assert_eq!(context.get_assignment(q_literal), LBool::True);
        assert_eq!(context.get_assign_level(q_literal), 0);
        assert!(matches!(
            context.justifications[get_var(q_literal) as usize],
            BJustification::BinClause(_) | BJustification::Clause(_)
        ));
        let not_q = not(&mut context, q);
        assert(&mut context, not_q);
        assert!(context.is_inconsistent());
        assert_eq!(context.search().unwrap(), LBool::False);
        assert_eq!(context.get_assignment(negate(q_literal)), LBool::False);
    }

    #[test]
    fn an_invariant_error_propagates() {
        let context = mk(2);
        assert!(matches!(
            context.get_bool_var(context.m.false_expr + 100),
            Err(SmtError::Invariant(_))
        ));
    }
}
