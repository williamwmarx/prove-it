//! Ported from Z3 (src/smt/smt_relevancy.h, src/smt/smt_relevancy.cpp), MIT license, see
//! z3-license.txt, through `relevancy.ts`. Relevancy level 2: only subterms that the current
//! assignment needs are relevant, and E-matching and the theories only look at relevant terms.
//!
//! The propagator lives in the context, and its methods that call back into the context (to read
//! an assignment, to notify a newly relevant expression, to run a handler) are associated functions
//! over a `RelevancyContext`, which reaches the propagator through `relevancy_mut`
//! (design/smt-core.md, "Interfaces passed instead of the context").

use crate::core::ast::{AstManager, Expr, KIND_APP, OP_AND, OP_IMPLIES, OP_ITE, OP_OR};
use crate::core::enode::{EnodeId, Enodes};
use crate::util::error::SmtError;
use crate::util::lbool::LBool;

/// The handlers the TypeScript stores as closures (`RelevancyHandler = () => void`), with what each
/// captures. `Context::run_relevancy_handler` applies them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RelevancyHandler {
    /// internalizer.ts's ite_term_relevancy_eh for the term `expr`, whose equalities with its
    /// branches are `then_eq` and `else_eq`.
    IteTerm {
        expr: Expr,
        then_eq: Expr,
        else_eq: Expr,
    },
    /// internalizer.ts's and_relevancy_eh: `if (isRelevant(expr)) relevancy.propagateAnd(expr)`.
    And { expr: Expr },
    /// or_relevancy_eh.
    Or { expr: Expr },
    /// ite_relevancy_eh.
    Ite { expr: Expr },
    /// `() => this.markAsRelevant(target)`: add_dependency's handler, and theory-lra-axioms.ts's
    /// simple_relevancy_eh.
    MarkAsRelevant { target: Expr },
    /// theory-lra-axioms.ts's handler of mk_axioms for an equality between `first` and `second`
    /// (their owners): once both are relevant, so are `eq`, `le` and `ge`.
    EqAxioms {
        first: Expr,
        second: Expr,
        eq: Expr,
        le: Expr,
        ge: Expr,
    },
}

/// What the propagator reads from the context and calls back.
pub trait RelevancyContext {
    fn relevancy(&self) -> &RelevancyPropagator;
    fn relevancy_mut(&mut self) -> &mut RelevancyPropagator;
    fn manager(&self) -> &AstManager;
    fn manager_mut(&mut self) -> &mut AstManager;
    /// lbool as 1, -1 or 0.
    fn find_assignment(&self, expr: Expr) -> LBool;
    fn find_enode(&self, expr: Expr) -> Option<EnodeId>;
    /// The context's nodes, to walk an equivalence class.
    fn enodes(&self) -> &Enodes;
    fn relevant_eh(&mut self, expr: Expr) -> Result<(), SmtError>;
    /// Calls a stored handler.
    fn run_relevancy_handler(&mut self, handler: RelevancyHandler) -> Result<(), SmtError>;
}

const TRAIL_POS_WATCH: u32 = 0;
const TRAIL_NEG_WATCH: u32 = 1;
const TRAIL_HANDLER: u32 = 2;

#[derive(Clone, Debug)]
pub struct RelevancyPropagator {
    qhead: usize,
    /// m_relevant_exprs: the relevant expressions in the order they were marked, which it holds.
    relevant_exprs: Vec<Expr>,
    /// A flag per expression, which grows with the expressions marked.
    is_relevant_flags: Vec<u8>,
    /// The watches and handlers of each expression, by trail kind, are lists of cons cells like
    /// Z3's relevancy_ehs. A trail entry is the cell it pushed: its handler and the list it
    /// extends. heads holds, at 3 * expr + kind, one past the trail index of the list's first cell,
    /// or 0.
    heads: Vec<u32>,
    trail_kinds: Vec<u32>,
    trail_exprs: Vec<Expr>,
    trail_handlers: Vec<RelevancyHandler>,
    trail_next: Vec<u32>,
    scopes: Vec<usize>,
    is_propagating: bool,
    pub is_enabled: bool,
}

impl RelevancyPropagator {
    /// At relevancy level 0 every expression is relevant and nothing propagates.
    pub fn new(is_enabled: bool) -> Self {
        RelevancyPropagator {
            qhead: 0,
            relevant_exprs: Vec::new(),
            is_relevant_flags: vec![0; 1024],
            heads: vec![0; 3072],
            trail_kinds: Vec::new(),
            trail_exprs: Vec::new(),
            trail_handlers: Vec::new(),
            trail_next: Vec::new(),
            scopes: Vec::new(),
            is_propagating: false,
            is_enabled,
        }
    }

    pub fn is_relevant(&self, expr: Expr) -> bool {
        !self.is_enabled || self.is_relevant_flags.get(expr as usize) == Some(&1)
    }

    pub fn add_handler(
        context: &mut impl RelevancyContext,
        source: Expr,
        handler: RelevancyHandler,
    ) -> Result<(), SmtError> {
        if !context.relevancy().is_enabled {
            return Ok(());
        }
        if context.relevancy().is_relevant(source) {
            return context.run_relevancy_handler(handler);
        }
        Self::push_trail(context, TRAIL_HANDLER, source, handler);
        Ok(())
    }

    pub fn add_dependency(
        context: &mut impl RelevancyContext,
        source: Expr,
        target: Expr,
    ) -> Result<(), SmtError> {
        if context.relevancy().is_relevant(source) {
            Self::mark_as_relevant(context, target)
        } else {
            Self::add_handler(context, source, RelevancyHandler::MarkAsRelevant { target })
        }
    }

    pub fn add_watch(
        context: &mut impl RelevancyContext,
        expr: Expr,
        value: bool,
        handler: RelevancyHandler,
    ) -> Result<(), SmtError> {
        if !context.relevancy().is_enabled {
            return Ok(());
        }
        let assignment =
            i32::from(context.find_assignment(expr).to_i8()) * if value { 1 } else { -1 };
        if assignment < 0 {
            return Ok(());
        }
        if assignment > 0 {
            return context.run_relevancy_handler(handler);
        }
        Self::push_trail(
            context,
            if value {
                TRAIL_POS_WATCH
            } else {
                TRAIL_NEG_WATCH
            },
            expr,
            handler,
        );
        Ok(())
    }

    /// push_trail: the trail holds its expressions. The cell goes in front of the expression's
    /// list.
    fn push_trail(
        context: &mut impl RelevancyContext,
        kind: u32,
        expr: Expr,
        handler: RelevancyHandler,
    ) {
        context.manager_mut().inc_ref(expr);
        let relevancy = context.relevancy_mut();
        let head = 3 * expr as usize + kind as usize;
        if head >= relevancy.heads.len() {
            let length = (2 * relevancy.heads.len()).max(3 * expr as usize + 3);
            relevancy.heads.resize(length, 0);
        }
        relevancy.trail_next.push(relevancy.heads[head]);
        relevancy.trail_handlers.push(handler);
        relevancy.trail_kinds.push(kind);
        relevancy.trail_exprs.push(expr);
        relevancy.heads[head] = relevancy.trail_kinds.len() as u32;
    }

    /// Runs the list of a kind and expression from its first cell, so the latest handler runs
    /// first. Handlers that a run adds go in front of the cell it started from, so the run skips
    /// them.
    fn run_list(
        context: &mut impl RelevancyContext,
        kind: u32,
        expr: Expr,
    ) -> Result<(), SmtError> {
        let head = 3 * expr as usize + kind as usize;
        if head >= context.relevancy().heads.len() {
            return Ok(());
        }
        let mut cell = context.relevancy().heads[head];
        while cell != 0 {
            let handler = context.relevancy().trail_handlers[cell as usize - 1];
            context.run_relevancy_handler(handler)?;
            cell = context.relevancy().trail_next[cell as usize - 1];
        }
        Ok(())
    }

    pub fn push(&mut self) {
        self.scopes.push(self.relevant_exprs.len());
        self.scopes.push(self.trail_kinds.len());
    }

    pub fn pop(&mut self, manager: &mut AstManager, num_scopes: usize) -> Result<(), SmtError> {
        let offset = self.scopes.len() - num_scopes * 2;
        let relevant_limit = self.scopes[offset];
        let trail_limit = self.scopes[offset + 1];
        for index in (relevant_limit..self.relevant_exprs.len()).rev() {
            self.is_relevant_flags[self.relevant_exprs[index] as usize] = 0;
        }
        for index in relevant_limit..self.relevant_exprs.len() {
            manager.dec_ref(self.relevant_exprs[index])?;
        }
        self.relevant_exprs.truncate(relevant_limit);
        self.qhead = relevant_limit;
        for index in (trail_limit..self.trail_kinds.len()).rev() {
            let expr = self.trail_exprs[index];
            self.heads[3 * expr as usize + self.trail_kinds[index] as usize] =
                self.trail_next[index];
            manager.dec_ref(expr)?;
        }
        self.trail_kinds.truncate(trail_limit);
        self.trail_exprs.truncate(trail_limit);
        self.trail_handlers.truncate(trail_limit);
        self.trail_next.truncate(trail_limit);
        self.scopes.truncate(offset);
        Ok(())
    }

    fn set_relevant(context: &mut impl RelevancyContext, expr: Expr) -> Result<(), SmtError> {
        let relevancy = context.relevancy_mut();
        if expr as usize >= relevancy.is_relevant_flags.len() {
            let length = (2 * relevancy.is_relevant_flags.len()).max(expr as usize + 1);
            relevancy.is_relevant_flags.resize(length, 0);
        }
        relevancy.is_relevant_flags[expr as usize] = 1;
        context.manager_mut().inc_ref(expr);
        context.relevancy_mut().relevant_exprs.push(expr);
        context.relevant_eh(expr)
    }

    /// Marks expr and every member of its equivalence class as relevant.
    pub fn mark_as_relevant(
        context: &mut impl RelevancyContext,
        expr: Expr,
    ) -> Result<(), SmtError> {
        if context.relevancy().is_relevant(expr) {
            return Ok(());
        }
        let Some(node) = context.find_enode(expr) else {
            return Self::set_relevant(context, expr);
        };
        let mut current = node;
        loop {
            let owner = context.enodes().get(current).owner;
            if !context.relevancy().is_relevant(owner) {
                Self::set_relevant(context, owner)?;
            }
            current = context.enodes().get(current).next;
            if current == node {
                return Ok(());
            }
        }
    }

    fn propagate_app(context: &mut impl RelevancyContext, expr: Expr) -> Result<(), SmtError> {
        for index in (0..context.manager().get_num_args(expr)).rev() {
            let arg = context.manager().get_arg(expr, index);
            Self::mark_as_relevant(context, arg)?;
        }
        Ok(())
    }

    pub fn propagate_implies(
        context: &mut impl RelevancyContext,
        expr: Expr,
    ) -> Result<(), SmtError> {
        let value = context.find_assignment(expr);
        if value == LBool::False {
            return Self::propagate_app(context, expr);
        }
        let first = context.manager().get_arg(expr, 0);
        if context.find_assignment(first) == LBool::False {
            return Self::mark_as_relevant(context, first);
        }
        let second = context.manager().get_arg(expr, 1);
        if context.find_assignment(second) == LBool::True {
            Self::mark_as_relevant(context, second)?;
        }
        Ok(())
    }

    pub fn propagate_or(context: &mut impl RelevancyContext, expr: Expr) -> Result<(), SmtError> {
        if context.find_assignment(expr) == LBool::False {
            return Self::propagate_app(context, expr);
        }
        let mut true_arg = -1;
        for index in 0..context.manager().get_num_args(expr) {
            let arg = context.manager().get_arg(expr, index);
            if context.find_assignment(arg) != LBool::True {
                continue;
            }
            if context.relevancy().is_relevant(arg) {
                return Ok(());
            }
            if true_arg == -1 {
                true_arg = arg;
            }
        }
        if true_arg != -1 {
            Self::mark_as_relevant(context, true_arg)?;
        }
        Ok(())
    }

    pub fn propagate_and(context: &mut impl RelevancyContext, expr: Expr) -> Result<(), SmtError> {
        let value = context.find_assignment(expr);
        if value == LBool::True {
            return Self::propagate_app(context, expr);
        }
        if value == LBool::Undef {
            return Ok(());
        }
        let mut false_arg = -1;
        for index in 0..context.manager().get_num_args(expr) {
            let arg = context.manager().get_arg(expr, index);
            if context.find_assignment(arg) != LBool::False {
                continue;
            }
            if context.relevancy().is_relevant(arg) {
                return Ok(());
            }
            if false_arg == -1 {
                false_arg = arg;
            }
        }
        if false_arg != -1 {
            Self::mark_as_relevant(context, false_arg)?;
        }
        Ok(())
    }

    pub fn propagate_ite(context: &mut impl RelevancyContext, expr: Expr) -> Result<(), SmtError> {
        let condition = context.manager().get_arg(expr, 0);
        Self::mark_as_relevant(context, condition)?;
        let value = context.find_assignment(condition);
        if value == LBool::False {
            let arg = context.manager().get_arg(expr, 2);
            Self::mark_as_relevant(context, arg)?;
        } else if value == LBool::True {
            let arg = context.manager().get_arg(expr, 1);
            Self::mark_as_relevant(context, arg)?;
        }
        Ok(())
    }

    pub fn can_propagate(&self) -> bool {
        self.qhead < self.relevant_exprs.len()
    }

    pub fn propagate(context: &mut impl RelevancyContext) -> Result<(), SmtError> {
        if context.relevancy().is_propagating {
            return Ok(());
        }
        context.relevancy_mut().is_propagating = true;
        let result = Self::propagate_core(context);
        context.relevancy_mut().is_propagating = false;
        result
    }

    fn propagate_core(context: &mut impl RelevancyContext) -> Result<(), SmtError> {
        while context.relevancy().can_propagate() {
            let relevancy = context.relevancy_mut();
            let expr = relevancy.relevant_exprs[relevancy.qhead];
            relevancy.qhead += 1;
            if context.manager().kinds[expr as usize] == KIND_APP {
                let op = context.manager().get_op(expr);
                if op == OP_OR {
                    Self::propagate_or(context, expr)?;
                } else if op == OP_AND {
                    Self::propagate_and(context, expr)?;
                } else if op == OP_IMPLIES {
                    Self::propagate_implies(context, expr)?;
                } else if op == OP_ITE {
                    Self::propagate_ite(context, expr)?;
                } else {
                    Self::propagate_app(context, expr)?;
                }
            }
            Self::run_list(context, TRAIL_HANDLER, expr)?;
        }
        Ok(())
    }

    pub fn assign_eh(
        context: &mut impl RelevancyContext,
        expr: Expr,
        value: bool,
    ) -> Result<(), SmtError> {
        if context.relevancy().is_relevant(expr) {
            let op = context.manager().get_op(expr);
            if op == OP_OR {
                Self::propagate_or(context, expr)?;
            } else if op == OP_AND {
                Self::propagate_and(context, expr)?;
            } else if op == OP_IMPLIES {
                Self::propagate_implies(context, expr)?;
            }
        }
        Self::run_list(
            context,
            if value {
                TRAIL_POS_WATCH
            } else {
                TRAIL_NEG_WATCH
            },
            expr,
        )
    }
}
