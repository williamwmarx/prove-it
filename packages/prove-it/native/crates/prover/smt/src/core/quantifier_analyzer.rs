//! Ported from Z3 (src/smt/smt_model_finder.cpp, src/ast/macros/quantifier_macro_info.cpp), MIT
//! license, through `quantifier-analyzer.ts`. The quantifier analyzer of the model finder, which
//! collects how the variables of each quantifier occur, and the quantifier info where it records
//! what it learns.
//!
//! `QuantifierInfo` keeps the context, which the model finder passes to the methods that read it
//! (the finder is out of the context while they run, `model_finder.rs`). The TypeScript compares
//! two `QInfo`s by their JSON, which is the derived equality of the enum.

use std::collections::HashSet;

use prove_num::{Int, Rational};

use crate::core::ast::{
    AstManager, Decl, Expr, FAMILY_BASIC, FAMILY_USER, KIND_APP, KIND_VAR, OP_ADD, OP_AND, OP_EQ,
    OP_GE, OP_IMPLIES, OP_ITE, OP_LE, OP_NOT, OP_OR, OP_XOR,
};
use crate::core::auf_solver::{AufSolver, InstantiationSet, NodeId};
use crate::core::context::Context;
use crate::core::model_macro_solver::{CondMacro, collect_macro_candidates, release_cond_macros};
use crate::core::pull_quant::pull_quant;
use crate::core::rewriter::Rewriter;
use crate::util::error::SmtError;
use crate::util::ordered_map::OrderedSet;

/// smt_params' mbqi_force_template: macros of quantifiers with at least this weight are used even
/// in the AUF fragment.
pub const MBQI_FORCE_TEMPLATE: i32 = 10;

/// qinfo: a bit of information about how a variable occurs in a quantifier.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum QInfo {
    FVar {
        decl: Decl,
        arg_index: u32,
        var_index: u32,
    },
    FVarPlusOffset {
        decl: Decl,
        arg_index: u32,
        var_index: u32,
        offset: Expr,
    },
    XEqY {
        first: u32,
        second: u32,
    },
    XNeqY {
        first: u32,
        second: u32,
    },
    XLeqY {
        first: u32,
        second: u32,
    },
    XEqT {
        var_index: u32,
        term: Expr,
    },
    XNeqT {
        var_index: u32,
        term: Expr,
    },
    XGleT {
        var_index: u32,
        term: Expr,
    },
}

#[derive(Clone, Copy)]
enum VarPair {
    XEqY,
    XNeqY,
    XLeqY,
}

fn mk_var_pair(kind: VarPair, first: u32, second: u32) -> QInfo {
    let (first, second) = if first > second {
        (second, first)
    } else {
        (first, second)
    };
    match kind {
        VarPair::XEqY => QInfo::XEqY { first, second },
        VarPair::XNeqY => QInfo::XNeqY { first, second },
        VarPair::XLeqY => QInfo::XLeqY { first, second },
    }
}

/// quantifier_info: what the analyzer learned about one quantifier.
pub struct QuantifierInfo {
    pub quantifier: Expr,
    pub flat_q: Expr,
    pub qinfos: Vec<QInfo>,
    pub is_auf: bool,
    pub has_x_eq_y: bool,
    pub ng_decls: OrderedSet<Decl>,
    pub the_one: Option<Decl>,
    // The sets of the variables a macro satisfies, by variable index. Like the TypeScript, they
    // are dropped without releasing their terms.
    uvar_inst_sets: Option<Vec<Option<InstantiationSet>>>,
    pub cond_macros: Vec<CondMacro>,
}

impl QuantifierInfo {
    pub fn new(
        m: &mut AstManager,
        quantifier: Expr,
        macro_rewriter: &mut Rewriter,
    ) -> Result<QuantifierInfo, SmtError> {
        // m_flat_q, which holds a reference.
        let body = m.get_quantifier(quantifier)?.body;
        let is_nested = m.has_quantifier_flags[body as usize] != 0;
        let flat_q = if is_nested {
            pull_quant(m, quantifier)?
        } else {
            quantifier
        };
        if !is_nested {
            m.inc_ref(quantifier);
        }
        let cond_macros = collect_macro_candidates(m, macro_rewriter, flat_q)?;
        Ok(QuantifierInfo {
            quantifier,
            flat_q,
            qinfos: Vec::new(),
            is_auf: true,
            has_x_eq_y: false,
            ng_decls: OrderedSet::new(),
            the_one: None,
            uvar_inst_sets: None,
            cond_macros,
        })
    }

    /// ~quantifier_info: the conditional macros go before the flat quantifier.
    pub fn release(&self, m: &mut AstManager) -> Result<(), SmtError> {
        release_cond_macros(m, &self.cond_macros)?;
        m.dec_ref(self.flat_q)
    }

    pub fn insert_q_info(&mut self, info: QInfo) {
        if !self.qinfos.contains(&info) {
            self.qinfos.push(info);
        }
    }

    pub fn process_auf(&self, m: &AstManager, solver: &mut AufSolver) -> Result<(), SmtError> {
        let flat_q = self.flat_q;
        let num_decls = m.get_quantifier(flat_q)?.sorts.len() as u32;
        for index in 0..num_decls {
            solver.get_uvar(m, flat_q, index)?;
        }
        for info in &self.qinfos {
            match *info {
                QInfo::FVar {
                    decl,
                    arg_index,
                    var_index,
                } => {
                    let a_f_i = solver.get_a_f_i(m, decl, arg_index);
                    let uvar = solver.get_uvar(m, flat_q, var_index)?;
                    solver.merge(a_f_i, uvar);
                }
                QInfo::FVarPlusOffset {
                    decl,
                    arg_index,
                    var_index,
                    ..
                } => {
                    solver.get_a_f_i(m, decl, arg_index);
                    solver.get_uvar(m, flat_q, var_index)?;
                }
                QInfo::XEqY { first, second } => {
                    let first = solver.get_uvar(m, flat_q, first)?;
                    let second = solver.get_uvar(m, flat_q, second)?;
                    solver.insert_avoid(first, second);
                    if first != second {
                        solver.insert_avoid(second, first);
                    }
                }
                QInfo::XNeqY { first, second } => {
                    let first = solver.get_uvar(m, flat_q, first)?;
                    let second = solver.get_uvar(m, flat_q, second)?;
                    solver.merge(first, second);
                }
                QInfo::XLeqY { first, second } => {
                    let first = solver.get_uvar(m, flat_q, first)?;
                    let second = solver.get_uvar(m, flat_q, second)?;
                    solver.merge(first, second);
                    solver.set_mono_proj(first);
                }
                QInfo::XEqT { var_index, term } => {
                    let node = solver.get_uvar(m, flat_q, var_index)?;
                    solver.insert_exception(node, term);
                }
                QInfo::XNeqT { var_index, .. } => {
                    solver.get_uvar(m, flat_q, var_index)?;
                }
                QInfo::XGleT { var_index, .. } => {
                    let node = solver.get_uvar(m, flat_q, var_index)?;
                    solver.set_mono_proj(node);
                }
            }
        }
        Ok(())
    }

    // The arguments at a position of the relevant applications of a declaration, with their
    // generations.
    fn get_relevant_args(context: &Context, decl: Decl, arg_index: u32) -> Vec<(Expr, u32)> {
        let mut args = Vec::new();
        for enode in context.enodes_of(decl) {
            if context.is_relevant(context.node(*enode).owner) {
                let arg = context.node(*enode).get_arg(arg_index);
                args.push((context.node(arg).owner, context.get_generation(arg)));
            }
        }
        args
    }

    fn populate_f_var(
        context: &mut Context,
        solver: &mut AufSolver,
        node: NodeId,
        decl: Decl,
        arg_index: u32,
    ) {
        for (arg, generation) in QuantifierInfo::get_relevant_args(context, decl, arg_index) {
            solver.insert(&mut context.m, node, arg, generation);
        }
    }

    pub fn populate_inst_sets(
        &self,
        context: &mut Context,
        solver: &mut AufSolver,
    ) -> Result<(), SmtError> {
        let flat_q = self.flat_q;
        let sorts = context.m.get_quantifier(flat_q)?.sorts.clone();
        for info in &self.qinfos {
            match *info {
                QInfo::FVar {
                    decl, arg_index, ..
                } => {
                    let node = solver.get_a_f_i(&context.m, decl, arg_index);
                    QuantifierInfo::populate_f_var(context, solver, node, decl, arg_index);
                }
                QInfo::FVarPlusOffset {
                    decl,
                    arg_index,
                    var_index,
                    offset,
                } => {
                    let a_f_i = solver.get_a_f_i(&context.m, decl, arg_index);
                    let a_f_i = solver.get_root(a_f_i);
                    let s_j = solver.get_uvar(&context.m, flat_q, var_index)?;
                    let s_j = solver.get_root(s_j);
                    if a_f_i == s_j {
                        // There is no finite fixpoint, so the arguments minus the offset join the
                        // set.
                        for (arg, generation) in
                            QuantifierInfo::get_relevant_args(context, decl, arg_index)
                        {
                            let term = solver.rewriter.mk_sub(&mut context.m, arg, offset)?;
                            solver.insert(&mut context.m, s_j, term, generation);
                        }
                    } else {
                        QuantifierInfo::populate_f_var(context, solver, a_f_i, decl, arg_index);
                        if solver.is_mono_proj(a_f_i) {
                            solver.set_mono_proj(s_j);
                        }
                        if solver.is_mono_proj(s_j) {
                            solver.set_mono_proj(a_f_i);
                        }
                    }
                }
                QInfo::XEqT { var_index, .. } => {
                    let sort = sorts[sorts.len() - var_index as usize - 1];
                    if context.m.is_uninterpreted_sort(sort) {
                        // Every term of the sort joins the set, see Section 4.1 of the paper.
                        let node = solver.get_uvar(&context.m, flat_q, var_index)?;
                        let mut terms = Vec::new();
                        for enode in &context.enodes {
                            let owner = context.node(*enode).owner;
                            if context.is_relevant(owner) && context.m.sorts[owner as usize] == sort
                            {
                                terms.push((owner, context.get_generation(*enode)));
                            }
                        }
                        for (term, generation) in terms {
                            solver.insert(&mut context.m, node, term, generation);
                        }
                    }
                }
                QInfo::XNeqT { var_index, term } | QInfo::XGleT { var_index, term } => {
                    let node = solver.get_uvar(&context.m, flat_q, var_index)?;
                    solver.insert(&mut context.m, node, term, 0);
                }
                _ => {}
            }
        }
        // The second pass for the offsets: A_f_i - k is in S_j and S_j + k is in A_f_i.
        for info in &self.qinfos {
            let QInfo::FVarPlusOffset {
                decl,
                arg_index,
                var_index,
                offset,
            } = *info
            else {
                continue;
            };
            let a_f_i = solver.get_a_f_i(&context.m, decl, arg_index);
            let a_f_i = solver.get_root(a_f_i);
            let s_j = solver.get_uvar(&context.m, flat_q, var_index)?;
            let s_j = solver.get_root(s_j);
            if a_f_i == s_j {
                continue;
            }
            QuantifierInfo::copy_instances(&mut context.m, solver, a_f_i, s_j, offset, false)?;
            QuantifierInfo::copy_instances(&mut context.m, solver, s_j, a_f_i, offset, true)?;
        }
        Ok(())
    }

    fn copy_instances(
        m: &mut AstManager,
        solver: &mut AufSolver,
        from: NodeId,
        to: NodeId,
        offset: Expr,
        is_plus: bool,
    ) -> Result<(), SmtError> {
        for (term, generation) in solver.get_instantiation_set(from)?.get_elems() {
            let term = if is_plus {
                solver.rewriter.mk_add(m, &[term, offset])?
            } else {
                solver.rewriter.mk_sub(m, term, offset)?
            };
            solver.insert(m, to, term, generation);
        }
        Ok(())
    }

    /// populate_macro_based_inst_sets: makes the sets of the variables a macro satisfies, once
    /// per model.
    pub fn mk_macro_based_inst_sets(
        &mut self,
        context: &mut Context,
        solver: &mut AufSolver,
    ) -> Result<(), SmtError> {
        let Some(the_one) = self.the_one else {
            return Ok(());
        };
        if self.uvar_inst_sets.is_some() {
            return Ok(());
        }
        let mut sets: Vec<Option<InstantiationSet>> = Vec::new();
        for info in &self.qinfos {
            let QInfo::FVar {
                decl,
                arg_index,
                var_index,
            } = *info
            else {
                continue;
            };
            if decl != the_one {
                continue;
            }
            let var_index = var_index as usize;
            if sets.len() <= var_index {
                sets.resize_with(var_index + 1, || None);
            }
            let set = sets[var_index].get_or_insert_with(InstantiationSet::new);
            for (arg, generation) in QuantifierInfo::get_relevant_args(context, decl, arg_index) {
                set.insert(&mut context.m, arg, generation);
            }
        }
        for set in sets.iter_mut().flatten() {
            set.mk_inverse(&mut context.m, |m, expr| solver.eval(m, expr, true))?;
        }
        self.uvar_inst_sets = Some(sets);
        Ok(())
    }

    /// The set of a variable that a macro satisfies, once `mk_macro_based_inst_sets` made them.
    pub fn get_macro_based_inst_set(&self, var_index: u32) -> Option<&InstantiationSet> {
        self.the_one?;
        self.uvar_inst_sets
            .as_ref()
            .and_then(|sets| sets.get(var_index as usize))
            .and_then(Option::as_ref)
    }

    pub fn reset_the_one(&mut self) {
        self.the_one = None;
        self.uvar_inst_sets = None;
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Polarity {
    Pos,
    Neg,
}

/// A variable and a ground term found in an atom, and whether the variable was negated.
struct VarAndGround {
    variable: Expr,
    term: Expr,
    is_inverted: bool,
}

/// quantifier_analyzer. One analyzer runs per quantifier and records what it learns in the
/// quantifier's info.
#[derive(Default)]
pub struct QuantifierAnalyzer {
    // Only looked up, never iterated.
    pos_cache: HashSet<Expr>,
    neg_cache: HashSet<Expr>,
    ftodo: Vec<(Expr, Polarity)>,
    ttodo: Vec<Expr>,
}

impl QuantifierAnalyzer {
    pub fn new() -> QuantifierAnalyzer {
        QuantifierAnalyzer::default()
    }

    fn is_var(m: &AstManager, expr: Expr) -> bool {
        m.kinds[expr as usize] == KIND_VAR
    }

    // poly_rewriter::is_var_plus_ground.
    fn is_var_plus_ground(
        m: &mut AstManager,
        rewriter: &mut Rewriter,
        expr: Expr,
    ) -> Result<Option<VarAndGround>, SmtError> {
        if m.get_op(expr) != OP_ADD || m.is_ground(expr) {
            return Ok(None);
        }
        let mut args = Vec::new();
        let mut variable = None;
        let mut is_inverted = false;
        let mut current = expr;
        let mut is_stopped = false;
        while !is_stopped {
            let arg = if m.get_op(current) == OP_ADD {
                let arg = m.get_arg(current, 0);
                current = m.get_arg(current, 1);
                arg
            } else {
                is_stopped = true;
                current
            };
            let negated = m.get_times_minus_one_arg(arg);
            if m.is_ground(arg) {
                args.push(arg);
            } else if QuantifierAnalyzer::is_var(m, arg) {
                if variable.is_some() {
                    return Ok(None);
                }
                variable = Some(arg);
            } else if let Some(negated) = negated
                && QuantifierAnalyzer::is_var(m, negated)
            {
                if variable.is_some() {
                    return Ok(None);
                }
                variable = Some(negated);
                is_inverted = true;
            } else {
                return Ok(None);
            }
        }
        let Some(variable) = variable else {
            return Ok(None);
        };
        let term = if args.len() == 1 {
            args[0]
        } else {
            rewriter.mk_add(m, &args)?
        };
        Ok(Some(VarAndGround {
            variable,
            term,
            is_inverted,
        }))
    }

    fn is_var_and_ground(
        m: &mut AstManager,
        rewriter: &mut Rewriter,
        lhs: Expr,
        rhs: Expr,
    ) -> Result<Option<VarAndGround>, SmtError> {
        if QuantifierAnalyzer::is_var(m, lhs) && m.is_ground(rhs) {
            return Ok(Some(VarAndGround {
                variable: lhs,
                term: rhs,
                is_inverted: false,
            }));
        }
        if QuantifierAnalyzer::is_var(m, rhs) && m.is_ground(lhs) {
            return Ok(Some(VarAndGround {
                variable: rhs,
                term: lhs,
                is_inverted: false,
            }));
        }
        let left = QuantifierAnalyzer::is_var_plus_ground(m, rewriter, lhs)?;
        if let Some(left) = left
            && m.is_ground(rhs)
        {
            let term = if left.is_inverted {
                rewriter.mk_sub(m, left.term, rhs)?
            } else {
                rewriter.mk_sub(m, rhs, left.term)?
            };
            return Ok(Some(VarAndGround {
                variable: left.variable,
                term,
                is_inverted: left.is_inverted,
            }));
        }
        let right = QuantifierAnalyzer::is_var_plus_ground(m, rewriter, rhs)?;
        if let Some(right) = right
            && m.is_ground(lhs)
        {
            let term = if right.is_inverted {
                rewriter.mk_sub(m, right.term, lhs)?
            } else {
                rewriter.mk_sub(m, lhs, right.term)?
            };
            return Ok(Some(VarAndGround {
                variable: right.variable,
                term,
                is_inverted: right.is_inverted,
            }));
        }
        Ok(None)
    }

    fn is_var_minus_var(m: &AstManager, expr: Expr) -> Option<(Expr, Expr)> {
        if m.get_op(expr) != OP_ADD {
            return None;
        }
        let mut first = m.get_arg(expr, 0);
        let mut second = m.get_arg(expr, 1);
        if !QuantifierAnalyzer::is_var(m, first) {
            std::mem::swap(&mut first, &mut second);
        }
        if !QuantifierAnalyzer::is_var(m, first) {
            return None;
        }
        let negated = m.get_times_minus_one_arg(second)?;
        if !QuantifierAnalyzer::is_var(m, negated) {
            return None;
        }
        Some((first, negated))
    }

    fn is_zero(m: &AstManager, expr: Expr) -> bool {
        m.get_numeral(expr).is_some_and(Int::is_zero)
    }

    fn is_var_and_var(m: &AstManager, lhs: Expr, rhs: Expr) -> Option<(Expr, Expr)> {
        if QuantifierAnalyzer::is_var(m, lhs) && QuantifierAnalyzer::is_var(m, rhs) {
            return Some((lhs, rhs));
        }
        if let Some(left) = QuantifierAnalyzer::is_var_minus_var(m, lhs)
            && QuantifierAnalyzer::is_zero(m, rhs)
        {
            return Some(left);
        }
        if let Some(right) = QuantifierAnalyzer::is_var_minus_var(m, rhs)
            && QuantifierAnalyzer::is_zero(m, lhs)
        {
            return Some(right);
        }
        None
    }

    fn is_le_ge(m: &AstManager, expr: Expr) -> bool {
        let op = m.get_op(expr);
        op == OP_LE || op == OP_GE
    }

    fn is_x_gle_t_atom(
        m: &mut AstManager,
        rewriter: &mut Rewriter,
        atom: Expr,
        is_negated: bool,
    ) -> Result<Option<(Expr, Expr)>, SmtError> {
        if m.kinds[atom as usize] != KIND_APP || !QuantifierAnalyzer::is_le_ge(m, atom) {
            return Ok(None);
        }
        let Some(found) = QuantifierAnalyzer::is_var_and_ground(
            m,
            rewriter,
            m.get_arg(atom, 0),
            m.get_arg(atom, 1),
        )?
        else {
            return Ok(None);
        };
        if is_negated {
            return Ok(Some((found.variable, found.term)));
        }
        let is_le = (m.get_op(atom) == OP_LE) != found.is_inverted;
        let sort = m.sorts[found.term as usize];
        let one = m.mk_numeral_of_sort(&Rational::one(), sort);
        let term = if is_le {
            rewriter.mk_add(m, &[found.term, one])?
        } else {
            rewriter.mk_sub(m, found.term, one)?
        };
        Ok(Some((found.variable, term)))
    }

    fn visit_formula(&mut self, m: &AstManager, expr: Expr, polarity: Polarity) {
        if m.is_ground(expr) {
            return;
        }
        let cache = match polarity {
            Polarity::Pos => &mut self.pos_cache,
            Polarity::Neg => &mut self.neg_cache,
        };
        if !cache.insert(expr) {
            return;
        }
        self.ftodo.push((expr, polarity));
    }

    fn visit_term(&mut self, m: &AstManager, expr: Expr) {
        if m.is_ground(expr) || !self.pos_cache.insert(expr) {
            return;
        }
        self.ttodo.push(expr);
    }

    fn process_u_app(
        &mut self,
        m: &mut AstManager,
        rewriter: &mut Rewriter,
        info: &mut QuantifierInfo,
        expr: Expr,
    ) -> Result<(), SmtError> {
        let decl = m.decls[expr as usize];
        for index in 0..m.get_num_args(expr) {
            let arg = m.get_arg(expr, index);
            if QuantifierAnalyzer::is_var(m, arg) {
                info.insert_q_info(QInfo::FVar {
                    decl,
                    arg_index: index as u32,
                    var_index: m.values[arg as usize] as u32,
                });
                continue;
            }
            if let Some(found) = QuantifierAnalyzer::is_var_plus_ground(m, rewriter, arg)?
                && !found.is_inverted
            {
                info.insert_q_info(QInfo::FVarPlusOffset {
                    decl,
                    arg_index: index as u32,
                    var_index: m.values[found.variable as usize] as u32,
                    offset: found.term,
                });
                continue;
            }
            self.visit_term(m, arg);
        }
        Ok(())
    }

    fn process_app(
        &mut self,
        m: &mut AstManager,
        rewriter: &mut Rewriter,
        info: &mut QuantifierInfo,
        expr: Expr,
    ) -> Result<(), SmtError> {
        let decl = m.decls[expr as usize];
        let family = m.func_decls[decl as usize].family;
        if family != FAMILY_BASIC {
            info.ng_decls.insert(decl);
        }
        if family == FAMILY_USER {
            return self.process_u_app(m, rewriter, info, expr);
        }
        for index in 0..m.get_num_args(expr) {
            self.visit_term(m, m.get_arg(expr, index));
        }
        Ok(())
    }

    fn process_terms_on_stack(
        &mut self,
        m: &mut AstManager,
        rewriter: &mut Rewriter,
        info: &mut QuantifierInfo,
    ) -> Result<(), SmtError> {
        while let Some(current) = self.ttodo.pop() {
            if m.is_bool(current) {
                self.visit_formula(m, current, Polarity::Pos);
                self.visit_formula(m, current, Polarity::Neg);
                continue;
            }
            if m.kinds[current as usize] == KIND_APP {
                self.process_app(m, rewriter, info, current)?;
            } else if QuantifierAnalyzer::is_var(m, current) {
                info.is_auf = false;
            }
        }
        Ok(())
    }

    fn process_literal(
        &mut self,
        m: &mut AstManager,
        rewriter: &mut Rewriter,
        info: &mut QuantifierInfo,
        atom: Expr,
        is_negated: bool,
    ) -> Result<(), SmtError> {
        if QuantifierAnalyzer::is_var(m, atom) {
            info.insert_q_info(QInfo::XNeqT {
                var_index: m.values[atom as usize] as u32,
                term: if is_negated {
                    m.true_expr
                } else {
                    m.false_expr
                },
            });
            return Ok(());
        }
        if m.kinds[atom as usize] != KIND_APP {
            return Ok(());
        }
        let is_eq = m.get_op(atom) == OP_EQ;
        let x_eq_t = if is_eq {
            QuantifierAnalyzer::is_var_and_ground(
                m,
                rewriter,
                m.get_arg(atom, 0),
                m.get_arg(atom, 1),
            )?
        } else {
            None
        };
        if let Some(x_eq_t) = x_eq_t {
            let var_index = m.values[x_eq_t.variable as usize] as u32;
            info.insert_q_info(if is_negated {
                QInfo::XNeqT {
                    var_index,
                    term: x_eq_t.term,
                }
            } else {
                QInfo::XEqT {
                    var_index,
                    term: x_eq_t.term,
                }
            });
            return Ok(());
        }
        let x_eq_y = if is_eq {
            QuantifierAnalyzer::is_var_and_var(m, m.get_arg(atom, 0), m.get_arg(atom, 1))
        } else {
            None
        };
        if let Some((first, second)) = x_eq_y {
            let first = m.values[first as usize] as u32;
            let second = m.values[second as usize] as u32;
            if is_negated {
                info.insert_q_info(mk_var_pair(VarPair::XNeqY, first, second));
            } else {
                info.has_x_eq_y = true;
                info.insert_q_info(mk_var_pair(VarPair::XEqY, first, second));
            }
            return Ok(());
        }
        let x_le_y = if is_negated && QuantifierAnalyzer::is_le_ge(m, atom) {
            QuantifierAnalyzer::is_var_and_var(m, m.get_arg(atom, 0), m.get_arg(atom, 1))
        } else {
            None
        };
        if let Some((first, second)) = x_le_y {
            info.insert_q_info(mk_var_pair(
                VarPair::XLeqY,
                m.values[first as usize] as u32,
                m.values[second as usize] as u32,
            ));
            return Ok(());
        }
        if let Some((variable, term)) =
            QuantifierAnalyzer::is_x_gle_t_atom(m, rewriter, atom, is_negated)?
        {
            info.insert_q_info(QInfo::XGleT {
                var_index: m.values[variable as usize] as u32,
                term,
            });
            return Ok(());
        }
        self.process_app(m, rewriter, info, atom)
    }

    fn process_formulas_on_stack(
        &mut self,
        m: &mut AstManager,
        rewriter: &mut Rewriter,
        info: &mut QuantifierInfo,
    ) -> Result<(), SmtError> {
        while let Some((current, polarity)) = self.ftodo.pop() {
            let negated = match polarity {
                Polarity::Pos => Polarity::Neg,
                Polarity::Neg => Polarity::Pos,
            };
            let is_neg = polarity == Polarity::Neg;
            if m.kinds[current as usize] == KIND_VAR {
                self.process_literal(m, rewriter, info, current, is_neg)?;
                continue;
            }
            if m.kinds[current as usize] != KIND_APP {
                continue;
            }
            if m.get_family(current) != FAMILY_BASIC || !m.is_bool(current) {
                self.process_literal(m, rewriter, info, current, is_neg)?;
                continue;
            }
            match m.get_op(current) {
                OP_IMPLIES => {
                    self.process_literal(
                        m,
                        rewriter,
                        info,
                        m.get_arg(current, 0),
                        negated == Polarity::Neg,
                    )?;
                    self.process_literal(m, rewriter, info, m.get_arg(current, 1), is_neg)?;
                }
                OP_XOR => {
                    for index in 0..m.get_num_args(current) {
                        let arg = m.get_arg(current, index);
                        self.visit_formula(m, arg, polarity);
                        self.visit_formula(m, arg, negated);
                    }
                }
                OP_OR | OP_AND => {
                    for index in 0..m.get_num_args(current) {
                        self.visit_formula(m, m.get_arg(current, index), polarity);
                    }
                }
                OP_NOT => self.visit_formula(m, m.get_arg(current, 0), negated),
                OP_ITE => {
                    self.visit_formula(m, m.get_arg(current, 0), polarity);
                    self.visit_formula(m, m.get_arg(current, 0), negated);
                    self.visit_formula(m, m.get_arg(current, 1), polarity);
                    self.visit_formula(m, m.get_arg(current, 2), polarity);
                }
                OP_EQ => {
                    if m.is_bool(m.get_arg(current, 0)) {
                        for index in 0..m.get_num_args(current) {
                            let arg = m.get_arg(current, index);
                            self.visit_formula(m, arg, Polarity::Pos);
                            self.visit_formula(m, arg, Polarity::Neg);
                        }
                    } else {
                        self.process_literal(m, rewriter, info, current, is_neg)?;
                    }
                }
                _ => self.process_literal(m, rewriter, info, current, is_neg)?,
            }
        }
        Ok(())
    }

    // is_clause: a disjunction of literals.
    fn is_literal(m: &AstManager, expr: Expr) -> bool {
        let atom = if m.is_not(expr) {
            m.get_arg(expr, 0)
        } else {
            expr
        };
        if m.kinds[atom as usize] != KIND_APP {
            return m.kinds[atom as usize] == KIND_VAR;
        }
        if m.get_family(atom) != FAMILY_BASIC {
            return true;
        }
        let op = m.get_op(atom);
        if op == OP_EQ {
            return !m.is_bool(m.get_arg(atom, 0));
        }
        m.get_num_args(atom) == 0
    }

    pub fn analyze(
        &mut self,
        m: &mut AstManager,
        rewriter: &mut Rewriter,
        info: &mut QuantifierInfo,
    ) -> Result<(), SmtError> {
        let body = m.get_quantifier(info.flat_q)?.body;
        let literals = if m.get_op(body) == OP_OR {
            m.get_args(body)
        } else {
            vec![body]
        };
        if literals
            .iter()
            .all(|literal| QuantifierAnalyzer::is_literal(m, *literal))
        {
            for literal in literals {
                let is_negated = m.is_not(literal);
                let atom = if is_negated {
                    m.get_arg(literal, 0)
                } else {
                    literal
                };
                if !m.is_ground(atom) {
                    self.process_literal(m, rewriter, info, atom, is_negated)?;
                }
            }
        } else {
            self.visit_formula(m, body, Polarity::Pos);
        }
        while !self.ftodo.is_empty() || !self.ttodo.is_empty() {
            self.process_formulas_on_stack(m, rewriter, info)?;
            self.process_terms_on_stack(m, rewriter, info)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use prove_decide::Limits;

    use super::{QInfo, QuantifierAnalyzer, QuantifierInfo};
    use crate::core::ast::{AstManager, Expr, QuantifierData, SORT_BOOL, SmtSymbol, Sort};
    use crate::core::rewriter::{Rewriter, TACTIC_REWRITER_OPTIONS};
    use crate::util::rlimit::ResourceLimit;

    fn mk_manager() -> AstManager {
        AstManager::new(ResourceLimit::new(&Limits::new(f64::INFINITY, None, None)))
    }

    fn forall(m: &mut AstManager, sort: Sort, num_vars: usize, body: Expr) -> Expr {
        m.mk_quantifier(QuantifierData {
            is_forall: true,
            sorts: vec![sort; num_vars],
            names: (0..num_vars)
                .map(|index| SmtSymbol::Name(format!("x{index}")))
                .collect(),
            body,
            patterns: Vec::new(),
            weight: 0,
            qid: String::new(),
        })
        .unwrap()
    }

    fn analyze(m: &mut AstManager, quantifier: Expr) -> QuantifierInfo {
        let mut macro_rewriter = Rewriter::new(m, TACTIC_REWRITER_OPTIONS, false);
        let mut rewriter = Rewriter::new(m, TACTIC_REWRITER_OPTIONS, false);
        let mut info = QuantifierInfo::new(m, quantifier, &mut macro_rewriter).unwrap();
        QuantifierAnalyzer::new()
            .analyze(m, &mut rewriter, &mut info)
            .unwrap();
        info
    }

    #[test]
    fn records_how_the_variables_of_a_clause_occur() {
        // ∀x y. x = y ∨ ¬r(x, y) ∨ f(x) ≠ a.
        let m = &mut mk_manager();
        let u = m.mk_sort("U");
        let r = m.mk_func_decl(SmtSymbol::Name("r".into()), &[u, u], SORT_BOOL, false);
        let f = m.mk_func_decl(SmtSymbol::Name("f".into()), &[u], u, false);
        let a_decl = m.mk_func_decl(SmtSymbol::Name("a".into()), &[], u, false);
        let a = m.mk_app(a_decl, &[], u).unwrap();
        let x = m.mk_var(1, u);
        let y = m.mk_var(0, u);
        let xy = m.mk_eq(x, y).unwrap();
        let rxy = m.mk_app(r, &[x, y], SORT_BOOL).unwrap();
        let not_rxy = m.mk_not(rxy).unwrap();
        let fx = m.mk_app(f, &[x], u).unwrap();
        let fxa = m.mk_eq(fx, a).unwrap();
        let not_fxa = m.mk_not(fxa).unwrap();
        let body = m.mk_or(&[xy, not_rxy, not_fxa]).unwrap();
        let quantifier = forall(m, u, 2, body);
        let info = analyze(m, quantifier);
        assert_eq!(
            info.qinfos,
            [
                QInfo::XEqY {
                    first: 0,
                    second: 1
                },
                QInfo::FVar {
                    decl: r,
                    arg_index: 0,
                    var_index: 1
                },
                QInfo::FVar {
                    decl: r,
                    arg_index: 1,
                    var_index: 0
                },
                QInfo::FVar {
                    decl: f,
                    arg_index: 0,
                    var_index: 1
                },
            ]
        );
        assert_eq!(info.ng_decls.iter().copied().collect::<Vec<_>>(), [r, f]);
        assert!(info.is_auf && info.has_x_eq_y);
        assert!(info.cond_macros.is_empty());
        assert_eq!(info.flat_q, quantifier);
    }

    #[test]
    fn collects_a_macro_for_each_side_of_an_equation() {
        // ∀x. f(x) = g(x).
        let m = &mut mk_manager();
        let u = m.mk_sort("U");
        let f = m.mk_func_decl(SmtSymbol::Name("f".into()), &[u], u, false);
        let g = m.mk_func_decl(SmtSymbol::Name("g".into()), &[u], u, false);
        let x = m.mk_var(0, u);
        let fx = m.mk_app(f, &[x], u).unwrap();
        let gx = m.mk_app(g, &[x], u).unwrap();
        let body = m.mk_eq(fx, gx).unwrap();
        let quantifier = forall(m, u, 1, body);
        m.inc_ref(quantifier);
        let info = analyze(m, quantifier);
        let macros: Vec<_> = info
            .cond_macros
            .iter()
            .map(|macro_| (macro_.decl, macro_.def, macro_.cond, macro_.is_hint))
            .collect();
        assert_eq!(
            macros,
            [
                (f, gx, Some(m.true_expr), false),
                (g, fx, Some(m.true_expr), false)
            ]
        );
        // The terms of the equation are visited from a stack, the last first.
        assert_eq!(
            info.qinfos,
            [
                QInfo::FVar {
                    decl: g,
                    arg_index: 0,
                    var_index: 0
                },
                QInfo::FVar {
                    decl: f,
                    arg_index: 0,
                    var_index: 0
                },
            ]
        );
        // The info holds the quantifier and each macro's definition.
        let count = m.get_ref_count(gx);
        info.release(m).unwrap();
        assert_eq!(m.get_ref_count(gx), count - 1);
        assert_eq!(m.get_ref_count(quantifier), 1);
    }
}
