//! Ported from Z3 (src/smt/smt_model_finder.cpp), MIT license, through `model-finder.ts`.
//! Completes the model of the ground formulas so that it may satisfy the universal quantifiers,
//! following "Complete instantiation for quantified SMT formulas": the quantifier analyzer collects
//! how the variables occur, and the AUF solver gives each group of argument positions and variables
//! a projection function onto its instantiation set.
//!
//! `ModelFinder` keeps the context, so (design/smt-core.md, "The context") its state is a struct
//! held by the quantifier manager. Its methods that read the context take it as an argument: the
//! `impl Context` methods `model_finder_<method>`, which the quantifier manager calls, move the
//! finder (with the model checker) out of the quantifier manager's `mbqi` while they run and put it
//! back after; nothing they reach in the context reads `mbqi` meanwhile (they internalize only
//! ground terms, so no quantifier is registered).

use std::collections::HashMap;

use crate::core::ast::{AstManager, Expr, OP_OR, SORT_BOOL};
use crate::core::auf_solver::{AufSolver, InstantiationSet};
use crate::core::clause::BJustification;
use crate::core::context::Context;
use crate::core::model_macro_solver::solve_macros;
use crate::core::proto_model::ProtoModelRef;
use crate::core::quantifier_analyzer::{MBQI_FORCE_TEMPLATE, QuantifierAnalyzer, QuantifierInfo};
use crate::core::ref_vector::RefVector;
use crate::core::rewriter::{Rewriter, TACTIC_REWRITER_OPTIONS};
use crate::util::error::SmtError;
use crate::util::lbool::LBool;

pub struct ModelFinder {
    // Only looked up, never iterated.
    q2info: HashMap<Expr, QuantifierInfo>,
    quantifiers: Vec<Expr>,
    scopes: Vec<usize>,
    // m_mutil of quantifier_analyzer: macro_util's rewriting, kept apart from the rewriter of the
    // AUF solver so that its last result is never released early.
    macro_rewriter: Rewriter,
    pub auf_solver: AufSolver,
}

impl ModelFinder {
    /// `new ModelFinder(manager, context)`: its rewriters and its AUF solver, whose constructor
    /// takes one step.
    pub fn new(m: &mut AstManager) -> ModelFinder {
        let rewriter = Rewriter::new(m, TACTIC_REWRITER_OPTIONS, false);
        let macro_rewriter = Rewriter::new(m, TACTIC_REWRITER_OPTIONS, false);
        let auf_solver = AufSolver::new(m, rewriter);
        ModelFinder {
            q2info: HashMap::new(),
            quantifiers: Vec::new(),
            scopes: Vec::new(),
            macro_rewriter,
            auf_solver,
        }
    }

    pub fn get_quantifier_info(
        &mut self,
        m: &mut AstManager,
        quantifier: Expr,
    ) -> Result<&mut QuantifierInfo, SmtError> {
        if !self.q2info.contains_key(&quantifier) {
            self.register_quantifier(m, quantifier)?;
        }
        self.q2info
            .get_mut(&quantifier)
            .ok_or_else(|| SmtError::Invariant("the quantifier has no info".into()))
    }

    pub fn register_quantifier(
        &mut self,
        m: &mut AstManager,
        quantifier: Expr,
    ) -> Result<(), SmtError> {
        let mut info = QuantifierInfo::new(m, quantifier, &mut self.macro_rewriter)?;
        self.quantifiers.push(quantifier);
        QuantifierAnalyzer::new().analyze(m, &mut self.auf_solver.rewriter, &mut info)?;
        self.q2info.insert(quantifier, info);
        Ok(())
    }

    pub fn push_scope(&mut self) {
        self.scopes.push(self.quantifiers.len());
    }

    pub fn pop_scope(&mut self, m: &mut AstManager, num_scopes: u32) -> Result<(), SmtError> {
        if num_scopes == 0 {
            return Ok(());
        }
        let new_len = self
            .scopes
            .len()
            .checked_sub(num_scopes as usize)
            .ok_or_else(|| SmtError::Invariant("the model finder pops a missing scope".into()))?;
        let limit = self.scopes[new_len];
        for index in limit..self.quantifiers.len() {
            if let Some(info) = self.q2info.remove(&self.quantifiers[index]) {
                info.release(m)?;
            }
        }
        self.quantifiers.truncate(limit);
        self.scopes.truncate(new_len);
        Ok(())
    }

    /// fix_model: tries to satisfy the relevant quantifiers by changing the model while keeping
    /// the ground formulas satisfied.
    pub fn fix_model(
        &mut self,
        context: &mut Context,
        model: &ProtoModelRef,
    ) -> Result<(), SmtError> {
        if self.quantifiers.is_empty() {
            return Ok(());
        }
        let mut quantifiers = Vec::new();
        for quantifier in &self.quantifiers {
            if context.is_relevant(*quantifier)
                && context.get_assignment(context.get_literal(*quantifier)?) == LBool::True
            {
                quantifiers.push(*quantifier);
            }
        }
        if quantifiers.is_empty() {
            return Ok(());
        }
        for quantifier in &quantifiers {
            self.get_quantifier_info(&mut context.m, *quantifier)?
                .reset_the_one();
        }
        let residue = solve_macros(
            &mut context.m,
            model,
            quantifiers,
            &mut self.q2info,
            MBQI_FORCE_TEMPLATE,
        )?;
        self.auf_solver.reset(&mut context.m)?;
        self.auf_solver.set_model(&mut context.m, model)?;
        for quantifier in &residue {
            self.get_quantifier_info(&mut context.m, *quantifier)?;
            if let Some(info) = self.q2info.get(quantifier) {
                info.process_auf(&context.m, &mut self.auf_solver)?;
            }
        }
        self.auf_solver.mk_instantiation_sets();
        for quantifier in &residue {
            self.get_quantifier_info(&mut context.m, *quantifier)?;
            if let Some(info) = self.q2info.get(quantifier) {
                info.populate_inst_sets(context, &mut self.auf_solver)?;
            }
        }
        self.auf_solver.fix_model(&mut context.m)
    }

    pub fn get_flat_quantifier(
        &mut self,
        m: &mut AstManager,
        quantifier: Expr,
    ) -> Result<Expr, SmtError> {
        Ok(self.get_quantifier_info(m, quantifier)?.flat_q)
    }

    /// get_uvar_inst_set: the set of variable index of the quantifier before flattening.
    pub fn get_uvar_inst_set(
        &mut self,
        context: &mut Context,
        quantifier: Expr,
        index: u32,
    ) -> Result<Option<&InstantiationSet>, SmtError> {
        let flat_q = self.get_flat_quantifier(&mut context.m, quantifier)?;
        let offset = context.m.get_quantifier(flat_q)?.sorts.len()
            - context.m.get_quantifier(quantifier)?.sorts.len();
        let flat_index = offset as u32 + index;
        if self.auf_solver.has_uvar(flat_q, flat_index) {
            return self.auf_solver.get_uvar_inst_set(flat_q, flat_index);
        }
        self.get_quantifier_info(&mut context.m, quantifier)?;
        let Some(info) = self.q2info.get_mut(&quantifier) else {
            return Ok(None);
        };
        info.mk_macro_based_inst_sets(context, &mut self.auf_solver)?;
        Ok(self
            .q2info
            .get(&quantifier)
            .and_then(|info| info.get_macro_based_inst_set(index)))
    }

    /// get_inv: a term of the instantiation set whose value is value, and its generation.
    pub fn get_inv(
        &mut self,
        context: &mut Context,
        quantifier: Expr,
        index: u32,
        value: Expr,
        model: &ProtoModelRef,
    ) -> Result<Option<(Expr, u32)>, SmtError> {
        let Some(set) = self.get_uvar_inst_set(context, quantifier, index)? else {
            return Ok(None);
        };
        let Some(term) = set.get_inv(&context.m, value, &model.borrow()) else {
            return Ok(None);
        };
        let generation = set.get_generation(&context.m, term);
        if self.auf_solver.is_default_representative(&context.m, term) {
            return Ok(Some((value, 0)));
        }
        Ok(Some((term, generation)))
    }

    /// restrict_sks_to_inst_set: each Skolem constant must take the value of a term in its set.
    pub fn restrict_sks_to_inst_set(
        &mut self,
        context: &mut Context,
        quantifier: Expr,
        sks: &[Expr],
        assert: &mut dyn FnMut(&mut AstManager, Expr) -> Result<(), SmtError>,
    ) -> Result<bool, SmtError> {
        let num_decls = context.m.get_quantifier(quantifier)?.sorts.len();
        let mut is_asserted = false;
        for index in 0..num_decls {
            let sk = sks[sks.len() - index - 1];
            let values: Vec<Expr> =
                match self.get_uvar_inst_set(context, quantifier, index as u32)? {
                    Some(set) if !set.inv.is_empty() => {
                        set.inv.keys().map(|value| value as Expr).collect()
                    }
                    _ => continue,
                };
            let m = &mut context.m;
            // eqs and new_cnstr hold their terms until the restriction is asserted.
            // ast_manager::mk_or keeps a single disjunct in an or.
            let mut eqs = RefVector::new();
            for value in values {
                if m.sorts[value as usize] == m.sorts[sk as usize] {
                    let eq = m.mk_eq(sk, value)?;
                    eqs.push(m, eq);
                }
            }
            if !eqs.is_empty() {
                let constraint = m.mk_app(OP_OR, &eqs.items, SORT_BOOL)?;
                m.inc_ref(constraint);
                assert(m, constraint)?;
                m.dec_ref(constraint)?;
                is_asserted = true;
            }
            eqs.reset(m)?;
        }
        Ok(is_asserted)
    }
}

impl Context {
    /// registerQuantifier: the quantifier's info, which the quantifier manager does not read.
    pub fn model_finder_register_quantifier(&mut self, quantifier: Expr) -> Result<(), SmtError> {
        match self.qmanager.mbqi.as_mut() {
            Some(mbqi) => mbqi.finder.register_quantifier(&mut self.m, quantifier),
            None => Ok(()),
        }
    }

    /// fix_model: tries to satisfy the relevant quantifiers by changing the model while keeping
    /// the ground formulas satisfied.
    pub fn model_finder_fix_model(&mut self, model: &ProtoModelRef) -> Result<(), SmtError> {
        let Some(mut mbqi) = self.qmanager.mbqi.take() else {
            return Ok(());
        };
        let result = mbqi.finder.fix_model(self, model);
        self.qmanager.mbqi = Some(mbqi);
        result
    }

    /// restart_eh: the constraints of the last model become axioms.
    pub fn model_finder_restart_eh(&mut self) -> Result<(), SmtError> {
        let Some(mbqi) = self.qmanager.mbqi.as_mut() else {
            return Ok(());
        };
        let constraints = std::mem::take(&mut mbqi.finder.auf_solver.new_constraints);
        for constraint in constraints {
            self.internalize(constraint, true)?;
            let literal = self.get_literal(constraint)?;
            self.mark_literal_as_relevant(literal)?;
            self.assign(literal, BJustification::Axiom, false);
        }
        Ok(())
    }
}
