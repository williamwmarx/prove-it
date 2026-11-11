//! Ported from Z3 (src/smt/theory_lra.cpp), MIT license, see z3-license.txt, through
//! `theory-lra-state.ts`. The state of theory_lra that every part of it shares: the lp solver, the
//! theory variables and their enodes, the bounds of atoms, and what the scopes undo. The theory is
//! a chain of classes in the TypeScript, one file each, from this state to TheoryLra, so each part
//! reaches the ones before it.
//!
//! Here (design/smt-core.md, "The context") the fields of the whole chain are one struct,
//! `TheoryLra`, held by the context as `theory`, each field under the TypeScript file that declares
//! it. The methods that reach the context are `impl Context` methods in the module of their file,
//! named `lra_<method>`, and those the kernel calls `theory_<method>`. A theory variable is an
//! `i32`, as `Enode::th_var` is, -1 for none; an lp column is a `usize`, `NULL_LPVAR` for none,
//! and `get_external` of a column without a theory variable, `usize::MAX`, reads -1 as an `i32`
//! as the TypeScript's `-1` does.
//!
//! The lp objects are owned here: the theory owns the `LarSolver`, the `BoundPropagator`, the
//! `IntSolver` and, once a nonlinear term needs it, the `NlaCore`. The TypeScript's back-pointers
//! are views built per call: `Lia { lia, lra }`, `Nla { core, lra, limit, is_relevant }` (with
//! `is_relevant` answered from the relevancy of each column's term as it is when the call starts,
//! which nla cannot change), and `LraView`, the theory's side of the bound propagator
//! (`theory_lra_propagate.rs`). The lp solver's cancel closure counts a step of a clone of the
//! manager's resource limit, which is the same limit (`util::rlimit`).

use std::collections::{HashMap, HashSet};

use prove_num::Rational;

use crate::core::ast::{AstManager, Expr};
use crate::core::context::Context;
use crate::core::enode::EnodeId;
use crate::core::literal::{BoolVar, Literal};
use crate::core::ref_vector::RefVector;
use crate::lp::bound_propagator::BoundPropagator;
use crate::lp::explanation::Explanation;
use crate::lp::int_solver::IntSolver;
use crate::lp::lar_solver::{LarSolver, NULL_LPVAR};
use crate::lp::nla_core::NlaCore;

/// api_bound: an atom v <= value or v >= value, with its constraints when true and when false.
/// The bounds are an arena of the theory (`TheoryLra::api_bounds`), compared by handle where the
/// TypeScript compares the objects.
#[derive(Clone, Debug)]
pub struct ApiBound {
    pub bool_var: BoolVar,
    pub th_var: i32,
    pub column: usize,
    pub is_int: bool,
    pub value: Rational,
    pub is_lower: bool,
    pub constraint_true: usize,
    pub constraint_false: usize,
}

#[derive(Clone, Copy, Debug)]
pub struct Scope {
    pub bounds_limit: usize,
    pub asserted_qhead: usize,
    pub asserted_atoms_limit: usize,
    pub num_vars: usize,
}

#[derive(Clone, Copy, Debug)]
pub struct AssertedAtom {
    pub bool_var: BoolVar,
    pub is_true: bool,
}

#[derive(Clone, Debug)]
pub struct TermBound {
    pub constraint: usize,
    pub value: Rational,
}

/// The closures the theory pushes with `pushTrail`, with what each captures. A closure that
/// captures a value that is not `Copy` (a rational) takes it from a stack of the theory's, which
/// the trail undoes in the same last-in first-out order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TheoryClosure {
    /// foundUnsupported: `() => this.unsupportedTerms.pop()`.
    PopUnsupportedTerm,
    /// foundUnderspecified: `() => this.underspecifiedTerms.pop()`.
    PopUnderspecifiedTerm,
    /// registerFixedVar: `() => this.value2var.delete(key)`, the key on `value2var_trail`.
    DeleteValue2Var,
    /// mkEqAxioms: `() => this.processedEqs.delete(key)`.
    DeleteProcessedEq { first: Expr, second: Expr },
    /// updateUnassignedBounds: `() => { this.unassignedBounds[thVar] = saved; }`.
    UnassignedBounds { th_var: usize, saved: i32 },
    /// internalizeAtom: `() => this.delayIneqs.pop()`.
    PopDelayIneq,
    /// propagateCore: `() => { this.delayIneqsQhead = saved; }`.
    DelayIneqsQhead { saved: usize },
    /// setTermBound: `() => { terms[column] = existing; }`, the existing bound on
    /// `term_bounds_trail`.
    TermBound { column: usize, is_lower: bool },
    /// initVariableValues: `() => { this.isModelInitialized = saved; }`.
    IsModelInitialized { saved: bool },
    /// assumeEqs: `() => { shrink(this.assumeEqCandidates, oldSize); }`.
    ShrinkAssumeEqCandidates { size: usize },
    /// delayedAssumeEqs: `() => { this.assumeEqHead = saved; }`.
    AssumeEqHead { saved: usize },
}

pub struct TheoryLra {
    // theory-lra-state.ts.
    pub(crate) var_enodes: Vec<EnodeId>,
    pub(crate) solver: LarSolver<'static>,
    // theory-lra-axioms.ts.
    pub(crate) processed_eqs: HashSet<(Expr, Expr)>,
    /// m_restart_pairs: equalities whose axioms a backjump to the base level drops, remade on
    /// restart.
    pub(crate) restart_pairs: Vec<(EnodeId, EnodeId)>,
    // theory-lra-internalize.ts. The four columns of the constants 1 and 0.
    pub(crate) one_var: usize,
    pub(crate) zero_var: usize,
    pub(crate) real_one_var: usize,
    pub(crate) real_zero_var: usize,
    /// The literal of each inequality constraint, and None for a definition (or a hole).
    pub(crate) constraint_sources: Vec<Option<Literal>>,
    pub(crate) api_bounds: Vec<ApiBound>,
    /// The bounds of each theory variable, as handles into `api_bounds`.
    pub(crate) bounds: Vec<Vec<usize>>,
    pub(crate) unassigned_bounds: Vec<i32>,
    pub(crate) is_new_def: bool,
    /// m_internalize_states: the terms of each nesting depth of internalize_def and mk_var_bound,
    /// which hold references until the next one at that depth resets them.
    pub(crate) internalize_states: Vec<RefVector>,
    pub(crate) internalize_head: usize,
    pub(crate) scopes: Vec<Scope>,
    /// The TypeScript's `${isInt}:${value}` keys, only looked up.
    pub(crate) value2var: HashMap<(bool, Rational), i32>,
    pub(crate) value2var_trail: Vec<(bool, Rational)>,
    /// m_not_handled: terms that the theory treats as uninterpreted, so a model may not satisfy
    /// them. Their arguments have variables, as the factors of an nla monomial do.
    pub(crate) unsupported_terms: Vec<Expr>,
    pub(crate) underspecified_terms: Vec<Expr>,
    pub(crate) nla: Option<NlaCore>,
    // theory-lra-bounds.ts.
    pub(crate) asserted_atoms: Vec<AssertedAtom>,
    pub(crate) bounds_trail: Vec<usize>,
    pub(crate) bool_var_to_bound: Vec<Option<usize>>,
    pub(crate) new_bounds: Vec<usize>,
    pub(crate) delay_ineqs: Vec<Expr>,
    // theory-lra-propagate.ts.
    pub(crate) bp: BoundPropagator,
    pub(crate) asserted_qhead: usize,
    pub(crate) delay_ineqs_qhead: usize,
    pub(crate) explanation: Explanation,
    pub(crate) core_literals: Vec<Literal>,
    pub(crate) num_conflicts: u32,
    pub(crate) lower_terms: Vec<Option<TermBound>>,
    pub(crate) upper_terms: Vec<Option<TermBound>>,
    pub(crate) term_bounds_trail: Vec<Option<TermBound>>,
    pub(crate) is_model_initialized: bool,
    // theory-lra-model.ts.
    pub(crate) assume_eq_candidates: Vec<(i32, i32)>,
    pub(crate) assume_eq_head: usize,
    // theory-lra-final-check.ts.
    pub(crate) lia: IntSolver,
}

impl TheoryLra {
    /// `new TheoryLra(context)`: the state, whose lp solver reads the context's resource limit.
    pub fn new(m: &mut AstManager) -> TheoryLra {
        let limit = m.limit.clone();
        let mut solver = LarSolver::new(Box::new(move || !limit.inc()));
        let bp = BoundPropagator::new();
        let lia = IntSolver::new(&mut solver);
        TheoryLra {
            var_enodes: Vec::new(),
            solver,
            processed_eqs: HashSet::new(),
            restart_pairs: Vec::new(),
            one_var: NULL_LPVAR,
            zero_var: NULL_LPVAR,
            real_one_var: NULL_LPVAR,
            real_zero_var: NULL_LPVAR,
            constraint_sources: Vec::new(),
            api_bounds: Vec::new(),
            bounds: Vec::new(),
            unassigned_bounds: Vec::new(),
            is_new_def: false,
            internalize_states: Vec::new(),
            internalize_head: 0,
            scopes: Vec::new(),
            value2var: HashMap::new(),
            value2var_trail: Vec::new(),
            unsupported_terms: Vec::new(),
            underspecified_terms: Vec::new(),
            nla: None,
            asserted_atoms: Vec::new(),
            bounds_trail: Vec::new(),
            bool_var_to_bound: Vec::new(),
            new_bounds: Vec::new(),
            delay_ineqs: Vec::new(),
            bp,
            asserted_qhead: 0,
            delay_ineqs_qhead: 0,
            explanation: Explanation::new(),
            core_literals: Vec::new(),
            num_conflicts: 0,
            lower_terms: Vec::new(),
            upper_terms: Vec::new(),
            term_bounds_trail: Vec::new(),
            is_model_initialized: false,
            assume_eq_candidates: Vec::new(),
            assume_eq_head: 0,
            lia,
        }
    }

    pub(crate) fn get_num_vars(&self) -> usize {
        self.var_enodes.len()
    }
}

/// The theory of a context whose `theory_*` entry point checked that `setup_context` made it, so
/// every method below an entry point has it.
pub(crate) fn get_lra(theory: &Option<TheoryLra>) -> &TheoryLra {
    match theory {
        Some(theory) => theory,
        None => unreachable!("the theory_* entry points check that setup_context made the theory"),
    }
}

pub(crate) fn get_lra_mut(theory: &mut Option<TheoryLra>) -> &mut TheoryLra {
    match theory {
        Some(theory) => theory,
        None => unreachable!("the theory_* entry points check that setup_context made the theory"),
    }
}

/// `array[index] = value` on a JavaScript array whose holes read as `fill`.
pub(crate) fn set_at<T: Clone>(values: &mut Vec<T>, index: usize, value: T, fill: T) {
    if index >= values.len() {
        values.resize(index + 1, fill);
    }
    values[index] = value;
}

impl Context {
    pub(crate) fn lra(&self) -> &TheoryLra {
        get_lra(&self.theory)
    }

    pub(crate) fn lra_mut(&mut self) -> &mut TheoryLra {
        get_lra_mut(&mut self.theory)
    }

    /// get_enode: the node of a theory variable. The theory reaches enodes only through this,
    /// get_expr and is_equal.
    pub fn theory_get_enode(&self, th_var: i32) -> EnodeId {
        self.lra().var_enodes[th_var as usize]
    }

    pub(crate) fn lra_get_expr(&self, th_var: i32) -> Expr {
        self.node(self.theory_get_enode(th_var)).owner
    }

    pub(crate) fn lra_is_int_expr(&self, expr: Expr) -> bool {
        self.m.is_int(expr)
    }

    pub(crate) fn lra_is_int_var(&self, th_var: i32) -> bool {
        self.lra_is_int_expr(self.lra_get_expr(th_var))
    }

    /// The trail's undo of a closure the theory pushed.
    pub(crate) fn lra_undo_closure(&mut self, closure: TheoryClosure) {
        let Some(theory) = self.theory.as_mut() else {
            return;
        };
        match closure {
            TheoryClosure::PopUnsupportedTerm => {
                theory.unsupported_terms.pop();
            }
            TheoryClosure::PopUnderspecifiedTerm => {
                theory.underspecified_terms.pop();
            }
            TheoryClosure::DeleteValue2Var => {
                if let Some(key) = theory.value2var_trail.pop() {
                    theory.value2var.remove(&key);
                }
            }
            TheoryClosure::DeleteProcessedEq { first, second } => {
                theory.processed_eqs.remove(&(first, second));
            }
            TheoryClosure::UnassignedBounds { th_var, saved } => {
                theory.unassigned_bounds[th_var] = saved;
            }
            TheoryClosure::PopDelayIneq => {
                theory.delay_ineqs.pop();
            }
            TheoryClosure::DelayIneqsQhead { saved } => theory.delay_ineqs_qhead = saved,
            TheoryClosure::TermBound { column, is_lower } => {
                let existing = theory.term_bounds_trail.pop().flatten();
                let terms = if is_lower {
                    &mut theory.lower_terms
                } else {
                    &mut theory.upper_terms
                };
                set_at(terms, column, existing, None);
            }
            TheoryClosure::IsModelInitialized { saved } => theory.is_model_initialized = saved,
            TheoryClosure::ShrinkAssumeEqCandidates { size } => {
                theory.assume_eq_candidates.truncate(size);
            }
            TheoryClosure::AssumeEqHead { saved } => theory.assume_eq_head = saved,
        }
    }
}
