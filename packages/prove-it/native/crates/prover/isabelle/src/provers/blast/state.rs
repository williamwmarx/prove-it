//! Ported from Isabelle2025's Provers/blast.ML. Copyright (c) 1986-2025 University of Cambridge,
//! Technische Universitaet Muenchen, and contributors, see LICENSE.
//!
//! The object logic's data for blast, and the state of one search: the names of its Skolem
//! constants and the trail of variable assignments that backtracking undoes.
//!
//! (`provers/blast/state.ts`.) The TypeScript's Backtrack exception is `Error::Backtrack`, whose
//! token, a fresh object compared by identity there, is a number unique within the search here.

use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::rc::Rc;

use crate::error::Error;
use crate::pure::consts::TypargPosition;
use crate::pure::list::List;
use crate::pure::name::{NameContext, bump_init, bump_string};
use crate::pure::table::{has_key, lookup_table, update_table};
use crate::pure::tactical::GoalTactic;
use crate::pure::term::Name;
use crate::pure::thm::{Thm, ThmNode};
use crate::tla::logic::{ConstInfo, TlaLogic};

use super::super::classical::Claset;
use super::rules::RuleTemplate;
use super::term::{BlastTerm, BlastTermNode, ConstType, VarRef, blast_aconv, var_occur, wk_norm};

impl ConstType for ConstInfo {
    fn typargs(&self) -> &[TypargPosition] {
        &self.typargs
    }
}

/// BLAST_DATA, with the two rules of other structures that blast uses.
pub struct BlastData {
    pub trueprop: Name,
    pub equality_name: Name,
    pub not_name: Name,
    /// ~P ==> P ==> R
    pub not_e: Thm,
    /// (~P ==> False) ==> P
    pub ccontr: Thm,
    pub hyp_subst_tac: GoalTactic,
    /// The classical reasoner's (~P ==> P) ==> P, which Classical.dup_intr resolves with.
    pub classical: Thm,
    /// The atomize rules of Object_Logic, newest first, for atomize_prems_tac.
    pub atomize: Vec<Thm>,
}

/// The rules converted to tableau rules so far, by the identity of the theorem (its address,
/// with the theorem held so that the address is not reused).
pub type Templates = RefCell<HashMap<usize, (Thm, Rc<RuleTemplate>)>>;

/// The address of a theorem, which the TypeScript's WeakMap keys by identity.
pub fn thm_address(thm: &Thm) -> usize {
    std::ptr::from_ref::<ThmNode>(thm) as usize
}

pub struct BlastContext {
    pub claset: Rc<Claset>,
    pub data: Rc<BlastData>,
    /// The logic, whose constants' declared types Sign.const_typargs reads.
    pub logic: Rc<TlaLogic>,
    /// The elimination and introduction rules converted to tableau rules so far.
    pub elim_templates: Templates,
    pub intro_templates: Templates,
}

impl BlastContext {
    pub fn new(claset: Rc<Claset>, data: Rc<BlastData>, logic: Rc<TlaLogic>) -> BlastContext {
        BlastContext {
            claset,
            data,
            logic,
            elim_templates: RefCell::new(HashMap::new()),
            intro_templates: RefCell::new(HashMap::new()),
        }
    }
}

/// A formula pending on a branch, with its may-duplicate flag.
#[derive(Clone)]
pub struct Formula {
    pub term: BlastTerm,
    pub md: bool,
}

/// The safe and unsafe formulae of one level of a branch.
#[derive(Clone)]
pub struct Level {
    pub safe: Vec<Formula>,
    pub r#unsafe: Vec<Formula>,
}

#[derive(Clone)]
pub struct Branch {
    pub pairs: Vec<Level>,
    /// Literals: irreducible formulae.
    pub lits: Vec<BlastTerm>,
    /// The variables occurring in the branch.
    pub vars: Vec<VarRef>,
    /// The resource limit.
    pub lim: i32,
}

/// A choice point: the trail length and branch count when it was made, and the token its handler
/// catches. The token is None for PROVE, the end of the search.
#[derive(Clone)]
pub struct Choice {
    pub ntrl: usize,
    pub nbrs: usize,
    pub token: Option<u64>,
}

pub struct BlastState {
    pub context: Rc<BlastContext>,
    /// The used names with their latest renaming, a Name.context replaced on each update.
    pub names: RefCell<NameContext>,
    /// The assigned variables, latest last, so that the trail's length is ntrail.
    pub trail: RefCell<Vec<VarRef>>,
    /// The last token a choice point took.
    pub tokens: Cell<u64>,
}

impl BlastState {
    /// A fresh token, the TypeScript's `{}`.
    pub fn new_token(&self) -> u64 {
        self.tokens.set(self.tokens.get() + 1);
        self.tokens.get()
    }

    pub fn trail_len(&self) -> usize {
        self.trail.borrow().len()
    }
}

/// The choice points, latest first. The last is PROVE's.
pub type Choices = List<Choice>;

pub fn is_backtrack_to(error: &Error, token: Option<u64>) -> bool {
    matches!(error, Error::Backtrack(raised) if *raised == token)
}

/// Raising the exception of a choice point: unwinds to the handler that owns the token.
pub fn backtrack(choices: &Choices) -> Error {
    Error::Backtrack(choices.as_ref().and_then(|choices| choices.head.token))
}

/// Name.variant on the state's names, for names without trailing underscores.
pub fn gensym(state: &BlastState, name: &str) -> Name {
    let mut names = state.names.borrow_mut();
    let name: Name = name.into();
    if !has_key(&names, &name) {
        *names = update_table(&names, name.clone(), None);
        return name;
    }
    let initial: Name = bump_init(&name).into();
    let mut current = initial.clone();
    while let Some(renamed) = lookup_table(&names, &current) {
        current = bump_string(renamed.as_ref().unwrap_or(&current)).into();
    }
    if current != initial {
        *names = update_table(&names, initial, Some(current.clone()));
    }
    *names = update_table(&names, current.clone(), None);
    current
}

/// Restores the trail to a previous length, for backtracking.
pub fn clear_to(state: &BlastState, count: usize) {
    let mut trail = state.trail.borrow_mut();
    while trail.len() > count {
        if let Some(var_ref) = trail.pop() {
            var_ref.set_value(None);
        }
    }
}

fn includes(vars: &[VarRef], var_ref: &VarRef) -> bool {
    vars.iter().any(|other| VarRef::ptr_eq(other, var_ref))
}

/// First-order unification with bound variables. The variables of vars are local to a rule: their
/// assignments are not trailed.
fn update_var(state: &BlastState, vars: &[VarRef], variable: &BlastTerm, term: &BlastTerm) -> bool {
    let BlastTermNode::Var { var_ref } = &**variable else {
        unreachable!("update_var of a term that isn't a Var")
    };
    if blast_aconv(variable, term) {
        return true;
    }
    if var_occur(var_ref, term) {
        return false;
    }
    if includes(vars, var_ref) {
        var_ref.set_value(Some(term.clone()));
    } else if let BlastTermNode::Var { var_ref: term_ref } = &**term
        && includes(vars, term_ref)
    {
        term_ref.set_value(Some(variable.clone()));
    } else {
        var_ref.set_value(Some(term.clone()));
        state.trail.borrow_mut().push(var_ref.clone());
    }
    true
}

fn unify_aux(state: &BlastState, vars: &[VarRef], left: &BlastTerm, right: &BlastTerm) -> bool {
    let normal_left = wk_norm(left);
    let normal_right = wk_norm(right);
    match (&*normal_left, &*normal_right) {
        (BlastTermNode::Var { .. }, _) => update_var(state, vars, &normal_left, &normal_right),
        (_, BlastTermNode::Var { .. }) => update_var(state, vars, &normal_right, &normal_left),
        (
            BlastTermNode::Const { name, typargs },
            BlastTermNode::Const {
                name: right_name,
                typargs: right_typargs,
            },
        ) => {
            name == right_name
                && typargs.len() == right_typargs.len()
                && typargs
                    .iter()
                    .zip(right_typargs)
                    .all(|(arg, right_arg)| unify_aux(state, vars, arg, right_arg))
        }
        (
            BlastTermNode::Abs { body, .. },
            BlastTermNode::Abs {
                body: right_body, ..
            },
        ) => unify_aux(state, vars, body, right_body),
        (
            BlastTermNode::App { fun, arg },
            BlastTermNode::App {
                fun: right_fun,
                arg: right_arg,
            },
        ) => unify_aux(state, vars, fun, right_fun) && unify_aux(state, vars, arg, right_arg),
        _ => blast_aconv(&normal_left, &normal_right),
    }
}

pub fn unify(state: &BlastState, vars: &[VarRef], left: &BlastTerm, right: &BlastTerm) -> bool {
    let start = state.trail_len();
    if unify_aux(state, vars, left, right) {
        return true;
    }
    clear_to(state, start);
    false
}
