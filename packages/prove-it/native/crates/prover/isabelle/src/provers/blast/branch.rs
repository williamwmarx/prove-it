//! Ported from Isabelle2025's Provers/blast.ML. Copyright (c) 1986-2025 University of Cambridge,
//! Technische Universitaet Muenchen, and contributors, see LICENSE.
//!
//! Operations on branches: naive substitution for equalities, closing a branch by complementary
//! literals, and the pruning of choice points.

use crate::pure::tactic::{assume_tac, ematch_tac, eq_assume_tac};
use crate::pure::tactical::{GoalTactic, or_else_goal, then_goal};

use super::state::{BlastState, Branch, Choices, Formula, Level, unify};
use super::term::{
    BlastTerm, BlastTermNode, GOAL_NAME, VarRef, blast_aconv, dest_const_app, has_loose_bound0,
    incr_blast_boundvars, ins_term, is_goal, mk_blast_abs, mk_blast_app, mk_blast_const,
    mk_blast_var, var_occur,
};

fn negate(state: &BlastState, term: BlastTerm) -> BlastTerm {
    mk_blast_app(
        mk_blast_const(state.context.data.not_name.clone(), Vec::new()),
        term,
    )
}

/// Converts a *Goal* to an ordinary negation.
pub fn neg_of_goal(state: &BlastState, term: &BlastTerm) -> BlastTerm {
    match dest_const_app(term, GOAL_NAME) {
        None => term.clone(),
        Some(goal) => negate(state, goal.clone()),
    }
}

fn neg_of_goal2(state: &BlastState, formula: &Formula) -> Formula {
    Formula {
        term: neg_of_goal(state, &formula.term),
        md: formula.md,
    }
}

/// Converts the goals to negations in the safe parts of a branch. They could have been moved there
/// from the literals by an equality substitution.
pub fn neg_of_goals(state: &BlastState, pairs: &[Level]) -> Vec<Level> {
    pairs
        .iter()
        .map(|level| Level {
            safe: level
                .safe
                .iter()
                .map(|formula| neg_of_goal2(state, formula))
                .collect(),
            r#unsafe: level.r#unsafe.clone(),
        })
        .collect()
}

/// Replaces the atomic term old by new, returning the very same term where nothing changes.
fn subst_atomic(old: &BlastTerm, replacement: &BlastTerm, term: &BlastTerm) -> BlastTerm {
    if let BlastTermNode::Var { var_ref } = &**term
        && let Some(value) = var_ref.value()
    {
        return subst_atomic(old, replacement, &value);
    }
    match &**term {
        BlastTermNode::Abs { name, body } => {
            let new_body = subst_atomic(old, replacement, body);
            if BlastTerm::ptr_eq(&new_body, body) {
                term.clone()
            } else {
                mk_blast_abs(name.clone(), new_body)
            }
        }
        BlastTermNode::App { fun, arg } => {
            let new_fun = subst_atomic(old, replacement, fun);
            let new_arg = subst_atomic(old, replacement, arg);
            if BlastTerm::ptr_eq(&new_fun, fun) && BlastTerm::ptr_eq(&new_arg, arg) {
                term.clone()
            } else {
                mk_blast_app(new_fun, new_arg)
            }
        }
        _ => {
            if blast_aconv(term, old) {
                replacement.clone()
            } else {
                term.clone()
            }
        }
    }
}

/// Eta-contracts a term from outside, just enough to reduce it to an atom.
fn eta_contract_atom(term: &BlastTerm) -> BlastTerm {
    let BlastTermNode::Abs { body, .. } = &**term else {
        return term.clone();
    };
    let body = eta_contract2(body);
    match &*body {
        BlastTermNode::App { fun, arg } if matches!(&**arg, BlastTermNode::Bound { index: 0 }) => {
            if has_loose_bound0(fun) {
                term.clone()
            } else {
                eta_contract_atom(&incr_blast_boundvars(-1, fun))
            }
        }
        _ => term.clone(),
    }
}

fn eta_contract2(term: &BlastTerm) -> BlastTerm {
    match &**term {
        BlastTermNode::App { fun, arg } => mk_blast_app(fun.clone(), eta_contract_atom(arg)),
        _ => eta_contract_atom(term),
    }
}

/// Can term occur in other? Does not examine the arguments of Skolem terms, which substitution does
/// not affect, and is reflexive because hyp_subst_tac fails on x = x. No variables may occur in
/// other except the arguments of a Skolem term, so that no equation that could be instantiated to
/// a cycle is deleted.
fn subst_occur(term: &BlastTerm, other: &BlastTerm) -> bool {
    let vars: &[VarRef] = match &**term {
        BlastTermNode::Skolem { args, .. } => args,
        _ => &[],
    };
    fn occ_eq(term: &BlastTerm, vars: &[VarRef], current: &BlastTerm) -> bool {
        blast_aconv(term, current) || occ(term, vars, current)
    }
    fn occ(term: &BlastTerm, vars: &[VarRef], current: &BlastTerm) -> bool {
        match &**current {
            BlastTermNode::Var { var_ref } => match var_ref.value() {
                None => !vars.iter().any(|other| VarRef::ptr_eq(other, var_ref)),
                Some(value) => occ_eq(term, vars, &value),
            },
            BlastTermNode::Abs { body, .. } => occ_eq(term, vars, body),
            BlastTermNode::App { fun, arg } => occ_eq(term, vars, arg) || occ_eq(term, vars, fun),
            _ => false,
        }
    }
    occ_eq(term, vars, other)
}

/// Takes apart an equality and orients it to eliminate a Skolem term or a free variable, or gives
/// None (DEST_EQ) if it has no substitutable side.
fn orient_equality(state: &BlastState, term: &BlastTerm) -> Option<(BlastTerm, BlastTerm)> {
    let BlastTermNode::App { fun, arg } = &**term else {
        return None;
    };
    let BlastTermNode::App {
        fun: equality,
        arg: left,
    } = &**fun
    else {
        return None;
    };
    let BlastTermNode::Const { name, .. } = &**equality else {
        return None;
    };
    if *name != state.context.data.equality_name {
        return None;
    }
    let left = eta_contract_atom(left);
    let right = eta_contract_atom(arg);
    let check = |old: &BlastTerm, replacement: &BlastTerm| {
        if subst_occur(old, replacement) {
            None
        } else {
            Some((old.clone(), replacement.clone()))
        }
    };
    let is_skolem = |term: &BlastTerm| matches!(&**term, BlastTermNode::Skolem { .. });
    let is_free = |term: &BlastTerm| matches!(&**term, BlastTermNode::Free { .. });
    if is_skolem(&left) {
        return check(&left, &right);
    }
    if is_skolem(&right) {
        return check(&right, &left);
    }
    if is_free(&left) {
        return check(&left, &right);
    }
    if is_free(&right) {
        return check(&right, &left);
    }
    None
}

/// The formulae of forms that substitution changed, in order before changed, and those it kept.
fn sub_forms(
    subst: &impl Fn(&BlastTerm) -> BlastTerm,
    forms: &[Formula],
    changed: Vec<Formula>,
) -> (Vec<Formula>, Vec<Formula>) {
    let mut new_changed = Vec::new();
    let mut kept = Vec::new();
    for form in forms.iter().rev() {
        let substituted = subst(&form.term);
        if blast_aconv(&substituted, &form.term) {
            kept.push(form.clone());
        } else {
            new_changed.push(Formula {
                term: substituted,
                md: form.md,
            });
        }
    }
    new_changed.reverse();
    new_changed.extend(changed);
    kept.reverse();
    (new_changed, kept)
}

/// Substitutes through the branch if the formula is an equality with a substitutable variable.
/// Moves the affected formulae and literals back to the safe formulae, but it is not clear where
/// they should go: this could make proofs fail.
pub fn equal_subst(state: &BlastState, formula: &BlastTerm, branch: &Branch) -> Option<Branch> {
    let (old, replacement) = orient_equality(state, formula)?;
    let subst = |term: &BlastTerm| subst_atomic(&old, &replacement, term);
    let mut lits_changed = Vec::new();
    let mut lits = Vec::new();
    for lit in branch.lits.iter().rev() {
        let substituted = subst(lit);
        if blast_aconv(&substituted, lit) {
            lits.push(substituted);
        } else {
            lits_changed.push(Formula {
                term: substituted,
                md: true,
            });
        }
    }
    lits_changed.reverse();
    lits.reverse();
    let mut changed = lits_changed;
    let mut frames = Vec::new();
    for level in branch.pairs.iter().rev() {
        let (safe_changed, safe_kept) = sub_forms(&subst, &level.safe, changed);
        let (unsafe_changed, unsafe_kept) = sub_forms(&subst, &level.r#unsafe, safe_changed);
        changed = unsafe_changed;
        frames.push(Level {
            safe: safe_kept,
            r#unsafe: unsafe_kept,
        });
    }
    frames.push(Level {
        safe: changed,
        r#unsafe: Vec::new(),
    });
    frames.reverse();
    Some(Branch {
        pairs: frames,
        lits,
        vars: branch.vars.clone(),
        lim: branch.lim,
    })
}

/// Tries to unify complementary literals, giving the tactic that closes the branch.
fn e_assume_tac() -> GoalTactic {
    or_else_goal(eq_assume_tac(), assume_tac())
}

/// contr_tac: trying eq_contr_tac first increases the effort, slowing reconstruction.
fn e_contr_tac(state: &BlastState) -> GoalTactic {
    then_goal(
        ematch_tac(std::slice::from_ref(&state.context.data.not_e)),
        e_assume_tac(),
    )
}

fn close(
    state: &BlastState,
    left: &BlastTerm,
    right: &BlastTerm,
    tactic: impl FnOnce(&BlastState) -> GoalTactic,
) -> Option<GoalTactic> {
    unify(state, &[], left, right).then(|| tactic(state))
}

pub fn try_close(
    state: &BlastState,
    formula: &BlastTerm,
    literal: &BlastTerm,
) -> Option<GoalTactic> {
    let not_name = &*state.context.data.not_name;
    if let Some(formula_goal) = dest_const_app(formula, GOAL_NAME) {
        return close(state, formula_goal, literal, |_| e_assume_tac());
    }
    if let Some(literal_goal) = dest_const_app(literal, GOAL_NAME) {
        return close(state, formula, literal_goal, |_| e_assume_tac());
    }
    if let Some(formula_not) = dest_const_app(formula, not_name) {
        return close(state, formula_not, literal, e_contr_tac);
    }
    if let Some(literal_not) = dest_const_app(literal, not_name) {
        return close(state, formula, literal_not, e_contr_tac);
    }
    None
}

/// Were there Skolem terms in the premise? Must not chase variables.
fn has_skolem(term: &BlastTerm) -> bool {
    match &**term {
        BlastTermNode::Skolem { .. } => true,
        BlastTermNode::Abs { body, .. } => has_skolem(body),
        BlastTermNode::App { fun, arg } => has_skolem(fun) || has_skolem(arg),
        _ => false,
    }
}

/// Attaches the may-duplicate flag to new formulae: those with Skolem terms may be duplicated.
pub fn join_md(md: bool, terms: &[BlastTerm]) -> Vec<Formula> {
    terms
        .iter()
        .map(|term| Formula {
            term: term.clone(),
            md: has_skolem(term) || md,
        })
        .collect()
}

/// Whether any of the last count assignments of the trail below top occurs in vars or their
/// instantiations.
fn clash_var(state: &BlastState, vars: &[BlastTerm], count: isize, top: isize) -> bool {
    if vars.is_empty() {
        return false;
    }
    let trail = state.trail.borrow();
    let mut remaining = count;
    let mut position = top - 1;
    while remaining != 0 && position >= 0 {
        let var_ref = &trail[position as usize];
        if vars.iter().any(|term| var_occur(var_ref, term)) {
            return true;
        }
        position -= 1;
        remaining -= 1;
    }
    false
}

/// Deletes the choice points for goals the latest inference proved, provided no variable of the
/// next branch was updated. nbrs is the number of branches just before closing this one. Does not
/// prune at the very end, to allow backtracking over bad proofs.
pub fn prune(state: &BlastState, nbrs: usize, nxt_vars: &[BlastTerm], choices: Choices) -> Choices {
    if nbrs == 1 {
        return choices;
    }
    let mut last = choices.clone();
    let mut ntrl = state.trail_len() as isize;
    let mut current = choices;
    while let Some(cell) = current {
        let choice = &cell.head;
        if choice.nbrs < nbrs {
            return last;
        }
        if choice.nbrs == nbrs {
            if clash_var(state, nxt_vars, ntrl - choice.ntrl as isize, ntrl) {
                return last;
            }
            last = cell.tail.clone();
            ntrl = choice.ntrl as isize;
        }
        current = cell.tail.clone();
    }
    last
}

pub fn next_vars(brs: &[Branch]) -> Vec<BlastTerm> {
    match brs.first() {
        None => Vec::new(),
        Some(branch) => branch
            .vars
            .iter()
            .map(|var_ref| mk_blast_var(var_ref.clone()))
            .collect(),
    }
}

/// Adds the literal, handling *Goal* and detecting duplicates. A new *Goal* turns the other goals
/// into negations.
pub fn add_lit(state: &BlastState, term: &BlastTerm, lits: &[BlastTerm]) -> Vec<BlastTerm> {
    let Some(goal) = dest_const_app(term, GOAL_NAME) else {
        return ins_term(term.clone(), lits.to_vec());
    };
    let not_name = &*state.context.data.not_name;
    let is_bad = |lit: &BlastTerm| {
        if is_goal(lit) {
            return true;
        }
        dest_const_app(lit, not_name).is_some_and(|negated| blast_aconv(goal, negated))
    };
    let mut result = vec![mk_blast_app(
        mk_blast_const(GOAL_NAME, Vec::new()),
        goal.clone(),
    )];
    if lits.iter().any(is_bad) {
        for lit in lits {
            let inner = dest_const_app(lit, GOAL_NAME).or_else(|| dest_const_app(lit, not_name));
            match inner {
                None => result.push(lit.clone()),
                Some(inner) if blast_aconv(goal, inner) => {}
                Some(inner) => result.push(negate(state, inner.clone())),
            }
        }
    } else {
        result.extend(lits.iter().cloned());
    }
    result
}

/// The penalty for a branching factor: log2 seems a little too severe.
pub fn log4(count: usize) -> i32 {
    if count < 4 { 0 } else { 1 + log4(count / 4) }
}

/// Whether term might be an instance of pattern, to detect recursive rules such as transitivity.
pub fn r#match(state: &BlastState, pattern: &BlastTerm, term: &BlastTerm) -> bool {
    match (&**pattern, &**term) {
        (BlastTermNode::Var { .. }, _) => true,
        (
            BlastTermNode::Const { name, typargs },
            BlastTermNode::Const {
                name: term_name,
                typargs: term_typargs,
            },
        ) => {
            let not_name = &state.context.data.not_name;
            (&**name == GOAL_NAME && term_name == not_name)
                || (name == not_name && &**term_name == GOAL_NAME)
                || (name == term_name
                    && typargs.len() == term_typargs.len()
                    && typargs
                        .iter()
                        .zip(term_typargs)
                        .all(|(arg, term_arg)| r#match(state, arg, term_arg)))
        }
        (BlastTermNode::Free { name }, BlastTermNode::Free { name: term_name }) => {
            name == term_name
        }
        (BlastTermNode::Bound { index }, BlastTermNode::Bound { index: term_index }) => {
            index == term_index
        }
        (
            BlastTermNode::Abs { body, .. },
            BlastTermNode::Abs {
                body: term_body, ..
            },
        ) => r#match(state, body, term_body),
        (
            BlastTermNode::App { fun, arg },
            BlastTermNode::App {
                fun: term_fun,
                arg: term_arg,
            },
        ) => r#match(state, fun, term_fun) && r#match(state, arg, term_arg),
        _ => false,
    }
}
