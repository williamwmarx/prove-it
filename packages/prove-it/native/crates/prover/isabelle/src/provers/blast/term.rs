//! Ported from Isabelle2025's Provers/blast.ML. Copyright (c) 1986-2025 University of Cambridge,
//! Technische Universitaet Muenchen, and contributors, see LICENSE.
//!
//! Blast's prototerms: untyped terms whose variables are mutable references, so that unification
//! updates them in place and backtracking resets them from the trail. Constants carry their type
//! arguments as terms, so that overloading is tracked faithfully.
//!
//! A variable's assignment is a `VarRef`, a shared mutable cell compared by identity, as the
//! TypeScript's `{ value }` object and blast.ML's `term option Unsynchronized.ref` are. Terms are
//! `Rc` handles compared by `BlastTerm::ptr_eq` where the TypeScript compares them with `===`.

use std::cell::RefCell;
use std::collections::HashMap;
use std::ops::Deref;
use std::rc::Rc;

use crate::error::Res;
use crate::pure::consts::{TypargPosition, typargs};
use crate::pure::term::{
    Name, Term, TermNode, Typ, TypNode, dummy_t, mk_app, mk_bound, mk_const, mk_free, mk_var,
};

/// A variable's assignment: term option Unsynchronized.ref, compared by identity
/// (`VarRef::ptr_eq`). Unification assigns it after an occurs check, so no assignment refers
/// back to its variable and the `Rc`s form no cycle.
#[derive(Clone)]
pub struct VarRef(Rc<RefCell<Option<BlastTerm>>>);

impl VarRef {
    /// A fresh variable, `{ value }`.
    pub fn new(value: Option<BlastTerm>) -> VarRef {
        VarRef(Rc::new(RefCell::new(value)))
    }

    /// `ref.value`.
    pub fn value(&self) -> Option<BlastTerm> {
        self.0.borrow().clone()
    }

    /// `ref.value = value`.
    pub fn set_value(&self, value: Option<BlastTerm>) {
        *self.0.borrow_mut() = value;
    }

    /// The TypeScript's `===` on variables.
    pub fn ptr_eq(left: &VarRef, right: &VarRef) -> bool {
        Rc::ptr_eq(&left.0, &right.0)
    }
}

pub enum BlastTermNode {
    Const { name: Name, typargs: Vec<BlastTerm> },
    Skolem { name: Name, args: Rc<[VarRef]> },
    Free { name: Name },
    Var { var_ref: VarRef },
    Bound { index: i32 },
    Abs { name: Name, body: BlastTerm },
    App { fun: BlastTerm, arg: BlastTerm },
}

#[derive(Clone)]
pub struct BlastTerm(Rc<BlastTermNode>);

impl Deref for BlastTerm {
    type Target = BlastTermNode;
    fn deref(&self) -> &BlastTermNode {
        &self.0
    }
}

impl BlastTerm {
    /// The TypeScript's `===` on prototerms.
    pub fn ptr_eq(left: &BlastTerm, right: &BlastTerm) -> bool {
        Rc::ptr_eq(&left.0, &right.0)
    }
}

/// What blast needs of a constant's declaration: the positions of its type arguments, for
/// Sign.const_typargs.
pub trait ConstType {
    fn typargs(&self) -> &[TypargPosition];
}

pub const GOAL_NAME: &str = "*Goal*";
pub const FALSE_NAME: &str = "*False*";

pub fn mk_blast_const(name: impl Into<Name>, typargs: Vec<BlastTerm>) -> BlastTerm {
    BlastTerm(Rc::new(BlastTermNode::Const {
        name: name.into(),
        typargs,
    }))
}

pub fn mk_blast_skolem(name: impl Into<Name>, args: Rc<[VarRef]>) -> BlastTerm {
    BlastTerm(Rc::new(BlastTermNode::Skolem {
        name: name.into(),
        args,
    }))
}

pub fn mk_blast_free(name: impl Into<Name>) -> BlastTerm {
    BlastTerm(Rc::new(BlastTermNode::Free { name: name.into() }))
}

pub fn mk_blast_var(var_ref: VarRef) -> BlastTerm {
    BlastTerm(Rc::new(BlastTermNode::Var { var_ref }))
}

pub fn mk_blast_bound(index: i32) -> BlastTerm {
    BlastTerm(Rc::new(BlastTermNode::Bound { index }))
}

pub fn mk_blast_abs(name: impl Into<Name>, body: BlastTerm) -> BlastTerm {
    BlastTerm(Rc::new(BlastTermNode::Abs {
        name: name.into(),
        body,
    }))
}

pub fn mk_blast_app(fun: BlastTerm, arg: BlastTerm) -> BlastTerm {
    BlastTerm(Rc::new(BlastTermNode::App { fun, arg }))
}

pub fn list_blast_comb(head: BlastTerm, args: Vec<BlastTerm>) -> BlastTerm {
    args.into_iter().fold(head, mk_blast_app)
}

/// Const (c, _) $ t: the argument of a constant applied to one term, if the term is one.
pub fn dest_const_app<'a>(term: &'a BlastTerm, name: &str) -> Option<&'a BlastTerm> {
    match &**term {
        BlastTermNode::App { fun, arg } => match &**fun {
            BlastTermNode::Const { name: fun_name, .. } if &**fun_name == name => Some(arg),
            _ => None,
        },
        _ => None,
    }
}

pub fn mk_goal(term: BlastTerm) -> BlastTerm {
    mk_blast_app(mk_blast_const(GOAL_NAME, Vec::new()), term)
}

pub fn is_goal(term: &BlastTerm) -> bool {
    dest_const_app(term, GOAL_NAME).is_some()
}

/// Tests whether two terms are alpha-convertible, chasing instantiations.
pub fn blast_aconv(left: &BlastTerm, right: &BlastTerm) -> bool {
    if BlastTerm::ptr_eq(left, right) {
        return true;
    }
    match (&**left, &**right) {
        (
            BlastTermNode::Const { name, typargs },
            BlastTermNode::Const {
                name: right_name,
                typargs: right_typargs,
            },
        ) => return name == right_name && blast_aconvs(typargs, right_typargs),
        (
            BlastTermNode::Skolem { name, .. },
            BlastTermNode::Skolem {
                name: right_name, ..
            },
        )
        | (BlastTermNode::Free { name }, BlastTermNode::Free { name: right_name }) => {
            return name == right_name;
        }
        _ => {}
    }
    if let BlastTermNode::Var { var_ref } = &**left
        && let Some(value) = var_ref.value()
    {
        return blast_aconv(&value, right);
    }
    if let BlastTermNode::Var { var_ref } = &**right
        && let Some(value) = var_ref.value()
    {
        return blast_aconv(left, &value);
    }
    match (&**left, &**right) {
        (BlastTermNode::Var { var_ref }, BlastTermNode::Var { var_ref: right_ref }) => {
            VarRef::ptr_eq(var_ref, right_ref)
        }
        (BlastTermNode::Bound { index }, BlastTermNode::Bound { index: right_index }) => {
            index == right_index
        }
        (
            BlastTermNode::Abs { body, .. },
            BlastTermNode::Abs {
                body: right_body, ..
            },
        ) => blast_aconv(body, right_body),
        (
            BlastTermNode::App { fun, arg },
            BlastTermNode::App {
                fun: right_fun,
                arg: right_arg,
            },
        ) => blast_aconv(fun, right_fun) && blast_aconv(arg, right_arg),
        _ => false,
    }
}

fn blast_aconvs(lefts: &[BlastTerm], rights: &[BlastTerm]) -> bool {
    lefts.len() == rights.len()
        && lefts
            .iter()
            .zip(rights)
            .all(|(left, right)| blast_aconv(left, right))
}

fn mem_term(term: &BlastTerm, terms: &[BlastTerm]) -> bool {
    terms.iter().any(|other| blast_aconv(term, other))
}

pub fn ins_term(term: BlastTerm, mut terms: Vec<BlastTerm>) -> Vec<BlastTerm> {
    if !mem_term(&term, &terms) {
        terms.insert(0, term);
    }
    terms
}

pub fn same_vars(left: &[VarRef], right: &[VarRef]) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|(var_ref, other)| VarRef::ptr_eq(var_ref, other))
}

fn mem_var(var_ref: &VarRef, refs: &[VarRef]) -> bool {
    refs.iter().any(|other| VarRef::ptr_eq(var_ref, other))
}

fn ins_var(var_ref: &VarRef, mut refs: Vec<VarRef>) -> Vec<VarRef> {
    if !mem_var(var_ref, &refs) {
        refs.insert(0, var_ref.clone());
    }
    refs
}

/// Accumulates the unassigned variables of a term, suppressing duplicates.
pub fn add_term_vars(term: &BlastTerm, refs: Vec<VarRef>) -> Vec<VarRef> {
    match &**term {
        BlastTermNode::Skolem { args, .. } => add_vars_vars(args, refs),
        BlastTermNode::Var { var_ref } => match var_ref.value() {
            None => ins_var(var_ref, refs),
            Some(value) => add_term_vars(&value, refs),
        },
        BlastTermNode::Const { typargs, .. } => add_terms_vars(typargs, refs),
        BlastTermNode::Abs { body, .. } => add_term_vars(body, refs),
        BlastTermNode::App { fun, arg } => add_term_vars(fun, add_term_vars(arg, refs)),
        _ => refs,
    }
}

pub fn add_terms_vars(terms: &[BlastTerm], refs: Vec<VarRef>) -> Vec<VarRef> {
    terms
        .iter()
        .fold(refs, |result, term| add_term_vars(term, result))
}

fn add_vars_vars(vars: &[VarRef], refs: Vec<VarRef>) -> Vec<VarRef> {
    vars.iter()
        .fold(refs, |result, var_ref| match var_ref.value() {
            None => ins_var(var_ref, result),
            Some(value) => add_term_vars(&value, result),
        })
}

/// Chases the assignments of the variables, returning the unassigned ones.
pub fn vars_in_vars(refs: &[VarRef]) -> Vec<VarRef> {
    add_vars_vars(refs, Vec::new())
}

fn incr_bv(increment: i32, level: i32, term: &BlastTerm) -> BlastTerm {
    match &**term {
        BlastTermNode::Bound { index } => {
            if *index >= level {
                mk_blast_bound(index + increment)
            } else {
                term.clone()
            }
        }
        BlastTermNode::Abs { name, body } => {
            mk_blast_abs(name.clone(), incr_bv(increment, level + 1, body))
        }
        BlastTermNode::App { fun, arg } => mk_blast_app(
            incr_bv(increment, level, fun),
            incr_bv(increment, level, arg),
        ),
        _ => term.clone(),
    }
}

pub fn incr_blast_boundvars(increment: i32, term: &BlastTerm) -> BlastTerm {
    if increment == 0 {
        term.clone()
    } else {
        incr_bv(increment, 0, term)
    }
}

/// member (op =) (loose_bnos term) 0, which does not chase variables.
pub fn has_loose_bound0(term: &BlastTerm) -> bool {
    has_loose_bound_at(term, 0)
}

fn has_loose_bound_at(term: &BlastTerm, level: i32) -> bool {
    match &**term {
        BlastTermNode::Bound { index } => *index == level,
        BlastTermNode::Abs { body, .. } => has_loose_bound_at(body, level + 1),
        BlastTermNode::App { fun, arg } => {
            has_loose_bound_at(fun, level) || has_loose_bound_at(arg, level)
        }
        _ => false,
    }
}

fn subst_bound_at(arg: &BlastTerm, level: i32, term: &BlastTerm) -> BlastTerm {
    match &**term {
        BlastTermNode::Bound { index } => {
            if *index < level {
                term.clone()
            } else if *index == level {
                incr_blast_boundvars(level, arg)
            } else {
                mk_blast_bound(index - 1)
            }
        }
        BlastTermNode::Abs { name, body } => {
            mk_blast_abs(name.clone(), subst_bound_at(arg, level + 1, body))
        }
        BlastTermNode::App { fun, arg: term_arg } => mk_blast_app(
            subst_bound_at(arg, level, fun),
            subst_bound_at(arg, level, term_arg),
        ),
        _ => term.clone(),
    }
}

pub fn blast_subst_bound(arg: &BlastTerm, body: &BlastTerm) -> BlastTerm {
    subst_bound_at(arg, 0, body)
}

/// Normalizes, but not the bodies of abstractions. Returns the very same term where nothing
/// changes, so normalizing a normal formula allocates nothing.
pub fn norm(term: &BlastTerm) -> BlastTerm {
    match &**term {
        BlastTermNode::Skolem { name, args } => {
            let normal = vars_in_vars(args);
            if same_vars(&normal, args) {
                term.clone()
            } else {
                mk_blast_skolem(name.clone(), normal.into())
            }
        }
        BlastTermNode::Const { name, typargs } => {
            if typargs.is_empty() {
                return term.clone();
            }
            let normal: Vec<BlastTerm> = typargs.iter().map(norm).collect();
            if normal
                .iter()
                .zip(typargs)
                .all(|(arg, old)| BlastTerm::ptr_eq(arg, old))
            {
                term.clone()
            } else {
                mk_blast_const(name.clone(), normal)
            }
        }
        BlastTermNode::Var { var_ref } => match var_ref.value() {
            None => term.clone(),
            Some(value) => norm(&value),
        },
        BlastTermNode::App { fun, arg } => {
            let normal_fun = norm(fun);
            if let BlastTermNode::Abs { body, .. } = &*normal_fun {
                return norm(&blast_subst_bound(arg, body));
            }
            let normal_arg = norm(arg);
            if BlastTerm::ptr_eq(&normal_fun, fun) && BlastTerm::ptr_eq(&normal_arg, arg) {
                term.clone()
            } else {
                mk_blast_app(normal_fun, normal_arg)
            }
        }
        _ => term.clone(),
    }
}

fn blast_head_of(term: &BlastTerm) -> &BlastTerm {
    let mut head = term;
    while let BlastTermNode::App { fun, .. } = &**head {
        head = fun;
    }
    head
}

fn wk_norm_aux(term: &BlastTerm) -> BlastTerm {
    match &**term {
        BlastTermNode::Var { var_ref } => match var_ref.value() {
            None => term.clone(),
            Some(value) => wk_norm(&value),
        },
        BlastTermNode::App { fun, arg } => {
            let normal_fun = wk_norm_aux(fun);
            match &*normal_fun {
                BlastTermNode::Abs { body, .. } => wk_norm(&blast_subst_bound(arg, body)),
                _ => mk_blast_app(normal_fun, arg.clone()),
            }
        }
        BlastTermNode::Abs { name, body } => {
            let normal_body = wk_norm_aux(body);
            let BlastTermNode::App { fun, arg } = &*normal_body else {
                return mk_blast_abs(name.clone(), normal_body);
            };
            let normal_arg = wk_norm(arg);
            if has_loose_bound0(fun) || !matches!(&*normal_arg, BlastTermNode::Bound { index: 0 }) {
                mk_blast_abs(name.clone(), normal_body.clone())
            } else {
                wk_norm(&incr_blast_boundvars(-1, fun))
            }
        }
        _ => term.clone(),
    }
}

/// Weak, one-level normalization for unification; eta-contracts where it can.
pub fn wk_norm(term: &BlastTerm) -> BlastTerm {
    match &**blast_head_of(term) {
        BlastTermNode::Const { .. } | BlastTermNode::Skolem { .. } | BlastTermNode::Free { .. } => {
            term.clone()
        }
        _ => wk_norm_aux(term),
    }
}

/// Does variable ref occur in term? Dangling bound variables count as occurrences too.
fn occurs(var_ref: &VarRef, level: i32, term: &BlastTerm) -> bool {
    match &**term {
        BlastTermNode::Var { var_ref: term_ref } => {
            VarRef::ptr_eq(var_ref, term_ref)
                || term_ref
                    .value()
                    .is_some_and(|value| occurs(var_ref, level, &value))
        }
        BlastTermNode::Skolem { args, .. } => args.iter().any(|arg| {
            VarRef::ptr_eq(var_ref, arg)
                || arg
                    .value()
                    .is_some_and(|value| occurs(var_ref, level, &value))
        }),
        BlastTermNode::Bound { index } => level <= *index,
        BlastTermNode::Abs { body, .. } => occurs(var_ref, level + 1, body),
        BlastTermNode::App { fun, arg } => {
            occurs(var_ref, level, arg) || occurs(var_ref, level, fun)
        }
        _ => false,
    }
}

pub fn var_occur(var_ref: &VarRef, term: &BlastTerm) -> bool {
    occurs(var_ref, 0, term)
}

/// An entry of the association lists from schematic variables to prototerms that from_term keeps.
pub struct VarEntry {
    pub name: Name,
    pub index: i32,
    pub term: BlastTerm,
}

/// AList.lookup, adding a fresh variable for a new one.
fn lookup_var(entries: &mut Vec<VarEntry>, name: &Name, index: i32) -> BlastTerm {
    if let Some(known) = entries
        .iter()
        .find(|entry| entry.index == index && entry.name == *name)
    {
        return known.term.clone();
    }
    let fresh = mk_blast_var(VarRef::new(None));
    entries.push(VarEntry {
        name: name.clone(),
        index,
        term: fresh.clone(),
    });
    fresh
}

fn from_type(tvars: &mut Vec<VarEntry>, ty: &Typ) -> BlastTerm {
    match &**ty {
        TypNode::Type { name, args, .. } => list_blast_comb(
            mk_blast_const(name.clone(), Vec::new()),
            args.iter().map(|arg| from_type(tvars, arg)).collect(),
        ),
        TypNode::TFree { name, .. } => mk_blast_free(name.clone()),
        TypNode::TVar { name, index, .. } => lookup_var(tvars, name, *index),
    }
}

pub fn from_const<C: ConstType>(
    consts: &HashMap<Name, C>,
    tvars: &mut Vec<VarEntry>,
    name: &Name,
    ty: &Typ,
) -> Res<BlastTerm> {
    // Sign.const_typargs. Constants the map lacks are the ones a theory declares, which have none.
    Ok(match consts.get(name) {
        Some(declared) if !declared.typargs().is_empty() => mk_blast_const(
            name.clone(),
            typargs(declared.typargs(), ty)?
                .iter()
                .map(|arg| from_type(tvars, arg))
                .collect(),
        ),
        _ => mk_blast_const(name.clone(), Vec::new()),
    })
}

fn from_term_aux<C: ConstType>(
    consts: &HashMap<Name, C>,
    vars: &mut Vec<VarEntry>,
    tvars: &mut Vec<VarEntry>,
    term: &Term,
) -> Res<BlastTerm> {
    Ok(match &**term {
        TermNode::Const { name, ty } => from_const(consts, tvars, name, ty)?,
        TermNode::Free { name, .. } => mk_blast_free(name.clone()),
        TermNode::Bound { index } => mk_blast_bound(*index),
        TermNode::Var { name, index, .. } => lookup_var(vars, name, *index),
        TermNode::Abs { name, body, .. } => {
            let blast_body = from_term_aux(consts, vars, tvars, body)?;
            match &*blast_body {
                BlastTermNode::App { fun, arg }
                    if matches!(&**arg, BlastTermNode::Bound { index: 0 })
                        && !has_loose_bound0(fun) =>
                {
                    incr_blast_boundvars(-1, fun)
                }
                _ => mk_blast_abs(name.clone(), blast_body),
            }
        }
        TermNode::App { fun, arg, .. } => {
            let blast_fun = from_term_aux(consts, vars, tvars, fun)?;
            mk_blast_app(blast_fun, from_term_aux(consts, vars, tvars, arg)?)
        }
    })
}

/// Converts a real term to a prototerm, eta-contracting it.
pub fn from_term<C: ConstType>(consts: &HashMap<Name, C>, term: &Term) -> Res<BlastTerm> {
    from_term_aux(consts, &mut Vec::new(), &mut Vec::new(), term)
}

/// A prototerm with its variables and Skolem terms numbered, so that instantiating it with fresh
/// ones gives a copy that shares the parts without them, which blast never updates.
pub enum Template {
    Ground(BlastTerm),
    Var(usize),
    Skolem(usize),
    Const {
        name: Name,
        typargs: Vec<Template>,
    },
    Abs {
        name: Name,
        body: Box<Template>,
    },
    App {
        fun: Box<Template>,
        arg: Box<Template>,
    },
}

fn is_ground(template: &Template) -> bool {
    matches!(template, Template::Ground(_))
}

/// Numbers the variables in refs, adding new ones, and the Skolem terms by their place in skolems.
pub fn to_template(refs: &mut Vec<VarRef>, skolems: &[BlastTerm], term: &BlastTerm) -> Template {
    match &**term {
        BlastTermNode::Var { var_ref } => {
            if let Some(index) = refs.iter().position(|other| VarRef::ptr_eq(other, var_ref)) {
                return Template::Var(index);
            }
            refs.push(var_ref.clone());
            Template::Var(refs.len() - 1)
        }
        BlastTermNode::Skolem { .. } => {
            match skolems
                .iter()
                .position(|skolem| BlastTerm::ptr_eq(skolem, term))
            {
                Some(slot) => Template::Skolem(slot),
                None => Template::Ground(term.clone()),
            }
        }
        BlastTermNode::Const { name, typargs } => {
            let templates: Vec<Template> = typargs
                .iter()
                .map(|arg| to_template(refs, skolems, arg))
                .collect();
            if templates.iter().all(is_ground) {
                Template::Ground(term.clone())
            } else {
                Template::Const {
                    name: name.clone(),
                    typargs: templates,
                }
            }
        }
        BlastTermNode::Abs { name, body } => {
            let template = to_template(refs, skolems, body);
            if is_ground(&template) {
                Template::Ground(term.clone())
            } else {
                Template::Abs {
                    name: name.clone(),
                    body: Box::new(template),
                }
            }
        }
        BlastTermNode::App { fun, arg } => {
            let fun_template = to_template(refs, skolems, fun);
            let arg_template = to_template(refs, skolems, arg);
            if is_ground(&fun_template) && is_ground(&arg_template) {
                Template::Ground(term.clone())
            } else {
                Template::App {
                    fun: Box::new(fun_template),
                    arg: Box::new(arg_template),
                }
            }
        }
        _ => Template::Ground(term.clone()),
    }
}

pub fn instantiate_template(
    vars: &[BlastTerm],
    skolems: &[BlastTerm],
    template: &Template,
) -> BlastTerm {
    match template {
        Template::Ground(term) => term.clone(),
        Template::Var(index) => vars[*index].clone(),
        Template::Skolem(slot) => skolems[*slot].clone(),
        Template::Const { name, typargs } => mk_blast_const(
            name.clone(),
            typargs
                .iter()
                .map(|arg| instantiate_template(vars, skolems, arg))
                .collect(),
        ),
        Template::Abs { name, body } => {
            mk_blast_abs(name.clone(), instantiate_template(vars, skolems, body))
        }
        Template::App { fun, arg } => mk_blast_app(
            instantiate_template(vars, skolems, fun),
            instantiate_template(vars, skolems, arg),
        ),
    }
}

fn dummy_var() -> Term {
    mk_var("etc", 0, dummy_t())
}

/// Converts a prototerm to a real term with dummy types for net lookup, stopping at depth.
pub fn to_term(depth: usize, term: &BlastTerm) -> Term {
    if depth == 0 {
        return dummy_var();
    }
    match &**term {
        BlastTermNode::Const { name, .. } | BlastTermNode::Skolem { name, .. } => {
            mk_const(name.clone(), dummy_t())
        }
        BlastTermNode::Free { name } => mk_free(name.clone(), dummy_t()),
        BlastTermNode::Bound { index } => mk_bound(*index),
        BlastTermNode::App { fun, arg } => mk_app(to_term(depth, fun), to_term(depth - 1, arg)),
        _ => dummy_var(),
    }
}

fn strip_trueprop<'a>(trueprop: &str, term: &'a BlastTerm) -> &'a BlastTerm {
    dest_const_app(term, trueprop).unwrap_or(term)
}

/// The premise and conclusion of A ==> B.
fn dest_blast_imp(term: &BlastTerm) -> Option<(&BlastTerm, &BlastTerm)> {
    let BlastTermNode::App { fun, arg } = &**term else {
        return None;
    };
    let BlastTermNode::App {
        fun: imp,
        arg: premise,
    } = &**fun
    else {
        return None;
    };
    matches!(&**imp, BlastTermNode::Const { name, .. } if &**name == "Pure.imp")
        .then_some((premise, arg))
}

/// A1 ==> ... ==> An ==> B goes to [A1, ..., An], where B is not an implication.
pub fn strip_blast_imp_prems(trueprop: &str, term: &BlastTerm) -> Vec<BlastTerm> {
    let mut prems = Vec::new();
    let mut current = term;
    while let Some((premise, conclusion)) = dest_blast_imp(current) {
        prems.push(strip_trueprop(trueprop, premise).clone());
        current = conclusion;
    }
    prems
}

/// A1 ==> ... ==> An ==> B goes to B, where B is not an implication.
pub fn strip_blast_imp_concl(trueprop: &str, term: &BlastTerm) -> BlastTerm {
    let mut current = term;
    while let Some((_, conclusion)) = dest_blast_imp(current) {
        current = conclusion;
    }
    strip_trueprop(trueprop, current).clone()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pure::logic::tests::show;
    use crate::tla::logic::load_logic;

    /// Labels variables in the order a rule's lines first show them.
    struct Printer {
        labels: Vec<VarRef>,
    }

    impl Printer {
        fn label(&mut self, var_ref: &VarRef) -> String {
            let position = match self
                .labels
                .iter()
                .position(|other| VarRef::ptr_eq(other, var_ref))
            {
                Some(position) => position,
                None => {
                    self.labels.push(var_ref.clone());
                    self.labels.len() - 1
                }
            };
            format!("?{position}")
        }

        fn labels(&mut self, refs: &[VarRef]) -> Vec<String> {
            refs.iter().map(|var_ref| self.label(var_ref)).collect()
        }

        fn print(&mut self, term: &BlastTerm) -> String {
            match &**term {
                BlastTermNode::Const { name, typargs } if typargs.is_empty() => name.to_string(),
                BlastTermNode::Const { name, typargs } => {
                    let args: Vec<String> = typargs.iter().map(|arg| self.print(arg)).collect();
                    format!("{name}{{{}}}", args.join(","))
                }
                BlastTermNode::Skolem { name, args } => {
                    format!("S:{name}[{}]", self.labels(args).join(","))
                }
                BlastTermNode::Free { name } => format!("F:{name}"),
                BlastTermNode::Var { var_ref } => {
                    let label = self.label(var_ref);
                    match var_ref.value() {
                        None => label,
                        Some(value) => format!("{label}={}", self.print(&value)),
                    }
                }
                BlastTermNode::Bound { index } => format!("B{index}"),
                BlastTermNode::Abs { name, body } => format!("(%{name}. {})", self.print(body)),
                BlastTermNode::App { fun, arg } => {
                    let fun = self.print(fun);
                    format!("({fun} {})", self.print(arg))
                }
            }
        }
    }

    fn flag(value: bool) -> &'static str {
        if value { "1" } else { "0" }
    }

    fn collect_abstractions(term: &BlastTerm, abstractions: &mut Vec<BlastTerm>) {
        match &**term {
            BlastTermNode::Abs { body, .. } => {
                abstractions.push(term.clone());
                collect_abstractions(body, abstractions);
            }
            BlastTermNode::App { fun, arg } => {
                collect_abstractions(fun, abstractions);
                collect_abstractions(arg, abstractions);
            }
            _ => {}
        }
    }

    // Expected values from running term.ts with bun on the same rules and operations: every third
    // classical rule of Isabelle/TLA+ converted, stripped, templated, instantiated, normalized,
    // Skolemized and beta and eta reduced.
    #[test]
    fn matches_the_typescript_on_the_classical_rules() {
        const TRUEPROP: &str = "PredicateLogic.Trueprop";
        let logic = load_logic();
        let consts = &logic.consts;
        let claset = &logic.claset;
        let rules = claset
            .safe_is
            .iter()
            .chain(&claset.safe_es)
            .chain(&claset.unsafe_is)
            .chain(&claset.unsafe_es);
        let mut lines = Vec::new();
        for (number, rule) in rules.enumerate() {
            if number % 3 != 0 {
                continue;
            }
            let mut printer = Printer { labels: Vec::new() };
            let mut out = |key: &str, value: String| lines.push(format!("{number} {key}: {value}"));

            let prop = &rule.rule.prop;
            let term = from_term(consts, prop).unwrap();
            out("from", printer.print(&term));
            let vars = add_term_vars(&term, Vec::new());
            out("vars", printer.labels(&vars).join(" "));
            let prems = strip_blast_imp_prems(TRUEPROP, &term);
            let concl = strip_blast_imp_concl(TRUEPROP, &term);
            out("prems", prems.len().to_string());
            out("concl", printer.print(&concl));
            out(
                "toTerm",
                format!("{} {}", show(&to_term(3, &term)), show(&to_term(2, &concl))),
            );
            out(
                "goal",
                format!(
                    "{}{}",
                    flag(is_goal(&mk_goal(concl.clone()))),
                    flag(is_goal(&concl))
                ),
            );

            let mut refs = Vec::new();
            let template = to_template(&mut refs, &[], &term);
            let fresh: Vec<BlastTerm> = refs
                .iter()
                .map(|_| mk_blast_var(VarRef::new(None)))
                .collect();
            let instance = instantiate_template(&fresh, &[], &template);
            out(
                "aconv",
                format!(
                    "{}{}{}",
                    flag(blast_aconv(&term, &instance)),
                    flag(blast_aconv(&instance, &instance)),
                    flag(BlastTerm::ptr_eq(&term, &instance))
                ),
            );
            if let BlastTermNode::Var { var_ref } = &*concl {
                var_ref.set_value(Some(mk_blast_const(FALSE_NAME, Vec::new())));
                out("norm", printer.print(&norm(&term)));
            }
            let fresh_refs: Vec<VarRef> = fresh
                .iter()
                .filter_map(|var| match &**var {
                    BlastTermNode::Var { var_ref } => Some(var_ref.clone()),
                    _ => None,
                })
                .collect();
            let term_occurs: String = vars
                .iter()
                .map(|var_ref| flag(var_occur(var_ref, &term)))
                .collect();
            let instance_occurs: String = fresh_refs
                .iter()
                .map(|var_ref| flag(var_occur(var_ref, &instance)))
                .collect();
            out("occurs", format!("{term_occurs} {instance_occurs}"));

            // Instantiates each fresh variable with a Skolem term over the later ones.
            for (index, var_ref) in fresh_refs.iter().enumerate() {
                if index % 2 == 0 {
                    var_ref.set_value(Some(mk_blast_skolem(
                        format!("S{index}"),
                        fresh_refs[index + 1..].into(),
                    )));
                }
            }
            let normal = norm(&instance);
            out("instantiated", printer.print(&normal));
            let remaining = vars_in_vars(&fresh_refs);
            let labels = printer.labels(&remaining).join(" ");
            let instance_vars = add_term_vars(&instance, Vec::new());
            out(
                "remaining",
                format!(
                    "{labels} {}{} {}",
                    flag(same_vars(&remaining, &fresh_refs)),
                    flag(same_vars(&fresh_refs, &fresh_refs)),
                    printer.labels(&instance_vars).join(" ")
                ),
            );
            out(
                "renorm",
                flag(BlastTerm::ptr_eq(&norm(&normal), &normal)).into(),
            );

            let remaining: Rc<[VarRef]> = remaining.into();
            for prem in strip_blast_imp_prems(TRUEPROP, &normal) {
                let mut current = prem.clone();
                while let Some(body) = dest_const_app(&current, "Pure.all")
                    && let BlastTermNode::Abs { body, .. } = &**body
                {
                    current = blast_subst_bound(&mk_blast_skolem("K", remaining.clone()), body);
                }
                if !BlastTerm::ptr_eq(&current, &prem) {
                    out("skolemized", printer.print(&norm(&current)));
                }
            }

            let mut abstractions = Vec::new();
            collect_abstractions(&term, &mut abstractions);
            for abs in abstractions.iter().take(1) {
                let redex = mk_blast_app(abs.clone(), mk_blast_free("a"));
                out(
                    "beta",
                    format!(
                        "{} {}",
                        printer.print(&wk_norm(&redex)),
                        flag(blast_aconv(&wk_norm(&redex), &norm(&redex)))
                    ),
                );
                let eta = mk_blast_abs(
                    "e",
                    mk_blast_app(incr_blast_boundvars(1, abs), mk_blast_bound(0)),
                );
                let BlastTermNode::Abs { body, .. } = &**abs else {
                    unreachable!()
                };
                out(
                    "eta",
                    format!(
                        "{} {}",
                        printer.print(&wk_norm(&eta)),
                        flag(has_loose_bound0(body))
                    ),
                );
                let nested = mk_blast_app(
                    mk_blast_app(mk_blast_abs("u", abs.clone()), mk_blast_bound(2)),
                    mk_blast_free("b"),
                );
                out("nested", printer.print(&norm(&nested)));
            }
            let chased = mk_blast_abs(
                "e",
                mk_blast_app(
                    mk_blast_var(VarRef::new(Some(incr_blast_boundvars(1, &concl)))),
                    mk_blast_bound(0),
                ),
            );
            out(
                "eta2",
                format!(
                    "{} {}",
                    printer.print(&wk_norm(&chased)),
                    printer.print(&norm(&chased))
                ),
            );
            let first = match prems.first() {
                Some(first) => ins_term(first.clone(), prems.clone()).len().to_string(),
                None => "-".into(),
            };
            out(
                "ins",
                format!("{} {first}", ins_term(concl.clone(), prems.clone()).len()),
            );
        }
        let expected: Vec<&str> = include_str!("../../../testdata/blast/term.txt")
            .lines()
            .collect();
        assert_eq!(lines.len(), expected.len());
        for (line, expected) in lines.iter().zip(expected) {
            assert_eq!(line, expected);
        }
    }
}
