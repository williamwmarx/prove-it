//! Ported from Isabelle2025's Pure/thm.ML, the inference kernel. Copyright (c) 1986-2025
//! University of Cambridge, Technische Universitaet Muenchen, and contributors, see LICENSE.
//!
//! Every TLA+ type variable has the empty sort, so the kernel drops the sort hypotheses and
//! constraints. Proof terms and certificates are not recorded either.
//!
//! (`pure/thm.ts`.) The TypeScript passes `limits: Limits | undefined` to the unifier, which
//! checks for an interrupt only with limits; here the checks see the limits installed for the
//! thread, and `without_limits` runs a computation as the TypeScript's `undefined`.

use std::ops::Deref;
use std::rc::Rc;

use crate::error::{Error, Exception, Res, term_exn, thm_exn};

use super::bicompose::{norm_term_skip, rename_bvars, strip_apply, strip_assums2, unify_var_types};
use super::envir::{Envir, above, beta_norm, empty_envir, eta_contract, is_empty_envir, norm_term};
use super::interrupt::without_limits;
use super::logic::{
    AssumProblems, Binder, all_const, assum_problems, count_prems, flatten_params, incr_indexes,
    lift_abs, lift_all, list_all, list_implies, mk_equals, mk_implies, occs, strip_assums_concl,
    strip_assums_hyp, strip_imp_concl, strip_imp_prems, strip_prems,
};
use super::seq::{
    Seq, Step, chop_seq, cons_seq, defer_seq, empty_seq, flat_seq, it_right_seq, make_seq, map_seq,
    mapp_seq, of_cell,
};
use super::term::{
    Name, Term, TermNode, Typ, TypNode, Var, abstract_over, aconv, betapply, could_unify, eq_typ,
    exists_subterm, fastype_of, maxidx_of_term, mk_abs, mk_app, mk_const, mk_free, mk_var, prop_t,
    strip_all_body, strip_all_vars, subst_bound, update_abs, update_app,
};
use super::types::{TyEnv, subst_type};
use super::unify::{Tpair, Unifier, smash_unifiers, unifiers};

/// The parts of a theorem, which its handle dereferences to.
pub struct ThmNode {
    pub maxidx: i32,
    pub hyps: Rc<[Term]>,
    pub tpairs: Rc<[Tpair]>,
    pub prop: Term,
}

/// A theorem. Only this module builds one, so every Thm follows from the axioms by the rules here.
/// Cloning shares it; `ptr_eq` is the TypeScript's `===`.
#[derive(Clone)]
pub struct Thm(Rc<ThmNode>);

impl Deref for Thm {
    type Target = ThmNode;
    fn deref(&self) -> &ThmNode {
        &self.0
    }
}

impl Thm {
    /// The TypeScript's `===` on theorems.
    pub fn ptr_eq(left: &Thm, right: &Thm) -> bool {
        Rc::ptr_eq(&left.0, &right.0)
    }
}

fn make_thm(maxidx: i32, hyps: Rc<[Term]>, tpairs: Rc<[Tpair]>, prop: Term) -> Thm {
    Thm(Rc::new(ThmNode {
        maxidx,
        hyps,
        tpairs,
        prop,
    }))
}

fn union_hyps(left: &Rc<[Term]>, right: &Rc<[Term]>) -> Rc<[Term]> {
    if right.is_empty() {
        return left.clone();
    }
    if left.is_empty() {
        return right.clone();
    }
    left.iter()
        .cloned()
        .chain(
            right
                .iter()
                .filter(|hyp| !left.iter().any(|other| aconv(hyp, other)))
                .cloned(),
        )
        .collect()
}

fn union_tpairs(left: &Rc<[Tpair]>, right: &[Tpair]) -> Rc<[Tpair]> {
    if right.is_empty() {
        return left.clone();
    }
    left.iter()
        .cloned()
        .chain(
            right
                .iter()
                .filter(|pair| {
                    !left
                        .iter()
                        .any(|other| aconv(&pair.0, &other.0) && aconv(&pair.1, &other.1))
                })
                .cloned(),
        )
        .collect()
}

fn maxidx_tpairs(tpairs: &[Tpair], maxidx: i32) -> i32 {
    tpairs.iter().fold(maxidx, |result, pair| {
        maxidx_of_term(&pair.1, maxidx_of_term(&pair.0, result))
    })
}

/// An axiom or a theorem that the reference theories prove, taken on trust.
pub fn axiom_thm(prop: Term) -> Thm {
    make_thm(maxidx_of_term(&prop, -1), Rc::from([]), Rc::from([]), prop)
}

pub fn nprems(thm: &Thm) -> usize {
    count_prems(&thm.prop)
}

pub fn prems_of(thm: &Thm) -> Vec<Term> {
    strip_imp_prems(&thm.prop)
}

pub fn concl_of(thm: &Thm) -> &Term {
    strip_imp_concl(&thm.prop)
}

pub fn major_prem_of(thm: &Thm) -> Res<Term> {
    let Some(premise) = prems_of(thm).into_iter().next() else {
        return Err(thm_exn("major_prem_of: rule with no premises"));
    };
    Ok(strip_assums_concl(&premise).clone())
}

pub fn prem_of(thm: &Thm, index: i32) -> Res<Term> {
    let premises = prems_of(thm);
    usize::try_from(index - 1)
        .ok()
        .and_then(|position| premises.get(position))
        .cloned()
        .ok_or_else(|| thm_exn(format!("No subgoal {index}")))
}

pub fn assume(prop: Term) -> Res<Thm> {
    if !eq_typ(&fastype_of(&prop)?, &prop_t()) {
        return Err(thm_exn("assume: prop"));
    }
    if maxidx_of_term(&prop, -1) != -1 {
        return Err(thm_exn("assume: variables"));
    }
    Ok(make_thm(-1, Rc::from([prop.clone()]), Rc::from([]), prop))
}

pub fn implies_intr(premise: &Term, thm: &Thm) -> Res<Thm> {
    if !eq_typ(&fastype_of(premise)?, &prop_t()) {
        return Err(thm_exn("implies_intr: assumptions must have type prop"));
    }
    Ok(make_thm(
        maxidx_of_term(premise, -1).max(thm.maxidx),
        thm.hyps
            .iter()
            .filter(|hyp| !aconv(hyp, premise))
            .cloned()
            .collect(),
        thm.tpairs.clone(),
        mk_implies(premise.clone(), thm.prop.clone()),
    ))
}

/// The head, left and right of `c $ x $ y` for the constant c of that name.
fn dest_const_app2<'term>(
    term: &'term Term,
    name: &str,
) -> Option<(&'term Term, &'term Term, &'term Term)> {
    let (fun, right) = term.dest_app()?;
    let (head, left) = fun.dest_app()?;
    head.is_const_named(name).then_some((head, left, right))
}

pub fn implies_elim(major: &Thm, minor: &Thm) -> Res<Thm> {
    let Some((_, _, conclusion)) = dest_const_app2(&major.prop, "Pure.imp")
        .filter(|(_, premise, _)| aconv(premise, &minor.prop))
    else {
        return Err(thm_exn("implies_elim: major premise"));
    };
    Ok(make_thm(
        major.maxidx.max(minor.maxidx),
        union_hyps(&minor.hyps, &major.hyps),
        union_tpairs(&minor.tpairs, &major.tpairs),
        conclusion.clone(),
    ))
}

fn occurs_in(variable: &Term, terms: &[Term], tpairs: &[Tpair]) -> bool {
    let occurs = |term: &Term| occs(variable, term);
    terms.iter().any(occurs) || tpairs.iter().any(|pair| occurs(&pair.0) || occurs(&pair.1))
}

/// The name and type of a Free or a Var, and whether it is a Free.
fn dest_variable(variable: &Term) -> Option<(&Name, &Typ, bool)> {
    match &**variable {
        TermNode::Free { name, ty } => Some((name, ty, true)),
        TermNode::Var { name, ty, .. } => Some((name, ty, false)),
        _ => None,
    }
}

pub fn forall_intr(variable: &Term, thm: &Thm) -> Res<Thm> {
    let Some((name, ty, is_free)) = dest_variable(variable) else {
        return Err(thm_exn("forall_intr: not a variable"));
    };
    if occurs_in(variable, if is_free { &thm.hyps } else { &[] }, &thm.tpairs) {
        return Err(thm_exn(format!(
            "forall_intr: variable \"{name}\" free in assumptions"
        )));
    }
    Ok(make_thm(
        maxidx_of_term(variable, -1).max(thm.maxidx),
        thm.hyps.clone(),
        thm.tpairs.clone(),
        mk_app(
            all_const(ty.clone()),
            mk_abs(name.clone(), ty.clone(), abstract_over(variable, &thm.prop)),
        ),
    ))
}

pub fn forall_elim(term: &Term, thm: &Thm) -> Res<Thm> {
    let quantified = thm.prop.dest_app().and_then(|(fun, arg)| match &**fun {
        TermNode::Const { name, ty } if &**name == "Pure.all" => match &**ty {
            TypNode::Type { args, .. } => match args.first().map(|first| &**first) {
                Some(TypNode::Type { args, .. }) => Some((arg, args.first()?.clone())),
                _ => None,
            },
            _ => None,
        },
        _ => None,
    });
    let Some((body, domain)) = quantified else {
        return Err(thm_exn("forall_elim: not quantified"));
    };
    if !eq_typ(&fastype_of(term)?, &domain) {
        return Err(thm_exn("forall_elim: type mismatch"));
    }
    Ok(make_thm(
        maxidx_of_term(term, -1).max(thm.maxidx),
        thm.hyps.clone(),
        thm.tpairs.clone(),
        betapply(body, term),
    ))
}

pub fn reflexive(term: &Term) -> Res<Thm> {
    Ok(make_thm(
        maxidx_of_term(term, -1),
        Rc::from([]),
        Rc::from([]),
        mk_equals(term.clone(), term.clone())?,
    ))
}

fn dest_eq(thm: &Thm) -> Option<(&Term, &Term, &Term)> {
    dest_const_app2(&thm.prop, "Pure.eq")
}

pub fn symmetric(thm: &Thm) -> Res<Thm> {
    let Some((head, left, right)) = dest_eq(thm) else {
        return Err(thm_exn("symmetric"));
    };
    Ok(make_thm(
        thm.maxidx,
        thm.hyps.clone(),
        thm.tpairs.clone(),
        mk_app(mk_app(head.clone(), right.clone()), left.clone()),
    ))
}

pub fn transitive(first: &Thm, second: &Thm) -> Res<Thm> {
    let (Some(left), Some(right)) = (dest_eq(first), dest_eq(second)) else {
        return Err(thm_exn("transitive: premises"));
    };
    if !aconv(left.2, right.1) {
        return Err(thm_exn("transitive: middle term"));
    }
    Ok(make_thm(
        first.maxidx.max(second.maxidx),
        union_hyps(&first.hyps, &second.hyps),
        union_tpairs(&first.tpairs, &second.tpairs),
        mk_app(mk_app(left.0.clone(), left.1.clone()), right.2.clone()),
    ))
}

/// The argument and abstraction body of a beta redex.
fn dest_redex(term: &Term) -> Option<(&Term, &Term)> {
    let (fun, arg) = term.dest_app()?;
    Some((arg, fun.abs_body()?))
}

pub fn beta_conversion(full: bool, term: &Term) -> Res<Thm> {
    let redex = dest_redex(term);
    if !full && redex.is_none() {
        return Err(thm_exn("beta_conversion: not a redex"));
    }
    let reduced = match redex {
        Some((arg, body)) if !full => subst_bound(arg, body),
        _ => beta_norm(term)?,
    };
    Ok(make_thm(
        maxidx_of_term(term, -1),
        Rc::from([]),
        Rc::from([]),
        mk_equals(term.clone(), reduced)?,
    ))
}

pub fn eta_conversion(term: &Term) -> Res<Thm> {
    Ok(make_thm(
        maxidx_of_term(term, -1),
        Rc::from([]),
        Rc::from([]),
        mk_equals(term.clone(), eta_contract(term))?,
    ))
}

pub fn abstract_rule(name: &str, variable: &Term, thm: &Thm) -> Res<Thm> {
    let Some((_, left, right)) = dest_eq(thm) else {
        return Err(thm_exn("abstract_rule: premise not an equality"));
    };
    let Some((variable_name, ty, is_free)) = dest_variable(variable) else {
        return Err(thm_exn("abstract_rule: not a variable"));
    };
    if occurs_in(variable, if is_free { &thm.hyps } else { &[] }, &thm.tpairs) {
        return Err(thm_exn(format!(
            "abstract_rule: variable \"{variable_name}\" free in assumptions"
        )));
    }
    Ok(make_thm(
        thm.maxidx,
        thm.hyps.clone(),
        thm.tpairs.clone(),
        mk_equals(
            mk_abs(name, ty.clone(), abstract_over(variable, left)),
            mk_abs(name, ty.clone(), abstract_over(variable, right)),
        )?,
    ))
}

pub fn combination(first: &Thm, second: &Thm) -> Res<Thm> {
    let (Some(left), Some(right)) = (dest_eq(first), dest_eq(second)) else {
        return Err(thm_exn("combination: premises"));
    };
    let fun_type = fastype_of(left.1)?;
    let Some((domain, _)) = fun_type.dest_fun() else {
        return Err(thm_exn("combination: not function type"));
    };
    if !eq_typ(domain, &fastype_of(right.1)?) {
        return Err(thm_exn("combination: types"));
    }
    Ok(make_thm(
        first.maxidx.max(second.maxidx),
        union_hyps(&first.hyps, &second.hyps),
        union_tpairs(&first.tpairs, &second.tpairs),
        mk_equals(
            mk_app(left.1.clone(), right.1.clone()),
            mk_app(left.2.clone(), right.2.clone()),
        )?,
    ))
}

pub fn equal_elim(first: &Thm, second: &Thm) -> Res<Thm> {
    let Some((_, left, right)) = dest_eq(first) else {
        return Err(thm_exn("equal_elim: major premise"));
    };
    if !aconv(&second.prop, left) {
        return Err(thm_exn("equal_elim: not equal"));
    }
    Ok(make_thm(
        first.maxidx.max(second.maxidx),
        union_hyps(&first.hyps, &second.hyps),
        union_tpairs(&first.tpairs, &second.tpairs),
        right.clone(),
    ))
}

pub fn flexflex_rule(thm: &Thm) -> Res<Seq<Thm>> {
    let original = thm.clone();
    Ok(map_seq(
        move |envir: Envir| {
            if is_empty_envir(&envir) {
                return Ok(original.clone());
            }
            let mut tpairs = Vec::new();
            for pair in original.tpairs.iter() {
                let normal = (norm_term(&envir, &pair.0)?, norm_term(&envir, &pair.1)?);
                if !aconv(&normal.0, &normal.1) {
                    tpairs.push(normal);
                }
            }
            let prop = norm_term(&envir, &original.prop)?;
            Ok(make_thm(
                maxidx_tpairs(&tpairs, maxidx_of_term(&prop, -1)),
                original.hyps.clone(),
                tpairs.into(),
                prop,
            ))
        },
        smash_unifiers(&thm.tpairs, &empty_envir(thm.maxidx))?,
    ))
}

/// Thm.generalize: turns the named free variables into schematic ones with the given index.
pub fn generalize(frees: &[Name], index: i32, thm: &Thm) -> Res<Thm> {
    if frees.is_empty() {
        return Ok(thm.clone());
    }
    if index <= thm.maxidx {
        return Err(thm_exn("generalize: bad index"));
    }
    if thm.hyps.iter().any(|hyp| {
        exists_subterm(
            &mut |sub| matches!(&**sub, TermNode::Free { name, .. } if frees.contains(name)),
            hyp,
        )
    }) {
        return Err(thm_exn("generalize: variable free in assumptions"));
    }
    fn generalize_term(frees: &[Name], index: i32, term: &Term) -> Term {
        match &**term {
            TermNode::Free { name, ty } => {
                if frees.contains(name) {
                    mk_var(name.clone(), index, ty.clone())
                } else {
                    term.clone()
                }
            }
            TermNode::Abs { name, ty, body, .. } => mk_abs(
                name.clone(),
                ty.clone(),
                generalize_term(frees, index, body),
            ),
            TermNode::App { fun, arg, .. } => mk_app(
                generalize_term(frees, index, fun),
                generalize_term(frees, index, arg),
            ),
            _ => term.clone(),
        }
    }
    let prop = generalize_term(frees, index, &thm.prop);
    let tpairs: Vec<Tpair> = thm
        .tpairs
        .iter()
        .map(|pair| {
            (
                generalize_term(frees, index, &pair.0),
                generalize_term(frees, index, &pair.1),
            )
        })
        .collect();
    Ok(make_thm(
        maxidx_tpairs(&tpairs, maxidx_of_term(&prop, -1)),
        thm.hyps.clone(),
        tpairs.into(),
        prop,
    ))
}

#[derive(Clone)]
pub struct Instantiation {
    pub variable: Var,
    pub term: Term,
}

fn instantiate_term(insts: &[Instantiation], term: &Term) -> Term {
    let find = |variable: &Term| {
        let TermNode::Var { name, index, ty } = &**variable else {
            return None;
        };
        insts
            .iter()
            .find(|inst| match &*inst.variable {
                TermNode::Var {
                    name: other,
                    index: other_index,
                    ty: other_ty,
                } => other == name && other_index == index && eq_typ(other_ty, ty),
                _ => false,
            })
            .map(|inst| inst.term.clone())
    };
    fn subst(find: &impl Fn(&Term) -> Option<Term>, current: &Term) -> Term {
        match &**current {
            TermNode::Var { .. } => find(current).unwrap_or_else(|| current.clone()),
            TermNode::Abs { body, .. } => update_abs(current, subst(find, body), None),
            TermNode::App { fun, arg, .. } => {
                update_app(current, subst(find, fun), subst(find, arg))
            }
            _ => current.clone(),
        }
    }
    subst(&find, term)
}

/// Thm.instantiate for term variables. Every instance must have the type of its variable.
pub fn instantiate(insts: &[Instantiation], thm: &Thm) -> Res<Thm> {
    if insts.is_empty() {
        return Ok(thm.clone());
    }
    for inst in insts {
        let ty = inst.variable.ty().expect("a Var");
        if !eq_typ(ty, &fastype_of(&inst.term)?) {
            return Err(thm_exn("instantiate: type conflict"));
        }
    }
    let prop = instantiate_term(insts, &thm.prop);
    let tpairs: Vec<Tpair> = thm
        .tpairs
        .iter()
        .map(|pair| {
            (
                instantiate_term(insts, &pair.0),
                instantiate_term(insts, &pair.1),
            )
        })
        .collect();
    Ok(make_thm(
        maxidx_tpairs(&tpairs, maxidx_of_term(&prop, -1)),
        thm.hyps.clone(),
        tpairs.into(),
        prop,
    ))
}

/// Thm.instantiate for type variables.
fn instantiate_types_term(tyenv: &TyEnv, term: &Term) -> Term {
    if maxidx_of_term(term, -1) < 0 {
        return term.clone();
    }
    match &**term {
        TermNode::Const { name, ty } => mk_const(name.clone(), subst_type(tyenv, ty)),
        TermNode::Free { name, ty } => mk_free(name.clone(), subst_type(tyenv, ty)),
        TermNode::Var { name, index, ty } => mk_var(name.clone(), *index, subst_type(tyenv, ty)),
        TermNode::Bound { .. } => term.clone(),
        TermNode::Abs { name, ty, body, .. } => mk_abs(
            name.clone(),
            subst_type(tyenv, ty),
            instantiate_types_term(tyenv, body),
        ),
        TermNode::App { fun, arg, .. } => mk_app(
            instantiate_types_term(tyenv, fun),
            instantiate_types_term(tyenv, arg),
        ),
    }
}

pub fn instantiate_types(tyenv: &TyEnv, thm: &Thm) -> Thm {
    let prop = instantiate_types_term(tyenv, &thm.prop);
    let tpairs: Vec<Tpair> = thm
        .tpairs
        .iter()
        .map(|pair| {
            (
                instantiate_types_term(tyenv, &pair.0),
                instantiate_types_term(tyenv, &pair.1),
            )
        })
        .collect();
    make_thm(
        maxidx_tpairs(&tpairs, maxidx_of_term(&prop, -1)),
        thm.hyps.clone(),
        tpairs.into(),
        prop,
    )
}

/// Thm.renamed_prop: the same theorem with an alpha-equivalent proposition.
pub fn renamed_prop(prop: Term, thm: &Thm) -> Res<Thm> {
    if !aconv(&prop, &thm.prop) {
        return Err(term_exn("renamed_prop: props disagree"));
    }
    Ok(make_thm(
        thm.maxidx,
        thm.hyps.clone(),
        thm.tpairs.clone(),
        prop,
    ))
}

pub fn trivial(prop: &Term) -> Res<Thm> {
    if !eq_typ(&fastype_of(prop)?, &prop_t()) {
        return Err(thm_exn("trivial: the term must have type prop"));
    }
    Ok(make_thm(
        maxidx_of_term(prop, -1),
        Rc::from([]),
        Rc::from([]),
        mk_implies(prop.clone(), prop.clone()),
    ))
}

struct State {
    tpairs: Rc<[Tpair]>,
    before: Vec<Term>,
    goal: Term,
    conclusion: Term,
}

fn dest_state(state: &Thm, index: i32) -> Res<State> {
    let premises = strip_imp_prems(&state.prop);
    if index < 1 || index as usize > premises.len() {
        return Err(thm_exn(format!("dest_state {index}")));
    }
    let position = index as usize - 1;
    Ok(State {
        tpairs: state.tpairs.clone(),
        before: premises[..position].to_vec(),
        goal: premises[position].clone(),
        conclusion: list_implies(
            &premises[position + 1..],
            strip_imp_concl(&state.prop).clone(),
        ),
    })
}

/// Thm.lift_rule: lifts a rule over the parameters and premises of a goal of a state.
pub fn lift_rule(goal: &Term, goal_maxidx: i32, rule: &Thm) -> Thm {
    let increment = goal_maxidx + 1;
    let premises: Vec<Term> = strip_imp_prems(&rule.prop)
        .iter()
        .map(|premise| lift_all(increment, goal, premise))
        .collect();
    make_thm(
        rule.maxidx + increment,
        rule.hyps.clone(),
        rule.tpairs
            .iter()
            .map(|pair| {
                (
                    lift_abs(increment, goal, &pair.0),
                    lift_abs(increment, goal, &pair.1),
                )
            })
            .collect(),
        list_implies(
            &premises,
            lift_all(increment, goal, strip_imp_concl(&rule.prop)),
        ),
    )
}

pub fn incr_indexes_thm(increment: i32, thm: &Thm) -> Res<Thm> {
    if increment < 0 {
        return Err(thm_exn("negative increment"));
    }
    if increment == 0 {
        return Ok(thm.clone());
    }
    Ok(make_thm(
        thm.maxidx + increment,
        thm.hyps.clone(),
        thm.tpairs
            .iter()
            .map(|pair| {
                (
                    incr_indexes(&[], increment, &pair.0),
                    incr_indexes(&[], increment, &pair.1),
                )
            })
            .collect(),
        incr_indexes(&[], increment, &thm.prop),
    ))
}

/// What Thm.assumption's sequence shares.
struct Assumption {
    state: Thm,
    parts: State,
    problems: AssumProblems,
    conclusion: Term,
}

impl Assumption {
    fn new_thm(&self, unifier: Unifier) -> Res<Thm> {
        let envir = &unifier.envir;
        let is_empty = is_empty_envir(envir);
        let prop = list_implies(&self.parts.before, self.parts.conclusion.clone());
        let tpairs: Rc<[Tpair]> = if is_empty {
            unifier.tpairs.into()
        } else {
            unifier
                .tpairs
                .iter()
                .map(|pair| Ok((norm_term(envir, &pair.0)?, norm_term(envir, &pair.1)?)))
                .collect::<Res<Vec<_>>>()?
                .into()
        };
        Ok(make_thm(
            envir.maxidx,
            self.state.hyps.clone(),
            tpairs,
            if is_empty {
                prop
            } else {
                norm_term(envir, &prop)?
            },
        ))
    }
}

fn addprfs(assumption: Rc<Assumption>, position: usize) -> Seq<Thm> {
    if position >= assumption.problems.hyps.len() {
        return empty_seq();
    }
    make_seq(move || {
        let hyp = &assumption.problems.hyps[position];
        let shared = assumption.clone();
        mapp_seq(
            move |unifier| shared.new_thm(unifier),
            if could_unify(hyp, &assumption.problems.conclusion) {
                let pairs: Vec<Tpair> = [(
                    assumption.problems.abstract_term(hyp.clone()),
                    assumption.conclusion.clone(),
                )]
                .into_iter()
                .chain(assumption.parts.tpairs.iter().cloned())
                .collect();
                unifiers(&empty_envir(assumption.state.maxidx), &pairs)?
            } else {
                empty_seq()
            },
            addprfs(assumption.clone(), position + 1),
        )
        .pull()
    })
}

/// Thm.assumption: solves goal index by any of its assumptions, with unification.
pub fn assumption(index: i32, state: &Thm) -> Res<Seq<Thm>> {
    let parts = dest_state(state, index)?;
    let problems = assum_problems(-1, &parts.goal);
    let conclusion = problems.abstract_term(problems.conclusion.clone());
    Ok(addprfs(
        Rc::new(Assumption {
            state: state.clone(),
            parts,
            problems,
            conclusion,
        }),
        0,
    ))
}

/// Thm.eq_assumption: solves goal index by an assumption equal to its conclusion up to alpha and
/// eta.
pub fn eq_assumption(index: i32, state: &Thm) -> Res<Thm> {
    let parts = dest_state(state, index)?;
    let problems = assum_problems(-1, &parts.goal);
    // Envir.aeconv against each assumption, contracting the conclusion only once.
    let conclusion = eta_contract(&problems.conclusion);
    let is_found = problems
        .hyps
        .iter()
        .any(|hyp| aconv(hyp, &problems.conclusion) || aconv(&eta_contract(hyp), &conclusion));
    if !is_found {
        return Err(thm_exn("eq_assumption"));
    }
    Ok(make_thm(
        state.maxidx,
        state.hyps.clone(),
        state.tpairs.clone(),
        list_implies(&parts.before, parts.conclusion),
    ))
}

pub fn rotate_rule(count: i32, index: i32, state: &Thm) -> Res<Thm> {
    let parts = dest_state(state, index)?;
    let params: Vec<Binder> = strip_all_vars(&parts.goal)
        .into_iter()
        .map(|(name, ty)| Binder { name, ty })
        .collect();
    let rest = strip_all_body(&parts.goal);
    let asms = strip_imp_prems(rest);
    let concl = strip_imp_concl(rest);
    let total = asms.len() as i32;
    let shift = if count < 0 { total + count } else { count };
    if shift < 0 || shift > total {
        return Err(thm_exn(format!("rotate_rule {count}")));
    }
    let goal = if shift == 0 || shift == total {
        parts.goal.clone()
    } else {
        let shift = shift as usize;
        list_all(
            &params,
            list_implies(&[&asms[shift..], &asms[..shift]].concat(), concl.clone()),
        )
    };
    let premises = strip_imp_prems(&state.prop);
    Ok(make_thm(
        state.maxidx,
        state.hyps.clone(),
        state.tpairs.clone(),
        list_implies(
            &[&parts.before[..], &[goal], &premises[index as usize..]].concat(),
            strip_imp_concl(&state.prop).clone(),
        ),
    ))
}

pub fn permute_prems(fixed: usize, count: i32, rule: &Thm) -> Res<Thm> {
    let premises = strip_imp_prems(&rule.prop);
    let concl = strip_imp_concl(&rule.prop);
    if fixed > premises.len() {
        return Err(thm_exn(format!("permute_prems: j {fixed}")));
    }
    let moved = &premises[fixed..];
    let length = moved.len() as i32;
    let shift = if count < 0 { length + count } else { count };
    if shift == 0 || shift == length {
        return Ok(rule.clone());
    }
    if shift < 0 || shift > length {
        return Err(thm_exn(format!("permute_prems: k {count}")));
    }
    let shift = shift as usize;
    Ok(make_thm(
        rule.maxidx,
        rule.hyps.clone(),
        rule.tpairs.clone(),
        list_implies(
            &[&premises[..fixed], &moved[shift..], &moved[..shift]].concat(),
            concl.clone(),
        ),
    ))
}

#[derive(Clone, Copy)]
pub struct ComposeFlags {
    pub flatten: bool,
    pub is_match: bool,
    pub incremented: bool,
}

#[derive(Clone)]
pub struct ComposeRule {
    pub is_elim: bool,
    pub rule: Thm,
    pub subgoals: usize,
}

/// What bicompose_aux's sequences share.
struct Composer {
    flags: ComposeFlags,
    state: Thm,
    parts: Rc<State>,
    is_lifted: bool,
    orule: Thm,
    lift: i32,
    conclusion: Term,
}

impl Composer {
    fn addth(&self, new_as: &[Term], unifier: Unifier, rest: Seq<Thm>) -> Res<Seq<Thm>> {
        let envir = &unifier.envir;
        let normt = |term: &Term| norm_term(envir, term);
        let parts = &self.parts;
        let computed = || -> Res<(Rc<[Tpair]>, Vec<Term>, Term)> {
            if is_empty_envir(envir) {
                return Ok((
                    unifier.tpairs.clone().into(),
                    [&parts.before[..], new_as].concat(),
                    parts.conclusion.clone(),
                ));
            }
            let tpairs: Rc<[Tpair]> = unifier
                .tpairs
                .iter()
                .map(|pair| Ok((normt(&pair.0)?, normt(&pair.1)?)))
                .collect::<Res<Vec<_>>>()?
                .into();
            if above(envir, self.state.maxidx) {
                let normalized = if self.is_lifted {
                    new_as
                        .iter()
                        .map(|premise| norm_term_skip(envir, self.lift, premise))
                        .collect::<Res<Vec<_>>>()?
                } else {
                    new_as.iter().map(normt).collect::<Res<Vec<_>>>()?
                };
                return Ok((
                    tpairs,
                    [&parts.before[..], &normalized].concat(),
                    parts.conclusion.clone(),
                ));
            }
            if self.flags.is_match {
                return Err(Error::Compose);
            }
            Ok((
                tpairs,
                parts
                    .before
                    .iter()
                    .chain(new_as)
                    .map(normt)
                    .collect::<Res<Vec<_>>>()?,
                normt(&parts.conclusion)?,
            ))
        };
        match computed() {
            Ok((tpairs, premises, conclusion)) => Ok(cons_seq(
                make_thm(
                    envir.maxidx,
                    union_hyps(&self.orule.hyps, &self.state.hyps),
                    tpairs,
                    list_implies(&premises, conclusion),
                ),
                rest,
            )),
            Err(Error::Compose) => Ok(rest),
            Err(error) => Err(error),
        }
    }

    fn new_as(
        &self,
        premises: &[Term],
        index: i32,
        dpairs: &[Tpair],
        tpairs: &[Tpair],
    ) -> Res<Vec<Term>> {
        let rename = if self.is_lifted {
            rename_bvars(dpairs, tpairs, &self.conclusion, premises)
        } else {
            None
        };
        let renamed: Vec<Term> = match rename {
            None => premises.to_vec(),
            Some(rename) => premises
                .iter()
                .map(|premise| strip_apply(&rename, &self.conclusion, premise))
                .collect(),
        };
        if !self.flags.flatten {
            return Ok(renamed);
        }
        renamed
            .iter()
            .map(|premise| flatten_params(index, premise))
            .collect::<Res<Vec<_>>>()
            .map_err(|error| {
                if error.is(Exception::Term) {
                    thm_exn("bicompose: 1st premise")
                } else {
                    error
                }
            })
    }
}

/// What eres's search over the assumptions shares.
struct Eres {
    composer: Rc<Composer>,
    envir: Envir,
    rest: Vec<Term>,
    problems: AssumProblems,
    concl: Term,
    bbi: Tpair,
    dpairs: Vec<Tpair>,
}

fn tryasms(eres: Rc<Eres>, position: usize) -> Res<Seq<Thm>> {
    for index in position..eres.problems.hyps.len() {
        let asm = &eres.problems.hyps[index];
        if !could_unify(asm, &eres.problems.conclusion) {
            continue;
        }
        let closed = eres.problems.abstract_term(asm.clone());
        let pairs: Vec<Tpair> = [(closed.clone(), eres.concl.clone())]
            .into_iter()
            .chain(eres.dpairs.iter().cloned())
            .collect();
        let cell = unifiers(&eres.envir, &pairs)?.pull()?;
        let Some((unifier, _)) = &cell else {
            continue;
        };
        let prepared = eres.composer.new_as(
            &eres.rest,
            index as i32 + 1,
            &[eres.bbi.clone(), (eres.concl.clone(), closed)],
            &unifier.tpairs,
        )?;
        let composer = eres.composer.clone();
        let next = eres.clone();
        return Ok(it_right_seq(
            move |unifier, tail: Seq<Thm>| composer.addth(&prepared, unifier, tail),
            of_cell(cell),
            defer_seq(move || Ok(Step::Seq(tryasms(next.clone(), index + 1)?))),
        ));
    }
    Ok(empty_seq())
}

fn bicompose_aux(
    flags: ComposeFlags,
    state: &Thm,
    parts: Rc<State>,
    is_lifted: bool,
    compose: ComposeRule,
) -> Res<Seq<Thm>> {
    let orule = compose.rule;
    let lift =
        count_prems(strip_all_body(&parts.goal)) as i32 + if compose.is_elim { -1 } else { 0 };
    let (reversed_as, conclusion) =
        strip_prems(compose.subgoals, &[], &orule.prop).map_err(|error| {
            if error.is(Exception::Term) {
                thm_exn("bicompose: rule")
            } else {
                error
            }
        })?;
    let bbi = if is_lifted {
        strip_assums2(&conclusion, &parts.goal)
    } else {
        (conclusion.clone(), parts.goal.clone())
    };
    let dpairs: Vec<Tpair> = [bbi.clone()]
        .into_iter()
        .chain(orule.tpairs.iter().cloned())
        .chain(parts.tpairs.iter().cloned())
        .collect();
    let composer = Rc::new(Composer {
        flags,
        state: state.clone(),
        parts,
        is_lifted,
        orule: orule.clone(),
        lift,
        conclusion,
    });
    let eres = |envir: Envir, premises: Vec<Term>| -> Res<Seq<Thm>> {
        let Some((first, rest)) = premises.split_first() else {
            return Err(thm_exn("bicompose: no premises"));
        };
        let problems = assum_problems(lift + 1, first);
        let concl = problems.abstract_term(problems.conclusion.clone());
        tryasms(
            Rc::new(Eres {
                composer: composer.clone(),
                envir,
                rest: rest.to_vec(),
                problems,
                concl,
                bbi: bbi.clone(),
                dpairs: dpairs.clone(),
            }),
            0,
        )
    };
    let res = |envir: Envir| -> Res<Seq<Thm>> {
        let cell = unifiers(&envir, &dpairs)?.pull()?;
        let Some((unifier, _)) = &cell else {
            return Ok(empty_seq());
        };
        let premises: Vec<Term> = reversed_as.iter().rev().cloned().collect();
        let prepared =
            composer.new_as(&premises, 0, std::slice::from_ref(&bbi), &unifier.tpairs)?;
        let composer = composer.clone();
        Ok(it_right_seq(
            move |unifier, tail: Seq<Thm>| composer.addth(&prepared, unifier, tail),
            of_cell(cell),
            empty_seq(),
        ))
    };
    let initial = empty_envir(orule.maxidx.max(state.maxidx));
    let envir = if flags.incremented {
        Some(initial)
    } else {
        unify_var_types(state, &orule, &initial)?
    };
    let Some(envir) = envir else {
        return Ok(empty_seq());
    };
    if compose.is_elim {
        eres(envir, reversed_as.iter().rev().cloned().collect())
    } else {
        res(envir)
    }
}

pub fn bicompose(
    flags: ComposeFlags,
    compose: ComposeRule,
    index: i32,
    state: &Thm,
) -> Res<Seq<Thm>> {
    bicompose_aux(
        flags,
        state,
        Rc::new(dest_state(state, index)?),
        false,
        compose,
    )
}

fn could_bires(hyps: &[Term], goal: &Term, is_elim: bool, rule: &Thm) -> bool {
    if !could_unify(concl_of(rule), goal) {
        return false;
    }
    if !is_elim {
        return true;
    }
    prems_of(rule)
        .first()
        .is_some_and(|first| hyps.iter().any(|hyp| could_unify(first, hyp)))
}

#[derive(Clone)]
pub struct BiresRule {
    pub is_elim: bool,
    pub rule: Thm,
}

/// What biresolution's sequence of rules shares.
struct Biresolution {
    is_match: bool,
    rules: Vec<BiresRule>,
    state: Thm,
    parts: Rc<State>,
    goal: Term,
    hyps: Vec<Term>,
}

fn bires(biresolution: Rc<Biresolution>, position: usize) -> Seq<Seq<Thm>> {
    for current in position..biresolution.rules.len() {
        let brule = &biresolution.rules[current];
        if !could_bires(
            &biresolution.hyps,
            &biresolution.goal,
            brule.is_elim,
            &brule.rule,
        ) {
            continue;
        }
        let shared = biresolution.clone();
        return make_seq(move || {
            let brule = &shared.rules[current];
            let results = bicompose_aux(
                ComposeFlags {
                    flatten: true,
                    is_match: shared.is_match,
                    incremented: true,
                },
                &shared.state,
                shared.parts.clone(),
                true,
                ComposeRule {
                    is_elim: brule.is_elim,
                    rule: lift_rule(&shared.parts.goal, shared.state.maxidx, &brule.rule),
                    subgoals: nprems(&brule.rule),
                },
            )?;
            Ok(Some((results, bires(shared.clone(), current + 1))))
        });
    }
    empty_seq()
}

/// Thm.biresolution: resolves goal index with each rule, the elimination rules also solving their
/// first premise by an assumption.
pub fn biresolution(is_match: bool, rules: &[BiresRule], index: i32, state: &Thm) -> Res<Seq<Thm>> {
    let parts = dest_state(state, index)?;
    let goal = strip_assums_concl(&parts.goal).clone();
    let hyps = strip_assums_hyp(&parts.goal);
    Ok(flat_seq(bires(
        Rc::new(Biresolution {
            is_match,
            rules: rules.to_vec(),
            state: state.clone(),
            parts: Rc::new(parts),
            goal,
            hyps,
        }),
        0,
    )))
}

/// Thm.RSN: resolution that must produce exactly one resolvent.
pub fn rsn(rule: &Thm, index: i32, state: &Thm) -> Res<Thm> {
    let (results, _) = without_limits(|| {
        chop_seq(
            2,
            &biresolution(
                false,
                &[BiresRule {
                    is_elim: false,
                    rule: rule.clone(),
                }],
                index,
                state,
            )?,
        )
    })?;
    match results.len() {
        0 => Err(thm_exn(format!("RSN: no unifiers {index}"))),
        1 => Ok(results[0].clone()),
        _ => Err(thm_exn(format!("RSN: multiple unifiers {index}"))),
    }
}

pub fn rs(rule: &Thm, state: &Thm) -> Res<Thm> {
    rsn(rule, 1, state)
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::pure::conv::{Conversion, fconv_rule, gconv_rule, params_conv, prems_conv};
    use crate::pure::drule::{
        comp_incr, comp_no_flatten, forall_intr_vars, gen_all, is_norm_hhf, make_elim, protect_i,
        thin_rl, zero_var_indexes,
    };
    use crate::pure::interrupt::with_limits;
    use crate::pure::table::{IndexKey, update_table};
    use crate::pure::term::{add_vars, fold_atyps, fold_types, mk_bound, mk_type};
    use crate::pure::testing::{attempt, check_problems, parse_term, show};
    use crate::pure::types::empty_ty_env;
    use crate::pure::variable::trade;
    use prove_decide::Limits;

    /// A term in an expectation: its text, or past 160 characters its length and FNV-1a hash.
    pub(crate) fn digest(term: &Term) -> String {
        let text = show(term);
        if text.len() <= 160 {
            return text;
        }
        let hash = text.bytes().fold(0x811c_9dc5_u32, |hash, byte| {
            (hash ^ u32::from(byte)).wrapping_mul(0x0100_0193)
        });
        format!("#{}:{hash:x}", text.len())
    }

    pub(crate) fn show_thm(thm: &Thm) -> Vec<String> {
        let mut lines = vec![format!("maxidx {}", thm.maxidx)];
        lines.extend(thm.hyps.iter().map(|hyp| format!("hyp {}", digest(hyp))));
        lines.extend(
            thm.tpairs
                .iter()
                .map(|pair| format!("tpair {} =?= {}", digest(&pair.0), digest(&pair.1))),
        );
        lines.push(format!("prop {}", digest(&thm.prop)));
        lines
    }

    pub(crate) fn one(lines: &mut Vec<String>, label: &str, run: impl FnOnce() -> Res<Thm>) {
        lines.push(label.into());
        attempt(lines, |lines| {
            lines.extend(show_thm(&run()?));
            Ok(())
        });
    }

    pub(crate) fn many(
        lines: &mut Vec<String>,
        label: &str,
        count: usize,
        run: impl FnOnce() -> Res<Seq<Thm>>,
    ) {
        lines.push(label.into());
        attempt(lines, |lines| {
            let mut seq = run()?;
            for index in 0.. {
                if index == count {
                    lines.push("stop".into());
                    return Ok(());
                }
                let Some((result, rest)) = seq.pull()? else {
                    lines.push("end".into());
                    return Ok(());
                };
                lines.push(format!("result {index}"));
                lines.extend(show_thm(&result));
                seq = rest;
            }
            Ok(())
        });
    }

    /// The rules the problems refer to by number.
    pub(crate) fn rule_of(id: &str) -> Thm {
        let text = include_str!("../../testdata/kernel/rules.txt")
            .lines()
            .nth(id.parse().unwrap())
            .unwrap();
        axiom_thm(parse_term(text))
    }

    fn beta_conv() -> Conversion {
        Rc::new(|term| beta_conversion(true, term))
    }

    /// The kernel's rules, Drule's, conversions and Variable.trade on one proposition.
    fn rule_problem(text: &str) -> Vec<String> {
        let p = parse_term(text);
        let i = mk_type("i", Vec::new());
        let mut lines = Vec::new();
        let limits = Limits::new(f64::INFINITY, None, None);
        with_limits(&limits, || {
            let lines = &mut lines;
            let thm = axiom_thm(p.clone());
            one(lines, "axiom", || Ok(thm.clone()));
            lines.push(format!("nprems {}", nprems(&thm)));
            lines.push("major_prem_of".into());
            attempt(lines, |lines| {
                lines.push(digest(&major_prem_of(&thm)?));
                Ok(())
            });
            lines.push("prem_of".into());
            attempt(lines, |lines| {
                lines.push(digest(&prem_of(&thm, 1)?));
                Ok(())
            });
            attempt(lines, |lines| {
                lines.push(digest(&prem_of(&thm, 0)?));
                Ok(())
            });
            one(lines, "trivial", || trivial(&p));
            one(lines, "assume", || assume(p.clone()));
            let first = prems_of(&thm).first().cloned().unwrap_or_else(|| p.clone());
            one(lines, "implies_intr", || implies_intr(&first, &thm));
            one(lines, "implies_elim", || implies_elim(&trivial(&p)?, &thm));
            one(lines, "implies_elim_bad", || implies_elim(&thm, &thm));
            one(lines, "incr_indexes", || incr_indexes_thm(2, &thm));
            one(lines, "permute_prems 0 1", || permute_prems(0, 1, &thm));
            one(lines, "permute_prems 1 -1", || permute_prems(1, -1, &thm));
            one(lines, "permute_prems 0 -5", || permute_prems(0, -5, &thm));
            one(lines, "rotate_rule 1", || rotate_rule(1, 1, &trivial(&p)?));
            one(lines, "rotate_rule -1", || {
                rotate_rule(-1, 1, &trivial(&p)?)
            });
            one(lines, "eq_assumption", || eq_assumption(1, &trivial(&p)?));
            many(lines, "assumption", 3, || assumption(1, &trivial(&p)?));
            many(lines, "flexflex", 3, || flexflex_rule(&thm));
            let vars = add_vars(&p, Vec::new());
            let insts: Vec<Instantiation> = vars
                .iter()
                .map(|variable| Instantiation {
                    variable: variable.clone(),
                    term: mk_free(
                        format!("f_{}", variable.name().unwrap()),
                        variable.ty().unwrap().clone(),
                    ),
                })
                .collect();
            let instantiated = instantiate(&insts, &thm).unwrap();
            one(lines, "instantiate", || Ok(instantiated.clone()));
            one(lines, "instantiate_bad", || {
                let bad: Vec<Instantiation> = insts
                    .iter()
                    .map(|inst| Instantiation {
                        variable: inst.variable.clone(),
                        term: mk_free("bad", mk_type("bad", Vec::new())),
                    })
                    .collect();
                instantiate(&bad, &thm)
            });
            let names: Vec<Name> = insts
                .iter()
                .map(|inst| inst.term.name().unwrap().clone())
                .collect();
            one(lines, "generalize", || {
                generalize(&names, thm.maxidx + 1, &instantiated)
            });
            let tvars = fold_types(
                &mut |ty, table| {
                    fold_atyps(
                        &mut |atom, inner: TyEnv| match &**atom {
                            TypNode::TVar { name, index, .. } => update_table(
                                &inner,
                                IndexKey {
                                    name: name.clone(),
                                    index: *index,
                                },
                                mk_type("c", Vec::new()),
                            ),
                            _ => inner,
                        },
                        ty,
                        table,
                    )
                },
                &p,
                empty_ty_env(),
            );
            one(lines, "instantiate_types", || {
                Ok(instantiate_types(&tvars, &thm))
            });
            let quantified = forall_intr_vars(&thm).unwrap();
            one(lines, "forall_intr_vars", || Ok(quantified.clone()));
            one(lines, "gen_all", || gen_all(&quantified));
            one(lines, "zero_var_indexes", || {
                zero_var_indexes(&incr_indexes_thm(3, &thm)?)
            });
            one(lines, "make_elim", || make_elim(&thm));
            one(lines, "comp_incr", || comp_incr(&thm, &thin_rl()));
            one(lines, "comp_no_flatten", || {
                comp_no_flatten(&thm, nprems(&thm), 1, &protect_i())
            });
            lines.push(format!(
                "is_norm_hhf {} {}",
                is_norm_hhf(false, &p),
                is_norm_hhf(true, &p)
            ));
            one(lines, "beta", || beta_conversion(true, &p));
            one(lines, "beta_redex", || beta_conversion(false, &p));
            one(lines, "eta", || eta_conversion(&p));
            one(lines, "symmetric", || symmetric(&reflexive(&p)?));
            one(lines, "transitive", || {
                transitive(&reflexive(&p)?, &symmetric(&reflexive(&p)?)?)
            });
            one(lines, "equal_elim", || equal_elim(&reflexive(&p)?, &thm));
            let domain = match quantified.prop.dest_app() {
                Some((_, arg)) if arg.is_abs() => arg.ty().unwrap().clone(),
                _ => i.clone(),
            };
            one(lines, "forall_elim", || {
                forall_elim(&mk_free("t", domain), &quantified)
            });
            let free = insts
                .first()
                .map_or_else(|| mk_free("t", i.clone()), |inst| inst.term.clone());
            one(lines, "forall_intr", || forall_intr(&free, &instantiated));
            one(lines, "forall_intr_hyp", || {
                forall_intr(
                    &free,
                    &implies_elim(
                        &trivial(&instantiated.prop)?,
                        &assume(instantiated.prop.clone())?,
                    )?,
                )
            });
            one(lines, "abstract_rule", || {
                abstract_rule("z", &free, &reflexive(&instantiated.prop)?)
            });
            one(lines, "combination", || match p.dest_app() {
                Some((fun, arg)) => combination(&reflexive(fun)?, &reflexive(arg)?),
                None => combination(&reflexive(&p)?, &reflexive(&p)?),
            });
            one(lines, "renamed_prop", || renamed_prop(p.clone(), &thm));
            let wrapped = list_implies(
                &prems_of(&thm)
                    .into_iter()
                    .map(|premise| mk_app(mk_abs("u", prop_t(), mk_bound(0)), premise))
                    .collect::<Vec<_>>(),
                concl_of(&thm).clone(),
            );
            one(lines, "fconv_prems", || {
                fconv_rule(&prems_conv(beta_conv()), &axiom_thm(wrapped.clone()))
            });
            one(lines, "fconv_params", || {
                fconv_rule(&params_conv(beta_conv()), &axiom_thm(wrapped.clone()))
            });
            let closed_goal = forall_intr_vars(&axiom_thm(wrapped.clone()))
                .unwrap()
                .prop
                .clone();
            one(lines, "gconv", || {
                gconv_rule(
                    &params_conv(prems_conv(beta_conv())),
                    1,
                    &trivial(&closed_goal)?,
                )
            });
            one(lines, "gconv_bad", || {
                gconv_rule(&beta_conv(), 2, &trivial(&closed_goal)?)
            });
            lines.push("trade".into());
            attempt(lines, |lines| {
                let derive = |fixed: Thm| {
                    Ok(vec![
                        fixed.clone(),
                        trivial(&fixed.prop)?,
                        incr_indexes_thm(1, &fixed)?,
                    ])
                };
                for result in trade(derive, &thm)? {
                    lines.extend(show_thm(&result));
                }
                Ok(())
            });
        });
        lines.push(format!("steps {}", limits.steps()));
        lines
    }

    /// Resolution of a rule with goal 1 of a state, in each of the kernel's ways.
    fn resolve_problem(fields: &[&str]) -> Vec<String> {
        let count: usize = fields[0].parse().unwrap();
        let rule = rule_of(fields[1]);
        let state = axiom_thm(parse_term(fields[2]));
        let mut lines = Vec::new();
        let limits = Limits::new(f64::INFINITY, None, None);
        with_limits(&limits, || {
            let lines = &mut lines;
            let brule = |is_elim| {
                [BiresRule {
                    is_elim,
                    rule: rule.clone(),
                }]
            };
            many(lines, "intro", count, || {
                biresolution(false, &brule(false), 1, &state)
            });
            many(lines, "elim", count, || {
                biresolution(false, &brule(true), 1, &state)
            });
            many(lines, "match", count, || {
                biresolution(true, &brule(false), 1, &state)
            });
            many(lines, "ematch", count, || {
                biresolution(true, &brule(true), 1, &state)
            });
            let compose = |is_elim, incremented| {
                bicompose(
                    ComposeFlags {
                        flatten: true,
                        is_match: false,
                        incremented,
                    },
                    ComposeRule {
                        is_elim,
                        rule: rule.clone(),
                        subgoals: nprems(&rule),
                    },
                    1,
                    &state,
                )
            };
            many(lines, "compose", count, || compose(false, false));
            many(lines, "ecompose", count, || compose(true, false));
            many(lines, "compose_incremented", count, || compose(false, true));
            one(lines, "rsn", || rsn(&rule, 1, &state));
        });
        lines.push(format!("steps {}", limits.steps()));
        lines
    }

    // The expectations are recorded from thm.ts, drule.ts, conv.ts and variable.ts.
    #[test]
    fn rules_match_the_typescript() {
        check_problems(
            include_str!("../../testdata/kernel/thm.txt"),
            |kind, fields| match kind {
                "rule" => rule_problem(fields[0]),
                _ => panic!("unknown problem {kind}"),
            },
        );
    }

    // The expectations are recorded from thm.ts and bicompose.ts.
    #[test]
    fn resolution_matches_the_typescript() {
        check_problems(
            include_str!("../../testdata/kernel/resolve.txt"),
            |kind, fields| match kind {
                "resolve" => resolve_problem(fields),
                _ => panic!("unknown problem {kind}"),
            },
        );
    }

    #[test]
    fn keeps_the_basic_rules_and_shares_theorems() {
        assert!(Thm::ptr_eq(&thin_rl(), &thin_rl()));
        let thm = axiom_thm(parse_term("?P.0:prop"));
        assert!(Thm::ptr_eq(&generalize(&[], 1, &thm).unwrap(), &thm));
        assert!(Thm::ptr_eq(&instantiate(&[], &thm).unwrap(), &thm));
        assert!(Thm::ptr_eq(&incr_indexes_thm(0, &thm).unwrap(), &thm));
    }
}
