//! Ported from Isabelle2025's Pure/raw_simplifier.ML, the simpset and its rewrite rules. Copyright
//! (c) 1986-2025 University of Cambridge, Technische Universitaet Muenchen, and contributors, see
//! LICENSE.
//!
//! Isabelle/TLA+ declares no congruence procedures, so the simpset leaves them out.
//!
//! (`pure/raw-simplifier.ts`.) The simpset's functions (how theorems become rewrite rules, the
//! simplification procedures, the subgoaler, loopers and solvers) may raise, so they return a
//! `Res`; building a tactic raises nothing.

use std::cmp::Ordering;
use std::collections::HashSet;
use std::rc::Rc;

use crate::error::{Exception, Res, error_exn};

use super::drule::symmetric_thm;
use super::envir::{empty_tenv, eta_contract};
use super::logic::{dest_equals, is_equals, occs, strip_imp_concl, strip_imp_prems};
use super::net::{Net, empty_net, insert_net, insert_term_net, key_of_term};
use super::pattern::{is_first_order, is_pattern, matches};
use super::table::{Table, empty_table};
use super::tactical::{GoalTactic, eq_thm_prop, no_tac};
use super::term::{
    Name, Term, TermNode, Typ, TypNode, Var, aconv, eq_typ, exists_subterm, exists_type, fold_vars,
    head_of,
};
use super::thm::{Thm, rs};
use super::types::empty_ty_env;

#[derive(Clone)]
pub struct Rrule {
    pub thm: Thm,
    pub lhs: Term,
    pub elhs: Term,
    pub extra: bool,
    pub fo: bool,
    pub perm: bool,
}

#[derive(Clone)]
pub struct Procedure {
    pub name: Name,
    pub lhs: Term,
    pub proc: Rc<dyn Fn(&SimpContext, &Term) -> Res<Option<Thm>>>,
}

#[derive(Clone)]
pub struct Solver {
    pub name: Name,
    pub tactic: Rc<dyn Fn(&SimpContext) -> GoalTactic>,
}

#[derive(Clone)]
pub struct LoopTac {
    pub name: Name,
    pub tactic: Rc<dyn Fn(&SimpContext) -> GoalTactic>,
}

#[derive(Clone)]
pub struct MkRews {
    pub mk: Rc<dyn Fn(&Thm, &SimpContext) -> Res<Vec<Thm>>>,
    pub mk_eq_true: Rc<dyn Fn(&Thm) -> Res<Option<Thm>>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CongName {
    pub is_const: bool,
    pub name: Name,
}

#[derive(Clone)]
pub struct Simpset {
    pub rules: Net<Rrule>,
    pub prems: Rc<[Thm]>,
    pub depth: usize,
    pub congs: Table<Name, Thm>,
    pub weak_congs: Rc<[CongName]>,
    pub simprocs: Net<Procedure>,
    pub mk_rews: MkRews,
    pub subgoal_tac: Rc<dyn Fn(&SimpContext) -> GoalTactic>,
    pub loop_tacs: Rc<[LoopTac]>,
    pub unsafe_solvers: Rc<[Solver]>,
    pub safe_solvers: Rc<[Solver]>,
}

/// The part of an Isabelle proof context that the simplifier reads: the simpset, and the counter
/// that names the free variables standing for bound ones. (The TypeScript's time limits are the
/// thread's, `interrupt::with_limits`.)
#[derive(Clone)]
pub struct SimpContext {
    pub simpset: Simpset,
    pub bounds: i32,
}

pub const SIMP_DEPTH_LIMIT: usize = 40;

pub fn cong_key(name: &CongName) -> Name {
    format!("{}{}", if name.is_const { "1" } else { "0" }, name.name).into()
}

pub fn cong_name(term: &Term) -> Option<CongName> {
    match &**term {
        TermNode::Const { name, .. } => Some(CongName {
            is_const: true,
            name: name.clone(),
        }),
        TermNode::Free { name, .. } => Some(CongName {
            is_const: false,
            name: name.clone(),
        }),
        _ => None,
    }
}

pub(crate) fn vars_of(term: &Term) -> Vec<Var> {
    fold_vars(
        &mut |atom, mut result: Vec<Var>| {
            result.push(atom.clone());
            result
        },
        term,
        Vec::new(),
    )
}

pub(crate) fn has_var(vars: &[Var], variable: &Var) -> bool {
    let TermNode::Var { name, index, ty } = &**variable else {
        return false;
    };
    vars.iter().any(|other| match &**other {
        TermNode::Var {
            name: other_name,
            index: other_index,
            ty: other_ty,
        } => other_name == name && other_index == index && eq_typ(other_ty, ty),
        _ => false,
    })
}

fn add_tvar_keys(ty: &Typ, keys: &mut HashSet<(i32, Name)>) {
    match &**ty {
        TypNode::TVar { name, index, .. } => {
            keys.insert((*index, name.clone()));
        }
        TypNode::Type { args, .. } => {
            for arg in args {
                add_tvar_keys(arg, keys);
            }
        }
        TypNode::TFree { .. } => {}
    }
}

fn has_new_tvar(ty: &Typ, keys: &HashSet<(i32, Name)>) -> bool {
    match &**ty {
        TypNode::TVar { name, index, .. } => !keys.contains(&(*index, name.clone())),
        TypNode::Type { args, .. } => args.iter().any(|arg| has_new_tvar(arg, keys)),
        TypNode::TFree { .. } => false,
    }
}

/// rewrite_rule_extra_vars: whether the right-hand sides have variables outside the left-hand side
/// and the premises.
fn rewrite_rule_extra_vars(prems: &[Term], elhs: &Term, erhss: &[Term]) -> bool {
    let terms: Vec<&Term> = std::iter::once(elhs).chain(prems).collect();
    let vars: Vec<Var> = terms.iter().flat_map(|term| vars_of(term)).collect();
    let mut tvars = HashSet::new();
    for term in &terms {
        exists_type(
            &mut |ty| {
                add_tvar_keys(ty, &mut tvars);
                false
            },
            term,
        );
    }
    erhss.iter().any(|erhs| {
        exists_type(&mut |ty| has_new_tvar(ty, &tvars), erhs)
            || exists_subterm(&mut |sub| sub.is_var() && !has_var(&vars, sub), erhs)
    })
}

fn mk_rrule2(thm: &Thm, lhs: Term, elhs: Term, perm: bool) -> Rrule {
    let rhss: Vec<Term> = thm
        .tpairs
        .iter()
        .flat_map(|pair| [pair.0.clone(), pair.1.clone()])
        .chain(std::iter::once(thm.prop.clone()))
        .collect();
    Rrule {
        thm: thm.clone(),
        extra: rewrite_rule_extra_vars(&[], &elhs, &rhss),
        fo: is_first_order(&elhs) || !is_pattern(&elhs),
        lhs,
        elhs,
        perm,
    }
}

fn vperm(left: &Term, right: &Term) -> bool {
    match (&**left, &**right) {
        (TermNode::Var { .. }, TermNode::Var { .. }) => true,
        (TermNode::Abs { body, .. }, TermNode::Abs { body: other, .. }) => vperm(body, other),
        (
            TermNode::App { fun, arg, .. },
            TermNode::App {
                fun: other_fun,
                arg: other_arg,
                ..
            },
        ) => vperm(fun, other_fun) && vperm(arg, other_arg),
        _ => aconv_exact(left, right),
    }
}

fn aconv_exact(left: &Term, right: &Term) -> bool {
    match (&**left, &**right) {
        (
            TermNode::Const { name, ty },
            TermNode::Const {
                name: other,
                ty: other_ty,
            },
        )
        | (
            TermNode::Free { name, ty },
            TermNode::Free {
                name: other,
                ty: other_ty,
            },
        ) => name == other && eq_typ(ty, other_ty),
        (
            TermNode::Var { name, index, ty },
            TermNode::Var {
                name: other,
                index: other_index,
                ty: other_ty,
            },
        ) => name == other && index == other_index && eq_typ(ty, other_ty),
        (TermNode::Bound { index }, TermNode::Bound { index: other }) => index == other,
        (
            TermNode::Abs { name, ty, body, .. },
            TermNode::Abs {
                name: other,
                ty: other_ty,
                body: other_body,
                ..
            },
        ) => name == other && eq_typ(ty, other_ty) && aconv_exact(body, other_body),
        (
            TermNode::App { fun, arg, .. },
            TermNode::App {
                fun: other_fun,
                arg: other_arg,
                ..
            },
        ) => aconv_exact(fun, other_fun) && aconv_exact(arg, other_arg),
        _ => false,
    }
}

fn is_var_perm(left: &Term, right: &Term) -> bool {
    if !vperm(left, right) {
        return false;
    }
    let left_vars = vars_of(left);
    let right_vars = vars_of(right);
    left_vars
        .iter()
        .all(|variable| has_var(&right_vars, variable))
        && right_vars
            .iter()
            .all(|variable| has_var(&left_vars, variable))
}

struct Decomposed {
    prems: Vec<Term>,
    lhs: Term,
    elhs: Term,
    rhs: Term,
    perm: bool,
}

fn decomp_simp(thm: &Thm) -> Res<Decomposed> {
    let prems = strip_imp_prems(&thm.prop);
    let concl = strip_imp_concl(&thm.prop);
    if !is_equals(concl) {
        return Err(error_exn("Rewrite rule not a meta-equality"));
    }
    let (lhs, rhs) = dest_equals(concl)?;
    let elhs = eta_contract(&lhs);
    let erhs = eta_contract(&rhs);
    let perm = is_var_perm(&elhs, &erhs) && !aconv(&elhs, &erhs) && !elhs.is_var();
    Ok(Decomposed {
        prems,
        lhs,
        elhs,
        rhs,
        perm,
    })
}

/// A rewrite rule before insert_rrule completes it.
#[derive(Clone)]
pub struct RawRrule {
    pub thm: Thm,
    pub lhs: Term,
    pub elhs: Term,
    pub perm: bool,
}

fn mk_eq_true(context: &SimpContext, thm: &Thm) -> Res<Vec<RawRrule>> {
    let Some(eq_true) = (context.simpset.mk_rews.mk_eq_true)(thm)? else {
        return Ok(Vec::new());
    };
    let decomposed = decomp_simp(&eq_true)?;
    Ok(vec![RawRrule {
        thm: eq_true,
        lhs: decomposed.lhs,
        elhs: decomposed.elhs,
        perm: false,
    }])
}

fn rrule_eq_true(
    context: &SimpContext,
    thm: &Thm,
    decomposed: Decomposed,
    original: &Thm,
) -> Res<Vec<RawRrule>> {
    let is_extra = rewrite_rule_extra_vars(&[], &decomposed.lhs, &[decomposed.rhs]);
    let rrule = RawRrule {
        thm: thm.clone(),
        lhs: decomposed.lhs,
        elhs: decomposed.elhs,
        perm: false,
    };
    if !is_extra {
        return Ok(vec![rrule]);
    }
    let mut rrules = mk_eq_true(context, original)?;
    rrules.push(rrule);
    Ok(rrules)
}

fn perm_rrule(thm: &Thm, decomposed: Decomposed) -> Vec<RawRrule> {
    vec![RawRrule {
        thm: thm.clone(),
        lhs: decomposed.lhs,
        elhs: decomposed.elhs,
        perm: true,
    }]
}

fn mk_rrule(context: &SimpContext, thm: &Thm) -> Res<Vec<RawRrule>> {
    let decomposed = decomp_simp(thm)?;
    if decomposed.perm {
        return Ok(perm_rrule(thm, decomposed));
    }
    if rewrite_rule_extra_vars(
        &decomposed.prems,
        &decomposed.lhs,
        std::slice::from_ref(&decomposed.rhs),
    ) || decomposed.elhs.is_var()
    {
        return mk_eq_true(context, thm);
    }
    rrule_eq_true(context, thm, decomposed, thm)
}

/// default_reorient: catches looping rules and stupid orientations.
fn default_reorient(prems: &[Term], lhs: &Term, rhs: &Term) -> Res<bool> {
    Ok(
        rewrite_rule_extra_vars(prems, lhs, std::slice::from_ref(rhs))
            || head_of(lhs).is_var()
            || std::iter::once(rhs)
                .chain(prems)
                .any(|term| occs(lhs, term))
            || (prems.is_empty() && matches(lhs, rhs, &empty_ty_env(), &empty_tenv())?)
            || (lhs.is_const() && !rhs.is_const()),
    )
}

fn orient_rrule(context: &SimpContext, thm: &Thm) -> Res<Vec<RawRrule>> {
    let decomposed = decomp_simp(thm)?;
    if decomposed.perm {
        return Ok(perm_rrule(thm, decomposed));
    }
    if !default_reorient(&decomposed.prems, &decomposed.lhs, &decomposed.rhs)? {
        return rrule_eq_true(context, thm, decomposed, thm);
    }
    if default_reorient(&decomposed.prems, &decomposed.rhs, &decomposed.lhs)? {
        return mk_eq_true(context, thm);
    }
    let symmetric = match rs(thm, &symmetric_thm()) {
        Ok(symmetric) => symmetric,
        Err(error) if error.is(Exception::Thm) => return Ok(Vec::new()),
        Err(error) => return Err(error),
    };
    let flipped = decomp_simp(&symmetric)?;
    rrule_eq_true(context, &symmetric, flipped, thm)
}

/// extract_safe_rrules: the rewrite rules of an assumption, oriented to avoid loops.
pub fn extract_safe_rrules(context: &SimpContext, thm: &Thm) -> Res<Vec<RawRrule>> {
    let mut rrules = Vec::new();
    for rew in (context.simpset.mk_rews.mk)(thm, context)? {
        rrules.extend(orient_rrule(context, &rew)?);
    }
    Ok(rrules)
}

fn eq_rrule(left: &Rrule, right: &Rrule) -> bool {
    eq_thm_prop(&left.thm, &right.thm)
}

pub fn insert_rrule(raw: &RawRrule, simpset: &Simpset) -> Simpset {
    let rrule = mk_rrule2(&raw.thm, raw.lhs.clone(), raw.elhs.clone(), raw.perm);
    let keys = key_of_term(&rrule.elhs);
    match insert_net(eq_rrule, &keys, rrule, &simpset.rules) {
        None => simpset.clone(),
        Some(rules) => Simpset {
            rules,
            ..simpset.clone()
        },
    }
}

pub fn add_simps(context: &SimpContext, thms: &[Thm]) -> Res<Simpset> {
    let mut rews = Vec::new();
    for thm in thms {
        rews.extend((context.simpset.mk_rews.mk)(thm, context)?);
    }
    let mut raws = Vec::new();
    for rew in &rews {
        raws.extend(mk_rrule(context, rew)?);
    }
    Ok(raws.iter().fold(context.simpset.clone(), |simpset, raw| {
        insert_rrule(raw, &simpset)
    }))
}

/// mk_procrule: the rewrite rule a simplification procedure proves.
pub fn mk_procrule(thm: &Thm) -> Res<Vec<Rrule>> {
    let decomposed = decomp_simp(thm)?;
    if rewrite_rule_extra_vars(
        &decomposed.prems,
        &decomposed.lhs,
        std::slice::from_ref(&decomposed.rhs),
    ) {
        return Ok(Vec::new());
    }
    Ok(vec![mk_rrule2(thm, decomposed.lhs, decomposed.elhs, false)])
}

pub fn add_prems(thms: &[Thm], simpset: &Simpset) -> Simpset {
    Simpset {
        prems: thms.iter().chain(simpset.prems.iter()).cloned().collect(),
        ..simpset.clone()
    }
}

/// Rebuilds a rule net from Net.entries, as the reference simpset lists them.
pub fn rules_from_entries(thms: &[Thm]) -> Res<Net<Rrule>> {
    thms.iter().rev().try_fold(empty_net(), |net, thm| {
        let decomposed = decomp_simp(thm)?;
        let rrule = mk_rrule2(thm, decomposed.lhs, decomposed.elhs, decomposed.perm);
        Ok(insert_term_net(&rrule.elhs.clone(), rrule, &net))
    })
}

fn string_ord(left: &Name, right: &Name) -> Ordering {
    left.as_bytes().cmp(right.as_bytes())
}

pub fn empty_congs() -> Table<Name, Thm> {
    empty_table(string_ord)
}

/// empty_ss: rewrites with meta-equalities only, and solves no subgoal.
pub fn empty_simpset() -> Simpset {
    Simpset {
        rules: empty_net(),
        prems: Rc::from([]),
        depth: 0,
        congs: empty_congs(),
        weak_congs: Rc::from([]),
        simprocs: empty_net(),
        mk_rews: MkRews {
            mk: Rc::new(|thm, _| {
                Ok(if is_equals(strip_imp_concl(&thm.prop)) {
                    vec![thm.clone()]
                } else {
                    Vec::new()
                })
            }),
            mk_eq_true: Rc::new(|_| Ok(None)),
        },
        subgoal_tac: Rc::new(|_| Rc::new(|_| no_tac())),
        loop_tacs: Rc::from([]),
        unsafe_solvers: Rc::from([]),
        safe_solvers: Rc::from([]),
    }
}
