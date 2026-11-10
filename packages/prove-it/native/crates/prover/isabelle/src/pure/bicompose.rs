//! Ported from Isabelle2025's Pure/thm.ML. Copyright (c) 1986-2025 University of Cambridge,
//! Technische Universitaet Muenchen, and contributors, see LICENSE.
//!
//! The term operations behind Thm.bicompose, which builds the theorem itself in thm.rs
//! (`pure/bicompose.ts`).

use crate::error::{Res, error_exn};

use super::envir::{Envir, norm_term};
use super::logic::{all_const, mk_implies};
use super::pattern::unify_types_envir;
use super::term::{
    Name, Term, TermNode, Typ, eq_typ, fold_vars, match_bvars, mk_abs, mk_app, mk_var,
};
use super::thm::Thm;
use super::types::norm_type;
use super::unify::Tpair;

/// The head, premise and conclusion of `Pure.imp $ A $ B`.
fn dest_imp_app(term: &Term) -> Option<(&Term, &Term, &Term)> {
    let (fun, conclusion) = term.dest_app()?;
    let (head, premise) = fun.dest_app()?;
    head.is_const_named("Pure.imp")
        .then_some((head, premise, conclusion))
}

/// The head, bound name, type and body of `Pure.all $ Abs …`.
fn dest_all_app(term: &Term) -> Option<(&Term, &Name, &Typ, &Term)> {
    let (fun, arg) = term.dest_app()?;
    if !fun.is_const_named("Pure.all") {
        return None;
    }
    match &**arg {
        TermNode::Abs { name, ty, body, .. } => Some((fun, name, ty, body)),
        _ => None,
    }
}

pub fn strip_apply(apply: &dyn Fn(&Term) -> Term, lifted: &Term, term: &Term) -> Term {
    if let (Some((head, _, lifted_concl)), Some((_, premise, concl))) =
        (dest_imp_app(lifted), dest_imp_app(term))
    {
        return mk_app(
            mk_app(head.clone(), premise.clone()),
            strip_apply(apply, lifted_concl, concl),
        );
    }
    if let (Some((lifted_fun, _, _, lifted_body)), Some((_, name, ty, body))) =
        (dest_all_app(lifted), dest_all_app(term))
    {
        return mk_app(
            lifted_fun.clone(),
            mk_abs(
                name.clone(),
                ty.clone(),
                strip_apply(apply, lifted_body, body),
            ),
        );
    }
    apply(term)
}

fn strip_lifted<'term>(lifted: &Term, term: &'term Term) -> &'term Term {
    if let (Some((_, _, lifted_concl)), Some((_, _, concl))) =
        (dest_imp_app(lifted), dest_imp_app(term))
    {
        return strip_lifted(lifted_concl, concl);
    }
    if let (Some((_, _, _, lifted_body)), Some((_, _, _, body))) =
        (dest_all_app(lifted), dest_all_app(term))
    {
        return strip_lifted(lifted_body, body);
    }
    term
}

/// Adds the names of the schematic variables of a term to an insertion-ordered set.
fn add_var_names(term: &Term, names: Vec<Name>) -> Vec<Name> {
    fold_vars(
        &mut |atom, mut result: Vec<Name>| {
            let name = atom.name().expect("a Var");
            if !result.contains(name) {
                result.push(name.clone());
            }
            result
        },
        term,
        names,
    )
}

/// The first pair for each name, in order.
fn make_distinct(pairs: &[(Name, Name)]) -> Vec<(Name, Name)> {
    let mut table: Vec<(Name, Name)> = Vec::new();
    for pair in pairs {
        if !table.iter().any(|(known, _)| *known == pair.0) {
            table.push(pair.clone());
        }
    }
    table
}

fn lookup_name<'table>(table: &'table [(Name, Name)], name: &Name) -> Option<&'table Name> {
    table
        .iter()
        .find(|(known, _)| known == name)
        .map(|(_, renamed)| renamed)
}

/// Thm.rename_bvars: renames bound variables and some unknowns of the new premises after the
/// names in the disagreement pairs.
pub fn rename_bvars(
    dpairs: &[Tpair],
    tpairs: &[Tpair],
    lifted: &Term,
    premises: &[Term],
) -> Option<impl Fn(&Term) -> Term + use<>> {
    let pairs = dpairs.iter().rev().fold(Vec::new(), |result, pair| {
        match_bvars(&pair.0, &pair.1, result)
    });
    if pairs.is_empty() {
        return None;
    }
    let mut unknowns = Vec::new();
    for pair in dpairs {
        unknowns = add_var_names(&pair.0, unknowns);
    }
    for pair in tpairs {
        unknowns = add_var_names(&pair.0, unknowns);
        unknowns = add_var_names(&pair.1, unknowns);
    }
    let mut premise_unknowns = Vec::new();
    for premise in premises {
        premise_unknowns = add_var_names(strip_lifted(lifted, premise), premise_unknowns);
    }
    let filtered: Vec<&(Name, Name)> = pairs
        .iter()
        .filter(|pair| {
            premise_unknowns.contains(&pair.0)
                && !unknowns.contains(&pair.0)
                && !unknowns.contains(&pair.1)
        })
        .collect();
    let distinct: Vec<(Name, Name)> = filtered
        .iter()
        .enumerate()
        .filter(|(position, pair)| {
            filtered.iter().position(|other| other.0 == pair.0) == Some(*position)
        })
        .map(|(_, pair)| (*pair).clone())
        .collect();
    let unchanged: Vec<Name> = premise_unknowns
        .iter()
        .filter(|name| !distinct.iter().any(|pair| pair.0 == **name))
        .cloned()
        .collect();
    let add = |set: &mut Vec<Name>, name: &Name| {
        if !set.contains(name) {
            set.push(name.clone());
        }
    };
    // del_clashing: `kept` lists the pairs kept so far, latest first, as the TypeScript's array;
    // `pushed` holds them in the order they were kept.
    let mut is_clash = false;
    let mut xs = unchanged.clone();
    let mut ys = unchanged;
    let mut rest = distinct;
    let kept = loop {
        let mut pushed: Vec<(Name, Name)> = Vec::new();
        for pair in rest {
            if ys.contains(&pair.1) {
                is_clash = true;
                add(&mut xs, &pair.0);
                add(&mut ys, &pair.0);
            } else {
                add(&mut ys, &pair.1);
                pushed.push(pair);
            }
        }
        let kept: Vec<(Name, Name)> = pushed.into_iter().rev().collect();
        if !is_clash {
            break kept;
        }
        is_clash = false;
        ys = xs.clone();
        rest = kept;
    };
    let vars = make_distinct(&kept);
    let bounds = make_distinct(&pairs);
    if vars.iter().all(|pair| pair.0 == pair.1) && bounds.iter().all(|pair| pair.0 == pair.1) {
        return None;
    }
    fn rename(vars: &[(Name, Name)], bounds: &[(Name, Name)], term: &Term) -> Term {
        match &**term {
            TermNode::Var { name, index, ty } => {
                let renamed = lookup_name(vars, name).unwrap_or(name);
                if renamed == name {
                    term.clone()
                } else {
                    mk_var(renamed.clone(), *index, ty.clone())
                }
            }
            TermNode::Abs { name, ty, body, .. } => mk_abs(
                lookup_name(bounds, name).unwrap_or(name).clone(),
                ty.clone(),
                rename(vars, bounds, body),
            ),
            TermNode::App { fun, arg, .. } => {
                mk_app(rename(vars, bounds, fun), rename(vars, bounds, arg))
            }
            _ => term.clone(),
        }
    }
    Some(move |term: &Term| rename(&vars, &bounds, term))
}

pub fn strip_assums2(lifted: &Term, goal: &Term) -> Tpair {
    if let (Some((_, _, lifted_concl)), Some((_, _, goal_concl))) =
        (dest_imp_app(lifted), dest_imp_app(goal))
    {
        return strip_assums2(lifted_concl, goal_concl);
    }
    if let (Some((_, name, ty, lifted_body)), Some((_, _, _, goal_body))) =
        (dest_all_app(lifted), dest_all_app(goal))
    {
        let (left, right) = strip_assums2(lifted_body, goal_body);
        return (
            mk_abs(name.clone(), ty.clone(), left),
            mk_abs(name.clone(), ty.clone(), right),
        );
    }
    (lifted.clone(), goal.clone())
}

pub fn norm_term_skip(envir: &Envir, count: i32, term: &Term) -> Res<Term> {
    if count == 0 {
        return norm_term(envir, term);
    }
    if let Some((_, name, ty, body)) = dest_all_app(term) {
        let ty = norm_type(&envir.tyenv, ty);
        return Ok(mk_app(
            all_const(ty.clone()),
            mk_abs(name.clone(), ty, norm_term_skip(envir, count, body)?),
        ));
    }
    if let Some((_, premise, conclusion)) = dest_imp_app(term) {
        return Ok(mk_implies(
            premise.clone(),
            norm_term_skip(envir, count - 1, conclusion)?,
        ));
    }
    Err(error_exn("norm_term_skip: too few assumptions??"))
}

/// `None` where the TypeScript returns undefined: the types of some variable don't unify.
pub fn unify_var_types(first: &Thm, second: &Thm, envir: &Envir) -> Res<Option<Envir>> {
    // The TypeScript's Map from `index:name`, in insertion order.
    let mut vars: Vec<((i32, Name), Vec<Typ>)> = Vec::new();
    let mut add = |term: &Term| {
        vars = fold_vars(
            &mut |atom, mut result: Vec<((i32, Name), Vec<Typ>)>| {
                let TermNode::Var { name, index, ty } = &**atom else {
                    unreachable!("a Var that isn't one")
                };
                let key = (*index, name.clone());
                match result.iter_mut().find(|(known, _)| *known == key) {
                    Some((_, types)) => {
                        if !types.iter().any(|other| eq_typ(other, ty)) {
                            types.insert(0, ty.clone());
                        }
                    }
                    None => result.push((key, vec![ty.clone()])),
                }
                result
            },
            term,
            std::mem::take(&mut vars),
        );
    };
    for thm in [first, second] {
        for pair in thm.tpairs.iter() {
            add(&pair.0);
            add(&pair.1);
        }
        add(&thm.prop);
    }
    let mut current = Some(envir.clone());
    for (_, types) in &vars {
        for ty in &types[1..] {
            current = match current {
                Some(known) => unify_types_envir(&types[0], ty, &known)?,
                None => None,
            };
        }
    }
    Ok(current)
}
