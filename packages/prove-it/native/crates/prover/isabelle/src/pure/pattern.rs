//! Ported from Isabelle2025's Pure/pattern.ML and Pure/more_pattern.ML. Copyright (c) 1986-2025
//! University of Cambridge, Technische Universitaet Muenchen, and contributors, see LICENSE.
//!
//! Unification and matching of higher-order patterns (`pure/pattern.ts`). Isabelle signals
//! failure with the exceptions Unif, Pattern and MATCH; here they are `Error::Unif`,
//! `Error::NotPattern` and `Error::Match`, which stay inside this module: the public functions
//! return `None` or a `PatternUnify` instead.

use std::cmp::Ordering;

use crate::error::{Error, Res, term_exn};

use super::envir::{
    Binding, Envir, TEnv, aeconv, dest_var, genvar, head_norm, lookup, lookup1, update, var_key,
};
use super::interrupt::check_stack;
use super::logic::Binder;
use super::table::{has_key, indexname_ord, update_table};
use super::term::{
    HAS_VAR, Term, TermNode, Typ, Var, aconv, eq_typ, fastype_of, flags_of, fun_ts, is_open,
    list_comb, loose_bnos, mk_abs, mk_app, mk_bound, strip_comb,
};
use super::types::{TyEnv, match_types, norm_type, subst_type, unify_types};

fn occurs(variable: &Var, term: &Term, envir: &Envir) -> Res<bool> {
    fn visit(variable: &Var, current: &Term, envir: &Envir) -> Res<bool> {
        if flags_of(current) & HAS_VAR == 0 {
            return Ok(false);
        }
        let _depth = check_stack()?;
        match &**current {
            TermNode::Var { name, index, .. } => match lookup(envir, current)? {
                None => {
                    let (variable_name, variable_index, _) = dest_var(variable);
                    Ok(name == variable_name && *index == variable_index)
                }
                Some(assigned) => visit(variable, &assigned, envir),
            },
            TermNode::App { fun, arg, .. } => {
                Ok(visit(variable, fun, envir)? || visit(variable, arg, envir)?)
            }
            TermNode::Abs { body, .. } => visit(variable, body, envir),
            _ => Ok(false),
        }
    }
    visit(variable, term, envir)
}

fn map_bound(map: &impl Fn(i32) -> Res<i32>, term: &Term) -> Res<Term> {
    fn visit(map: &impl Fn(i32) -> Res<i32>, current: &Term, depth: i32) -> Res<Term> {
        Ok(match &**current {
            TermNode::Bound { index } => {
                if *index < depth {
                    current.clone()
                } else {
                    mk_bound(map(index - depth)? + depth)
                }
            }
            TermNode::Abs { name, ty, body, .. } => {
                mk_abs(name.clone(), ty.clone(), visit(map, body, depth + 1)?)
            }
            TermNode::App { fun, arg, .. } => {
                let fun = visit(map, fun, depth)?;
                mk_app(fun, visit(map, arg, depth)?)
            }
            _ => current.clone(),
        })
    }
    visit(map, term, 0)
}

fn index_of(indexes: &[i32], target: i32) -> Res<i32> {
    match indexes.iter().position(|index| *index == target) {
        None => Err(Error::Unif),
        Some(position) => Ok((indexes.len() - 1 - position) as i32),
    }
}

fn mk_abs_over(binders: &[Binder], indexes: &[i32], body: Term) -> Term {
    indexes.iter().rev().fold(body, |result, index| {
        let binder = &binders[*index as usize];
        mk_abs(binder.name.clone(), binder.ty.clone(), result)
    })
}

fn incr(term: &Term) -> Term {
    match map_bound(&|index| Ok(index + 1), term) {
        Ok(term) => term,
        Err(_) => unreachable!("the map raises nothing"),
    }
}

fn ints_of(terms: &[Term]) -> Res<Vec<i32>> {
    let mut indexes = Vec::new();
    for term in terms.iter().rev() {
        match &**term {
            TermNode::Bound { index } if !indexes.contains(index) => indexes.insert(0, *index),
            _ => return Err(Error::NotPattern),
        }
    }
    Ok(indexes)
}

fn ints_of_env(envir: &Envir, terms: &[Term]) -> Res<Vec<i32>> {
    let normal = terms
        .iter()
        .map(|term| head_norm(envir, term))
        .collect::<Res<Vec<_>>>()?;
    ints_of(&normal)
}

fn app_bounds(head: Term, indexes: &[i32]) -> Term {
    indexes
        .iter()
        .fold(head, |result, index| mk_app(result, mk_bound(*index)))
}

fn red(term: &Term, indexes: &[i32], bound: &[i32]) -> Res<Term> {
    if let TermNode::Abs { body, .. } = &**term
        && let Some((first, rest)) = indexes.split_first()
    {
        let mut inner = vec![*first];
        inner.extend_from_slice(bound);
        return red(body, rest, &inner);
    }
    if indexes.is_empty() && bound.is_empty() {
        return Ok(term.clone());
    }
    Ok(app_bounds(
        map_bound(&|index| Ok(bound[index as usize]), term)?,
        indexes,
    ))
}

fn split_type(ty: &Typ, count: usize) -> Res<(Vec<Typ>, Typ)> {
    let mut types = Vec::new();
    let mut current = ty.clone();
    for _ in 0..count {
        let Some((domain, range)) = current.dest_fun() else {
            return Err(term_exn("split_type"));
        };
        types.insert(0, domain.clone());
        current = range.clone();
    }
    Ok((types, current))
}

fn type_of_g(envir: &Envir, ty: &Typ, count: usize, indexes: &[i32]) -> Res<Typ> {
    let (types, range) = split_type(&norm_type(&envir.tyenv, ty), count)?;
    Ok(fun_ts(
        &indexes
            .iter()
            .map(|index| types[*index as usize].clone())
            .collect::<Vec<_>>(),
        range,
    ))
}

fn mk_hnf(binders: &[Binder], indexes: &[i32], head: Term, args: &[i32]) -> Term {
    mk_abs_over(binders, indexes, app_bounds(head, args))
}

fn mk_new_hnf(
    envir: &Envir,
    binders: &[Binder],
    indexes: &[i32],
    variable: &Var,
    args: &[i32],
) -> Res<Envir> {
    let (name, _, ty) = dest_var(variable);
    let (updated, fresh) = genvar(name, envir, type_of_g(envir, ty, indexes.len(), args)?);
    update(variable, mk_hnf(binders, indexes, fresh, args), &updated)
}

/// downto0 (is, n): whether is is [n, n - 1, ..., 0].
fn is_downto0(indexes: &[i32], count: i32) -> bool {
    indexes.len() as i32 == count + 1
        && indexes
            .iter()
            .enumerate()
            .all(|(position, index)| *index == count - position as i32)
}

fn mk_proj_list(indexes: &[Option<i32>]) -> Vec<i32> {
    indexes
        .iter()
        .enumerate()
        .filter(|(_, index)| index.is_some())
        .map(|(position, _)| (indexes.len() - 1 - position) as i32)
        .collect()
}

fn prepend(binder: Binder, binders: &[Binder]) -> Vec<Binder> {
    let mut result = Vec::with_capacity(binders.len() + 1);
    result.push(binder);
    result.extend_from_slice(binders);
    result
}

fn project(term: &Term, envir: &Envir, binders: &[Binder], indexes: &[i32]) -> Res<(Term, Envir)> {
    fn translate(indexes: &[i32], depth: i32, index: i32) -> Res<i32> {
        if index < depth {
            return Ok(index);
        }
        Ok(index_of(indexes, index - depth)? + depth)
    }
    fn try_translate(indexes: &[i32], depth: i32, index: i32) -> Option<i32> {
        if index < depth {
            return Some(index);
        }
        indexes
            .iter()
            .position(|other| *other == index - depth)
            .map(|position| (indexes.len() - 1 - position) as i32 + depth)
    }
    fn project_list(
        indexes: &[i32],
        terms: &[Term],
        state: &Envir,
        depth: i32,
        inner_binders: &[Binder],
    ) -> Res<(Vec<Term>, Envir)> {
        let mut results = Vec::new();
        let mut current = state.clone();
        for item in terms {
            let (projected, next) = project_term(indexes, item, &current, depth, inner_binders)?;
            results.push(projected);
            current = next;
        }
        Ok((results, current))
    }
    fn project_term(
        indexes: &[i32],
        current: &Term,
        state: &Envir,
        depth: i32,
        inner_binders: &[Binder],
    ) -> Res<(Term, Envir)> {
        let _depth = check_stack()?;
        let normal = head_norm(state, current)?;
        if let TermNode::Abs { name, ty, body, .. } = &*normal {
            let binder = Binder {
                name: name.clone(),
                ty: ty.clone(),
            };
            let (body, next) = project_term(
                indexes,
                body,
                state,
                depth + 1,
                &prepend(binder, inner_binders),
            )?;
            return Ok((mk_abs(name.clone(), ty.clone(), body), next));
        }
        let (head, args) = strip_comb(&normal);
        match &*head {
            TermNode::Const { .. } | TermNode::Free { .. } => {
                let (projected, next) = project_list(indexes, &args, state, depth, inner_binders)?;
                Ok((list_comb(head, &projected), next))
            }
            TermNode::Bound { index } => {
                let index = translate(indexes, depth, *index)?;
                let (projected, next) = project_list(indexes, &args, state, depth, inner_binders)?;
                Ok((list_comb(mk_bound(index), &projected), next))
            }
            TermNode::Var { name, ty, .. } => {
                let arg_indexes = ints_of_env(state, &args)?;
                let translated: Vec<Option<i32>> = arg_indexes
                    .iter()
                    .map(|index| try_translate(indexes, depth, *index))
                    .collect();
                let kept = mk_proj_list(&translated);
                let projected_bounds: Vec<i32> = translated.iter().flatten().copied().collect();
                let (updated, fresh) =
                    genvar(name, state, type_of_g(state, ty, arg_indexes.len(), &kept)?);
                let next = update(
                    &head,
                    mk_hnf(inner_binders, &arg_indexes, fresh.clone(), &kept),
                    &updated,
                )?;
                Ok((app_bounds(fresh, &projected_bounds), next))
            }
            _ => Err(Error::NotPattern),
        }
    }
    if is_downto0(indexes, binders.len() as i32 - 1) {
        return Ok((term.clone(), envir.clone()));
    }
    project_term(indexes, term, envir, 0, binders)
}

fn mk_ff_list(left: &[i32], right: &[i32]) -> Res<Vec<i32>> {
    if left.len() != right.len() {
        return Err(term_exn("mk_ff_list"));
    }
    Ok(left
        .iter()
        .enumerate()
        .filter(|(position, index)| **index == right[*position])
        .map(|(position, _)| (left.len() - 1 - position) as i32)
        .collect())
}

fn flexflex1(
    envir: &Envir,
    binders: &[Binder],
    variable: &Var,
    left: &[i32],
    right: &[i32],
) -> Res<Envir> {
    if left == right {
        return Ok(envir.clone());
    }
    mk_new_hnf(envir, binders, left, variable, &mk_ff_list(left, right)?)
}

fn flexflex2(
    envir: &Envir,
    binders: &[Binder],
    left_var: &Var,
    left_indexes: &[i32],
    right_var: &Var,
    right_indexes: &[i32],
) -> Res<Envir> {
    let assign = |first: &Var, first_indexes: &[i32], second: &Var, second_indexes: &[i32]| {
        if second_indexes
            .iter()
            .all(|index| first_indexes.contains(index))
        {
            let term = mk_abs_over(
                binders,
                first_indexes,
                app_bounds(
                    second.clone(),
                    &second_indexes
                        .iter()
                        .map(|index| index_of(first_indexes, *index))
                        .collect::<Res<Vec<_>>>()?,
                ),
            );
            return update(first, term, envir);
        }
        let common: Vec<i32> = first_indexes
            .iter()
            .filter(|index| second_indexes.contains(index))
            .copied()
            .collect();
        let (second_name, _, _) = dest_var(second);
        let (_, _, first_ty) = dest_var(first);
        let (updated, fresh) = genvar(
            second_name,
            envir,
            type_of_g(
                envir,
                first_ty,
                first_indexes.len(),
                &common
                    .iter()
                    .map(|index| index_of(first_indexes, *index))
                    .collect::<Res<Vec<_>>>()?,
            )?,
        );
        let lam = |indexes: &[i32]| -> Res<Term> {
            Ok(mk_abs_over(
                binders,
                indexes,
                app_bounds(
                    fresh.clone(),
                    &common
                        .iter()
                        .map(|index| index_of(indexes, *index))
                        .collect::<Res<Vec<_>>>()?,
                ),
            ))
        };
        let second_term = lam(second_indexes)?;
        update(
            second,
            second_term,
            &update(first, lam(first_indexes)?, &updated)?,
        )
    };
    if indexname_ord(&var_key(right_var), &var_key(left_var)) == Ordering::Less {
        assign(left_var, left_indexes, right_var, right_indexes)
    } else {
        assign(right_var, right_indexes, left_var, left_indexes)
    }
}

/// Pattern.unify_types: `None` where Isabelle raises Unif. Raises TYPE on a duplicate assignment.
pub fn unify_types_envir(left: &Typ, right: &Typ, envir: &Envir) -> Res<Option<Envir>> {
    if eq_typ(left, right) {
        return Ok(Some(envir.clone()));
    }
    Ok(unify_types(right, left, &envir.tyenv)?.map(|tyenv| Envir {
        tyenv,
        ..envir.clone()
    }))
}

fn unify_types_or_fail(left: &Typ, right: &Typ, envir: &Envir) -> Res<Envir> {
    unify_types_envir(left, right, envir)?.ok_or(Error::Unif)
}

fn unif(binders: &[Binder], left: &Term, right: &Term, envir: &Envir) -> Res<Envir> {
    let _depth = check_stack()?;
    let left_norm = head_norm(envir, left)?;
    let right_norm = head_norm(envir, right)?;
    match (&*left_norm, &*right_norm) {
        (
            TermNode::Abs {
                name,
                ty,
                body: left_body,
                ..
            },
            TermNode::Abs {
                name: right_name,
                ty: right_ty,
                body: right_body,
                ..
            },
        ) => {
            let name = if name.is_empty() { right_name } else { name };
            unif(
                &prepend(
                    Binder {
                        name: name.clone(),
                        ty: ty.clone(),
                    },
                    binders,
                ),
                left_body,
                right_body,
                &unify_types_or_fail(ty, right_ty, envir)?,
            )
        }
        (TermNode::Abs { name, ty, body, .. }, _) => unif(
            &prepend(
                Binder {
                    name: name.clone(),
                    ty: ty.clone(),
                },
                binders,
            ),
            body,
            &mk_app(incr(&right_norm), mk_bound(0)),
            envir,
        ),
        (_, TermNode::Abs { name, ty, body, .. }) => unif(
            &prepend(
                Binder {
                    name: name.clone(),
                    ty: ty.clone(),
                },
                binders,
            ),
            &mk_app(incr(&left_norm), mk_bound(0)),
            body,
            envir,
        ),
        _ => cases(binders, envir, &left_norm, &right_norm),
    }
}

fn unif_args(binders: &[Binder], left: &[Term], right: &[Term], envir: Envir) -> Res<Envir> {
    if left.len() != right.len() {
        return Err(Error::Unif);
    }
    left.iter()
        .zip(right)
        .try_fold(envir, |state, (item, other)| {
            unif(binders, item, other, &state)
        })
}

fn cases(binders: &[Binder], envir: &Envir, left: &Term, right: &Term) -> Res<Envir> {
    let (left_head, left_args) = strip_comb(left);
    let (right_head, right_args) = strip_comb(right);
    match (&*left_head, &*right_head) {
        (
            TermNode::Var { name, index, .. },
            TermNode::Var {
                name: right_name,
                index: right_index,
                ..
            },
        ) => {
            if name == right_name && index == right_index {
                let left_indexes = ints_of_env(envir, &left_args)?;
                let right_indexes = ints_of_env(envir, &right_args)?;
                return flexflex1(envir, binders, &left_head, &left_indexes, &right_indexes);
            }
            let left_indexes = ints_of_env(envir, &left_args)?;
            let right_indexes = ints_of_env(envir, &right_args)?;
            flexflex2(
                envir,
                binders,
                &left_head,
                &left_indexes,
                &right_head,
                &right_indexes,
            )
        }
        (TermNode::Var { .. }, _) => {
            let indexes = ints_of_env(envir, &left_args)?;
            flex_rigid(envir, binders, &left_head, &indexes, right)
        }
        (_, TermNode::Var { .. }) => {
            let indexes = ints_of_env(envir, &right_args)?;
            flex_rigid(envir, binders, &right_head, &indexes, left)
        }
        (
            TermNode::Const { name, ty },
            TermNode::Const {
                name: right_name,
                ty: right_ty,
            },
        )
        | (
            TermNode::Free { name, ty },
            TermNode::Free {
                name: right_name,
                ty: right_ty,
            },
        ) => {
            if name != right_name {
                return Err(Error::Unif);
            }
            unif_args(
                binders,
                &left_args,
                &right_args,
                unify_types_or_fail(ty, right_ty, envir)?,
            )
        }
        (TermNode::Bound { index }, TermNode::Bound { index: right_index }) => {
            if index != right_index {
                return Err(Error::Unif);
            }
            unif_args(binders, &left_args, &right_args, envir.clone())
        }
        (TermNode::Abs { .. }, _) | (_, TermNode::Abs { .. }) => Err(Error::NotPattern),
        _ => Err(Error::Unif),
    }
}

fn flex_rigid(
    envir: &Envir,
    binders: &[Binder],
    variable: &Var,
    indexes: &[i32],
    term: &Term,
) -> Res<Envir> {
    if occurs(variable, term, envir)? {
        return Err(Error::Unif);
    }
    let (projected, updated) = project(term, envir, binders, indexes)?;
    update(variable, mk_abs_over(binders, indexes, projected), &updated)
}

/// The outcome of Pattern.unify.
#[derive(Clone)]
pub enum PatternUnify {
    Unified(Envir),
    /// Isabelle's Unif.
    Clash,
    /// Isabelle's Pattern: the terms are outside the pattern fragment.
    NotAPattern,
}

/// Pattern.unify: distinguishes a clash (Unif) from terms outside the pattern fragment (Pattern).
pub fn unify_pattern(left: &Term, right: &Term, envir: &Envir) -> Res<PatternUnify> {
    match unif(&[], left, right, envir) {
        Ok(envir) => Ok(PatternUnify::Unified(envir)),
        Err(Error::Unif) => Ok(PatternUnify::Clash),
        Err(Error::NotPattern) => Ok(PatternUnify::NotAPattern),
        Err(error) => Err(error),
    }
}

#[derive(Clone)]
pub struct MatchEnv {
    pub tyenv: TyEnv,
    pub tenv: TEnv,
}

fn typ_match(pattern: &Typ, object: &Typ, tyenv: &TyEnv) -> Res<TyEnv> {
    match_types(pattern, object, tyenv)?.ok_or(Error::Match)
}

fn update_new_tenv(tenv: &TEnv, variable: &Var, term: Term) -> Res<TEnv> {
    let key = var_key(variable);
    if has_key(tenv, &key) {
        return Err(term_exn("Vartab.update_new: duplicate"));
    }
    Ok(update_table(
        tenv,
        key,
        Binding {
            ty: dest_var(variable).2.clone(),
            term,
        },
    ))
}

fn first_order_match_at(
    is_in_abs: bool,
    state: &MatchEnv,
    pat: &Term,
    obj: &Term,
) -> Res<MatchEnv> {
    let _depth = check_stack()?;
    match (&**pat, &**obj) {
        (TermNode::Var { ty, .. }, _) => {
            if is_in_abs && is_open(obj) {
                return Err(Error::Match);
            }
            match lookup1(&state.tenv, pat)? {
                None => {
                    let tyenv = typ_match(ty, &fastype_of(obj)?, &state.tyenv)?;
                    Ok(MatchEnv {
                        tyenv,
                        tenv: update_new_tenv(&state.tenv, pat, obj.clone())?,
                    })
                }
                Some(assigned) => {
                    if aeconv(obj, &assigned) {
                        Ok(state.clone())
                    } else {
                        Err(Error::Match)
                    }
                }
            }
        }
        (
            TermNode::Free { name, ty },
            TermNode::Free {
                name: obj_name,
                ty: obj_ty,
            },
        )
        | (
            TermNode::Const { name, ty },
            TermNode::Const {
                name: obj_name,
                ty: obj_ty,
            },
        ) => {
            if name != obj_name {
                return Err(Error::Match);
            }
            Ok(MatchEnv {
                tyenv: typ_match(ty, obj_ty, &state.tyenv)?,
                tenv: state.tenv.clone(),
            })
        }
        (TermNode::Bound { index }, TermNode::Bound { index: obj_index }) => {
            if index != obj_index {
                return Err(Error::Match);
            }
            Ok(state.clone())
        }
        (
            TermNode::Abs { ty, body, .. },
            TermNode::Abs {
                ty: obj_ty,
                body: obj_body,
                ..
            },
        ) => first_order_match_at(
            true,
            &MatchEnv {
                tyenv: typ_match(ty, obj_ty, &state.tyenv)?,
                tenv: state.tenv.clone(),
            },
            body,
            obj_body,
        ),
        (
            TermNode::App { fun, arg, .. },
            TermNode::App {
                fun: obj_fun,
                arg: obj_arg,
                ..
            },
        ) => first_order_match_at(
            is_in_abs,
            &first_order_match_at(is_in_abs, state, fun, obj_fun)?,
            arg,
            obj_arg,
        ),
        (_, TermNode::Abs { body, .. }) => {
            first_order_match_at(true, state, &mk_app(incr(pat), mk_bound(0)), body)
        }
        _ => Err(Error::Match),
    }
}

fn first_order_match(pattern: &Term, object: &Term, env: &MatchEnv) -> Res<MatchEnv> {
    first_order_match_at(false, env, pattern, object)
}

fn match_bind(
    tenv: &TEnv,
    binders: &[Binder],
    variable: &Var,
    indexes: &[i32],
    term: &Term,
) -> Res<TEnv> {
    let loose = loose_bnos(term);
    if indexes.is_empty() {
        if loose.is_empty() {
            return update_new_tenv(tenv, variable, term.clone());
        }
        return Err(Error::Match);
    }
    if !loose.iter().all(|index| indexes.contains(index)) {
        return Err(Error::Match);
    }
    let body = if is_downto0(indexes, binders.len() as i32 - 1) {
        term.clone()
    } else {
        map_bound(&|index| index_of(indexes, index), term)?
    };
    update_new_tenv(tenv, variable, mk_abs_over(binders, indexes, body))
}

fn higher_order_match(pattern: &Term, object: &Term, env: &MatchEnv) -> Res<MatchEnv> {
    fn visit(binders: &[Binder], pat: &Term, obj: &Term, state: &MatchEnv) -> Res<MatchEnv> {
        let _depth = check_stack()?;
        if let TermNode::Abs { name, ty, body, .. } = &**pat {
            if let TermNode::Abs {
                name: obj_name,
                ty: obj_ty,
                body: obj_body,
                ..
            } = &**obj
            {
                return visit(
                    &prepend(
                        Binder {
                            name: obj_name.clone(),
                            ty: obj_ty.clone(),
                        },
                        binders,
                    ),
                    body,
                    obj_body,
                    state,
                );
            }
            let ty = subst_type(&state.tyenv, ty);
            return visit(
                &prepend(
                    Binder {
                        name: name.clone(),
                        ty,
                    },
                    binders,
                ),
                body,
                &mk_app(incr(obj), mk_bound(0)),
                state,
            );
        }
        if let TermNode::Abs { name, ty, body, .. } = &**obj {
            return visit(
                &prepend(
                    Binder {
                        name: name.clone(),
                        ty: ty.clone(),
                    },
                    binders,
                ),
                &mk_app(incr(pat), mk_bound(0)),
                body,
                state,
            );
        }
        match_cases(binders, state, pat, obj)
    }

    fn match_cases(binders: &[Binder], state: &MatchEnv, pat: &Term, obj: &Term) -> Res<MatchEnv> {
        let (pat_head, pat_args) = strip_comb(pat);
        let rigid_args = |tyenv: TyEnv, obj_args: &[Term]| -> Res<MatchEnv> {
            if pat_args.len() != obj_args.len() {
                return Err(Error::Match);
            }
            pat_args.iter().zip(obj_args).try_fold(
                MatchEnv {
                    tyenv,
                    tenv: state.tenv.clone(),
                },
                |result, (arg, obj_arg)| visit(binders, arg, obj_arg, &result),
            )
        };
        if pat_head.is_var() {
            let indexes = ints_of(&pat_args)?;
            return match lookup1(&state.tenv, &pat_head)? {
                None => Ok(MatchEnv {
                    tyenv: state.tyenv.clone(),
                    tenv: match_bind(&state.tenv, binders, &pat_head, &indexes, obj)?,
                }),
                Some(assigned) => {
                    if aeconv(obj, &red(&assigned, &indexes, &[])?) {
                        Ok(state.clone())
                    } else {
                        Err(Error::Match)
                    }
                }
            };
        }
        let (obj_head, obj_args) = strip_comb(obj);
        match (&*pat_head, &*obj_head) {
            (
                TermNode::Const { name, ty },
                TermNode::Const {
                    name: obj_name,
                    ty: obj_ty,
                },
            )
            | (
                TermNode::Free { name, ty },
                TermNode::Free {
                    name: obj_name,
                    ty: obj_ty,
                },
            ) => {
                if name != obj_name {
                    return Err(Error::Match);
                }
                rigid_args(typ_match(ty, obj_ty, &state.tyenv)?, &obj_args)
            }
            (TermNode::Bound { index }, TermNode::Bound { index: obj_index }) => {
                if index != obj_index {
                    return Err(Error::Match);
                }
                rigid_args(state.tyenv.clone(), &obj_args)
            }
            (TermNode::Abs { .. }, _) | (_, TermNode::Abs { .. }) => Err(Error::NotPattern),
            _ => Err(Error::Match),
        }
    }

    let initial = MatchEnv {
        tyenv: typ_match(&fastype_of(pattern)?, &fastype_of(object)?, &env.tyenv)?,
        tenv: env.tenv.clone(),
    };
    match visit(&[], pattern, object, &initial) {
        Err(Error::NotPattern) => first_order_match(pattern, object, &initial),
        result => result,
    }
}

fn catch_match(result: Res<MatchEnv>) -> Res<Option<MatchEnv>> {
    match result {
        Ok(env) => Ok(Some(env)),
        Err(Error::Match) => Ok(None),
        Err(error) => Err(error),
    }
}

/// Pattern.match: `None` where Isabelle raises MATCH.
pub fn match_pattern(pattern: &Term, object: &Term, env: &MatchEnv) -> Res<Option<MatchEnv>> {
    catch_match(higher_order_match(pattern, object, env))
}

/// Pattern.first_order_match
pub fn first_order_match_pattern(
    pattern: &Term,
    object: &Term,
    env: &MatchEnv,
) -> Res<Option<MatchEnv>> {
    catch_match(first_order_match(pattern, object, env))
}

/// Pattern.matches
pub fn matches(pattern: &Term, object: &Term, tyenv: &TyEnv, tenv: &TEnv) -> Res<bool> {
    Ok(match_pattern(
        pattern,
        object,
        &MatchEnv {
            tyenv: tyenv.clone(),
            tenv: tenv.clone(),
        },
    )?
    .is_some())
}

/// Pattern.pattern
pub fn is_pattern(term: &Term) -> bool {
    if let TermNode::Abs { body, .. } = &**term {
        return is_pattern(body);
    }
    let (head, args) = strip_comb(term);
    if head.is_var() {
        return args.iter().all(Term::is_bound)
            && !args.iter().enumerate().any(|(index, arg)| {
                args.iter().position(|other| aconv(other, arg)) != Some(index)
            });
    }
    args.iter().all(is_pattern)
}

/// Pattern.first_order
pub fn is_first_order(term: &Term) -> bool {
    match &**term {
        TermNode::Abs { body, .. } => is_first_order(body),
        TermNode::App { fun, arg, .. } => {
            !fun.is_var() && is_first_order(fun) && is_first_order(arg)
        }
        _ => true,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pure::envir::{beta_norm, empty_envir, eta_contract, norm_term, subst_term};
    use crate::pure::testing::{
        attempt, check_problems, parse_term, show, show_envir, show_tables,
    };

    // The expectations are recorded from pattern.ts (see pure/testing.rs).
    #[test]
    fn matches_the_typescript() {
        check_problems(
            include_str!("../../testdata/kernel/pattern.txt"),
            |kind, fields| {
                let mut lines = Vec::new();
                match kind {
                    "classify" => {
                        let term = parse_term(fields[0]);
                        lines.push(format!(
                            "pattern {} first_order {}",
                            is_pattern(&term),
                            is_first_order(&term)
                        ));
                    }
                    "unify" => attempt(&mut lines, |lines| {
                        let left = parse_term(fields[1]);
                        let right = parse_term(fields[2]);
                        let envir = empty_envir(fields[0].parse().unwrap());
                        match unify_pattern(&left, &right, &envir)? {
                            PatternUnify::Clash => lines.push("clash".into()),
                            PatternUnify::NotAPattern => lines.push("not a pattern".into()),
                            PatternUnify::Unified(envir) => {
                                lines.push("unified".into());
                                lines.extend(show_envir(&envir));
                                lines.push(format!("left {}", show(&norm_term(&envir, &left)?)));
                                lines.push(format!("right {}", show(&norm_term(&envir, &right)?)));
                            }
                        }
                        Ok(())
                    }),
                    "match" => {
                        let pattern = parse_term(fields[0]);
                        let object = parse_term(fields[1]);
                        let extra: Vec<Term> =
                            fields[2..].iter().map(|text| parse_term(text)).collect();
                        let empty = empty_envir(0);
                        let env = MatchEnv {
                            tyenv: empty.tyenv,
                            tenv: empty.tenv,
                        };
                        let runs: [(&str, fn(&Term, &Term, &MatchEnv) -> Res<Option<MatchEnv>>);
                            2] = [
                            ("match", match_pattern),
                            ("first_order_match", first_order_match_pattern),
                        ];
                        for (label, run) in runs {
                            attempt(&mut lines, |lines| {
                                let Some(env) = run(&pattern, &object, &env)? else {
                                    lines.push(format!("{label} none"));
                                    return Ok(());
                                };
                                lines.push(label.into());
                                lines.extend(show_tables(&env.tyenv, &env.tenv));
                                let instance = subst_term(&env.tyenv, &env.tenv, &pattern)?;
                                lines.push(format!("instance {}", show(&instance)));
                                lines.push(format!(
                                    "aeconv {}",
                                    aeconv(&beta_norm(&instance)?, &object)
                                ));
                                for term in &extra {
                                    let substituted = subst_term(&env.tyenv, &env.tenv, term)?;
                                    lines.push(format!("extra {}", show(&substituted)));
                                    let normal = eta_contract(&beta_norm(&substituted)?);
                                    lines.push(format!("extra_norm {}", show(&normal)));
                                }
                                Ok(())
                            });
                        }
                    }
                    _ => panic!("unknown problem {kind}"),
                }
                lines
            },
        );
    }
}
