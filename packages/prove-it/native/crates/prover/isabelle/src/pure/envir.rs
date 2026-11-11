//! Ported from Isabelle2025's Pure/envir.ML. Copyright (c) 1986-2025 University of Cambridge,
//! Technische Universitaet Muenchen, and contributors, see LICENSE.
//!
//! Environments of assignments to schematic variables, and beta and eta normalization
//! (`pure/envir.ts`).

use std::cmp::Ordering;

use crate::error::{Res, term_exn, type_exn};

use super::interrupt::check_stack;
use super::table::{
    IndexKey, Table, empty_table, fast_indexname_ord, has_key, indexname_ord, is_empty_table,
    lookup_table, min_table, update_table,
};
use super::term::{
    HAS_ETA_REDEX, HAS_REDEX, HAS_VAR, Name, Term, TermNode, Typ, TypNode, Var, aconv, flags_of,
    fun_t, is_dependent, maxidx_of_term, mk_abs, mk_app, mk_bound, mk_const, mk_free, mk_var,
    subst_bound, update_abs, update_app,
};
use super::types::{TyEnv, devar, empty_ty_env, norm_type, subst_type, unified_types};

#[derive(Clone)]
pub struct Binding {
    pub ty: Typ,
    pub term: Term,
}

pub type TEnv = Table<IndexKey, Binding>;

#[derive(Clone)]
pub struct Envir {
    pub maxidx: i32,
    pub tenv: TEnv,
    pub tyenv: TyEnv,
}

pub fn empty_tenv() -> TEnv {
    empty_table(fast_indexname_ord)
}

pub fn empty_envir(maxidx: i32) -> Envir {
    Envir {
        maxidx,
        tenv: empty_tenv(),
        tyenv: empty_ty_env(),
    }
}

pub fn is_empty_envir(envir: &Envir) -> bool {
    is_empty_table(&envir.tenv) && is_empty_table(&envir.tyenv)
}

/// The name, index and type of a Var.
pub(crate) fn dest_var(variable: &Var) -> (&Name, i32, &Typ) {
    match &**variable {
        TermNode::Var { name, index, ty } => (name, *index, ty),
        _ => unreachable!("a Var that isn't one"),
    }
}

/// The key of a schematic variable in an environment, its name and index: the TypeScript looks
/// variables up by the Var itself.
pub fn var_key(variable: &Var) -> IndexKey {
    let (name, index, _) = dest_var(variable);
    IndexKey {
        name: name.clone(),
        index,
    }
}

/// radixstring (26, "a", n)
fn radix_string(value: usize) -> String {
    let mut digits = Vec::new();
    let mut remaining = value;
    loop {
        digits.insert(0, remaining % 26);
        remaining /= 26;
        if remaining == 0 {
            break;
        }
    }
    digits
        .into_iter()
        .map(|digit| char::from(b'a' + digit as u8))
        .collect()
}

/// Envir.genvars: fresh variables with an index above every present one.
pub fn genvars(name: &str, envir: &Envir, types: &[Typ]) -> (Envir, Vec<Var>) {
    let index = envir.maxidx + 1;
    let vars = types
        .iter()
        .enumerate()
        .map(|(position, ty)| {
            let var_name = if types.len() == 1 {
                name.to_string()
            } else {
                format!("{name}{}", radix_string(position))
            };
            mk_var(var_name, index, ty.clone())
        })
        .collect();
    (
        Envir {
            maxidx: index,
            ..envir.clone()
        },
        vars,
    )
}

pub fn genvar(name: &str, envir: &Envir, ty: Typ) -> (Envir, Var) {
    let (updated, mut vars) = genvars(name, envir, std::slice::from_ref(&ty));
    (updated, vars.remove(0))
}

fn eq_typ_exact(left: &Typ, right: &Typ) -> bool {
    unified_types(&empty_ty_env(), left, right)
}

/// Envir.lookup1: lookup without chasing type assignments, for environments from matching.
pub fn lookup1(tenv: &TEnv, variable: &Var) -> Res<Option<Term>> {
    let Some(binding) = lookup_table(tenv, &var_key(variable)) else {
        return Ok(None);
    };
    if !eq_typ_exact(dest_var(variable).2, &binding.ty) {
        return Err(type_exn("Variable has two distinct types"));
    }
    Ok(Some(binding.term.clone()))
}

pub fn lookup(envir: &Envir, variable: &Var) -> Res<Option<Term>> {
    let Some(binding) = lookup_table(&envir.tenv, &var_key(variable)) else {
        return Ok(None);
    };
    if !unified_types(&envir.tyenv, dest_var(variable).2, &binding.ty) {
        return Err(type_exn("Variable has two distinct types"));
    }
    Ok(Some(binding.term.clone()))
}

pub fn update(variable: &Var, term: Term, envir: &Envir) -> Res<Envir> {
    let key = var_key(variable);
    if has_key(&envir.tenv, &key) {
        return Err(term_exn("Envir.update: duplicate assignment"));
    }
    Ok(Envir {
        tenv: update_table(
            &envir.tenv,
            key,
            Binding {
                ty: dest_var(variable).2.clone(),
                term,
            },
        ),
        ..envir.clone()
    })
}

/// Envir.above: whether the least index updated exceeds limit.
pub fn above(envir: &Envir, limit: i32) -> bool {
    min_table(&envir.tenv).is_none_or(|(key, _)| key.index > limit)
        && min_table(&envir.tyenv).is_none_or(|(key, _)| key.index > limit)
}

/// Envir.vupdate: an assignment that suppresses higher indexes between variables.
pub fn vupdate(variable: &Var, term: Term, envir: &Envir) -> Res<Envir> {
    let TermNode::Var {
        name,
        index,
        ty: term_ty,
    } = &*term
    else {
        return update(variable, term, envir);
    };
    let (variable_name, variable_index, _) = dest_var(variable);
    if variable_name == name && variable_index == *index {
        return Ok(envir.clone());
    }
    if indexname_ord(&var_key(variable), &var_key(&term)) == Ordering::Less {
        return match lookup(envir, &term)? {
            None => update(
                &term,
                mk_var(variable_name.clone(), variable_index, term_ty.clone()),
                envir,
            ),
            Some(assigned) => vupdate(variable, assigned, envir),
        };
    }
    update(variable, term, envir)
}

fn could_beta_contract(term: &Term) -> bool {
    flags_of(term) & HAS_REDEX != 0
}

fn norm_term1(tenv: &TEnv, term: &Term) -> Res<Term> {
    if flags_of(term) & (HAS_VAR | HAS_REDEX) == 0 {
        return Ok(term.clone());
    }
    let _depth = check_stack()?;
    match &**term {
        TermNode::Var { .. } => match lookup1(tenv, term)? {
            None => Ok(term.clone()),
            Some(assigned) => norm_term1(tenv, &assigned),
        },
        TermNode::Abs { body, .. } => Ok(update_abs(term, norm_term1(tenv, body)?, None)),
        TermNode::App { fun, arg, .. } => {
            if let TermNode::Abs { body, .. } = &**fun {
                return norm_term1(tenv, &subst_bound(arg, body));
            }
            let normal = norm_term1(tenv, fun)?;
            if let TermNode::Abs { body, .. } = &*normal {
                return norm_term1(tenv, &subst_bound(arg, body));
            }
            Ok(update_app(term, normal, norm_term1(tenv, arg)?))
        }
        _ => Ok(term.clone()),
    }
}

fn norm_term2(envir: &Envir, term: &Term) -> Res<Term> {
    if maxidx_of_term(term, -1) < 0 && flags_of(term) & HAS_REDEX == 0 {
        return Ok(term.clone());
    }
    let _depth = check_stack()?;
    match &**term {
        TermNode::Const { name, ty } => {
            let normal = norm_type(&envir.tyenv, ty);
            Ok(if Typ::ptr_eq(&normal, ty) {
                term.clone()
            } else {
                mk_const(name.clone(), normal)
            })
        }
        TermNode::Free { name, ty } => {
            let normal = norm_type(&envir.tyenv, ty);
            Ok(if Typ::ptr_eq(&normal, ty) {
                term.clone()
            } else {
                mk_free(name.clone(), normal)
            })
        }
        TermNode::Var { name, index, ty } => {
            if let Some(assigned) = lookup(envir, term)? {
                return norm_term2(envir, &assigned);
            }
            let normal = norm_type(&envir.tyenv, ty);
            Ok(if Typ::ptr_eq(&normal, ty) {
                term.clone()
            } else {
                mk_var(name.clone(), *index, normal)
            })
        }
        TermNode::Abs { ty, body, .. } => Ok(update_abs(
            term,
            norm_term2(envir, body)?,
            Some(norm_type(&envir.tyenv, ty)),
        )),
        TermNode::App { fun, arg, .. } => {
            if let TermNode::Abs { body, .. } = &**fun {
                return norm_term2(envir, &subst_bound(arg, body));
            }
            let normal = norm_term2(envir, fun)?;
            if let TermNode::Abs { body, .. } = &*normal {
                return norm_term2(envir, &subst_bound(arg, body));
            }
            Ok(update_app(term, normal, norm_term2(envir, arg)?))
        }
        TermNode::Bound { .. } => Ok(term.clone()),
    }
}

/// Envir.norm_term: instantiates the environment and beta-normalizes.
pub fn norm_term(envir: &Envir, term: &Term) -> Res<Term> {
    if is_empty_envir(envir) && !could_beta_contract(term) {
        return Ok(term.clone());
    }
    if is_empty_table(&envir.tyenv) {
        norm_term1(&envir.tenv, term)
    } else {
        norm_term2(envir, term)
    }
}

/// Without assignments nothing raises, but a term deeper than `check_stack` allows.
pub fn beta_norm(term: &Term) -> Res<Term> {
    norm_term(&empty_envir(-1), term)
}

/// Envir.head_norm: normalizes the head only, for unification.
pub fn head_norm(envir: &Envir, term: &Term) -> Res<Term> {
    if flags_of(term) & (HAS_VAR | HAS_REDEX) == 0 {
        return Ok(term.clone());
    }
    let _depth = check_stack()?;
    match &**term {
        TermNode::Var { .. } => match lookup(envir, term)? {
            None => Ok(term.clone()),
            Some(assigned) => head_norm(envir, &assigned),
        },
        TermNode::Abs { body, .. } => Ok(update_abs(term, head_norm(envir, body)?, None)),
        TermNode::App { fun, arg, .. } => {
            if let TermNode::Abs { body, .. } = &**fun {
                return head_norm(envir, &subst_bound(arg, body));
            }
            let normal = head_norm(envir, fun)?;
            if let TermNode::Abs { body, .. } = &*normal {
                return head_norm(envir, &subst_bound(arg, body));
            }
            Ok(if Term::ptr_eq(&normal, fun) {
                term.clone()
            } else {
                mk_app(normal, arg.clone())
            })
        }
        _ => Ok(term.clone()),
    }
}

fn decrement_loose(term: &Term, level: i32) -> Term {
    match &**term {
        TermNode::Bound { index } => {
            if *index >= level {
                mk_bound(index - 1)
            } else {
                term.clone()
            }
        }
        TermNode::Abs { body, .. } => update_abs(term, decrement_loose(body, level + 1), None),
        TermNode::App { fun, arg, .. } => update_app(
            term,
            decrement_loose(fun, level),
            decrement_loose(arg, level),
        ),
        _ => term.clone(),
    }
}

fn could_eta_contract(term: &Term) -> bool {
    flags_of(term) & HAS_ETA_REDEX != 0
}

fn eta_same(term: &Term) -> Term {
    if !could_eta_contract(term) {
        return term.clone();
    }
    match &**term {
        TermNode::Abs {
            name,
            ty,
            body: old_body,
            ..
        } => {
            let body = eta_same(old_body);
            let keep = || {
                if Term::ptr_eq(&body, old_body) {
                    term.clone()
                } else {
                    mk_abs(name.clone(), ty.clone(), body.clone())
                }
            };
            if let TermNode::App { fun, arg, .. } = &*body
                && matches!(&**arg, TermNode::Bound { index: 0 })
            {
                if is_dependent(fun) {
                    return keep();
                }
                return decrement_loose(fun, 0);
            }
            keep()
        }
        TermNode::App { fun, arg, .. } => update_app(term, eta_same(fun), eta_same(arg)),
        _ => term.clone(),
    }
}

/// Envir.eta_contract
pub fn eta_contract(term: &Term) -> Term {
    if could_eta_contract(term) {
        eta_same(term)
    } else {
        term.clone()
    }
}

pub fn aeconv(left: &Term, right: &Term) -> bool {
    aconv(left, right) || aconv(&eta_contract(left), &eta_contract(right))
}

/// The key of a type variable.
fn tvar_key(ty: &Typ) -> Option<IndexKey> {
    match &**ty {
        TypNode::TVar { name, index, .. } => Some(IndexKey {
            name: name.clone(),
            index: *index,
        }),
        _ => None,
    }
}

pub fn env_body_type(envir: &Envir, ty: &Typ) -> Typ {
    if let Some((_, range)) = ty.dest_fun() {
        return env_body_type(envir, range);
    }
    if let Some(key) = tvar_key(ty) {
        return match lookup_table(&envir.tyenv, &key) {
            None => ty.clone(),
            Some(assigned) => env_body_type(envir, assigned),
        };
    }
    ty.clone()
}

pub fn env_binder_types(envir: &Envir, ty: &Typ) -> Vec<Typ> {
    if let Some((domain, range)) = ty.dest_fun() {
        let mut types = vec![domain.clone()];
        types.extend(env_binder_types(envir, range));
        return types;
    }
    if let Some(key) = tvar_key(ty) {
        return match lookup_table(&envir.tyenv, &key) {
            None => Vec::new(),
            Some(assigned) => env_binder_types(envir, assigned),
        };
    }
    Vec::new()
}

/// Envir.fastype: the type of a term, chasing type assignments at applications.
pub fn fastype(envir: &Envir, types: &[Typ], term: &Term) -> Res<Typ> {
    match &**term {
        TermNode::App { fun, .. } => {
            let ty = devar(&envir.tyenv, &fastype(envir, types, fun)?);
            match ty.dest_fun() {
                Some((_, range)) => Ok(range.clone()),
                None => Err(type_exn("fastype: expected function type")),
            }
        }
        TermNode::Bound { index } => types
            .get(*index as usize)
            .cloned()
            .ok_or_else(|| type_exn("fastype: Bound")),
        TermNode::Abs { ty, body, .. } => {
            let mut inner = vec![ty.clone()];
            inner.extend_from_slice(types);
            Ok(fun_t(ty.clone(), fastype(envir, &inner, body)?))
        }
        TermNode::Const { ty, .. } | TermNode::Free { ty, .. } | TermNode::Var { ty, .. } => {
            Ok(ty.clone())
        }
    }
}

/// Envir.subst_term: instantiates without chasing variables.
fn subst_term_aux(tyenv: &TyEnv, tenv: &TEnv, term: &Term) -> Res<Term> {
    if maxidx_of_term(term, -1) < 0 {
        return Ok(term.clone());
    }
    let subst = |ty: &Typ| {
        if is_empty_table(tyenv) {
            ty.clone()
        } else {
            subst_type(tyenv, ty)
        }
    };
    let _depth = check_stack()?;
    Ok(match &**term {
        TermNode::Const { name, ty } => {
            let substituted = subst(ty);
            if Typ::ptr_eq(&substituted, ty) {
                term.clone()
            } else {
                mk_const(name.clone(), substituted)
            }
        }
        TermNode::Free { name, ty } => {
            let substituted = subst(ty);
            if Typ::ptr_eq(&substituted, ty) {
                term.clone()
            } else {
                mk_free(name.clone(), substituted)
            }
        }
        TermNode::Var { name, index, ty } => {
            if let Some(assigned) = lookup1(tenv, term)? {
                return Ok(assigned);
            }
            let substituted = subst(ty);
            if Typ::ptr_eq(&substituted, ty) {
                term.clone()
            } else {
                mk_var(name.clone(), *index, substituted)
            }
        }
        TermNode::Bound { .. } => term.clone(),
        TermNode::Abs { ty, body, .. } => {
            update_abs(term, subst_term_aux(tyenv, tenv, body)?, Some(subst(ty)))
        }
        TermNode::App { fun, arg, .. } => update_app(
            term,
            subst_term_aux(tyenv, tenv, fun)?,
            subst_term_aux(tyenv, tenv, arg)?,
        ),
    })
}

pub fn subst_term(tyenv: &TyEnv, tenv: &TEnv, term: &Term) -> Res<Term> {
    if is_empty_table(tenv) && is_empty_table(tyenv) {
        return Ok(term.clone());
    }
    subst_term_aux(tyenv, tenv, term)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pure::testing::{
        attempt, check_problems, parse_term, parse_typ, show, show_envir, show_typ,
    };

    // The expectations are recorded from envir.ts (see pure/testing.rs).
    #[test]
    fn matches_the_typescript() {
        check_problems(
            include_str!("../../testdata/kernel/envir.txt"),
            |kind, fields| {
                let mut lines = Vec::new();
                match kind {
                    "term" => {
                        let term = parse_term(fields[0]);
                        let normal = beta_norm(&term).unwrap();
                        lines.push(format!("beta_norm {}", show(&normal)));
                        lines.push(format!("eta_contract {}", show(&eta_contract(&term))));
                        lines.push(format!("aeconv_beta {}", aeconv(&term, &normal)));
                        attempt(&mut lines, |lines| {
                            let ty = fastype(&empty_envir(-1), &[], &term)?;
                            lines.push(format!("fastype {}", show_typ(&ty)));
                            Ok(())
                        });
                    }
                    "genvars" => {
                        let types: Vec<Typ> =
                            fields[2..].iter().map(|text| parse_typ(text)).collect();
                        let (envir, vars) =
                            genvars(fields[0], &empty_envir(fields[1].parse().unwrap()), &types);
                        lines.push(format!("maxidx {}", envir.maxidx));
                        lines.extend(
                            vars.iter()
                                .map(|variable| format!("var {}", show(variable))),
                        );
                    }
                    "instantiate" => attempt(&mut lines, |lines| {
                        let (target, pairs) = fields[1..].split_last().unwrap();
                        let mut envir = empty_envir(fields[0].parse().unwrap());
                        for pair in pairs.chunks(2) {
                            envir = vupdate(&parse_term(pair[0]), parse_term(pair[1]), &envir)?;
                        }
                        let target = parse_term(target);
                        lines.extend(show_envir(&envir));
                        let above = [-1, 0, 1, 2].map(|limit| above(&envir, limit).to_string());
                        lines.push(format!("above {}", above.join(" ")));
                        lines.push(format!("norm_term {}", show(&norm_term(&envir, &target)?)));
                        lines.push(format!("head_norm {}", show(&head_norm(&envir, &target)?)));
                        let substituted = subst_term(&envir.tyenv, &envir.tenv, &target)?;
                        lines.push(format!("subst_term {}", show(&substituted)));
                        let ty = fastype(&envir, &[], &target)?;
                        lines.push(format!("fastype {}", show_typ(&ty)));
                        Ok(())
                    }),
                    _ => panic!("unknown problem {kind}"),
                }
                lines
            },
        );
    }
}
