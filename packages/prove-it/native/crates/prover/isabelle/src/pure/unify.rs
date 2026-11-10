//! Ported from Isabelle2025's Pure/unify.ML, Huet's higher-order unification with the search
//! bound of 60. Copyright (c) 1986-2025 University of Cambridge, Technische Universitaet Muenchen,
//! and contributors, see LICENSE.
//!
//! (`pure/unify.ts`.) The search is lazy: each unifier is computed when its cell is pulled, and
//! each step of the search checks for an interrupt.

use std::cmp::Ordering;
use std::rc::Rc;

use crate::error::{Error, Res, error_exn, term_exn};

use super::envir::{
    Envir, dest_var, env_binder_types, env_body_type, fastype, genvar, genvars, head_norm, lookup,
    norm_term, update, var_key, vupdate,
};
use super::interrupt::{check_interrupt, check_stack};
use super::logic::{Binder, combound, rlist_abs};
use super::pattern::{PatternUnify, unify_pattern, unify_types_envir};
use super::seq::{
    Seq, Step, cons_seq, defer_seq, empty_seq, it_right_seq, map_seq, maps_seq, single_seq,
};
use super::table::{IndexKey, indexname_ord};
use super::term::{
    HAS_VAR, Name, Term, TermNode, Typ, TypNode, Var, aconv, eq_typ, flags_of, fun_ts, head_of,
    incr_boundvars, list_comb, loose_bnos, mk_abs, mk_app, mk_bound, strip_abs_body, strip_comb,
};
use super::types::lookup_ty_env;

const SEARCH_BOUND: usize = 60;

#[derive(Clone)]
struct Dpair {
    binders: Rc<[Binder]>,
    left: Term,
    right: Term,
}

pub type Tpair = (Term, Term);

fn binder_types(binders: &[Binder]) -> Vec<Typ> {
    binders.iter().map(|binder| binder.ty.clone()).collect()
}

fn fastype_in(envir: &Envir, binders: &[Binder], term: &Term) -> Res<Typ> {
    fastype(envir, &binder_types(binders), term)
}

fn prepend(binder: Binder, binders: &[Binder]) -> Rc<[Binder]> {
    std::iter::once(binder)
        .chain(binders.iter().cloned())
        .collect()
}

fn eta_norm(envir: &Envir, binders: &[Binder], term: &Term) -> Res<Term> {
    fn etif(envir: &Envir, ty: &Typ, current: Term) -> Term {
        if let Some((domain, range)) = ty.dest_fun() {
            return mk_abs(
                "",
                domain.clone(),
                etif(
                    envir,
                    range,
                    mk_app(incr_boundvars(1, &current), mk_bound(0)),
                ),
            );
        }
        if let TypNode::TVar { name, index, .. } = &**ty {
            let key = IndexKey {
                name: name.clone(),
                index: *index,
            };
            return match lookup_ty_env(&envir.tyenv, &key) {
                None => current,
                Some(assigned) => etif(envir, assigned, current),
            };
        }
        current
    }
    fn eta_nm(envir: &Envir, scope: &[Binder], current: &Term) -> Res<Term> {
        let _depth = check_stack()?;
        match &**current {
            TermNode::Abs { name, ty, body, .. } => {
                let inner = prepend(
                    Binder {
                        name: name.clone(),
                        ty: ty.clone(),
                    },
                    scope,
                );
                Ok(mk_abs(
                    name.clone(),
                    ty.clone(),
                    eta_nm(envir, &inner, body)?,
                ))
            }
            _ => Ok(etif(
                envir,
                &fastype_in(envir, scope, current)?,
                current.clone(),
            )),
        }
    }
    eta_nm(envir, binders, term)
}

fn same_indexname(left: &Term, right: &Term) -> bool {
    let (left_name, left_index, _) = dest_var(left);
    let (right_name, right_index, _) = dest_var(right);
    left_name == right_name && left_index == right_index
}

fn occurs_terms(seen: &mut Vec<Var>, envir: &Envir, variable: &Var, terms: &[Term]) -> Res<bool> {
    fn occur(seen: &mut Vec<Var>, envir: &Envir, variable: &Var, term: &Term) -> Res<bool> {
        if flags_of(term) & HAS_VAR == 0 {
            return Ok(false);
        }
        let _depth = check_stack()?;
        match &**term {
            TermNode::Const { .. } | TermNode::Bound { .. } | TermNode::Free { .. } => Ok(false),
            TermNode::Var { .. } => {
                if seen.iter().any(|other| same_indexname(other, term)) {
                    return Ok(false);
                }
                if same_indexname(variable, term) {
                    return Ok(true);
                }
                seen.push(term.clone());
                match lookup(envir, term)? {
                    None => Ok(false),
                    Some(assigned) => occur(seen, envir, variable, &assigned),
                }
            }
            TermNode::Abs { body, .. } => occur(seen, envir, variable, body),
            TermNode::App { fun, arg, .. } => {
                Ok(occur(seen, envir, variable, arg)? || occur(seen, envir, variable, fun)?)
            }
        }
    }
    for term in terms {
        if occur(seen, envir, variable, term)? {
            return Ok(true);
        }
    }
    Ok(false)
}

fn head_of_in(envir: &Envir, term: &Term) -> Res<Term> {
    match &**term {
        TermNode::App { fun, .. } => head_of_in(envir, fun),
        TermNode::Var { .. } => match lookup(envir, term)? {
            None => Ok(term.clone()),
            Some(assigned) => head_of_in(envir, &assigned),
        },
        _ => Ok(term.clone()),
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Occurrence {
    None,
    Nonrigid,
    Rigid,
}

fn rigid_occurs_term(
    seen: &mut Vec<Var>,
    envir: &Envir,
    variable: &Var,
    term: &Term,
) -> Res<Occurrence> {
    fn nonrigid(
        seen: &mut Vec<Var>,
        envir: &Envir,
        variable: &Var,
        current: &Term,
    ) -> Res<Occurrence> {
        Ok(
            if occurs_terms(seen, envir, variable, std::slice::from_ref(current))? {
                Occurrence::Nonrigid
            } else {
                Occurrence::None
            },
        )
    }
    fn occomb(
        seen: &mut Vec<Var>,
        envir: &Envir,
        variable: &Var,
        current: &Term,
    ) -> Res<Occurrence> {
        let TermNode::App { fun, arg, .. } = &**current else {
            return occur(seen, envir, variable, current);
        };
        let _depth = check_stack()?;
        let argument = occur(seen, envir, variable, arg)?;
        if argument == Occurrence::Rigid {
            return Ok(Occurrence::Rigid);
        }
        let rest = occomb(seen, envir, variable, fun)?;
        Ok(if rest == Occurrence::None {
            argument
        } else {
            rest
        })
    }
    fn occur(
        seen: &mut Vec<Var>,
        envir: &Envir,
        variable: &Var,
        current: &Term,
    ) -> Res<Occurrence> {
        let _depth = check_stack()?;
        match &**current {
            TermNode::Const { .. } | TermNode::Bound { .. } | TermNode::Free { .. } => {
                Ok(Occurrence::None)
            }
            TermNode::Var { .. } => {
                if seen.iter().any(|other| same_indexname(other, current)) {
                    return Ok(Occurrence::None);
                }
                if same_indexname(variable, current) {
                    return Ok(Occurrence::Rigid);
                }
                seen.push(current.clone());
                match lookup(envir, current)? {
                    None => Ok(Occurrence::None),
                    Some(assigned) => occur(seen, envir, variable, &assigned),
                }
            }
            TermNode::Abs { body, .. } => occur(seen, envir, variable, body),
            TermNode::App { fun, .. } => {
                let head = head_of_in(envir, fun)?;
                match &*head {
                    TermNode::Var { .. } => {
                        if same_indexname(variable, &head) {
                            Ok(Occurrence::Rigid)
                        } else {
                            nonrigid(seen, envir, variable, current)
                        }
                    }
                    TermNode::Abs { .. } => nonrigid(seen, envir, variable, current),
                    _ => occomb(seen, envir, variable, current),
                }
            }
        }
    }
    occur(seen, envir, variable, term)
}

fn unify_types(left: &Typ, right: &Typ, envir: &Envir) -> Res<Envir> {
    unify_types_envir(left, right, envir)?.ok_or(Error::CantUnify)
}

/// get_eta_var: the variable a term eta-contracts to over the binders, or `None` for ASSIGN.
fn get_eta_var(binders: &[Binder], level: i32, term: &Term) -> Option<Var> {
    if binders.is_empty() {
        return term.is_var().then(|| term.clone());
    }
    if let TermNode::App { fun, arg, .. } = &**term
        && matches!(&**arg, TermNode::Bound { index } if *index == level)
    {
        return get_eta_var(&binders[1..], level + 1, fun);
    }
    None
}

/// assignment: `None` where Isabelle raises ASSIGN.
fn assignment(binders: &[Binder], left: &Term, right: &Term, envir: &Envir) -> Res<Option<Envir>> {
    let Some(variable) = get_eta_var(binders, 0, left) else {
        return Ok(None);
    };
    match rigid_occurs_term(&mut Vec::new(), envir, &variable, right)? {
        Occurrence::Nonrigid => return Ok(None),
        Occurrence::Rigid => return Err(Error::CantUnify),
        Occurrence::None => {}
    }
    let unified = unify_types(
        &env_body_type(envir, dest_var(&variable).2),
        &fastype_in(envir, binders, right)?,
        envir,
    )?;
    update(&variable, rlist_abs(binders, right.clone()), &unified).map(Some)
}

fn new_dpair(
    binders: Rc<[Binder]>,
    left: &Term,
    right: &Term,
    envir: &Envir,
) -> Res<(Dpair, Envir)> {
    match (&**left, &**right) {
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
            let unified = unify_types(ty, right_ty, envir)?;
            let name = if name.is_empty() { right_name } else { name };
            new_dpair(
                prepend(
                    Binder {
                        name: name.clone(),
                        ty: ty.clone(),
                    },
                    &binders,
                ),
                left_body,
                right_body,
                &unified,
            )
        }
        (TermNode::Abs { .. }, _) | (_, TermNode::Abs { .. }) => Err(term_exn("new_dpair")),
        _ => Ok((
            Dpair {
                binders,
                left: left.clone(),
                right: right.clone(),
            },
            envir.clone(),
        )),
    }
}

fn head_norm_dpair(envir: &Envir, dpair: &Dpair) -> Res<(Dpair, Envir)> {
    let left = eta_norm(envir, &dpair.binders, &head_norm(envir, &dpair.left)?)?;
    let right = eta_norm(envir, &dpair.binders, &head_norm(envir, &dpair.right)?)?;
    new_dpair(dpair.binders.clone(), &left, &right, envir)
}

struct Simplified {
    envir: Envir,
    flexflex: Vec<Dpair>,
    flexrigid: Vec<Dpair>,
}

fn prepended(dpair: Dpair, dpairs: Vec<Dpair>) -> Vec<Dpair> {
    let mut result = Vec::with_capacity(dpairs.len() + 1);
    result.push(dpair);
    result.extend(dpairs);
    result
}

fn simpl0(start: &Dpair, state: Simplified) -> Res<Simplified> {
    let _depth = check_stack()?;
    let (dpair, envir) = head_norm_dpair(&state.envir, start)?;
    let sim_rands = |left: &Term, right: &Term, current: Simplified| -> Res<Simplified> {
        fn go(
            binders: &Rc<[Binder]>,
            left: &Term,
            right: &Term,
            current: Simplified,
        ) -> Res<Simplified> {
            match (&**left, &**right) {
                (
                    TermNode::App { fun, arg, .. },
                    TermNode::App {
                        fun: right_fun,
                        arg: right_arg,
                        ..
                    },
                ) => {
                    let current = go(binders, fun, right_fun, current)?;
                    simpl0(
                        &Dpair {
                            binders: binders.clone(),
                            left: arg.clone(),
                            right: right_arg.clone(),
                        },
                        current,
                    )
                }
                (TermNode::App { .. }, _) | (_, TermNode::App { .. }) => {
                    Err(term_exn("SIMPL: operands mismatch"))
                }
                _ => Ok(current),
            }
        }
        go(&dpair.binders, left, right, current)
    };
    let left_head = head_of(&dpair.left);
    let right_head = head_of(&dpair.right);
    match (&**left_head, &**right_head) {
        (TermNode::Var { ty, .. }, TermNode::Var { ty: right_ty, .. }) => {
            let unified = unify_types(
                &env_body_type(&envir, ty),
                &env_body_type(&envir, right_ty),
                &envir,
            )?;
            Ok(Simplified {
                envir: unified,
                flexflex: prepended(dpair, state.flexflex),
                flexrigid: state.flexrigid,
            })
        }
        (TermNode::Var { .. }, _) => Ok(
            match assignment(&dpair.binders, &dpair.left, &dpair.right, &envir)? {
                None => Simplified {
                    envir,
                    flexflex: state.flexflex,
                    flexrigid: prepended(dpair, state.flexrigid),
                },
                Some(assigned) => Simplified {
                    envir: assigned,
                    flexflex: state.flexflex,
                    flexrigid: state.flexrigid,
                },
            },
        ),
        (_, TermNode::Var { .. }) => Ok(
            match assignment(&dpair.binders, &dpair.right, &dpair.left, &envir)? {
                None => Simplified {
                    envir,
                    flexflex: state.flexflex,
                    flexrigid: prepended(
                        Dpair {
                            binders: dpair.binders.clone(),
                            left: dpair.right.clone(),
                            right: dpair.left.clone(),
                        },
                        state.flexrigid,
                    ),
                },
                Some(assigned) => Simplified {
                    envir: assigned,
                    flexflex: state.flexflex,
                    flexrigid: state.flexrigid,
                },
            },
        ),
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
                return Err(Error::CantUnify);
            }
            let current = Simplified {
                envir: unify_types(ty, right_ty, &envir)?,
                flexflex: state.flexflex,
                flexrigid: state.flexrigid,
            };
            sim_rands(&dpair.left, &dpair.right, current)
        }
        (TermNode::Bound { index }, TermNode::Bound { index: right_index }) => {
            if index != right_index {
                return Err(Error::CantUnify);
            }
            let current = Simplified {
                envir,
                flexflex: state.flexflex,
                flexrigid: state.flexrigid,
            };
            sim_rands(&dpair.left, &dpair.right, current)
        }
        _ => Err(Error::CantUnify),
    }
}

fn is_changed(envir: &Envir, term: &Term) -> Res<bool> {
    match &**term {
        TermNode::App { fun, .. } => is_changed(envir, fun),
        TermNode::Var { .. } => Ok(lookup(envir, term)?.is_some()),
        _ => Ok(false),
    }
}

fn simpl(envir: &Envir, dpairs: &[Dpair]) -> Res<Simplified> {
    let all = dpairs.iter().rev().try_fold(
        Simplified {
            envir: envir.clone(),
            flexflex: Vec::new(),
            flexrigid: Vec::new(),
        },
        |state, dpair| simpl0(dpair, state),
    )?;
    let remaining: Vec<Dpair> = all.flexrigid.iter().chain(&all.flexflex).cloned().collect();
    for dpair in &remaining {
        if is_changed(&all.envir, &dpair.left)? || is_changed(&all.envir, &dpair.right)? {
            let _depth = check_stack()?;
            return simpl(&all.envir, &remaining);
        }
    }
    Ok(all)
}

fn make_args(name: &str, binder: &[Typ], envir: &Envir, types: &[Typ]) -> (Envir, Vec<Term>) {
    if types.is_empty() {
        return (envir.clone(), Vec::new());
    }
    let (updated, vars) = genvars(
        name,
        envir,
        &types
            .iter()
            .map(|ty| fun_ts(binder, ty.clone()))
            .collect::<Vec<_>>(),
    );
    (
        updated,
        vars.into_iter()
            .map(|variable| combound(variable, 0, binder.len()))
            .collect(),
    )
}

fn types_abs(types: &[Typ], body: Term) -> Term {
    types
        .iter()
        .rev()
        .fold(body, |result, ty| mk_abs("", ty.clone(), result))
}

fn strip_type(envir: &Envir, ty: &Typ) -> (Vec<Typ>, Typ) {
    (env_binder_types(envir, ty), env_body_type(envir, ty))
}

#[derive(Clone)]
struct Copied {
    term: Term,
    envir: Envir,
    dpairs: Vec<Dpair>,
}

#[derive(Clone)]
struct Prefix {
    args: Vec<Term>,
    envir: Envir,
    dpairs: Vec<Dpair>,
}

/// matchcopy's copy, with the name of the variable it copies for.
fn copy(
    name: &Name,
    binders: &Rc<[Binder]>,
    targs: &Rc<[Term]>,
    target: &Term,
    envir: &Envir,
    dpairs: &[Dpair],
) -> Res<Seq<Copied>> {
    let _depth = check_stack()?;
    let copycons = {
        let (name, binders, targs) = (name.clone(), binders.clone(), targs.clone());
        move |uarg: &Term, prefix: Prefix| -> Res<Seq<Prefix>> {
            let normal = eta_norm(&prefix.envir, &binders, &head_norm(&prefix.envir, uarg)?)?;
            let args = prefix.args;
            Ok(map_seq(
                move |result: Copied| {
                    let mut all = vec![result.term];
                    all.extend(args.iter().cloned());
                    Ok(Prefix {
                        args: all,
                        envir: result.envir,
                        dpairs: result.dpairs,
                    })
                },
                copy(
                    &name,
                    &binders,
                    &targs,
                    &normal,
                    &prefix.envir,
                    &prefix.dpairs,
                )?,
            ))
        }
    };
    let copycons = Rc::new(copycons);
    fn copyargs(
        copycons: &Rc<dyn Fn(&Term, Prefix) -> Res<Seq<Prefix>>>,
        uargs: &[Term],
        envir: &Envir,
        dpairs: &[Dpair],
    ) -> Seq<Prefix> {
        let Some((first, rest)) = uargs.split_first() else {
            return cons_seq(
                Prefix {
                    args: Vec::new(),
                    envir: envir.clone(),
                    dpairs: dpairs.to_vec(),
                },
                empty_seq(),
            );
        };
        let (copycons_here, first) = (copycons.clone(), first.clone());
        maps_seq(
            move |prefix| copycons_here(&first, prefix),
            copyargs(copycons, rest, envir, dpairs),
        )
    }
    let (uhead, uargs) = strip_comb(target);
    let base = env_body_type(envir, &fastype_in(envir, binders, &uhead)?);
    let types = targs
        .iter()
        .map(|targ| fastype_in(envir, binders, targ))
        .collect::<Res<Vec<_>>>()?;
    let projenv = |head: Term,
                   arg_types: Vec<Typ>,
                   body_type: &Typ,
                   targ: Term,
                   tail: Seq<Copied>|
     -> Res<Seq<Copied>> {
        let Some(unified) = unify_types_envir(&base, body_type, envir)? else {
            return Ok(tail);
        };
        let (name, binders, targs, target, dpairs, types) = (
            name.clone(),
            binders.clone(),
            targs.clone(),
            target.clone(),
            dpairs.to_vec(),
            types.clone(),
        );
        Ok(defer_seq(move || {
            let attempt = || -> Res<Copied> {
                let (with_args, args) = make_args(&name, &types, &unified, &arg_types);
                let plugin = |arg: &Term| list_comb(head_of(arg).clone(), &targs);
                let dpair = Dpair {
                    binders: binders.clone(),
                    left: list_comb(targ.clone(), &args.iter().map(plugin).collect::<Vec<_>>()),
                    right: target.clone(),
                };
                let simplified = simpl(&with_args, &prepended(dpair, dpairs.clone()))?;
                Ok(Copied {
                    term: list_comb(head.clone(), &args),
                    envir: simplified.envir,
                    dpairs: simplified
                        .flexrigid
                        .into_iter()
                        .chain(simplified.flexflex)
                        .collect(),
                })
            };
            match attempt() {
                Ok(result) => Ok(Step::Cell(Some((result, tail.clone())))),
                Err(Error::CantUnify) => Ok(Step::Seq(tail.clone())),
                Err(error) => Err(error),
            }
        }))
    };
    let joinargs = {
        let uhead = uhead.clone();
        move |result: Prefix| -> Res<Copied> {
            Ok(Copied {
                term: list_comb(uhead.clone(), &result.args),
                envir: result.envir,
                dpairs: result.dpairs,
            })
        }
    };
    let matchfun = |projections: &[(Term, Typ, Term)]| -> Res<Seq<Copied>> {
        let mut result = if uhead.is_const() || uhead.is_free() {
            let copycons: Rc<dyn Fn(&Term, Prefix) -> Res<Seq<Prefix>>> = copycons.clone();
            map_seq(joinargs, copyargs(&copycons, &uargs, envir, dpairs))
        } else {
            empty_seq()
        };
        // matchfun builds its sequence from the last projection to the first, as the TypeScript
        // evaluates the tail argument of each projenv before the projenv itself.
        for (bvar, ty, targ) in projections.iter().rev() {
            let (arg_types, body_type) = strip_type(envir, ty);
            result = projenv(bvar.clone(), arg_types, &body_type, targ.clone(), result)?;
        }
        Ok(result)
    };
    match &*uhead {
        TermNode::Abs {
            name: abs_name,
            ty,
            body,
            ..
        } => {
            let inner_binders = prepend(
                Binder {
                    name: abs_name.clone(),
                    ty: ty.clone(),
                },
                binders,
            );
            let inner_targs: Rc<[Term]> = targs
                .iter()
                .map(|targ| incr_boundvars(1, targ))
                .chain(std::iter::once(mk_bound(0)))
                .collect();
            let (abs_name, ty) = (abs_name.clone(), ty.clone());
            Ok(map_seq(
                move |result: Copied| {
                    Ok(Copied {
                        term: mk_abs(abs_name.clone(), ty.clone(), result.term),
                        ..result
                    })
                },
                copy(name, &inner_binders, &inner_targs, body, envir, dpairs)?,
            ))
        }
        TermNode::Var { name: var_name, .. } => {
            let (updated, head) = genvar(var_name, envir, fun_ts(&types, base.clone()));
            Ok(single_seq(Copied {
                term: combound(head.clone(), 0, types.len()),
                envir: updated,
                dpairs: prepended(
                    Dpair {
                        binders: binders.clone(),
                        left: list_comb(head, targs),
                        right: target.clone(),
                    },
                    dpairs.to_vec(),
                ),
            }))
        }
        _ => {
            let mut projections: Vec<(Term, Typ, Term)> = types
                .iter()
                .enumerate()
                .map(|(index, ty)| {
                    (
                        mk_bound((types.len() - 1 - index) as i32),
                        ty.clone(),
                        targs[index].clone(),
                    )
                })
                .collect();
            projections.reverse();
            matchfun(&projections)
        }
    }
}

/// match: the ways to assign the head of a flex-rigid pair.
fn match_dpair(envir: &Envir, dpair: &Dpair, dpairs: &[Dpair]) -> Res<Seq<(Envir, Vec<Dpair>)>> {
    let (head, targs) = strip_comb(&dpair.left);
    let TermNode::Var { name, ty, .. } = &*head else {
        return Err(term_exn("MATCH"));
    };
    let types = env_binder_types(envir, ty);
    let copied = copy(
        name,
        &dpair.binders,
        &Rc::from(targs),
        &dpair.right,
        envir,
        dpairs,
    )?;
    Ok(map_seq(
        move |result: Copied| -> Res<(Envir, Vec<Dpair>)> {
            Ok(match lookup(&result.envir, &head)? {
                None => (
                    update(&head, types_abs(&types, result.term), &result.envir)?,
                    result.dpairs,
                ),
                Some(assigned) => (
                    result.envir,
                    prepended(
                        Dpair {
                            binders: Rc::from([]),
                            left: assigned,
                            right: types_abs(&types, result.term),
                        },
                        result.dpairs,
                    ),
                ),
            })
        },
        copied,
    ))
}

/// ff_assign: `None` where Isabelle raises ASSIGN.
fn ff_assign(envir: &Envir, binders: &[Binder], left: &Term, right: &Term) -> Res<Option<Envir>> {
    let Some(variable) = get_eta_var(binders, 0, left) else {
        return Ok(None);
    };
    if occurs_terms(
        &mut Vec::new(),
        envir,
        &variable,
        std::slice::from_ref(right),
    )? {
        return Ok(None);
    }
    let unified = unify_types(
        &env_body_type(envir, dest_var(&variable).2),
        &fastype_in(envir, binders, right)?,
        envir,
    )?;
    vupdate(&variable, rlist_abs(binders, right.clone()), &unified).map(Some)
}

#[derive(Clone)]
struct Flarg {
    index: i32,
    term: Term,
    ty: Typ,
}

fn rigid_bound(level: i32, banned: &[i32], term: &Term) -> bool {
    let (head, args) = strip_comb(term);
    match &*head {
        TermNode::Bound { index } => {
            banned.contains(&(index - level))
                || args.iter().any(|arg| rigid_bound(level, banned, arg))
        }
        TermNode::Var { .. } => false,
        TermNode::Abs { body, .. } => {
            rigid_bound(level + 1, banned, body)
                || args.iter().any(|arg| rigid_bound(level, banned, arg))
        }
        _ => args.iter().any(|arg| rigid_bound(level, banned, arg)),
    }
}

fn change_bnos(banned: &[i32], term: &Term) -> Res<Term> {
    fn change(banned: &[i32], level: i32, current: &Term) -> Res<Term> {
        match &**current {
            TermNode::Bound { index } => {
                if *index < level {
                    return Ok(current.clone());
                }
                if banned.contains(&(index - level)) {
                    return Err(Error::ChangeFail);
                }
                Ok(mk_bound(
                    index
                        - banned
                            .iter()
                            .filter(|banned_index| **banned_index < index - level)
                            .count() as i32,
                ))
            }
            TermNode::Abs { name, ty, body, .. } => Ok(mk_abs(
                name.clone(),
                ty.clone(),
                change(banned, level + 1, body)?,
            )),
            TermNode::App { fun, arg, .. } => {
                let fun = change(banned, level, fun)?;
                Ok(mk_app(fun, change(banned, level, arg)?))
            }
            _ => Ok(current.clone()),
        }
    }
    change(banned, 0, term)
}

fn sort_args(args: &[Flarg]) -> Vec<Flarg> {
    fn less_arg(left: &Flarg, right: &Flarg) -> bool {
        matches!(
            (&*left.term, &*right.term),
            (TermNode::Bound { index }, TermNode::Bound { index: right_index }) if right_index < index
        )
    }
    fn insert(item: &Flarg, sorted: &[Flarg]) -> Vec<Flarg> {
        let Some((first, rest)) = sorted.split_first() else {
            return vec![item.clone()];
        };
        if less_arg(first, item) {
            let mut result = vec![first.clone()];
            result.extend(insert(item, rest));
            return result;
        }
        let mut result = vec![item.clone()];
        result.extend_from_slice(sorted);
        result
    }
    match args.split_first() {
        None => Vec::new(),
        Some((first, rest)) => insert(first, &sort_args(rest)),
    }
}

fn is_decreasing(count: i32, args: &[Flarg]) -> bool {
    match args.split_first() {
        None => count == 0,
        Some((first, rest)) => first.index == count - 1 && is_decreasing(count - 1, rest),
    }
}

fn clean_term(banned: &[i32], envir: &Envir, term: &Term) -> Res<(Envir, Term)> {
    let (head, terms) = strip_comb(term);
    let TermNode::Var { name, ty, .. } = &*head else {
        return Err(term_exn("clean_term"));
    };
    let (types, body_type) = strip_type(envir, ty);
    if terms.len() != types.len() {
        return Err(Error::ChangeFail);
    }
    let flexargs: Vec<Flarg> = terms
        .iter()
        .enumerate()
        .map(|(position, arg)| Flarg {
            index: (terms.len() - 1 - position) as i32,
            term: arg.clone(),
            ty: types[position].clone(),
        })
        .collect();
    let mut changed: Vec<Flarg> = Vec::new();
    for arg in flexargs.iter().rev() {
        if !rigid_bound(0, banned, &arg.term) {
            changed.insert(
                0,
                Flarg {
                    term: change_bnos(banned, &arg.term)?,
                    ..arg.clone()
                },
            );
        }
    }
    let args = sort_args(&changed);
    if is_decreasing(types.len() as i32, &args) {
        return Ok((
            envir.clone(),
            list_comb(
                head.clone(),
                &args.iter().map(|arg| arg.term.clone()).collect::<Vec<_>>(),
            ),
        ));
    }
    let (with_var, fresh) = genvar(
        name,
        envir,
        fun_ts(
            &args.iter().map(|arg| arg.ty.clone()).collect::<Vec<_>>(),
            body_type,
        ),
    );
    let body = list_comb(
        fresh.clone(),
        &args
            .iter()
            .map(|arg| mk_bound(arg.index))
            .collect::<Vec<_>>(),
    );
    let updated = vupdate(&head, types_abs(&types, body), &with_var)?;
    let normal = norm_term(
        &updated,
        &list_comb(
            fresh,
            &args.iter().map(|arg| arg.term.clone()).collect::<Vec<_>>(),
        ),
    )?;
    Ok((updated, normal))
}

fn add_tpair(binders: &[Binder], left: &Term, right: &Term, tpairs: &[Tpair]) -> Vec<Tpair> {
    if aconv(left, right) {
        return tpairs.to_vec();
    }
    let left_abs = rlist_abs(binders, left.clone());
    let right_abs = rlist_abs(binders, right.clone());
    if tpairs
        .iter()
        .any(|pair| aconv(&left_abs, &pair.0) && aconv(&right_abs, &pair.1))
    {
        return tpairs.to_vec();
    }
    let mut result = vec![(left_abs, right_abs)];
    result.extend_from_slice(tpairs);
    result
}

fn clean_ffpair(dpair: &Dpair, envir: &Envir, tpairs: &[Tpair]) -> Res<(Envir, Vec<Tpair>)> {
    let attempt = || -> Res<(Envir, Vec<Tpair>)> {
        let left_loose = loose_bnos(&dpair.left);
        let right_loose = loose_bnos(&dpair.right);
        let mut banned: Vec<i32> = Vec::new();
        let mut kept: Vec<Binder> = Vec::new();
        for index in (0..dpair.binders.len()).rev() {
            let bound = index as i32;
            if left_loose.contains(&bound) && right_loose.contains(&bound) {
                kept.insert(0, dpair.binders[index].clone());
            } else {
                banned.insert(0, bound);
            }
        }
        let (left_envir, left) = clean_term(&banned, envir, &dpair.left)?;
        let (right_envir, right) = clean_term(&banned, &left_envir, &dpair.right)?;
        let assigned = match ff_assign(&right_envir, &kept, &left, &right)? {
            Some(assigned) => Some(assigned),
            None => ff_assign(&right_envir, &kept, &right, &left)?,
        };
        Ok(match assigned {
            None => (right_envir, add_tpair(&kept, &left, &right, tpairs)),
            Some(assigned) => (assigned, tpairs.to_vec()),
        })
    };
    match attempt() {
        Err(Error::ChangeFail) => Ok((
            envir.clone(),
            add_tpair(&dpair.binders, &dpair.left, &dpair.right, tpairs),
        )),
        result => result,
    }
}

fn add_ffpair(dpair: &Dpair, envir: &Envir, tpairs: &[Tpair]) -> Res<(Envir, Vec<Tpair>)> {
    let left = norm_term(envir, &dpair.left)?;
    let right = norm_term(envir, &dpair.right)?;
    let left_head = head_of(&left);
    let right_head = head_of(&right);
    let (TermNode::Var { ty, .. }, TermNode::Var { ty: right_ty, .. }) =
        (&**left_head, &**right_head)
    else {
        return Err(term_exn("add_ffpair: Vars expected"));
    };
    if same_indexname(left_head, right_head) {
        if !eq_typ(ty, right_ty) {
            return Err(term_exn("add_ffpair: Var name confusion"));
        }
        return Ok((
            envir.clone(),
            add_tpair(&dpair.binders, &left, &right, tpairs),
        ));
    }
    if indexname_ord(&var_key(left_head), &var_key(right_head)) == Ordering::Less {
        clean_ffpair(
            &Dpair {
                binders: dpair.binders.clone(),
                left: right.clone(),
                right: left.clone(),
            },
            envir,
            tpairs,
        )
    } else {
        clean_ffpair(
            &Dpair {
                binders: dpair.binders.clone(),
                left: left.clone(),
                right: right.clone(),
            },
            envir,
            tpairs,
        )
    }
}

#[derive(Clone)]
pub struct Unifier {
    pub envir: Envir,
    pub tpairs: Vec<Tpair>,
}

fn hounifiers(binders: Rc<[Binder]>, envir: &Envir, pairs: &[Tpair]) -> Seq<Unifier> {
    // Isabelle pulls the alternatives inside its handler for CANTUNIFY, but each alternative
    // handles its own, so handing them over to the caller's loop changes nothing.
    fn add_unify(
        depth: usize,
        envir_in: Envir,
        dpairs: Vec<Dpair>,
        rest: Seq<Unifier>,
    ) -> Seq<Unifier> {
        defer_seq(move || {
            check_interrupt()?;
            let attempt = || -> Res<Step<Unifier>> {
                let simplified = simpl(&envir_in, &dpairs)?;
                let Some((first, others)) = simplified.flexrigid.split_first() else {
                    let (envir, tpairs) = simplified.flexflex.iter().rev().try_fold(
                        (simplified.envir.clone(), Vec::new()),
                        |(envir, tpairs), dpair| add_ffpair(dpair, &envir, &tpairs),
                    )?;
                    return Ok(Step::Cell(Some((Unifier { envir, tpairs }, rest.clone()))));
                };
                if depth > SEARCH_BOUND {
                    return Ok(Step::Seq(rest.clone()));
                }
                let others: Vec<Dpair> =
                    others.iter().chain(&simplified.flexflex).cloned().collect();
                Ok(Step::Seq(it_right_seq(
                    move |item: (Envir, Vec<Dpair>), tail| {
                        Ok(add_unify(depth + 1, item.0, item.1, tail))
                    },
                    match_dpair(&simplified.envir, first, &others)?,
                    rest.clone(),
                )))
            };
            match attempt() {
                Err(Error::CantUnify) => Ok(Step::Seq(rest.clone())),
                result => result,
            }
        })
    }
    add_unify(
        1,
        envir.clone(),
        pairs
            .iter()
            .map(|pair| Dpair {
                binders: binders.clone(),
                left: pair.0.clone(),
                right: pair.1.clone(),
            })
            .collect(),
        empty_seq(),
    )
}

/// Unify.unifiers: pattern unification first, Huet's procedure outside the pattern fragment.
pub fn unifiers(envir: &Envir, pairs: &[Tpair]) -> Res<Seq<Unifier>> {
    let mut current = envir.clone();
    for pair in pairs {
        match unify_pattern(&pair.0, &pair.1, &current)? {
            PatternUnify::Clash => return Ok(empty_seq()),
            PatternUnify::NotAPattern => return Ok(hounifiers(Rc::from([]), envir, pairs)),
            PatternUnify::Unified(unified) => current = unified,
        }
    }
    Ok(single_seq(Unifier {
        envir: current,
        tpairs: Vec::new(),
    }))
}

fn var_head_of(envir: &Envir, term: &Term) -> Res<Var> {
    let normal = norm_term(envir, term)?;
    let head = head_of(strip_abs_body(&normal));
    if !head.is_var() {
        return Err(error_exn("CANTUNIFY"));
    }
    Ok(head.clone())
}

fn type_abs(envir: &Envir, ty: &Typ, term: Term) -> Term {
    types_abs(&env_binder_types(envir, ty), term)
}

fn smash_flexflex1(pair: &Tpair, envir: &Envir) -> Res<Envir> {
    let left = var_head_of(envir, &pair.0)?;
    let right = var_head_of(envir, &pair.1)?;
    let (left_name, _, left_ty) = dest_var(&left);
    let (_, _, right_ty) = dest_var(&right);
    let (with_var, fresh) = genvar(left_name, envir, env_body_type(envir, left_ty));
    let updated = vupdate(
        &right,
        type_abs(&with_var, right_ty, fresh.clone()),
        &with_var,
    )?;
    if same_indexname(&left, &right) && eq_typ(left_ty, right_ty) {
        return Ok(updated);
    }
    vupdate(&left, type_abs(&with_var, left_ty, fresh), &updated)
}

/// Unify.smash_unifiers: unifiers with no remaining flex-flex pairs. A pair whose side is not
/// flexible stops the sequence, as CANTUNIFY escapes Seq.map in Isabelle.
pub fn smash_unifiers(pairs: &[Tpair], envir: &Envir) -> Res<Seq<Envir>> {
    Ok(map_seq(
        |unifier: Unifier| {
            unifier
                .tpairs
                .iter()
                .rev()
                .try_fold(unifier.envir.clone(), |state, pair| {
                    smash_flexflex1(pair, &state)
                })
        },
        unifiers(envir, pairs)?,
    ))
}

#[cfg(test)]
mod tests {
    use prove_decide::Limits;

    use super::*;
    use crate::pure::envir::empty_envir;
    use crate::pure::interrupt::with_limits;
    use crate::pure::testing::{attempt, check_problems, parse_term, show, show_envir};

    /// Pulls up to count unifiers, printing each, and then the interrupt checks the search made.
    fn solve(is_smash: bool, fields: &[&str]) -> Vec<String> {
        let count: usize = fields[0].parse().unwrap();
        let envir = empty_envir(fields[1].parse().unwrap());
        let pairs: Vec<Tpair> = fields[2..]
            .chunks(2)
            .map(|pair| (parse_term(pair[0]), parse_term(pair[1])))
            .collect();
        let mut lines = Vec::new();
        let limits = Limits::new(f64::INFINITY, None, None);
        with_limits(&limits, || {
            attempt(&mut lines, |lines| {
                let mut seq = if is_smash {
                    map_seq(
                        |envir| {
                            Ok(Unifier {
                                envir,
                                tpairs: Vec::new(),
                            })
                        },
                        smash_unifiers(&pairs, &envir)?,
                    )
                } else {
                    unifiers(&envir, &pairs)?
                };
                for index in 0.. {
                    if index == count {
                        lines.push("stop".into());
                        return Ok(());
                    }
                    let Some((unifier, rest)) = seq.pull()? else {
                        lines.push("end".into());
                        return Ok(());
                    };
                    lines.push(format!("unifier {index}"));
                    lines.extend(show_envir(&unifier.envir));
                    for (left, right) in &unifier.tpairs {
                        lines.push(format!("tpair {} =?= {}", show(left), show(right)));
                    }
                    for (left, right) in &pairs {
                        lines.push(format!("left {}", show(&norm_term(&unifier.envir, left)?)));
                        lines.push(format!(
                            "right {}",
                            show(&norm_term(&unifier.envir, right)?)
                        ));
                    }
                    seq = rest;
                }
                Ok(())
            });
        });
        lines.push(format!("steps {}", limits.steps()));
        lines
    }

    // The expectations are recorded from unify.ts (see pure/testing.rs).
    #[test]
    fn matches_the_typescript() {
        check_problems(
            include_str!("../../testdata/kernel/unify.txt"),
            |kind, fields| match kind {
                "unifiers" => solve(false, fields),
                "smash" => solve(true, fields),
                _ => panic!("unknown problem {kind}"),
            },
        );
    }
}
