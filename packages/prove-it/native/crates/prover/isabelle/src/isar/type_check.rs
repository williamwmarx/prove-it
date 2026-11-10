//! Ported from Isabelle2025's Pure/type_infer_context.ML, Pure/type_infer.ML (fixate) and the
//! abbreviation expansion of Pure/consts.ML. Copyright (c) 1986-2025 University of Cambridge,
//! Technische Universitaet Muenchen, and contributors, see LICENSE.
//!
//! Resolves the names of parsed propositions and infers their types together, as
//! Syntax.check_props does for the statement of a lemma: a free variable has one type across all
//! of them, and type parameters that stay open become the type variables 'a, 'b, and so on.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::error::{Res, error_exn};
use crate::isar::inner_syntax::Ast;
use crate::pure::interrupt::check_stack;
use crate::pure::name::bump_string;
use crate::pure::term::{
    Name, Term, TermNode, Typ, TypNode, betapplys, empty_sort, fold_atyps, fold_types, fun_t,
    map_types, mk_abs, mk_app, mk_bound, mk_const, mk_free, mk_tfree, mk_tvar, mk_type, strip_comb,
};
use crate::tla::logic::ConstInfo;

/// The name a type parameter carries until it is fixed, as Type_Infer.param does.
const PARAM_NAME: &str = "?'a";

pub struct NameScope {
    pub consts: HashMap<Name, ConstInfo>,
    /// The constant an unqualified name stands for.
    pub const_names: HashMap<Name, Name>,
}

pub struct PropToCheck {
    pub ast: Rc<Ast>,
    /// The variables fixed where the proposition appears.
    pub fixed: Rc<HashSet<Name>>,
}

struct Inference {
    substitution: HashMap<i32, Typ>,
    free_types: HashMap<Name, Typ>,
    next_param: i32,
}

fn fresh_param(inference: &mut Inference) -> Typ {
    let param = mk_tvar(PARAM_NAME, inference.next_param, empty_sort());
    inference.next_param += 1;
    param
}

/// The index of a type parameter, if the type is one.
fn param_index(ty: &Typ) -> Option<i32> {
    match &**ty {
        TypNode::TVar { name, index, .. } if &**name == PARAM_NAME => Some(*index),
        _ => None,
    }
}

fn resolve(inference: &Inference, ty: &Typ) -> Typ {
    match param_index(ty).and_then(|index| inference.substitution.get(&index)) {
        Some(bound) => resolve(inference, bound),
        None => ty.clone(),
    }
}

fn normalize(inference: &Inference, ty: &Typ) -> Typ {
    let resolved = resolve(inference, ty);
    match &*resolved {
        TypNode::Type { name, args, .. } => mk_type(
            name.clone(),
            args.iter().map(|arg| normalize(inference, arg)).collect(),
        ),
        _ => resolved,
    }
}

fn occurs(inference: &Inference, index: i32, ty: &Typ) -> bool {
    let resolved = resolve(inference, ty);
    if let Some(param) = param_index(&resolved) {
        return param == index;
    }
    match &*resolved {
        TypNode::Type { args, .. } => args.iter().any(|arg| occurs(inference, index, arg)),
        _ => false,
    }
}

fn unify(inference: &mut Inference, left: &Typ, right: &Typ) -> Res<()> {
    let resolved_left = resolve(inference, left);
    let resolved_right = resolve(inference, right);
    if let Some(left_index) = param_index(&resolved_left) {
        if param_index(&resolved_right) == Some(left_index) {
            return Ok(());
        }
        if occurs(inference, left_index, &resolved_right) {
            return Err(error_exn("Type unification failed: occurs check"));
        }
        inference.substitution.insert(left_index, resolved_right);
        return Ok(());
    }
    if param_index(&resolved_right).is_some() {
        return unify(inference, &resolved_right, &resolved_left);
    }
    match (&*resolved_left, &*resolved_right) {
        (
            TypNode::Type {
                name: left_name,
                args: left_args,
                ..
            },
            TypNode::Type {
                name: right_name,
                args: right_args,
                ..
            },
        ) if left_name == right_name => {
            for (arg, right_arg) in left_args.iter().zip(right_args) {
                unify(inference, arg, right_arg)?;
            }
            Ok(())
        }
        (
            TypNode::TFree {
                name: left_name, ..
            },
            TypNode::TFree {
                name: right_name, ..
            },
        ) if left_name == right_name => Ok(()),
        _ => Err(error_exn("Type unification failed")),
    }
}

/// The key of a type variable in a scheme: a TFree's name, or a TVar's `name.index`.
fn scheme_key(ty: &Typ) -> String {
    match &**ty {
        TypNode::TVar { name, index, .. } => format!("{name}.{index}"),
        TypNode::TFree { name, .. } => name.to_string(),
        TypNode::Type { .. } => unreachable!("a scheme key is of a type variable"),
    }
}

/// A constant's declared type with fresh parameters for its type variables.
fn instantiate_scheme(inference: &mut Inference, ty: &Typ) -> Typ {
    fn instantiate(
        inference: &mut Inference,
        params: &mut HashMap<String, Typ>,
        current: &Typ,
    ) -> Typ {
        if let TypNode::Type { name, args, .. } = &**current {
            return mk_type(
                name.clone(),
                args.iter()
                    .map(|arg| instantiate(inference, params, arg))
                    .collect(),
            );
        }
        let key = scheme_key(current);
        if let Some(known) = params.get(&key) {
            return known.clone();
        }
        let param = fresh_param(inference);
        params.insert(key, param.clone());
        param
    }
    instantiate(inference, &mut HashMap::new(), ty)
}

fn const_type(scope: &NameScope, name: &str) -> Res<Typ> {
    match scope.consts.get(name) {
        Some(info) => Ok(info.ty.clone()),
        None => Err(error_exn(format!("Undeclared constant: {name}"))),
    }
}

/// Builds the term with parameter types and infers its type, constraining the parameters.
fn elaborate(
    scope: &NameScope,
    inference: &mut Inference,
    fixed: &HashSet<Name>,
    bound: &[(Name, Typ)],
    ast: &Ast,
) -> Res<(Term, Typ)> {
    let _depth = check_stack()?;
    match ast {
        Ast::Name(name) => {
            if let Some(index) = bound.iter().position(|binder| binder.0 == *name) {
                let index_term = i32::try_from(index).expect("a binder index fits an i32");
                return Ok((mk_bound(index_term), bound[index].1.clone()));
            }
            let constant = if fixed.contains(name) {
                None
            } else {
                scope.const_names.get(name)
            };
            if let Some(constant) = constant {
                let ty = instantiate_scheme(inference, &const_type(scope, constant)?);
                return Ok((mk_const(constant.clone(), ty.clone()), ty));
            }
            let ty = match inference.free_types.get(name) {
                Some(known) => known.clone(),
                None => {
                    let ty = fresh_param(inference);
                    inference.free_types.insert(name.clone(), ty.clone());
                    ty
                }
            };
            Ok((mk_free(name.clone(), ty.clone()), ty))
        }
        Ast::Const(name) => {
            let ty = instantiate_scheme(inference, &const_type(scope, name)?);
            Ok((mk_const(name.clone(), ty.clone()), ty))
        }
        Ast::App { fun, arg } => {
            let (fun, fun_type) = elaborate(scope, inference, fixed, bound, fun)?;
            let (arg, arg_type) = elaborate(scope, inference, fixed, bound, arg)?;
            let result = fresh_param(inference);
            unify(inference, &fun_type, &fun_t(arg_type, result.clone()))?;
            Ok((mk_app(fun, arg), result))
        }
        Ast::Abs { name, ty, body } => {
            let ty = match ty {
                Some(ty) => ty.clone(),
                None => fresh_param(inference),
            };
            let inner = [vec![(name.clone(), ty.clone())], bound.to_vec()].concat();
            let (body, body_type) = elaborate(scope, inference, fixed, &inner, body)?;
            Ok((mk_abs(name.clone(), ty.clone(), body), fun_t(ty, body_type)))
        }
        Ast::Constrain { term, ty } => {
            let (term, term_type) = elaborate(scope, inference, fixed, bound, term)?;
            unify(inference, &term_type, ty)?;
            Ok((term, term_type))
        }
    }
}

fn match_scheme(pattern: &Typ, object: &Typ, instantiation: &mut HashMap<String, Typ>) {
    if let TypNode::Type { args, .. } = &**pattern {
        if let TypNode::Type {
            args: object_args, ..
        } = &**object
        {
            for (arg, object_arg) in args.iter().zip(object_args) {
                match_scheme(arg, object_arg, instantiation);
            }
        }
        return;
    }
    instantiation.insert(scheme_key(pattern), object.clone());
}

fn instantiate_matched(ty: &Typ, instantiation: &HashMap<String, Typ>) -> Typ {
    match &**ty {
        TypNode::Type { name, args, .. } => mk_type(
            name.clone(),
            args.iter()
                .map(|arg| instantiate_matched(arg, instantiation))
                .collect(),
        ),
        _ => instantiation
            .get(&scheme_key(ty))
            .cloned()
            .unwrap_or_else(|| ty.clone()),
    }
}

/// Consts.certify with normalize: unfolds abbreviations and applies them to their arguments.
fn expand_abbreviations(scope: &NameScope, term: &Term) -> Term {
    let (head, args) = strip_comb(term);
    let expanded_args: Vec<_> = args
        .iter()
        .map(|arg| expand_abbreviations(scope, arg))
        .collect();
    if let TermNode::Abs { name, ty, body, .. } = &*head {
        return betapplys(
            &mk_abs(name.clone(), ty.clone(), expand_abbreviations(scope, body)),
            &expanded_args,
        );
    }
    let TermNode::Const { name, ty } = &*head else {
        return betapplys(&head, &expanded_args);
    };
    let Some((info, abbreviation)) = scope
        .consts
        .get(name)
        .and_then(|info| Some((info, info.abbreviation.as_ref()?)))
    else {
        return betapplys(&head, &expanded_args);
    };
    let mut instantiation = HashMap::new();
    match_scheme(&info.ty, ty, &mut instantiation);
    betapplys(
        &map_types(
            &mut |ty| instantiate_matched(ty, &instantiation),
            abbreviation,
        ),
        &expanded_args,
    )
}

pub fn check_props(scope: &NameScope, props: &[PropToCheck]) -> Res<Vec<Term>> {
    let mut inference = Inference {
        substitution: HashMap::new(),
        free_types: HashMap::new(),
        next_param: 0,
    };
    let elaborated = props
        .iter()
        .map(|prop| {
            let (term, ty) = elaborate(scope, &mut inference, &prop.fixed, &[], &prop.ast)?;
            unify(&mut inference, &ty, &mk_type("prop", Vec::new()))?;
            Ok(term)
        })
        .collect::<Res<Vec<_>>>()?;
    let expanded: Vec<_> = elaborated
        .iter()
        .map(|term| {
            expand_abbreviations(scope, &map_types(&mut |ty| normalize(&inference, ty), term))
        })
        .collect();
    // Type_Infer.fixate: the parameters left open become type variables named in order of their
    // first appearance.
    let params = expanded.iter().fold(Vec::new(), |result, term| {
        fold_types(
            &mut |ty, state| {
                fold_atyps(
                    &mut |atom, mut current: Vec<i32>| {
                        if let Some(index) = param_index(atom)
                            && !current.contains(&index)
                        {
                            current.push(index);
                        }
                        current
                    },
                    ty,
                    state,
                )
            },
            term,
            result,
        )
    });
    let mut names = HashMap::new();
    params.iter().fold("'a".to_string(), |name, param| {
        let next = bump_string(&name);
        names.insert(*param, name);
        next
    });
    fn fix_type(names: &HashMap<i32, String>, ty: &Typ) -> Typ {
        if let TypNode::Type { name, args, .. } = &**ty {
            return mk_type(
                name.clone(),
                args.iter().map(|arg| fix_type(names, arg)).collect(),
            );
        }
        match param_index(ty) {
            Some(index) => mk_tfree(names.get(&index).map_or("'a", String::as_str), empty_sort()),
            None => ty.clone(),
        }
    }
    Ok(expanded
        .iter()
        .map(|term| map_types(&mut |ty| fix_type(&names, ty), term))
        .collect())
}
