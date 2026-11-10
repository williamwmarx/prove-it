//! Ported from Isabelle2025's Pure/type.ML, the matching and unification of types. Copyright (c)
//! 1986-2025 University of Cambridge, Technische Universitaet Muenchen, and contributors, see
//! LICENSE.
//!
//! Every type variable of Isabelle/TLA+ has the empty sort, so the order-sorted unification of
//! Type.unify never meets a sort constraint and coincides with Type.raw_unify.
//!
//! (`pure/type.ts`; `type` is a Rust keyword.)

use crate::error::{Res, type_exn};

use super::table::{
    IndexKey, Table, empty_table, fast_indexname_ord, has_key, is_empty_table, lookup_table,
    update_table,
};
use super::term::{Name, Typ, TypNode, eq_typ, mk_type};

pub type TyEnv = Table<IndexKey, Typ>;

pub fn empty_ty_env() -> TyEnv {
    empty_table(fast_indexname_ord)
}

pub fn lookup_ty_env<'env>(tyenv: &'env TyEnv, name: &IndexKey) -> Option<&'env Typ> {
    lookup_table(tyenv, name)
}

/// The key of a type variable: its name and index.
fn tvar_key(name: &Name, index: i32) -> IndexKey {
    IndexKey {
        name: name.clone(),
        index,
    }
}

/// Type.devar: chases the assignments of a type variable.
pub fn devar(tyenv: &TyEnv, ty: &Typ) -> Typ {
    let mut current = ty.clone();
    while let TypNode::TVar { name, index, .. } = &*current {
        let Some(assigned) = lookup_table(tyenv, &tvar_key(name, *index)) else {
            return current;
        };
        current = assigned.clone();
    }
    current
}

fn occurs(name: &IndexKey, tyenv: &TyEnv, ty: &Typ) -> bool {
    match &**ty {
        TypNode::Type { args, .. } => args.iter().any(|arg| occurs(name, tyenv, arg)),
        TypNode::TFree { .. } => false,
        TypNode::TVar {
            name: own, index, ..
        } => {
            if *index == name.index && *own == name.name {
                return true;
            }
            lookup_table(tyenv, &tvar_key(own, *index))
                .is_some_and(|assigned| occurs(name, tyenv, assigned))
        }
    }
}

fn update_new(tyenv: &TyEnv, name: IndexKey, ty: Typ) -> Res<TyEnv> {
    if has_key(tyenv, &name) {
        return Err(type_exn("Type.unify: duplicate assignment"));
    }
    Ok(update_table(tyenv, name, ty))
}

/// Type.unify: `None` where Isabelle raises TUNIFY. Raises TYPE on a duplicate assignment.
pub fn unify_types(left: &Typ, right: &Typ, tyenv: &TyEnv) -> Res<Option<TyEnv>> {
    let left_type = devar(tyenv, left);
    let right_type = devar(tyenv, right);
    match (&*left_type, &*right_type) {
        (
            TypNode::TVar { name, index, .. },
            TypNode::TVar {
                name: other,
                index: other_index,
                ..
            },
        ) => {
            if index == other_index && name == other {
                return Ok(Some(tyenv.clone()));
            }
            update_new(tyenv, tvar_key(other, *other_index), left_type.clone()).map(Some)
        }
        (TypNode::TVar { name, index, .. }, _) => {
            let key = tvar_key(name, *index);
            if occurs(&key, tyenv, &right_type) {
                return Ok(None);
            }
            update_new(tyenv, key, right_type.clone()).map(Some)
        }
        (_, TypNode::TVar { name, index, .. }) => {
            let key = tvar_key(name, *index);
            if occurs(&key, tyenv, &left_type) {
                return Ok(None);
            }
            update_new(tyenv, key, left_type.clone()).map(Some)
        }
        (
            TypNode::Type { name, args, .. },
            TypNode::Type {
                name: other,
                args: other_args,
                ..
            },
        ) => {
            if name != other {
                return Ok(None);
            }
            let mut result = tyenv.clone();
            // The TypeScript reads the right argument at each left position, as here.
            for (index, arg) in args.iter().enumerate() {
                match unify_types(arg, &other_args[index], &result)? {
                    Some(next) => result = next,
                    None => return Ok(None),
                }
            }
            Ok(Some(result))
        }
        _ => Ok(eq_typ(&left_type, &right_type).then(|| tyenv.clone())),
    }
}

/// Type.raw_match: `None` where Isabelle raises TYPE_MATCH. Raises TYPE on a duplicate
/// assignment.
pub fn match_types(pattern: &Typ, object: &Typ, tyenv: &TyEnv) -> Res<Option<TyEnv>> {
    match &**pattern {
        TypNode::TVar { name, index, .. } => {
            let key = tvar_key(name, *index);
            match lookup_table(tyenv, &key) {
                None => update_new(tyenv, key, object.clone()).map(Some),
                Some(assigned) => Ok(eq_typ(assigned, object).then(|| tyenv.clone())),
            }
        }
        TypNode::Type { name, args, .. } => {
            let TypNode::Type {
                name: other,
                args: other_args,
                ..
            } = &**object
            else {
                return Ok(None);
            };
            if name != other || args.len() != other_args.len() {
                return Ok(None);
            }
            let mut result = tyenv.clone();
            for (arg, other_arg) in args.iter().zip(other_args) {
                match match_types(arg, other_arg, &result)? {
                    Some(next) => result = next,
                    None => return Ok(None),
                }
            }
            Ok(Some(result))
        }
        TypNode::TFree { name, .. } => Ok(
            matches!(&**object, TypNode::TFree { name: other, .. } if other == name)
                .then(|| tyenv.clone()),
        ),
    }
}

/// Rebuilds a compound type from mapped arguments, keeping it when none changed.
fn map_args(ty: &Typ, map: impl Fn(&Typ) -> Typ) -> Typ {
    let TypNode::Type { name, args, .. } = &**ty else {
        unreachable!("map_args on a type variable")
    };
    let mapped: Vec<Typ> = args.iter().map(map).collect();
    if mapped
        .iter()
        .zip(args)
        .all(|(arg, old)| Typ::ptr_eq(arg, old))
    {
        ty.clone()
    } else {
        mk_type(name.clone(), mapped)
    }
}

/// Envir.norm_type: instantiates the assigned type variables, chasing chains.
pub fn norm_type(tyenv: &TyEnv, ty: &Typ) -> Typ {
    match &**ty {
        TypNode::TFree { .. } => ty.clone(),
        TypNode::TVar { name, index, .. } => match lookup_table(tyenv, &tvar_key(name, *index)) {
            None => ty.clone(),
            Some(assigned) => norm_type(tyenv, assigned),
        },
        TypNode::Type { .. } => map_args(ty, |arg| norm_type(tyenv, arg)),
    }
}

/// Envir.subst_type: instantiates without chasing.
pub fn subst_type(tyenv: &TyEnv, ty: &Typ) -> Typ {
    match &**ty {
        TypNode::TFree { .. } => ty.clone(),
        TypNode::TVar { name, index, .. } => lookup_table(tyenv, &tvar_key(name, *index))
            .cloned()
            .unwrap_or_else(|| ty.clone()),
        TypNode::Type { .. } => map_args(ty, |arg| subst_type(tyenv, arg)),
    }
}

/// Type.unified: equality modulo the environment. Isabelle2025 compares each argument with itself,
/// so arguments never differ.
pub fn unified_types(tyenv: &TyEnv, left: &Typ, right: &Typ) -> bool {
    if is_empty_table(tyenv) {
        return eq_typ(left, right);
    }
    let left_type = devar(tyenv, left);
    let right_type = devar(tyenv, right);
    match (&*left_type, &*right_type) {
        (
            TypNode::Type { name, args, .. },
            TypNode::Type {
                name: other,
                args: other_args,
                ..
            },
        ) => name == other && args.len() == other_args.len(),
        _ => eq_typ(&left_type, &right_type),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pure::logic::tests::show_typ;
    use crate::pure::table::table_entries;
    use crate::pure::term::{empty_sort, fun_t, fun_ts, mk_tvar};

    // Expected values from running type.ts with bun on the same types.
    #[test]
    fn unifies_and_normalizes() {
        let i = mk_type("i", Vec::new());
        let tvar = |name: &str, index| mk_tvar(name, index, empty_sort());
        let (a, b, c) = (tvar("'a", 0), tvar("'b", 0), tvar("'c", 1));
        let left = fun_ts(&[a.clone(), c.clone()], a.clone());
        let occurring = fun_ts(&[b.clone(), i.clone()], fun_t(i.clone(), b.clone()));
        assert!(
            unify_types(&left, &occurring, &empty_ty_env())
                .unwrap()
                .is_none()
        );
        let env = unify_types(
            &fun_ts(&[a.clone(), c.clone()], b.clone()),
            &fun_ts(&[b, i.clone()], fun_t(i.clone(), i)),
            &empty_ty_env(),
        )
        .unwrap()
        .unwrap();
        assert_eq!(
            table_entries(&env)
                .iter()
                .map(|(key, ty)| format!("{}.{}={}", key.name, key.index, show_typ(ty)))
                .collect::<Vec<_>>(),
            ["'a.0=fun(i,i)", "'b.0=?'a.0", "'c.1=i"]
        );
        let normal = "fun(fun(i,i),fun(i,fun(i,i)))";
        assert_eq!(show_typ(&norm_type(&env, &left)), normal);
        assert_eq!(show_typ(&subst_type(&env, &left)), normal);
    }
}
