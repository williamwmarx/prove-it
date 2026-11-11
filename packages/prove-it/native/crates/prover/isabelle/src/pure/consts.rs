//! Ported from Isabelle2025's Pure/consts.ML. Copyright (c) 1986-2025 University of Cambridge,
//! Technische Universitaet Muenchen, and contributors, see LICENSE.
//!
//! A constant's type arguments: the instances of the type variables of its declared type, which
//! Consts.declare locates once so that Consts.typargs only has to look them up.

use crate::error::{Res, type_exn};

use super::table::IndexKey;
use super::term::{Typ, TypNode};

/// The argument positions leading from a type to one of its subtypes.
pub type TypargPosition = Vec<usize>;

/// Consts.typargs_of: the path to the first occurrence of each type variable.
pub fn typargs_of(ty: &Typ) -> Vec<TypargPosition> {
    // The type variables in order of first occurrence, with their paths.
    fn visit(current: &Typ, path: &mut Vec<usize>, found: &mut Vec<(IndexKey, TypargPosition)>) {
        match &**current {
            TypNode::Type { args, .. } => {
                for (index, arg) in args.iter().enumerate() {
                    path.push(index);
                    visit(arg, path, found);
                    path.pop();
                }
            }
            TypNode::TVar { name, index, .. } => {
                if !found
                    .iter()
                    .any(|(key, _)| key.index == *index && key.name == *name)
                {
                    let key = IndexKey {
                        name: name.clone(),
                        index: *index,
                    };
                    found.push((key, path.clone()));
                }
            }
            TypNode::TFree { .. } => {}
        }
    }
    let mut found = Vec::new();
    visit(ty, &mut Vec::new(), &mut found);
    found.into_iter().map(|(_, path)| path).collect()
}

/// Consts.typargs: the type arguments of a constant at an instance of its declared type.
/// Raises TYPE where a position leaves the type.
pub fn typargs(positions: &[TypargPosition], ty: &Typ) -> Res<Vec<Typ>> {
    positions
        .iter()
        .map(|path| {
            path.iter()
                .try_fold(ty.clone(), |current, index| match &*current {
                    TypNode::Type { args, .. } if *index < args.len() => Ok(args[*index].clone()),
                    _ => Err(type_exn("Consts.typargs: subscript")),
                })
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::error::{Exception, type_exn};
    use crate::pure::logic::tests::show_typ;
    use crate::pure::term::{empty_sort, fun_t, fun_ts, mk_tfree, mk_tvar, mk_type, prop_t};

    // Expected values from running consts.ts with bun on the same types.
    #[test]
    fn locates_type_arguments() {
        let i = mk_type("i", Vec::new());
        let tvar = |name: &str, index| mk_tvar(name, index, empty_sort());
        let (a, c) = (tvar("'a", 0), tvar("'c", 1));
        let declared = fun_ts(&[a.clone(), mk_type("set", vec![c]), a], tvar("'b", 0));
        let positions = typargs_of(&declared);
        assert_eq!(positions, [vec![0], vec![1, 0, 0], vec![1, 1, 1]]);
        let instance = fun_ts(
            &[
                i.clone(),
                mk_type("set", vec![mk_tfree("'a", empty_sort())]),
                i.clone(),
            ],
            prop_t(),
        );
        assert_eq!(
            typargs(&positions, &instance)
                .unwrap()
                .iter()
                .map(show_typ)
                .collect::<Vec<_>>(),
            ["i", "'a", "prop"]
        );
        let error = typargs(&positions, &fun_t(i.clone(), i)).err();
        assert!(
            error
                .as_ref()
                .is_some_and(|error| error.is(Exception::Type))
        );
        assert_eq!(error, Some(type_exn("Consts.typargs: subscript")));
    }
}
