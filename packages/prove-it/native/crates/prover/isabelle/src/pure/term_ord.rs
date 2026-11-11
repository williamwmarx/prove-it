//! Ported from Isabelle2025's Pure/term_ord.ML. Copyright (c) 1986-2025 University of Cambridge,
//! Technische Universitaet Muenchen, and contributors, see LICENSE.
//!
//! The TypeScript's orders return numbers whose callers only look at the sign, so these return
//! `Ordering`.

use std::cmp::Ordering;

use super::table::{IndexKey, fast_indexname_ord, fast_string_ord, indexname_ord};
use super::term::{Name, Sort, Term, TermNode, Typ, TypNode, dummy_t, size_of_term};

/// The first difference of the items at the same position, else the shorter list first.
fn dict_ord<Item>(
    ord: impl Fn(&Item, &Item) -> Ordering,
    left: &[Item],
    right: &[Item],
) -> Ordering {
    left.iter()
        .zip(right)
        .map(|(left_item, right_item)| ord(left_item, right_item))
        .find(|order| order.is_ne())
        .unwrap_or_else(|| left.len().cmp(&right.len()))
}

fn sort_ord(left: &Sort, right: &Sort) -> Ordering {
    dict_ord(fast_string_ord, left, right)
}

fn typ_cons_nr(ty: &Typ) -> i32 {
    match &**ty {
        TypNode::TVar { .. } => 0,
        TypNode::TFree { .. } => 1,
        TypNode::Type { .. } => 2,
    }
}

fn typ_ord(left: &Typ, right: &Typ) -> Ordering {
    if Typ::ptr_eq(left, right) {
        return Ordering::Equal;
    }
    match (&**left, &**right) {
        (
            TypNode::Type { name, args, .. },
            TypNode::Type {
                name: other,
                args: other_args,
                ..
            },
        ) => fast_string_ord(name, other).then_with(|| dict_ord(typ_ord, args, other_args)),
        (
            TypNode::TFree { name, sort },
            TypNode::TFree {
                name: other,
                sort: other_sort,
            },
        ) => fast_string_ord(name, other).then_with(|| sort_ord(sort, other_sort)),
        (
            TypNode::TVar { name, index, sort },
            TypNode::TVar {
                name: other,
                index: other_index,
                sort: other_sort,
            },
        ) => fast_indexname_ord(
            &IndexKey {
                name: name.clone(),
                index: *index,
            },
            &IndexKey {
                name: other.clone(),
                index: *other_index,
            },
        )
        .then_with(|| sort_ord(sort, other_sort)),
        _ => typ_cons_nr(left).cmp(&typ_cons_nr(right)),
    }
}

fn hd_depth(term: &Term) -> (&Term, usize) {
    let mut current = term;
    let mut depth = 0;
    while let TermNode::App { fun, .. } = &**current {
        current = fun;
        depth += 1;
    }
    (current, depth)
}

fn dest_hd(term: &Term) -> (IndexKey, Typ, i32) {
    let key = |name: &Name, index| IndexKey {
        name: name.clone(),
        index,
    };
    let unnamed = |index| IndexKey {
        name: "".into(),
        index,
    };
    match &**term {
        TermNode::Const { name, ty } => (key(name, 0), ty.clone(), 0),
        TermNode::Free { name, ty } => (key(name, 0), ty.clone(), 1),
        TermNode::Var { name, index, ty } => (key(name, *index), ty.clone(), 2),
        TermNode::Bound { index } => (unnamed(*index), dummy_t(), 3),
        TermNode::Abs { ty, .. } => (unnamed(0), ty.clone(), 4),
        TermNode::App { .. } => (unnamed(0), dummy_t(), 5),
    }
}

fn hd_ord(left: &Term, right: &Term) -> Ordering {
    let (left_name, left_type, left_nr) = dest_hd(left);
    let (right_name, right_type, right_nr) = dest_hd(right);
    indexname_ord(&left_name, &right_name)
        .then_with(|| typ_ord(&left_type, &right_type))
        .then_with(|| left_nr.cmp(&right_nr))
}

fn args_ord(left: &Term, right: &Term) -> Ordering {
    match (&**left, &**right) {
        (
            TermNode::App { fun, arg, .. },
            TermNode::App {
                fun: other_fun,
                arg: other_arg,
                ..
            },
        ) => args_ord(fun, other_fun).then_with(|| term_ord(arg, other_arg)),
        _ => Ordering::Equal,
    }
}

/// Term_Ord.term_ord: a linear well-founded AC-compatible order for ordered rewriting.
pub fn term_ord(left: &Term, right: &Term) -> Ordering {
    if Term::ptr_eq(left, right) {
        return Ordering::Equal;
    }
    if let (
        TermNode::Abs { body, ty, .. },
        TermNode::Abs {
            body: other_body,
            ty: other_ty,
            ..
        },
    ) = (&**left, &**right)
    {
        return term_ord(body, other_body).then_with(|| typ_ord(ty, other_ty));
    }
    size_of_term(left).cmp(&size_of_term(right)).then_with(|| {
        let (left_head, left_depth) = hd_depth(left);
        let (right_head, right_depth) = hd_depth(right);
        hd_ord(left_head, right_head)
            .then_with(|| left_depth.cmp(&right_depth))
            .then_with(|| args_ord(left, right))
    })
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::pure::term::{
        empty_sort, fun_t, fun_ts, mk_abs, mk_app, mk_bound, mk_const, mk_free, mk_tfree, mk_tvar,
        mk_type, mk_var,
    };

    /// Terms of every kind, shared with the tests of net.rs.
    pub(crate) fn sample_terms() -> Vec<Term> {
        let i = mk_type("i", Vec::new());
        let a = mk_tfree("'a", empty_sort());
        let c = mk_const("c", i.clone());
        let f = mk_const("f", fun_t(i.clone(), i.clone()));
        let g = mk_const("g", fun_ts(&[i.clone(), i.clone()], i.clone()));
        let x = mk_free("x", i.clone());
        let y = mk_var("y", 0, i.clone());
        let g2 = |left: &Term, right: Term| mk_app(mk_app(g.clone(), left.clone()), right);
        vec![
            c.clone(),
            mk_const("d", i.clone()),
            f.clone(),
            x.clone(),
            y.clone(),
            mk_var("y", 1, i.clone()),
            mk_app(f.clone(), c.clone()),
            mk_app(f.clone(), x),
            mk_app(f.clone(), y.clone()),
            g2(&c, c.clone()),
            mk_abs("x", i.clone(), mk_app(f.clone(), mk_bound(0))),
            mk_abs("x", a.clone(), mk_bound(0)),
            mk_bound(0),
            mk_app(f.clone(), mk_app(f, c.clone())),
            mk_const("c", a),
            mk_const("c", mk_tvar("'a", 0, empty_sort())),
            g2(&y, mk_bound(0)),
            g2(&c, mk_abs("z", i, c.clone())),
        ]
    }

    // Expected values from running term-ord.ts with bun on the same terms.
    #[test]
    fn orders_terms() {
        let expected = [
            "=<<<<<<<<<<<><>><<",
            ">=<<<<<<<<<<><>><<",
            ">>=<<<<<<<<<><>><<",
            ">>>=<<<<<<<<><>><<",
            ">>>>=<<<<<<<><>><<",
            ">>>>>=<<<<<<><>><<",
            ">>>>>>=<<<<>><>><<",
            ">>>>>>>=<<<>><>><<",
            ">>>>>>>>=<<>><>><<",
            ">>>>>>>>>=>>>>>><<",
            ">>>>>>>>><=>><>><<",
            ">>>>>><<<<<=><>><<",
            "<<<<<<<<<<<<=<<<<<",
            ">>>>>>>>><>>>=>><<",
            "<<<<<<<<<<<<><=><<",
            "<<<<<<<<<<<<><<=<<",
            ">>>>>>>>>>>>>>>>=<",
            ">>>>>>>>>>>>>>>>>=",
        ];
        let terms = sample_terms();
        let actual: Vec<String> = terms
            .iter()
            .map(|left| {
                terms
                    .iter()
                    .map(|right| match term_ord(left, right) {
                        Ordering::Less => '<',
                        Ordering::Equal => '=',
                        Ordering::Greater => '>',
                    })
                    .collect()
            })
            .collect();
        assert_eq!(actual, expected);
    }
}
