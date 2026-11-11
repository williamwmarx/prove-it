//! Ported from Isabelle2025's Pure/logic.ML, the abstract syntax of the meta logic. Copyright (c)
//! 1986-2025 University of Cambridge, Technische Universitaet Muenchen, and contributors, see
//! LICENSE.

use crate::error::{Res, term_exn};

use super::name::variant_list;
use super::term::{
    Name, Term, TermNode, Typ, TypNode, aconv, fastype_of, fun_t, fun_ts, incr_boundvars,
    map_atyps, may_occur, mk_abs, mk_app, mk_bound, mk_const, mk_free, mk_tvar, mk_var, prop_t,
};

/// Logic.occs: whether a subterm of other is aconv to term.
pub fn occs(term: &Term, other: &Term) -> bool {
    may_occur(term, other)
        && (aconv(term, other)
            || match &**other {
                TermNode::App { fun, arg, .. } => occs(term, fun) || occs(term, arg),
                TermNode::Abs { body, .. } => occs(term, body),
                _ => false,
            })
}

#[derive(Clone)]
pub struct Binder {
    pub name: Name,
    pub ty: Typ,
}

pub fn all_const(ty: Typ) -> Term {
    mk_const("Pure.all", fun_t(fun_t(ty, prop_t()), prop_t()))
}

pub fn list_all(vars: &[Binder], body: Term) -> Term {
    vars.iter().rev().fold(body, |result, variable| {
        mk_app(
            all_const(variable.ty.clone()),
            mk_abs(variable.name.clone(), variable.ty.clone(), result),
        )
    })
}

/// Raises TYPE where fastype_of does.
pub fn mk_equals(left: Term, right: Term) -> Res<Term> {
    let ty = fastype_of(&left)?;
    Ok(mk_app(
        mk_app(
            mk_const("Pure.eq", fun_ts(&[ty.clone(), ty], prop_t())),
            left,
        ),
        right,
    ))
}

/// The head and the two arguments of a term c $ x $ y for the constant c of that name.
fn dest_const_app2_head<'term>(
    term: &'term Term,
    name: &str,
) -> Option<(&'term Term, &'term Term, &'term Term)> {
    let (fun, right) = term.dest_app()?;
    let (head, left) = fun.dest_app()?;
    head.is_const_named(name).then_some((head, left, right))
}

/// The two arguments of a term c $ x $ y for the constant c of that name.
fn dest_const_app2<'term>(term: &'term Term, name: &str) -> Option<(&'term Term, &'term Term)> {
    dest_const_app2_head(term, name).map(|(_, left, right)| (left, right))
}

pub fn is_equals(term: &Term) -> bool {
    dest_const_app2(term, "Pure.eq").is_some()
}

pub fn dest_equals(term: &Term) -> Res<(Term, Term)> {
    dest_const_app2(term, "Pure.eq")
        .map(|(left, right)| (left.clone(), right.clone()))
        .ok_or_else(|| term_exn("dest_equals"))
}

pub fn implies() -> Term {
    thread_local!(static IMPLIES: Term = mk_const("Pure.imp", fun_ts(&[prop_t(), prop_t()], prop_t())));
    IMPLIES.with(Clone::clone)
}

pub fn mk_implies(premise: Term, conclusion: Term) -> Term {
    mk_app(mk_app(implies(), premise), conclusion)
}

pub fn is_implies(term: &Term) -> bool {
    dest_const_app2(term, "Pure.imp").is_some()
}

pub fn dest_implies(term: &Term) -> Res<(Term, Term)> {
    dest_const_app2(term, "Pure.imp")
        .map(|(premise, conclusion)| (premise.clone(), conclusion.clone()))
        .ok_or_else(|| term_exn("dest_implies"))
}

pub fn list_implies(premises: &[Term], conclusion: Term) -> Term {
    premises.iter().rev().fold(conclusion, |result, premise| {
        mk_implies(premise.clone(), result)
    })
}

pub fn strip_imp_prems(term: &Term) -> Vec<Term> {
    let mut premises = Vec::new();
    let mut current = term;
    while let Some((premise, conclusion)) = dest_const_app2(current, "Pure.imp") {
        premises.push(premise.clone());
        current = conclusion;
    }
    premises
}

pub fn strip_imp_concl(term: &Term) -> &Term {
    let mut current = term;
    while let Some((_, conclusion)) = dest_const_app2(current, "Pure.imp") {
        current = conclusion;
    }
    current
}

/// Logic.strip_prems: removes count premises, returning them reversed onto premises. Raises TERM
/// where fewer premises are left.
pub fn strip_prems(count: usize, premises: &[Term], term: &Term) -> Res<(Vec<Term>, Term)> {
    let mut stripped = premises.to_vec();
    let mut current = term;
    for _ in 0..count {
        let Some((premise, conclusion)) = dest_const_app2(current, "Pure.imp") else {
            return Err(term_exn("strip_prems"));
        };
        stripped.insert(0, premise.clone());
        current = conclusion;
    }
    Ok((stripped, current.clone()))
}

pub fn count_prems(term: &Term) -> usize {
    strip_imp_prems(term).len()
}

fn protect_const() -> Term {
    thread_local!(static PROTECT: Term = mk_const("Pure.prop", fun_t(prop_t(), prop_t())));
    PROTECT.with(Clone::clone)
}

pub fn protect(term: Term) -> Term {
    mk_app(protect_const(), term)
}

pub fn is_protected(term: &Term) -> bool {
    term.dest_app()
        .is_some_and(|(fun, _)| fun.is_const_named("Pure.prop"))
}

/// Raises TYPE where fastype_of does.
pub fn mk_term(term: Term) -> Res<Term> {
    Ok(mk_app(
        mk_const("Pure.term", fun_t(fastype_of(&term)?, prop_t())),
        term,
    ))
}

/// Logic.combound: term(Bound (start+count-1), ..., Bound start).
pub fn combound(term: Term, start: i32, count: usize) -> Term {
    if count > 0 {
        mk_app(combound(term, start + 1, count - 1), mk_bound(start))
    } else {
        term
    }
}

/// Logic.rlist_abs: ([xn, ..., x1], body) to %x1 ... xn. body.
pub fn rlist_abs(binders: &[Binder], body: Term) -> Term {
    binders.iter().fold(body, |result, binder| {
        mk_abs(binder.name.clone(), binder.ty.clone(), result)
    })
}

fn incr_tvar(increment: i32, ty: &Typ) -> Typ {
    if increment == 0 {
        return ty.clone();
    }
    map_atyps(
        &mut |atom| match &**atom {
            TypNode::TVar { name, index, sort } => {
                mk_tvar(name.clone(), index + increment, sort.clone())
            }
            _ => atom.clone(),
        },
        ty,
    )
}

/// Logic.incr_indexes_operation: lifts the variables over the types and increments their indexes.
fn incr_indexes_fixed(
    fixed: &[Name],
    types: &[Typ],
    increment: i32,
    level: i32,
    term: &Term,
) -> Term {
    if fixed.is_empty() && types.is_empty() && increment == 0 {
        return term.clone();
    }
    let count = types.len();
    fn incr(
        fixed: &[Name],
        types: &[Typ],
        increment: i32,
        count: usize,
        depth: i32,
        current: &Term,
    ) -> Term {
        match &**current {
            TermNode::Var { name, index, ty } => combound(
                mk_var(
                    name.clone(),
                    index + increment,
                    fun_ts(types, incr_tvar(increment, ty)),
                ),
                depth,
                count,
            ),
            TermNode::Free { name, ty } => {
                if fixed.contains(name) {
                    combound(
                        mk_free(name.clone(), fun_ts(types, incr_tvar(increment, ty))),
                        depth,
                        count,
                    )
                } else {
                    mk_free(name.clone(), incr_tvar(increment, ty))
                }
            }
            TermNode::Abs { name, ty, body, .. } => mk_abs(
                name.clone(),
                incr_tvar(increment, ty),
                incr(fixed, types, increment, count, depth + 1, body),
            ),
            TermNode::App { fun, arg, .. } => mk_app(
                incr(fixed, types, increment, count, depth, fun),
                incr(fixed, types, increment, count, depth, arg),
            ),
            TermNode::Const { name, ty } => mk_const(name.clone(), incr_tvar(increment, ty)),
            TermNode::Bound { .. } => current.clone(),
        }
    }
    incr(fixed, types, increment, count, level, term)
}

pub fn incr_indexes(types: &[Typ], increment: i32, term: &Term) -> Term {
    incr_indexes_fixed(&[], types, increment, 0, term)
}

/// The head, bound name, type and body of `Pure.all $ Abs …`.
fn dest_all_abs(term: &Term) -> Option<(&Term, &Name, &Typ, &Term)> {
    let (fun, arg) = term.dest_app()?;
    if !fun.is_const_named("Pure.all") {
        return None;
    }
    match &**arg {
        TermNode::Abs { name, ty, body, .. } => Some((fun, name, ty, body)),
        _ => None,
    }
}

/// Logic.lift_abs: lifts a term over the parameters of a goal.
pub fn lift_abs(increment: i32, goal: &Term, term: &Term) -> Term {
    fn lift(increment: i32, term: &Term, types: Vec<Typ>, current: &Term) -> Term {
        if let Some((_, conclusion)) = dest_const_app2(current, "Pure.imp") {
            return lift(increment, term, types, conclusion);
        }
        if let Some((_, name, ty, body)) = dest_all_abs(current) {
            return mk_abs(
                name.clone(),
                ty.clone(),
                lift(increment, term, [vec![ty.clone()], types].concat(), body),
            );
        }
        let reversed: Vec<Typ> = types.into_iter().rev().collect();
        incr_indexes(&reversed, increment, term)
    }
    lift(increment, term, Vec::new(), goal)
}

/// Logic.lift_all: lifts a proposition over the parameters and premises of a goal.
pub fn lift_all(increment: i32, goal: &Term, term: &Term) -> Term {
    fn lift(increment: i32, term: &Term, types: Vec<Typ>, current: &Term) -> Term {
        if let Some((head, premise, conclusion)) = dest_const_app2_head(current, "Pure.imp") {
            return mk_app(
                mk_app(head.clone(), premise.clone()),
                lift(increment, term, types, conclusion),
            );
        }
        if let Some((fun, name, ty, body)) = dest_all_abs(current) {
            return mk_app(
                fun.clone(),
                mk_abs(
                    name.clone(),
                    ty.clone(),
                    lift(increment, term, [vec![ty.clone()], types].concat(), body),
                ),
            );
        }
        let reversed: Vec<Typ> = types.into_iter().rev().collect();
        incr_indexes(&reversed, increment, term)
    }
    lift(increment, term, Vec::new(), goal)
}

pub fn strip_assums_hyp(term: &Term) -> Vec<Term> {
    let mut hyps: Vec<Term> = Vec::new();
    let mut current = term;
    loop {
        if let Some((premise, conclusion)) = dest_const_app2(current, "Pure.imp") {
            hyps.insert(0, premise.clone());
            current = conclusion;
        } else if let Some((_, _, _, body)) = dest_all_abs(current) {
            hyps = hyps.iter().map(|hyp| incr_boundvars(1, hyp)).collect();
            current = body;
        } else {
            hyps.reverse();
            return hyps;
        }
    }
}

pub fn strip_assums_concl(term: &Term) -> &Term {
    let mut current = term;
    loop {
        if let Some((_, conclusion)) = dest_const_app2(current, "Pure.imp") {
            current = conclusion;
        } else if let Some((_, _, _, body)) = dest_all_abs(current) {
            current = body;
        } else {
            return current;
        }
    }
}

pub fn strip_params(term: &Term) -> Vec<Binder> {
    let mut params = Vec::new();
    let mut current = term;
    loop {
        if let Some((_, conclusion)) = dest_const_app2(current, "Pure.imp") {
            current = conclusion;
        } else if let Some((_, name, ty, body)) = dest_all_abs(current) {
            params.push(Binder {
                name: name.clone(),
                ty: ty.clone(),
            });
            current = body;
        } else {
            return params;
        }
    }
}

fn is_meta(term: &Term) -> bool {
    dest_const_app2(term, "Pure.eq").is_some()
        || dest_const_app2(term, "Pure.imp").is_some()
        || term
            .dest_app()
            .is_some_and(|(fun, _)| fun.is_const_named("Pure.all"))
}

pub fn has_meta_prems(term: &Term) -> bool {
    if let Some((premise, conclusion)) = dest_const_app2(term, "Pure.imp") {
        return is_meta(premise) || has_meta_prems(conclusion);
    }
    if let Some((_, _, _, body)) = dest_all_abs(term) {
        return has_meta_prems(body);
    }
    false
}

/// Logic.remove_params: drops count parameters and premise number index. Raises TERM where the
/// premise is missing.
fn remove_params(count: i32, index: i32, term: &Term) -> Res<Term> {
    if count == 0 && index <= 0 {
        return Ok(term.clone());
    }
    if let Some((premise, conclusion)) = dest_const_app2(term, "Pure.imp") {
        return Ok(if index == 1 {
            remove_params(count, index - 1, conclusion)?
        } else {
            mk_implies(
                incr_boundvars(count, premise),
                remove_params(count, index - 1, conclusion)?,
            )
        });
    }
    if let Some((_, _, _, body)) = dest_all_abs(term) {
        return remove_params(count - 1, index, body);
    }
    if index > 0 {
        return Err(term_exn("remove_params"));
    }
    Ok(term.clone())
}

/// Logic.flatten_params: moves all parameters to the front, renaming them apart. Raises TERM where
/// premise number index is missing.
pub fn flatten_params(index: i32, term: &Term) -> Res<Term> {
    let params = strip_params(term);
    let names = variant_list(
        &[],
        &params
            .iter()
            .map(|param| param.name.clone())
            .collect::<Vec<_>>(),
    );
    let vars: Vec<Binder> = params
        .iter()
        .zip(names)
        .map(|(param, name)| Binder {
            name,
            ty: param.ty.clone(),
        })
        .collect();
    Ok(list_all(
        &vars,
        remove_params(vars.len() as i32, index, term)?,
    ))
}

/// Logic.strip_assums_imp: strips at most count premises. A negative count strips them all.
fn strip_assums_imp(count: i32, hyps: Vec<Term>, term: &Term) -> (Vec<Term>, Term) {
    let mut hyps = hyps;
    let mut count = count;
    let mut current = term;
    while count != 0 {
        let Some((premise, conclusion)) = dest_const_app2(current, "Pure.imp") else {
            break;
        };
        hyps.insert(0, premise.clone());
        current = conclusion;
        count -= 1;
    }
    (hyps, current.clone())
}

fn strip_assums_all(params: Vec<Binder>, term: &Term) -> (Vec<Binder>, Term) {
    let mut params = params;
    let mut current = term;
    while let Some((_, name, ty, body)) = dest_all_abs(current) {
        params.insert(
            0,
            Binder {
                name: name.clone(),
                ty: ty.clone(),
            },
        );
        current = body;
    }
    (params, current.clone())
}

pub struct AssumProblems {
    /// The parameters, innermost first, that `abstract_term` binds again.
    params: Vec<Binder>,
    pub hyps: Vec<Term>,
    pub conclusion: Term,
}

impl AssumProblems {
    /// The TypeScript's `abstract`: binds the goal's parameters over a term.
    pub fn abstract_term(&self, inner: Term) -> Term {
        rlist_abs(&self.params, inner)
    }
}

pub fn assum_problems(count: i32, term: &Term) -> AssumProblems {
    let (params, body) = strip_assums_all(Vec::new(), term);
    let (mut hyps, conclusion) = strip_assums_imp(count, Vec::new(), &body);
    hyps.reverse();
    AssumProblems {
        params,
        hyps,
        conclusion,
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::error::Exception;
    use crate::pure::term::{empty_sort, mk_tfree, mk_type};

    /// The printing of the TypeScript script that computed the expected values.
    pub(crate) fn show_typ(ty: &Typ) -> String {
        match &**ty {
            TypNode::Type { name, args, .. } if args.is_empty() => name.to_string(),
            TypNode::Type { name, args, .. } => format!(
                "{name}({})",
                args.iter().map(show_typ).collect::<Vec<_>>().join(",")
            ),
            TypNode::TFree { name, .. } => name.to_string(),
            TypNode::TVar { name, index, .. } => format!("?{name}.{index}"),
        }
    }

    pub(crate) fn show(term: &Term) -> String {
        match &**term {
            TermNode::Const { name, ty } => format!("{name}::{}", show_typ(ty)),
            TermNode::Free { name, ty } => format!("{name}:{}", show_typ(ty)),
            TermNode::Var { name, index, ty } => format!("?{name}.{index}:{}", show_typ(ty)),
            TermNode::Bound { index } => format!("B{index}"),
            TermNode::Abs { name, ty, body, .. } => {
                format!("(%{name}:{}. {})", show_typ(ty), show(body))
            }
            TermNode::App { fun, arg, .. } => format!("({} {})", show(fun), show(arg)),
        }
    }

    const ALL_I: &str = "Pure.all::fun(fun(i,prop),prop)";
    const ALL_A: &str = "Pure.all::fun(fun('a,prop),prop)";
    const IMP: &str = "Pure.imp::fun(prop,fun(prop,prop))";
    const Q_B0_B1: &str = "((Q::fun('a,fun(i,prop)) B0) B1)";

    /// !!x::i. P x ==> (!!x::'a. Q x x' ==> R x'), and P ?v ==> R (k ?w).
    fn goal_and_term() -> (Term, Term) {
        let i = mk_type("i", Vec::new());
        let a = mk_tfree("'a", empty_sort());
        let b = mk_tvar("'b", 0, empty_sort());
        let p = mk_const("P", fun_t(i.clone(), prop_t()));
        let q = mk_const("Q", fun_ts(&[a.clone(), i.clone()], prop_t()));
        let r = mk_const("R", fun_t(i.clone(), prop_t()));
        let all = |name: &str, ty: &Typ, body| {
            mk_app(all_const(ty.clone()), mk_abs(name, ty.clone(), body))
        };
        let goal = all(
            "x",
            &i,
            mk_implies(
                mk_app(p.clone(), mk_bound(0)),
                all(
                    "x",
                    &a,
                    mk_implies(
                        mk_app(mk_app(q, mk_bound(0)), mk_bound(1)),
                        mk_app(r.clone(), mk_bound(1)),
                    ),
                ),
            ),
        );
        let k = mk_const("k", fun_t(b.clone(), i.clone()));
        let term = mk_implies(
            mk_app(p, mk_var("v", 0, i)),
            mk_app(r, mk_app(k, mk_var("w", 2, b))),
        );
        (goal, term)
    }

    // Expected values from running logic.ts with bun on the same terms.
    #[test]
    fn lifts_over_a_goal() {
        let (goal, term) = goal_and_term();
        let lifted = format!(
            "(({IMP} (P::fun(i,prop) ((?v.3:fun(i,fun('a,i)) B1) B0))) (R::fun(i,prop) (k::fun(?'b.3,i) ((?w.5:fun(i,fun('a,?'b.3)) B1) B0))))"
        );
        assert_eq!(
            show(&lift_all(3, &goal, &term)),
            format!(
                "({ALL_I} (%x:i. (({IMP} (P::fun(i,prop) B0)) ({ALL_A} (%x:'a. (({IMP} {Q_B0_B1}) {lifted}))))))"
            )
        );
        assert_eq!(
            show(&lift_abs(3, &goal, &term)),
            format!("(%x:i. (%x:'a. {lifted}))")
        );
    }

    #[test]
    fn strips_and_flattens() {
        let (goal, _) = goal_and_term();
        assert_eq!(
            strip_assums_hyp(&goal).iter().map(show).collect::<Vec<_>>(),
            ["(P::fun(i,prop) B1)", Q_B0_B1]
        );
        let flattened = |premise: &str| {
            format!("({ALL_I} (%x:i. ({ALL_A} (%xa:'a. (({IMP} {premise}) (R::fun(i,prop) B1))))))")
        };
        assert_eq!(show(&flatten_params(1, &goal).unwrap()), flattened(Q_B0_B1));
        assert_eq!(
            show(&flatten_params(2, &goal).unwrap()),
            flattened("(P::fun(i,prop) B1)")
        );
        assert!(
            flatten_params(3, &goal)
                .is_err_and(|error| error == term_exn("remove_params") && error.is(Exception::Term))
        );
        for count in [-1, 1] {
            let problems = assum_problems(count, &goal);
            assert_eq!(
                show(&problems.abstract_term(problems.conclusion.clone())),
                format!("(%x:i. ({ALL_A} (%x:'a. (({IMP} {Q_B0_B1}) (R::fun(i,prop) B1)))))")
            );
            assert_eq!(
                problems.hyps.iter().map(show).collect::<Vec<_>>(),
                ["(P::fun(i,prop) B0)"]
            );
        }
    }
}
