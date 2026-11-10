//! Ported from Isabelle2025's Pure/term.ML. Copyright (c) 1986-2025 University of Cambridge,
//! Technische Universitaet Muenchen, and contributors, see LICENSE.
//!
//! Simply typed lambda terms with de Bruijn indices (`pure/term.ts`). Functions that rebuild a
//! term return the very same `Rc` when nothing changes, as Isabelle's Same.SAME does, so pointer
//! equality (`Term::ptr_eq`) stays a fast path. Neither `Term` nor `Typ` implements `PartialEq`:
//! a comparison says which one it means, `ptr_eq` (the TypeScript's `===`), `aconv`, `eq_term` or
//! `eq_typ`.
//!
//! Unlike Isabelle, applications, abstractions and compound types record what their subterms
//! contain when built: the largest index (maxidx), a bound above every loose bound variable (loose),
//! whether a schematic variable, a beta redex or an eta redex occurs, and a bit for the name of each
//! free variable (flags). A term has every flag of its subterms. Traversals use this to skip
//! subterms they would return unchanged, which gives the same results while touching only the parts
//! that change.
//!
//! Names are ASCII (decide declines other input), so comparing them by bytes compares them by
//! UTF-16 code units, as JavaScript does, and their byte length is their JavaScript length.

use std::ops::Deref;
use std::rc::Rc;

use crate::error::{Res, type_exn};

pub type Name = Rc<str>;

pub type Sort = Rc<[Name]>;

pub enum TypNode {
    Type {
        name: Name,
        args: Vec<Typ>,
        maxidx: i32,
    },
    TFree {
        name: Name,
        sort: Sort,
    },
    TVar {
        name: Name,
        index: i32,
        sort: Sort,
    },
}

#[derive(Clone)]
pub struct Typ(Rc<TypNode>);

impl Deref for Typ {
    type Target = TypNode;
    fn deref(&self) -> &TypNode {
        &self.0
    }
}

impl Typ {
    /// The TypeScript's `===` on types.
    pub fn ptr_eq(left: &Typ, right: &Typ) -> bool {
        Rc::ptr_eq(&left.0, &right.0)
    }

    /// The name of any kind of type.
    pub fn name(&self) -> &Name {
        match &**self {
            TypNode::Type { name, .. }
            | TypNode::TFree { name, .. }
            | TypNode::TVar { name, .. } => name,
        }
    }

    pub fn is_fun(&self) -> bool {
        matches!(&**self, TypNode::Type { name, .. } if &**name == "fun")
    }

    /// The domain and range of a function type.
    pub fn dest_fun(&self) -> Option<(&Typ, &Typ)> {
        match &**self {
            TypNode::Type { name, args, .. } if &**name == "fun" && args.len() == 2 => {
                Some((&args[0], &args[1]))
            }
            _ => None,
        }
    }
}

pub enum TermNode {
    Const {
        name: Name,
        ty: Typ,
    },
    Free {
        name: Name,
        ty: Typ,
    },
    Var {
        name: Name,
        index: i32,
        ty: Typ,
    },
    Bound {
        index: i32,
    },
    Abs {
        name: Name,
        ty: Typ,
        body: Term,
        loose: i32,
        maxidx: i32,
        flags: u32,
    },
    App {
        fun: Term,
        arg: Term,
        loose: i32,
        maxidx: i32,
        flags: u32,
    },
}

#[derive(Clone)]
pub struct Term(Rc<TermNode>);

/// A term known to be a `Var`, as the TypeScript's `Var` type.
pub type Var = Term;

impl Deref for Term {
    type Target = TermNode;
    fn deref(&self) -> &TermNode {
        &self.0
    }
}

impl Term {
    /// The TypeScript's `===` on terms.
    pub fn ptr_eq(left: &Term, right: &Term) -> bool {
        Rc::ptr_eq(&left.0, &right.0)
    }

    /// An address that identifies the term while it is alive, for caches keyed by identity. A
    /// cache that keys by it must keep the term alive, so that the address isn't reused.
    pub fn address(&self) -> usize {
        Rc::as_ptr(&self.0) as *const () as usize
    }

    pub fn is_const(&self) -> bool {
        matches!(&**self, TermNode::Const { .. })
    }
    pub fn is_free(&self) -> bool {
        matches!(&**self, TermNode::Free { .. })
    }
    pub fn is_var(&self) -> bool {
        matches!(&**self, TermNode::Var { .. })
    }
    pub fn is_bound(&self) -> bool {
        matches!(&**self, TermNode::Bound { .. })
    }
    pub fn is_abs(&self) -> bool {
        matches!(&**self, TermNode::Abs { .. })
    }
    pub fn is_app(&self) -> bool {
        matches!(&**self, TermNode::App { .. })
    }

    /// Whether this is the constant of that name.
    pub fn is_const_named(&self, constant: &str) -> bool {
        matches!(&**self, TermNode::Const { name, .. } if &**name == constant)
    }

    /// The name of a Const, Free, Var or Abs.
    pub fn name(&self) -> Option<&Name> {
        match &**self {
            TermNode::Const { name, .. }
            | TermNode::Free { name, .. }
            | TermNode::Var { name, .. }
            | TermNode::Abs { name, .. } => Some(name),
            _ => None,
        }
    }

    /// The type of a Const, Free, Var or Abs.
    pub fn ty(&self) -> Option<&Typ> {
        match &**self {
            TermNode::Const { ty, .. }
            | TermNode::Free { ty, .. }
            | TermNode::Var { ty, .. }
            | TermNode::Abs { ty, .. } => Some(ty),
            _ => None,
        }
    }

    /// The index of a Var or a Bound.
    pub fn index(&self) -> Option<i32> {
        match &**self {
            TermNode::Var { index, .. } | TermNode::Bound { index } => Some(*index),
            _ => None,
        }
    }

    /// The function and argument of an application.
    pub fn dest_app(&self) -> Option<(&Term, &Term)> {
        match &**self {
            TermNode::App { fun, arg, .. } => Some((fun, arg)),
            _ => None,
        }
    }

    /// The body of an abstraction.
    pub fn abs_body(&self) -> Option<&Term> {
        match &**self {
            TermNode::Abs { body, .. } => Some(body),
            _ => None,
        }
    }
}

pub const HAS_VAR: u32 = 1;
pub const HAS_REDEX: u32 = 2;
pub const HAS_ETA_REDEX: u32 = 4;

pub fn maxidx_of_typ(ty: &Typ, maxidx: i32) -> i32 {
    maxidx.max(match &**ty {
        TypNode::TFree { .. } => -1,
        TypNode::TVar { index, .. } => *index,
        TypNode::Type { maxidx, .. } => *maxidx,
    })
}

pub fn maxidx_of_term(term: &Term, maxidx: i32) -> i32 {
    match &**term {
        TermNode::Var { index, ty, .. } => maxidx.max(*index).max(maxidx_of_typ(ty, -1)),
        TermNode::Const { ty, .. } | TermNode::Free { ty, .. } => maxidx_of_typ(ty, maxidx),
        TermNode::Bound { .. } => maxidx,
        TermNode::Abs { maxidx: own, .. } | TermNode::App { maxidx: own, .. } => maxidx.max(*own),
    }
}

/// The bound on loose bound variables: every one is below it.
pub fn loose_of(term: &Term) -> i32 {
    match &**term {
        TermNode::Bound { index } => index + 1,
        TermNode::App { loose, .. } | TermNode::Abs { loose, .. } => *loose,
        _ => 0,
    }
}

/// One of the 28 bits above the others, picked by a cheap hash of the name.
fn free_bit(name: &str) -> u32 {
    let bytes = name.as_bytes();
    let first = bytes.first().copied().unwrap_or(0) as u64;
    let last = bytes.last().copied().unwrap_or(0) as u64;
    8 << ((bytes.len() as u64 * 31 + first * 7 + last) % 28)
}

pub fn flags_of(term: &Term) -> u32 {
    match &**term {
        TermNode::Var { .. } => HAS_VAR,
        TermNode::Free { name, .. } => free_bit(name),
        TermNode::App { flags, .. } | TermNode::Abs { flags, .. } => *flags,
        _ => 0,
    }
}

/// Whether a subterm aconv to pattern could occur in term.
pub fn may_occur(pattern: &Term, term: &Term) -> bool {
    flags_of(pattern) & !flags_of(term) == 0
}

pub fn mk_type(name: impl Into<Name>, args: Vec<Typ>) -> Typ {
    let maxidx = args
        .iter()
        .fold(-1, |result, arg| maxidx_of_typ(arg, result));
    Typ(Rc::new(TypNode::Type {
        name: name.into(),
        args,
        maxidx,
    }))
}

pub fn mk_tfree(name: impl Into<Name>, sort: Sort) -> Typ {
    Typ(Rc::new(TypNode::TFree {
        name: name.into(),
        sort,
    }))
}

pub fn mk_tvar(name: impl Into<Name>, index: i32, sort: Sort) -> Typ {
    Typ(Rc::new(TypNode::TVar {
        name: name.into(),
        index,
        sort,
    }))
}

/// The empty sort, which every type variable of Isabelle/TLA+ has.
pub fn empty_sort() -> Sort {
    thread_local!(static EMPTY: Sort = Rc::from(Vec::<Name>::new()));
    EMPTY.with(Clone::clone)
}

pub fn mk_const(name: impl Into<Name>, ty: Typ) -> Term {
    Term(Rc::new(TermNode::Const {
        name: name.into(),
        ty,
    }))
}

pub fn mk_free(name: impl Into<Name>, ty: Typ) -> Term {
    Term(Rc::new(TermNode::Free {
        name: name.into(),
        ty,
    }))
}

pub fn mk_var(name: impl Into<Name>, index: i32, ty: Typ) -> Var {
    Term(Rc::new(TermNode::Var {
        name: name.into(),
        index,
        ty,
    }))
}

pub fn mk_bound(index: i32) -> Term {
    Term(Rc::new(TermNode::Bound { index }))
}

pub fn mk_abs(name: impl Into<Name>, ty: Typ, body: Term) -> Term {
    let is_eta = matches!(&*body, TermNode::App { arg, .. } if matches!(&**arg, TermNode::Bound { index: 0 }));
    Term(Rc::new(TermNode::Abs {
        name: name.into(),
        loose: (loose_of(&body) - 1).max(0),
        maxidx: maxidx_of_term(&body, maxidx_of_typ(&ty, -1)),
        flags: flags_of(&body) | if is_eta { HAS_ETA_REDEX } else { 0 },
        ty,
        body,
    }))
}

pub fn mk_app(fun: Term, arg: Term) -> Term {
    Term(Rc::new(TermNode::App {
        loose: loose_of(&fun).max(loose_of(&arg)),
        maxidx: maxidx_of_term(&arg, maxidx_of_term(&fun, -1)),
        flags: flags_of(&fun) | flags_of(&arg) | if fun.is_abs() { HAS_REDEX } else { 0 },
        fun,
        arg,
    }))
}

pub fn dummy_t() -> Typ {
    thread_local!(static DUMMY: Typ = mk_type("dummy", Vec::new()));
    DUMMY.with(Clone::clone)
}

pub fn prop_t() -> Typ {
    thread_local!(static PROP: Typ = mk_type("prop", Vec::new()));
    PROP.with(Clone::clone)
}

pub fn fun_t(domain: Typ, range: Typ) -> Typ {
    mk_type("fun", vec![domain, range])
}

/// op --->
pub fn fun_ts(domains: &[Typ], range: Typ) -> Typ {
    domains
        .iter()
        .rev()
        .fold(range, |result, domain| fun_t(domain.clone(), result))
}

pub fn binder_types(ty: &Typ) -> Vec<Typ> {
    let mut types = Vec::new();
    let mut current = ty;
    while let Some((domain, range)) = current.dest_fun() {
        types.push(domain.clone());
        current = range;
    }
    types
}

pub fn body_type(ty: &Typ) -> Typ {
    let mut current = ty;
    while let Some((_, range)) = current.dest_fun() {
        current = range;
    }
    current.clone()
}

pub fn eq_sort(left: &Sort, right: &Sort) -> bool {
    Rc::ptr_eq(left, right) || left[..] == right[..]
}

pub fn eq_typ(left: &Typ, right: &Typ) -> bool {
    if Typ::ptr_eq(left, right) {
        return true;
    }
    match (&**left, &**right) {
        (
            TypNode::Type { name, args, .. },
            TypNode::Type {
                name: other,
                args: other_args,
                ..
            },
        ) => {
            name == other
                && args.len() == other_args.len()
                && args
                    .iter()
                    .zip(other_args)
                    .all(|(arg, other)| eq_typ(arg, other))
        }
        (
            TypNode::TFree { name, sort },
            TypNode::TFree {
                name: other,
                sort: other_sort,
            },
        ) => name == other && eq_sort(sort, other_sort),
        (
            TypNode::TVar { name, index, sort },
            TypNode::TVar {
                name: other,
                index: other_index,
                sort: other_sort,
            },
        ) => name == other && index == other_index && eq_sort(sort, other_sort),
        _ => false,
    }
}

/// fastype_of1: the type of a term, with minimal checking. Types holds the types of the loose
/// bound variables, innermost first.
pub fn fastype_of1(types: &[Typ], term: &Term) -> Res<Typ> {
    // The binders entered below, innermost last, in front of types.
    fn go(types: &[Typ], inner: &mut Vec<Typ>, term: &Term) -> Res<Typ> {
        match &**term {
            TermNode::Const { ty, .. } | TermNode::Free { ty, .. } | TermNode::Var { ty, .. } => {
                Ok(ty.clone())
            }
            TermNode::Bound { index } => {
                let index = *index as usize;
                let found = if index < inner.len() {
                    inner.get(inner.len() - 1 - index)
                } else {
                    types.get(index - inner.len())
                };
                found.cloned().ok_or_else(|| type_exn("fastype_of: Bound"))
            }
            TermNode::Abs { ty, body, .. } => {
                inner.push(ty.clone());
                let range = go(types, inner, body);
                inner.pop();
                Ok(fun_t(ty.clone(), range?))
            }
            TermNode::App { fun, .. } => {
                let ty = go(types, inner, fun)?;
                match ty.dest_fun() {
                    Some((_, range)) => Ok(range.clone()),
                    None => Err(type_exn("fastype_of: expected function type")),
                }
            }
        }
    }
    go(types, &mut Vec::new(), term)
}

pub fn fastype_of(term: &Term) -> Res<Typ> {
    fastype_of1(&[], term)
}

pub fn list_comb(head: Term, args: &[Term]) -> Term {
    args.iter()
        .fold(head, |result, arg| mk_app(result, arg.clone()))
}

pub fn strip_comb(term: &Term) -> (Term, Vec<Term>) {
    let mut args = Vec::new();
    let mut current = term;
    while let TermNode::App { fun, arg, .. } = &**current {
        args.push(arg.clone());
        current = fun;
    }
    args.reverse();
    (current.clone(), args)
}

pub fn head_of(term: &Term) -> &Term {
    let mut current = term;
    while let TermNode::App { fun, .. } = &**current {
        current = fun;
    }
    current
}

pub fn strip_abs_body(term: &Term) -> &Term {
    let mut current = term;
    while let TermNode::Abs { body, .. } = &**current {
        current = body;
    }
    current
}

pub fn size_of_term(term: &Term) -> usize {
    match &**term {
        TermNode::Abs { body, .. } => 1 + size_of_term(body),
        TermNode::App { fun, arg, .. } => size_of_term(fun) + size_of_term(arg),
        _ => 1,
    }
}

/// The bound variable and body of `Pure.all (Abs …)`.
fn dest_all_abs(term: &Term) -> Option<(&Name, &Typ, &Term)> {
    let (fun, arg) = term.dest_app()?;
    if !fun.is_const_named("Pure.all") {
        return None;
    }
    match &**arg {
        TermNode::Abs { name, ty, body, .. } => Some((name, ty, body)),
        _ => None,
    }
}

pub fn strip_all_body(term: &Term) -> &Term {
    let mut current = term;
    while let Some((_, _, body)) = dest_all_abs(current) {
        current = body;
    }
    current
}

pub fn strip_all_vars(term: &Term) -> Vec<(Name, Typ)> {
    let mut vars = Vec::new();
    let mut current = term;
    while let Some((name, ty, body)) = dest_all_abs(current) {
        vars.push((name.clone(), ty.clone()));
        current = body;
    }
    vars
}

/// Rebuilds an application, keeping the original term when neither part changed. `term` must be
/// an App.
pub fn update_app(term: &Term, fun: Term, arg: Term) -> Term {
    match &**term {
        TermNode::App {
            fun: old_fun,
            arg: old_arg,
            ..
        } if Term::ptr_eq(&fun, old_fun) && Term::ptr_eq(&arg, old_arg) => term.clone(),
        _ => mk_app(fun, arg),
    }
}

/// Rebuilds an abstraction with a new body, and a new type if given, keeping the original term
/// when neither changed. `term` must be an Abs.
pub fn update_abs(term: &Term, body: Term, ty: Option<Typ>) -> Term {
    let TermNode::Abs {
        name,
        ty: old_ty,
        body: old_body,
        ..
    } = &**term
    else {
        unreachable!("update_abs on a term that isn't an abstraction")
    };
    let ty = ty.unwrap_or_else(|| old_ty.clone());
    if Term::ptr_eq(&body, old_body) && Typ::ptr_eq(&ty, old_ty) {
        return term.clone();
    }
    mk_abs(name.clone(), ty, body)
}

/// incr_bv: increments the bound variables at or above level by increment.
fn incr_bv_at(increment: i32, level: i32, term: &Term) -> Term {
    if loose_of(term) <= level {
        return term.clone();
    }
    match &**term {
        TermNode::Bound { index } => mk_bound(index + increment),
        TermNode::Abs { body, .. } => {
            update_abs(term, incr_bv_at(increment, level + 1, body), None)
        }
        TermNode::App { fun, arg, .. } => update_app(
            term,
            incr_bv_at(increment, level, fun),
            incr_bv_at(increment, level, arg),
        ),
        _ => term.clone(),
    }
}

pub fn incr_bv(increment: i32, level: i32, term: &Term) -> Term {
    if increment == 0 {
        term.clone()
    } else {
        incr_bv_at(increment, level, term)
    }
}

pub fn incr_boundvars(increment: i32, term: &Term) -> Term {
    incr_bv(increment, 0, term)
}

/// loose_bvar: whether term has a loose bound variable at level or beyond.
pub fn loose_bvar(term: &Term, level: i32) -> bool {
    loose_of(term) > level
}

pub fn loose_bvar1(term: &Term, level: i32) -> bool {
    if loose_of(term) <= level {
        return false;
    }
    match &**term {
        TermNode::Bound { index } => *index == level,
        TermNode::App { fun, arg, .. } => loose_bvar1(fun, level) || loose_bvar1(arg, level),
        TermNode::Abs { body, .. } => loose_bvar1(body, level + 1),
        _ => false,
    }
}

pub fn is_open(term: &Term) -> bool {
    loose_bvar(term, 0)
}

pub fn is_dependent(term: &Term) -> bool {
    loose_bvar1(term, 0)
}

/// loose_bnos: the loose bound variables, in Isabelle's insertion order.
pub fn loose_bnos(term: &Term) -> Vec<i32> {
    fn add(numbers: &mut Vec<i32>, current: &Term, level: i32) {
        match &**current {
            TermNode::Bound { index } => {
                if *index >= level && !numbers.contains(&(index - level)) {
                    numbers.insert(0, index - level);
                }
            }
            TermNode::Abs { body, .. } => add(numbers, body, level + 1),
            TermNode::App { fun, arg, .. } => {
                add(numbers, arg, level);
                add(numbers, fun, level);
            }
            _ => {}
        }
    }
    let mut numbers = Vec::new();
    add(&mut numbers, term, 0);
    numbers
}

/// subst_bounds: Bound i becomes args[i]; loose bound variables beyond shift down.
fn subst_bounds_at(args: &[Term], level: i32, term: &Term) -> Term {
    if loose_of(term) <= level {
        return term.clone();
    }
    match &**term {
        TermNode::Bound { index } => {
            let offset = index - level;
            if (offset as usize) < args.len() {
                incr_boundvars(level, &args[offset as usize])
            } else {
                mk_bound(index - args.len() as i32)
            }
        }
        TermNode::Abs { body, .. } => {
            update_abs(term, subst_bounds_at(args, level + 1, body), None)
        }
        TermNode::App { fun, arg, .. } => update_app(
            term,
            subst_bounds_at(args, level, fun),
            subst_bounds_at(args, level, arg),
        ),
        _ => term.clone(),
    }
}

pub fn subst_bounds(args: &[Term], body: &Term) -> Term {
    if args.is_empty() {
        body.clone()
    } else {
        subst_bounds_at(args, 0, body)
    }
}

pub fn subst_bound(arg: &Term, body: &Term) -> Term {
    subst_bounds(std::slice::from_ref(arg), body)
}

pub fn betapply(fun: &Term, arg: &Term) -> Term {
    match &**fun {
        TermNode::Abs { body, .. } => subst_bound(arg, body),
        _ => mk_app(fun.clone(), arg.clone()),
    }
}

pub fn betapplys(fun: &Term, args: &[Term]) -> Term {
    args.iter()
        .fold(fun.clone(), |result, arg| betapply(&result, arg))
}

pub fn aconv(left: &Term, right: &Term) -> bool {
    if Term::ptr_eq(left, right) {
        return true;
    }
    match (&**left, &**right) {
        (
            TermNode::App { fun, arg, .. },
            TermNode::App {
                fun: other_fun,
                arg: other_arg,
                ..
            },
        ) => aconv(fun, other_fun) && aconv(arg, other_arg),
        (
            TermNode::Abs { body, ty, .. },
            TermNode::Abs {
                body: other_body,
                ty: other_ty,
                ..
            },
        ) => aconv(body, other_body) && eq_typ(ty, other_ty),
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
        _ => false,
    }
}

/// Structural equality including the names of abstractions, ML's (op =) on terms.
pub fn eq_term(left: &Term, right: &Term) -> bool {
    if Term::ptr_eq(left, right) {
        return true;
    }
    match (&**left, &**right) {
        (
            TermNode::App { fun, arg, .. },
            TermNode::App {
                fun: other_fun,
                arg: other_arg,
                ..
            },
        ) => eq_term(fun, other_fun) && eq_term(arg, other_arg),
        (
            TermNode::Abs { name, ty, body, .. },
            TermNode::Abs {
                name: other,
                ty: other_ty,
                body: other_body,
                ..
            },
        ) => name == other && eq_typ(ty, other_ty) && eq_term(body, other_body),
        (TermNode::App { .. } | TermNode::Abs { .. }, _) => false,
        _ => aconv(left, right),
    }
}

/// could_unify: a fast filter, false only if the normal terms can't unify.
fn match_rands(left: &Term, right: &Term) -> bool {
    let mut current_left = left;
    let mut current_right = right;
    while let (
        TermNode::App { fun, arg, .. },
        TermNode::App {
            fun: other_fun,
            arg: other_arg,
            ..
        },
    ) = (&**current_left, &**current_right)
    {
        if !could_unify(arg, other_arg) {
            return false;
        }
        current_left = fun;
        current_right = other_fun;
    }
    true
}

pub fn could_unify(left: &Term, right: &Term) -> bool {
    let left_head = head_of(left);
    let right_head = head_of(right);
    match (&**left_head, &**right_head) {
        (_, TermNode::Var { .. }) | (TermNode::Var { .. }, _) => true,
        (TermNode::Abs { .. }, _) | (_, TermNode::Abs { .. }) => true,
        (TermNode::Const { name, .. }, TermNode::Const { name: other, .. })
        | (TermNode::Free { name, .. }, TermNode::Free { name: other, .. }) => {
            name == other && match_rands(left, right)
        }
        (TermNode::Bound { index }, TermNode::Bound { index: other }) => {
            index == other && match_rands(left, right)
        }
        _ => false,
    }
}

/// abstract_over: replaces the occurrences of pattern with Bound, ready to become an Abs body.
fn abstract_at(pattern: &Term, level: i32, term: &Term) -> Term {
    if !may_occur(pattern, term) {
        return term.clone();
    }
    if aconv(pattern, term) {
        return mk_bound(level);
    }
    match &**term {
        TermNode::Abs { body, .. } => update_abs(term, abstract_at(pattern, level + 1, body), None),
        TermNode::App { fun, arg, .. } => update_app(
            term,
            abstract_at(pattern, level, fun),
            abstract_at(pattern, level, arg),
        ),
        _ => term.clone(),
    }
}

pub fn abstract_over(pattern: &Term, body: &Term) -> Term {
    abstract_at(pattern, 0, body)
}

pub fn base_name(name: &str) -> &str {
    name.rfind('.').map_or(name, |dot| &name[dot + 1..])
}

pub fn term_name(term: &Term) -> Name {
    match &**term {
        TermNode::Const { name, .. } => base_name(name).into(),
        TermNode::Free { name, .. } | TermNode::Var { name, .. } => name.clone(),
        _ => "uu".into(),
    }
}

/// map_types, with a map that may raise.
pub fn try_map_types(map_type: &mut impl FnMut(&Typ) -> Res<Typ>, term: &Term) -> Res<Term> {
    Ok(match &**term {
        TermNode::Const { name, ty } => {
            let mapped = map_type(ty)?;
            if Typ::ptr_eq(&mapped, ty) {
                term.clone()
            } else {
                mk_const(name.clone(), mapped)
            }
        }
        TermNode::Free { name, ty } => {
            let mapped = map_type(ty)?;
            if Typ::ptr_eq(&mapped, ty) {
                term.clone()
            } else {
                mk_free(name.clone(), mapped)
            }
        }
        TermNode::Var { name, index, ty } => {
            let mapped = map_type(ty)?;
            if Typ::ptr_eq(&mapped, ty) {
                term.clone()
            } else {
                mk_var(name.clone(), *index, mapped)
            }
        }
        TermNode::Bound { .. } => term.clone(),
        TermNode::Abs { ty, body, .. } => {
            let body = try_map_types(map_type, body)?;
            let ty = map_type(ty)?;
            update_abs(term, body, Some(ty))
        }
        TermNode::App { fun, arg, .. } => {
            let fun = try_map_types(map_type, fun)?;
            let arg = try_map_types(map_type, arg)?;
            update_app(term, fun, arg)
        }
    })
}

pub fn map_types(map_type: &mut impl FnMut(&Typ) -> Typ, term: &Term) -> Term {
    match try_map_types(&mut |ty| Ok(map_type(ty)), term) {
        Ok(term) => term,
        Err(_) => unreachable!("the map raises nothing"),
    }
}

/// map_atyps, with a map that may raise.
pub fn try_map_atyps(map_atyp: &mut impl FnMut(&Typ) -> Res<Typ>, ty: &Typ) -> Res<Typ> {
    let TypNode::Type { name, args, .. } = &**ty else {
        return map_atyp(ty);
    };
    let mapped = args
        .iter()
        .map(|arg| try_map_atyps(map_atyp, arg))
        .collect::<Res<Vec<_>>>()?;
    Ok(
        if mapped
            .iter()
            .zip(args)
            .all(|(arg, old)| Typ::ptr_eq(arg, old))
        {
            ty.clone()
        } else {
            mk_type(name.clone(), mapped)
        },
    )
}

pub fn map_atyps(map_atyp: &mut impl FnMut(&Typ) -> Typ, ty: &Typ) -> Typ {
    match try_map_atyps(&mut |ty| Ok(map_atyp(ty)), ty) {
        Ok(ty) => ty,
        Err(_) => unreachable!("the map raises nothing"),
    }
}

pub fn fold_aterms<S>(visit: &mut impl FnMut(&Term, S) -> S, term: &Term, state: S) -> S {
    match &**term {
        TermNode::App { fun, arg, .. } => {
            let state = fold_aterms(visit, fun, state);
            fold_aterms(visit, arg, state)
        }
        TermNode::Abs { body, .. } => fold_aterms(visit, body, state),
        _ => visit(term, state),
    }
}

/// fold_aterms over the schematic variables only, skipping the subterms without one.
pub fn fold_vars<S>(visit: &mut impl FnMut(&Var, S) -> S, term: &Term, state: S) -> S {
    if flags_of(term) & HAS_VAR == 0 {
        return state;
    }
    match &**term {
        TermNode::App { fun, arg, .. } => {
            let state = fold_vars(visit, fun, state);
            fold_vars(visit, arg, state)
        }
        TermNode::Abs { body, .. } => fold_vars(visit, body, state),
        TermNode::Var { .. } => visit(term, state),
        _ => state,
    }
}

pub fn fold_atyps<S>(visit: &mut impl FnMut(&Typ, S) -> S, ty: &Typ, state: S) -> S {
    match &**ty {
        TypNode::Type { args, .. } => args
            .iter()
            .fold(state, |result, arg| fold_atyps(visit, arg, result)),
        _ => visit(ty, state),
    }
}

pub fn fold_types<S>(visit: &mut impl FnMut(&Typ, S) -> S, term: &Term, state: S) -> S {
    match &**term {
        TermNode::Const { ty, .. } | TermNode::Free { ty, .. } | TermNode::Var { ty, .. } => {
            visit(ty, state)
        }
        TermNode::Bound { .. } => state,
        TermNode::Abs { ty, body, .. } => {
            let state = visit(ty, state);
            fold_types(visit, body, state)
        }
        TermNode::App { fun, arg, .. } => {
            let state = fold_types(visit, fun, state);
            fold_types(visit, arg, state)
        }
    }
}

pub fn exists_subterm(predicate: &mut impl FnMut(&Term) -> bool, term: &Term) -> bool {
    if predicate(term) {
        return true;
    }
    match &**term {
        TermNode::App { fun, arg, .. } => {
            exists_subterm(predicate, fun) || exists_subterm(predicate, arg)
        }
        TermNode::Abs { body, .. } => exists_subterm(predicate, body),
        _ => false,
    }
}

pub fn exists_type(predicate: &mut impl FnMut(&Typ) -> bool, term: &Term) -> bool {
    match &**term {
        TermNode::Const { ty, .. } | TermNode::Free { ty, .. } | TermNode::Var { ty, .. } => {
            predicate(ty)
        }
        TermNode::Bound { .. } => false,
        TermNode::Abs { ty, body, .. } => predicate(ty) || exists_type(predicate, body),
        TermNode::App { fun, arg, .. } => {
            exists_type(predicate, fun) || exists_type(predicate, arg)
        }
    }
}

fn same_var(left: &Var, right: &Var) -> bool {
    match (&**left, &**right) {
        (
            TermNode::Var { name, index, ty },
            TermNode::Var {
                name: other,
                index: other_index,
                ty: other_ty,
            },
        ) => name == other && index == other_index && eq_typ(ty, other_ty),
        _ => false,
    }
}

/// add_vars: the schematic variables, latest first, as Isabelle's insert builds the list.
pub fn add_vars(term: &Term, vars: Vec<Var>) -> Vec<Var> {
    fold_vars(
        &mut |current, mut result: Vec<Var>| {
            if !result.iter().any(|other| same_var(other, current)) {
                result.insert(0, current.clone());
            }
            result
        },
        term,
        vars,
    )
}

/// add_free_names: the names of the free variables, latest first.
pub fn add_free_names(term: &Term, names: Vec<Name>) -> Vec<Name> {
    fold_aterms(
        &mut |current, mut result: Vec<Name>| {
            if let TermNode::Free { name, .. } = &**current
                && !result.contains(name)
            {
                result.insert(0, name.clone());
            }
            result
        },
        term,
        names,
    )
}

/// match_bvs: the pairs of corresponding abstraction names while two terms look alike.
fn match_bvs(left: &Term, right: &Term, pairs: Vec<(Name, Name)>) -> Vec<(Name, Name)> {
    match (&**left, &**right) {
        (
            TermNode::Abs { name, body, .. },
            TermNode::Abs {
                name: other,
                body: other_body,
                ..
            },
        ) => {
            let mut added = pairs;
            if !name.is_empty() && !other.is_empty() {
                added.insert(0, (name.clone(), other.clone()));
            }
            match_bvs(body, other_body, added)
        }
        (
            TermNode::App { fun, arg, .. },
            TermNode::App {
                fun: other_fun,
                arg: other_arg,
                ..
            },
        ) => match_bvs(fun, other_fun, match_bvs(arg, other_arg, pairs)),
        _ => pairs,
    }
}

pub fn match_bvars(left: &Term, right: &Term, pairs: Vec<(Name, Name)>) -> Vec<(Name, Name)> {
    match_bvs(strip_abs_body(left), strip_abs_body(right), pairs)
}

fn map_abs_vars(rename: &impl Fn(&Name) -> Name, term: &Term) -> Term {
    match &**term {
        TermNode::Abs { name, ty, body, .. } => {
            let renamed = rename(name);
            let body = map_abs_vars(rename, body);
            if renamed == *name {
                update_abs(term, body, None)
            } else {
                mk_abs(renamed, ty.clone(), body)
            }
        }
        TermNode::App { fun, arg, .. } => {
            update_app(term, map_abs_vars(rename, fun), map_abs_vars(rename, arg))
        }
        _ => term.clone(),
    }
}

/// rename_abs: renames the abstractions of term after those of obj where pat matches obj.
pub fn rename_abs(pattern: &Term, object: &Term, term: &Term) -> Option<Term> {
    let mut renaming: Vec<(Name, Name)> = Vec::new();
    for (from, to) in match_bvs(pattern, object, Vec::new()) {
        if !renaming.iter().any(|(known, _)| *known == from) {
            renaming.push((from, to));
        }
    }
    if renaming.iter().all(|(from, to)| from == to) {
        return None;
    }
    let renamed = map_abs_vars(
        &|name| {
            renaming
                .iter()
                .find(|(from, _)| from == name)
                .map_or_else(|| name.clone(), |(_, to)| to.clone())
        },
        term,
    );
    (!Term::ptr_eq(&renamed, term)).then_some(renamed)
}
