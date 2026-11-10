// Ported from Zenon's expr.ml, as shipped in tlapm. Copyright 2002 INRIA, see LICENSE.
//! Formulas and terms, hash-consed so that equal expressions are the same node. Like Zenon,
//! equality treats bound variables up to renaming, and a hash ignores the names of bound variables.
//! Each run builds its expressions in its own store, so that fresh names and hashes start over.
//!
//! An [`Expr`] is a shared pointer whose equality and hash are its identity, as a JavaScript object
//! is in a `Map`; the store guarantees that equal expressions are one node.

use std::cell::{Cell, RefCell};
use std::cmp::Ordering;
use std::collections::HashMap;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::Deref;
use std::rc::Rc;

use crate::ZenonError;
use crate::ocaml::{combine, hash_int_and_strings, hash_string};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Kind {
    Var,
    /// A metavariable stands for a term that instantiates its quantifier.
    Meta,
    App,
    Not,
    And,
    Or,
    Imply,
    Equiv,
    True,
    False,
    All,
    Ex,
    Tau,
    Lam,
}

impl Kind {
    /// The TypeScript's name of the kind, which orders kinds in [`compare_exprs`].
    pub fn name(self) -> &'static str {
        match self {
            Kind::Var => "var",
            Kind::Meta => "meta",
            Kind::App => "app",
            Kind::Not => "not",
            Kind::And => "and",
            Kind::Or => "or",
            Kind::Imply => "imply",
            Kind::Equiv => "equiv",
            Kind::True => "true",
            Kind::False => "false",
            Kind::All => "all",
            Kind::Ex => "ex",
            Kind::Tau => "tau",
            Kind::Lam => "lam",
        }
    }

    pub fn is_binary(self) -> bool {
        matches!(self, Kind::And | Kind::Or | Kind::Imply | Kind::Equiv)
    }

    pub fn is_binder(self) -> bool {
        matches!(self, Kind::All | Kind::Ex | Kind::Tau | Kind::Lam)
    }

    fn skeleton(self) -> i64 {
        match self {
            Kind::True => 0xb063cd7,
            Kind::False => 0xd5ab9f0,
            Kind::Meta => 0x33d092c,
            Kind::App => 0x33b9c25,
            Kind::Not => 0x7c3e7d2,
            Kind::And => 0xccdc15b,
            Kind::Or => 0x49b55b9,
            Kind::Imply => 0x7ebfa6f,
            Kind::Equiv => 0xb0f18f7,
            Kind::All => 0xfb437ff,
            Kind::Ex => 0x0716b52,
            Kind::Tau => 0x4ae7fad,
            Kind::Lam => 0x24adcb3,
            Kind::Var => 0,
        }
    }
}

/// An expression and what it caches about itself. `symbol` is a variable's name, an application's
/// function, or a binder's type; it is empty otherwise. A metavariable's argument is the formula it
/// instantiates; a binder's arguments are its variable and its body.
pub struct ExprNode {
    pub id: u32,
    pub kind: Kind,
    pub symbol: Rc<str>,
    pub args: Vec<Expr>,
    pub hash: u32,
    pub skeleton: i64,
    pub free_vars: Rc<Vec<Rc<str>>>,
    pub size: i64,
    pub taus: i64,
    pub metas: Rc<Vec<Expr>>,
}

#[derive(Clone)]
pub struct Expr(Rc<ExprNode>);

impl Deref for Expr {
    type Target = ExprNode;
    fn deref(&self) -> &ExprNode {
        &self.0
    }
}

impl PartialEq for Expr {
    fn eq(&self, other: &Expr) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for Expr {}

impl Hash for Expr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.id.hash(state);
    }
}

impl fmt::Debug for Expr {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind {
            Kind::Var => write!(formatter, "{}", self.symbol),
            Kind::True => write!(formatter, "T."),
            Kind::False => write!(formatter, "F."),
            Kind::App if self.args.is_empty() => write!(formatter, "({})", self.symbol),
            Kind::App => {
                write!(formatter, "({}", self.symbol)?;
                self.args
                    .iter()
                    .try_for_each(|arg| write!(formatter, " {arg:?}"))?;
                write!(formatter, ")")
            }
            Kind::Meta => write!(formatter, "(meta {:?})", self.args[0]),
            kind if kind.is_binder() => write!(
                formatter,
                "({} (({:?} \"{}\") {:?}))",
                kind.name(),
                self.args[0],
                self.symbol,
                self.args[1]
            ),
            kind => {
                write!(formatter, "({}", kind.name())?;
                self.args
                    .iter()
                    .try_for_each(|arg| write!(formatter, " {arg:?}"))?;
                write!(formatter, ")")
            }
        }
    }
}

impl Expr {
    pub fn is_app(&self, symbol: &str) -> bool {
        self.kind == Kind::App && &*self.symbol == symbol
    }

    pub fn is_app_with_arity(&self, symbol: &str, arity: usize) -> bool {
        self.is_app(symbol) && self.args.len() == arity
    }

    pub fn is_meta(&self) -> bool {
        self.kind == Kind::Meta
    }

    /// An application to two arguments, such as an equality or another relation between terms.
    pub fn is_relation(&self) -> bool {
        self.kind == Kind::App && self.args.len() == 2
    }

    pub fn is_negated_relation(&self) -> bool {
        self.kind == Kind::Not && self.args[0].is_relation()
    }

    /// Whether `name` is free in the expression.
    pub fn has_free_var(&self, name: &str) -> bool {
        self.free_vars.iter().any(|free| &**free == name)
    }
}

pub const VAR_PREFIX: &str = "zenon_V";
pub const UNIVERSE: &str = "zenon_U";
pub const GOAL_NAME: &str = "zenon_G";

fn make_constant(kind: Kind, id: u32) -> Expr {
    let skeleton = kind.skeleton();
    Expr(Rc::new(ExprNode {
        id,
        kind,
        symbol: "".into(),
        args: Vec::new(),
        hash: hash_int_and_strings::<&str>(skeleton, &[]),
        skeleton,
        free_vars: Rc::default(),
        size: 1,
        taus: 0,
        metas: Rc::default(),
    }))
}

thread_local! {
    static TRUE: Expr = make_constant(Kind::True, 0);
    static FALSE: Expr = make_constant(Kind::False, 1);
}

/// `TRUE`, shared by every store on the thread.
pub fn etrue() -> Expr {
    TRUE.with(Expr::clone)
}

/// `FALSE`, shared by every store on the thread.
pub fn efalse() -> Expr {
    FALSE.with(Expr::clone)
}

/// Zenon's str_union: the names of the first list missing from the second, in reverse, then the
/// second. Hashes depend on this order.
fn union_names(left: &Rc<Vec<Rc<str>>>, right: &Rc<Vec<Rc<str>>>) -> Rc<Vec<Rc<str>>> {
    if left.is_empty() {
        return right.clone();
    }
    if right.is_empty() {
        return left.clone();
    }
    let added: Vec<Rc<str>> = left
        .iter()
        .scan(Vec::<&Rc<str>>::new(), |seen, name| {
            let is_new = !right.contains(name) && !seen.contains(&name);
            seen.push(name);
            Some(is_new.then(|| name.clone()))
        })
        .flatten()
        .collect();
    Rc::new(
        added
            .into_iter()
            .rev()
            .chain(right.iter().cloned())
            .collect(),
    )
}

fn remove_name(name: &str, names: &Rc<Vec<Rc<str>>>) -> Rc<Vec<Rc<str>>> {
    match names.iter().position(|inner| &**inner == name) {
        None => names.clone(),
        Some(index) => {
            let mut removed = (**names).clone();
            removed.remove(index);
            Rc::new(removed)
        }
    }
}

pub fn difference(left: &[Expr], right: &[Expr]) -> Vec<Expr> {
    left.iter()
        .filter(|inner| !right.contains(inner))
        .cloned()
        .collect()
}

/// Zenon's union on small sets: the first list's new elements in reverse, then the second list.
pub fn union(left: &[Expr], right: &[Expr]) -> Vec<Expr> {
    let added = difference(left, right);
    added
        .into_iter()
        .rev()
        .chain(right.iter().cloned())
        .collect()
}

fn union_metas(left: &Rc<Vec<Expr>>, right: &Rc<Vec<Expr>>) -> Rc<Vec<Expr>> {
    if left.iter().all(|inner| right.contains(inner)) {
        right.clone()
    } else {
        Rc::new(union(left, right))
    }
}

pub fn is_disjoint(left: &[Expr], right: &[Expr]) -> bool {
    !left.iter().any(|inner| right.contains(inner))
}

fn intersects(env: &[Expr], names: &[Rc<str>]) -> bool {
    names
        .iter()
        .any(|name| env.iter().any(|variable| variable.symbol == *name))
}

fn is_same_binding(left_env: &[Expr], left: &Expr, right_env: &[Expr], right: &Expr) -> bool {
    let left_index = left_env.iter().position(|inner| inner == left);
    let right_index = right_env.iter().position(|inner| inner == right);
    match left_index {
        None => right_index.is_none() && left == right,
        Some(_) => left_index == right_index,
    }
}

fn is_equal_in_env(left_env: &[Expr], right_env: &[Expr], left: &Expr, right: &Expr) -> bool {
    let is_left_bound = intersects(left_env, &left.free_vars);
    let is_right_bound = intersects(right_env, &right.free_vars);
    if !is_left_bound && !is_right_bound {
        return left == right;
    }
    if !is_left_bound || !is_right_bound || left.kind != right.kind {
        return false;
    }
    match left.kind {
        Kind::Var => is_same_binding(left_env, left, right_env, right),
        Kind::Meta => left.args[0] == right.args[0],
        Kind::App => {
            left.symbol == right.symbol
                && left.args.len() == right.args.len()
                && left
                    .args
                    .iter()
                    .zip(&right.args)
                    .all(|(left, right)| is_equal_in_env(left_env, right_env, left, right))
        }
        Kind::Not => is_equal_in_env(left_env, right_env, &left.args[0], &right.args[0]),
        Kind::And | Kind::Or | Kind::Imply | Kind::Equiv => {
            is_equal_in_env(left_env, right_env, &left.args[0], &right.args[0])
                && is_equal_in_env(left_env, right_env, &left.args[1], &right.args[1])
        }
        Kind::True | Kind::False => true,
        Kind::All | Kind::Ex | Kind::Tau | Kind::Lam => {
            left.args[1].has_free_var(&left.args[0].symbol)
                == right.args[1].has_free_var(&right.args[0].symbol)
                && is_equal_in_env(
                    &[&[left.args[0].clone()], left_env].concat(),
                    &[&[right.args[0].clone()], right_env].concat(),
                    &left.args[1],
                    &right.args[1],
                )
        }
    }
}

fn is_equal_body(left_var: &Expr, right_var: &Expr, left: &Expr, right: &Expr) -> bool {
    let is_left_bound = left.has_free_var(&left_var.symbol);
    let is_right_bound = right.has_free_var(&right_var.symbol);
    (!is_left_bound && !is_right_bound && left == right)
        || (is_left_bound
            && is_right_bound
            && is_equal_in_env(
                std::slice::from_ref(left_var),
                std::slice::from_ref(right_var),
                left,
                right,
            ))
}

/// Zenon's HashedExpr.equal on two binders whose children are already hash-consed.
fn is_same_binder(left: &Expr, right: &Expr) -> bool {
    left.kind == right.kind
        && left.symbol == right.symbol
        && if left.args[0] == right.args[0] {
            left.args[1] == right.args[1]
        } else {
            is_equal_body(&left.args[0], &right.args[0], &left.args[1], &right.args[1])
        }
}

/// Zenon orders by hash, and only breaks ties structurally: `compareExprs`.
pub fn compare_exprs(left: &Expr, right: &Expr) -> Ordering {
    if left.hash != right.hash {
        return left.hash.cmp(&right.hash);
    }
    if left == right {
        return Ordering::Equal;
    }
    if left.kind != right.kind {
        return left.kind.name().cmp(right.kind.name());
    }
    if left.symbol != right.symbol {
        return compare_utf16(&left.symbol, &right.symbol);
    }
    if left.args.len() != right.args.len() {
        return left.args.len().cmp(&right.args.len());
    }
    left.args
        .iter()
        .zip(&right.args)
        .map(|(left, right)| compare_exprs(left, right))
        .find(|order| *order != Ordering::Equal)
        .unwrap_or(Ordering::Equal)
}

/// JavaScript's `<` on strings: by UTF-16 code units.
pub fn compare_utf16(left: &str, right: &str) -> Ordering {
    left.encode_utf16().cmp(right.encode_utf16())
}

/// A substitution, as pairs of a variable and its value.
pub type Substitution = Vec<(Expr, Expr)>;

fn lookup(map: &[(Expr, Expr)], variable: &Expr) -> Option<Expr> {
    map.iter()
        .find(|pair| pair.0 == *variable)
        .map(|pair| pair.1.clone())
}

fn is_irrelevant(names: &[Rc<str>], map: &[(Expr, Expr)]) -> bool {
    names
        .iter()
        .all(|name| map.iter().all(|pair| pair.0.symbol != *name))
}

fn has_conflict(variable: &Expr, map: &[(Expr, Expr)]) -> bool {
    map.iter().any(|pair| pair.1.has_free_var(&variable.symbol))
}

/// An expression's kind, symbol and the ids of its arguments.
type InternKey = (Kind, Rc<str>, Vec<u32>);

/// The store of one run's expressions, and the operations that build expressions in it.
pub struct Expressions {
    /// Binders are hash-consed by hash, since they're equal up to the names of their variables.
    binders: RefCell<HashMap<u32, Vec<Expr>>>,
    /// Other expressions are equal exactly when their kind, symbol and children are.
    interned: RefCell<HashMap<InternKey, Expr>>,
    string_hashes: RefCell<HashMap<Rc<str>, u32>>,
    next_id: Cell<u32>,
    created_count: Cell<u64>,
    /// Zenon's Ext_focal takes the first five fresh names when the program starts, for its
    /// built-in definitions, so the first name Zenon gives out is zenon_Vf.
    name_counter: RefCell<Vec<u8>>,
}

impl Default for Expressions {
    fn default() -> Self {
        Self::new()
    }
}

impl Expressions {
    pub fn new() -> Self {
        Expressions {
            binders: RefCell::default(),
            interned: RefCell::default(),
            string_hashes: RefCell::default(),
            next_id: Cell::new(2),
            created_count: Cell::new(0),
            name_counter: RefCell::new(b"e".to_vec()),
        }
    }

    pub fn get_created_count(&self) -> u64 {
        self.created_count.get()
    }

    fn hash_string(&self, value: &Rc<str>) -> u32 {
        if let Some(hash) = self.string_hashes.borrow().get(value) {
            return *hash;
        }
        let hash = hash_string(value);
        self.string_hashes.borrow_mut().insert(value.clone(), hash);
        hash
    }

    #[expect(clippy::too_many_arguments, reason = "the fields of a node")]
    fn create(
        &self,
        kind: Kind,
        symbol: Rc<str>,
        args: Vec<Expr>,
        skeleton: i64,
        free_vars: Rc<Vec<Rc<str>>>,
        size: i64,
        taus: i64,
        metas: Rc<Vec<Expr>>,
    ) -> Expr {
        let id = self.next_id.get();
        self.next_id.set(id + 1);
        Expr(Rc::new(ExprNode {
            id,
            kind,
            symbol,
            args,
            hash: hash_int_and_strings(skeleton, &free_vars),
            skeleton,
            free_vars,
            size,
            taus,
            metas,
        }))
    }

    fn merge_binder(&self, candidate: Expr) -> Expr {
        let mut binders = self.binders.borrow_mut();
        let bucket = binders.entry(candidate.hash).or_default();
        if let Some(existing) = bucket
            .iter()
            .find(|inner| is_same_binder(inner, &candidate))
        {
            return existing.clone();
        }
        bucket.push(candidate.clone());
        self.created_count.set(self.created_count.get() + 1);
        candidate
    }

    fn intern(
        &self,
        kind: Kind,
        symbol: &str,
        args: &[Expr],
        build: impl FnOnce(Rc<str>, Vec<Expr>) -> Expr,
    ) -> Expr {
        let key = (
            kind,
            Rc::<str>::from(symbol),
            args.iter().map(|arg| arg.id).collect::<Vec<_>>(),
        );
        if let Some(existing) = self.interned.borrow().get(&key) {
            return existing.clone();
        }
        let result = build(key.1.clone(), args.to_vec());
        self.interned.borrow_mut().insert(key, result.clone());
        self.created_count.set(self.created_count.get() + 1);
        result
    }

    pub fn evar(&self, name: &str) -> Expr {
        self.intern(Kind::Var, name, &[], |symbol, args| {
            let free_vars = Rc::new(vec![symbol.clone()]);
            self.create(Kind::Var, symbol, args, 0, free_vars, 1, 0, Rc::default())
        })
    }

    pub fn emeta(&self, quantified: &Expr) -> Expr {
        self.intern(
            Kind::Meta,
            "",
            std::slice::from_ref(quantified),
            |symbol, args| {
                let skeleton = combine(Kind::Meta.skeleton(), quantified.skeleton);
                let metas = Rc::new(vec![quantified.clone()]);
                self.create(
                    Kind::Meta,
                    symbol,
                    args,
                    skeleton,
                    Rc::default(),
                    1,
                    0,
                    metas,
                )
            },
        )
    }

    pub fn eapp(&self, symbol: &str, args: &[Expr]) -> Expr {
        self.intern(Kind::App, symbol, args, |symbol, args| {
            let mut skeleton = i64::from(self.hash_string(&symbol));
            let mut free_vars = Rc::default();
            let mut size = 1;
            let mut taus = 0;
            let mut metas = Rc::default();
            for arg in &args {
                skeleton = combine(arg.skeleton, skeleton);
                free_vars = union_names(&free_vars, &arg.free_vars);
                size += arg.size;
                taus = arg.taus.max(taus);
                metas = union_metas(&arg.metas, &metas);
            }
            let skeleton = combine(Kind::App.skeleton(), skeleton);
            self.create(
                Kind::App,
                symbol,
                args,
                skeleton,
                free_vars,
                size,
                taus,
                metas,
            )
        })
    }

    pub fn enot(&self, operand: &Expr) -> Expr {
        self.intern(
            Kind::Not,
            "",
            std::slice::from_ref(operand),
            |symbol, args| {
                self.create(
                    Kind::Not,
                    symbol,
                    args,
                    combine(Kind::Not.skeleton(), operand.skeleton),
                    operand.free_vars.clone(),
                    operand.size + 1,
                    operand.taus,
                    operand.metas.clone(),
                )
            },
        )
    }

    pub fn binary(&self, kind: Kind, left: &Expr, right: &Expr) -> Expr {
        debug_assert!(kind.is_binary());
        self.intern(kind, "", &[left.clone(), right.clone()], |symbol, args| {
            self.create(
                kind,
                symbol,
                args,
                combine(kind.skeleton(), combine(left.skeleton, right.skeleton)),
                union_names(&left.free_vars, &right.free_vars),
                left.size + right.size + 1,
                left.taus.max(right.taus),
                union_metas(&left.metas, &right.metas),
            )
        })
    }

    pub fn eand(&self, left: &Expr, right: &Expr) -> Expr {
        self.binary(Kind::And, left, right)
    }

    pub fn eor(&self, left: &Expr, right: &Expr) -> Expr {
        self.binary(Kind::Or, left, right)
    }

    pub fn eimply(&self, left: &Expr, right: &Expr) -> Expr {
        self.binary(Kind::Imply, left, right)
    }

    pub fn eequiv(&self, left: &Expr, right: &Expr) -> Expr {
        self.binary(Kind::Equiv, left, right)
    }

    /// A binder of `kind` on `variable`, of type `type_name`.
    pub fn binder(&self, kind: Kind, variable: &Expr, type_name: &str, body: &Expr) -> Expr {
        debug_assert!(kind.is_binder() && variable.kind == Kind::Var);
        let type_name: Rc<str> = type_name.into();
        let skeleton = combine(
            kind.skeleton(),
            combine(i64::from(self.hash_string(&type_name)), body.skeleton),
        );
        self.merge_binder(self.create(
            kind,
            type_name,
            vec![variable.clone(), body.clone()],
            skeleton,
            remove_name(&variable.symbol, &body.free_vars),
            if matches!(kind, Kind::Tau | Kind::Lam) {
                1
            } else {
                body.size + 1
            },
            if kind == Kind::Tau {
                body.taus + 1
            } else {
                body.taus
            },
            body.metas.clone(),
        ))
    }

    pub fn eall(&self, variable: &Expr, type_name: &str, body: &Expr) -> Expr {
        self.binder(Kind::All, variable, type_name, body)
    }

    pub fn eex(&self, variable: &Expr, type_name: &str, body: &Expr) -> Expr {
        self.binder(Kind::Ex, variable, type_name, body)
    }

    pub fn etau(&self, variable: &Expr, type_name: &str, body: &Expr) -> Expr {
        self.binder(Kind::Tau, variable, type_name, body)
    }

    pub fn elam(&self, variable: &Expr, type_name: &str, body: &Expr) -> Expr {
        self.binder(Kind::Lam, variable, type_name, body)
    }

    /// The expression of `expression`'s kind and symbol on other arguments, for an application,
    /// a negation or a binary connective.
    pub fn rebuild(&self, expression: &Expr, args: &[Expr]) -> Expr {
        match expression.kind {
            Kind::App => self.eapp(&expression.symbol, args),
            Kind::Not => self.enot(&args[0]),
            kind => self.binary(kind, &args[0], &args[1]),
        }
    }

    pub fn new_var(&self) -> Expr {
        let name = {
            let mut letters = self.name_counter.borrow_mut();
            let mut position = 0;
            while position < letters.len() && letters[position] == b'z' {
                letters[position] = b'a';
                position += 1;
            }
            if position == letters.len() {
                letters.push(b'a');
            } else {
                letters[position] += 1;
            }
            format!("{VAR_PREFIX}{}", String::from_utf8_lossy(&letters))
        };
        self.evar(&name)
    }

    /// A binder's variable for a substitution, renamed when the substituted values capture it, and
    /// the substitution to apply to its body.
    fn enter_binder(&self, expression: &Expr, map: &[(Expr, Expr)]) -> (Expr, Substitution) {
        let variable = &expression.args[0];
        let rest: Substitution = map
            .iter()
            .filter(|pair| pair.0 != *variable)
            .cloned()
            .collect();
        if !has_conflict(variable, &rest) {
            return (variable.clone(), rest);
        }
        let fresh = self.new_var();
        let entered = std::iter::once((variable.clone(), fresh.clone()))
            .chain(rest)
            .collect();
        (fresh, entered)
    }

    pub fn substitute(&self, map: &[(Expr, Expr)], expression: &Expr) -> Expr {
        if is_irrelevant(&expression.free_vars, map) {
            return expression.clone();
        }
        match expression.kind {
            Kind::Var => lookup(map, expression).unwrap_or_else(|| expression.clone()),
            Kind::Meta | Kind::True | Kind::False => expression.clone(),
            kind if kind.is_binder() => {
                let entered = self.enter_binder(expression, map);
                let body = self.substitute(&entered.1, &expression.args[1]);
                self.binder(kind, &entered.0, &expression.symbol, &body)
            }
            _ => {
                let args: Vec<Expr> = expression
                    .args
                    .iter()
                    .map(|inner| self.substitute(map, inner))
                    .collect();
                self.rebuild(expression, &args)
            }
        }
    }

    fn substitute_all(&self, map: &[(Expr, Expr)], expressions: &[Expr]) -> Option<Vec<Expr>> {
        expressions
            .iter()
            .map(|inner| self.substitute_second_order(map, inner))
            .collect()
    }

    /// Zenon's substitute_2nd: also replaces applied symbols bound in the map, for definitions with
    /// operator parameters. `None` stands for Zenon's Higher_order exception.
    pub fn substitute_second_order(&self, map: &[(Expr, Expr)], expression: &Expr) -> Option<Expr> {
        match expression.kind {
            Kind::Var => Some(lookup(map, expression).unwrap_or_else(|| expression.clone())),
            Kind::Meta | Kind::True | Kind::False => Some(expression.clone()),
            Kind::App => {
                let actuals = self.substitute_all(map, &expression.args)?;
                let Some(operator) = lookup(map, &self.evar(&expression.symbol)) else {
                    return Some(self.eapp(&expression.symbol, &actuals));
                };
                match operator.kind {
                    Kind::Lam if actuals.len() == 1 => Some(self.substitute(
                        &[(operator.args[0].clone(), actuals[0].clone())],
                        &operator.args[1],
                    )),
                    Kind::Var => Some(self.eapp(&operator.symbol, &actuals)),
                    Kind::App => Some(self.eapp(
                        &operator.symbol,
                        &[operator.args.as_slice(), &actuals].concat(),
                    )),
                    _ => None,
                }
            }
            kind if kind.is_binder() => {
                let entered = self.enter_binder(expression, map);
                let body = self.substitute_second_order(&entered.1, &expression.args[1])?;
                Some(self.binder(kind, &entered.0, &expression.symbol, &body))
            }
            _ => {
                let args = self.substitute_all(map, &expression.args)?;
                Some(self.rebuild(expression, &args))
            }
        }
    }

    pub fn apply(&self, lambda: &Expr, argument: &Expr) -> Result<Expr, ZenonError> {
        if lambda.kind != Kind::Lam {
            return Err(ZenonError::new("Zenon: higher-order application"));
        }
        Ok(self.substitute(
            &[(lambda.args[0].clone(), argument.clone())],
            &lambda.args[1],
        ))
    }
}
