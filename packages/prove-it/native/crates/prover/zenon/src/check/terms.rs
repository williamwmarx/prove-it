//! What the rule checks share: the formulas they build and take apart, and how a check rejects a
//! proof.

use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use super::keys::Keys;
use super::relations::RelationProperties;
use crate::expr::{Expr, Kind, efalse, etrue};
use crate::parse::Definition;
use crate::proof::RuleName;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TermKind {
    Var,
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
    Subst,
}

impl TermKind {
    pub fn name(self) -> &'static str {
        match self {
            TermKind::Var => "var",
            TermKind::Meta => "meta",
            TermKind::App => "app",
            TermKind::Not => "not",
            TermKind::And => "and",
            TermKind::Or => "or",
            TermKind::Imply => "imply",
            TermKind::Equiv => "equiv",
            TermKind::True => "true",
            TermKind::False => "false",
            TermKind::All => "all",
            TermKind::Ex => "ex",
            TermKind::Tau => "tau",
            TermKind::Lam => "lam",
            TermKind::Subst => "subst",
        }
    }
}

impl From<Kind> for TermKind {
    fn from(kind: Kind) -> TermKind {
        match kind {
            Kind::Var => TermKind::Var,
            Kind::Meta => TermKind::Meta,
            Kind::App => TermKind::App,
            Kind::Not => TermKind::Not,
            Kind::And => TermKind::And,
            Kind::Or => TermKind::Or,
            Kind::Imply => TermKind::Imply,
            Kind::Equiv => TermKind::Equiv,
            Kind::True => TermKind::True,
            Kind::False => TermKind::False,
            Kind::All => TermKind::All,
            Kind::Ex => TermKind::Ex,
            Kind::Tau => TermKind::Tau,
            Kind::Lam => TermKind::Lam,
        }
    }
}

pub struct TermNode {
    kind: TermKind,
    symbol: Rc<str>,
    args: Vec<Term>,
}

/// A formula as the checker sees it: one of the prover's expressions, or one the checker built.
/// "subst" stands for its first argument with the variable named `symbol` replaced by its second
/// argument.
#[derive(Clone)]
pub enum Term {
    Expr(Expr),
    Built(Rc<TermNode>),
}

impl From<&Expr> for Term {
    fn from(expression: &Expr) -> Term {
        Term::Expr(expression.clone())
    }
}

impl Term {
    pub fn kind(&self) -> TermKind {
        match self {
            Term::Expr(expression) => expression.kind.into(),
            Term::Built(node) => node.kind,
        }
    }

    pub fn symbol(&self) -> &Rc<str> {
        match self {
            Term::Expr(expression) => &expression.symbol,
            Term::Built(node) => &node.symbol,
        }
    }

    pub fn arity(&self) -> usize {
        match self {
            Term::Expr(expression) => expression.args.len(),
            Term::Built(node) => node.args.len(),
        }
    }

    pub fn arg(&self, index: usize) -> Term {
        match self {
            Term::Expr(expression) => Term::Expr(expression.args[index].clone()),
            Term::Built(node) => node.args[index].clone(),
        }
    }

    pub fn args(&self) -> Vec<Term> {
        match self {
            Term::Expr(expression) => expression.args.iter().map(Term::from).collect(),
            Term::Built(node) => node.args.clone(),
        }
    }
}

/// A term as a key by identity, as a JavaScript `WeakMap` holds it. The key keeps the term alive,
/// so that its address isn't reused while the key is in a map.
pub struct TermKey(pub Term);

impl TermKey {
    fn address(&self) -> usize {
        match &self.0 {
            Term::Expr(expression) => std::ptr::from_ref(&**expression).addr(),
            Term::Built(node) => Rc::as_ptr(node).addr(),
        }
    }
}

impl PartialEq for TermKey {
    fn eq(&self, other: &TermKey) -> bool {
        matches!(
            (&self.0, &other.0),
            (Term::Expr(_), Term::Expr(_)) | (Term::Built(_), Term::Built(_))
        ) && self.address() == other.address()
    }
}

impl Eq for TermKey {}

impl Hash for TermKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.address().hash(state);
    }
}

pub struct CheckContext {
    pub hypotheses: Vec<Expr>,
    pub definitions: Vec<Rc<Definition>>,
}

/// What a rule needs on its branch: its premises, and the formulas each of its branches adds.
pub struct RuleSpec {
    pub premises: Vec<Term>,
    pub branches: Vec<Vec<Term>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RelationProperty {
    Reflexive,
    Symmetric,
    Transitive,
}

impl RelationProperty {
    pub fn name(self) -> &'static str {
        match self {
            RelationProperty::Reflexive => "reflexive",
            RelationProperty::Symmetric => "symmetric",
            RelationProperty::Transitive => "transitive",
        }
    }
}

/// What a variable stands for while printing a key: the depth of its binder, or a term substituted
/// for it with the environment where the substitution was made. A substituted term prints where it
/// lands, so its own binders get depths below the binders around it.
#[derive(Clone)]
pub enum Binding {
    Depth(i64),
    Term {
        formula: Term,
        env: Rc<Env>,
        operators: Option<Rc<Operators>>,
    },
}

pub type Env = HashMap<Rc<str>, Binding>;

pub type Operators = HashMap<Rc<str>, Term>;

/// One check of a proof, with the caches that last as long as it does.
pub struct Checker<'a> {
    pub context: &'a CheckContext,
    pub keys: Keys,
    pub relations: RelationProperties<'a>,
}

impl Checker<'_> {
    /// A canonical text for a formula up to the names of bound variables.
    pub fn get_key(
        &mut self,
        formula: &Term,
        env: &Rc<Env>,
        depth: i64,
        operators: Option<&Rc<Operators>>,
    ) -> Checked<Rc<str>> {
        self.keys.get_key(formula, env, depth, operators)
    }

    pub fn get_top_key(&mut self, formula: &Term) -> Checked<Rc<str>> {
        self.keys.get_top_key(formula)
    }

    pub fn is_same(&mut self, left: &Term, right: &Term) -> Checked<bool> {
        self.keys.is_same(left, right)
    }

    /// A binder whose variable can't clash with any name in the input.
    pub fn bind(
        &mut self,
        kind: TermKind,
        type_name: &str,
        build: impl FnOnce(&Term) -> Term,
    ) -> Term {
        self.keys.bind(kind, type_name, build)
    }

    /// Rejects the proof unless the hypotheses give the relation these properties.
    pub fn ensure_relation(
        &mut self,
        symbol: &str,
        properties: &[RelationProperty],
    ) -> Checked<()> {
        ensure(self.relations.has(symbol, properties))
    }
}

/// Raised inside a rule check to reject the proof.
#[derive(Debug)]
pub struct UncheckedError;

pub type Checked<T> = Result<T, UncheckedError>;

/// The check of the rules of one table, given the rule's arguments and the formulas the proof says
/// it uses; `None` when the rule isn't in the table.
pub type SpecTable = fn(RuleName, &[Term], &mut Checker<'_>, &[Term]) -> Option<Checked<RuleSpec>>;

pub fn ensure(condition: bool) -> Checked<()> {
    if condition {
        Ok(())
    } else {
        Err(UncheckedError)
    }
}

pub fn spec(premises: Vec<Term>, branches: Vec<Vec<Term>>) -> Checked<RuleSpec> {
    Ok(RuleSpec { premises, branches })
}

pub fn term(kind: TermKind, symbol: &str, args: Vec<Term>) -> Term {
    Term::Built(Rc::new(TermNode {
        kind,
        symbol: symbol.into(),
        args,
    }))
}

pub fn variable(name: &str) -> Term {
    term(TermKind::Var, name, Vec::new())
}

pub fn app(symbol: &str, args: Vec<Term>) -> Term {
    term(TermKind::App, symbol, args)
}

pub fn not(operand: &Term) -> Term {
    term(TermKind::Not, "", vec![operand.clone()])
}

pub fn and(left: &Term, right: &Term) -> Term {
    term(TermKind::And, "", vec![left.clone(), right.clone()])
}

pub fn or(left: &Term, right: &Term) -> Term {
    term(TermKind::Or, "", vec![left.clone(), right.clone()])
}

pub fn imply(left: &Term, right: &Term) -> Term {
    term(TermKind::Imply, "", vec![left.clone(), right.clone()])
}

pub fn equiv(left: &Term, right: &Term) -> Term {
    term(TermKind::Equiv, "", vec![left.clone(), right.clone()])
}

pub fn equal(left: &Term, right: &Term) -> Term {
    app("=", vec![left.clone(), right.clone()])
}

pub fn member(element: &Term, set: &Term) -> Term {
    app("TLA.in", vec![element.clone(), set.clone()])
}

pub fn fapply(fcn: &Term, argument: &Term) -> Term {
    app("TLA.fapply", vec![fcn.clone(), argument.clone()])
}

pub fn domain(fcn: &Term) -> Term {
    app("TLA.DOMAIN", vec![fcn.clone()])
}

pub fn true_term() -> Term {
    Term::Expr(etrue())
}

pub fn false_term() -> Term {
    Term::Expr(efalse())
}

/// Instantiates the body of a binder with a term.
pub fn instantiate(binder: &Term, value: &Term) -> Term {
    term(
        TermKind::Subst,
        binder.arg(0).symbol(),
        vec![binder.arg(1), value.clone()],
    )
}

pub fn is_app(formula: &Term, symbol: &str, arity: Option<usize>) -> bool {
    formula.kind() == TermKind::App
        && &**formula.symbol() == symbol
        && arity.is_none_or(|count| formula.arity() == count)
}

pub fn expect_app(formula: &Term, symbol: &str, arity: Option<usize>) -> Checked<Vec<Term>> {
    ensure(is_app(formula, symbol, arity))?;
    Ok(formula.args())
}

pub fn expect_kind(formula: &Term, kind: TermKind) -> Checked<Vec<Term>> {
    ensure(formula.kind() == kind)?;
    Ok(formula.args())
}

pub fn expect_not(formula: &Term) -> Checked<Term> {
    ensure(formula.kind() == TermKind::Not)?;
    Ok(formula.arg(0))
}

pub fn is_variable(formula: &Term, name: &str) -> bool {
    formula.kind() == TermKind::Var && &**formula.symbol() == name
}

/// The text of a string literal. Escapes could spell one string two ways, so they don't count.
pub fn get_string_text(formula: &Term) -> Checked<Rc<str>> {
    ensure(is_app(formula, "$string", Some(1)) && formula.arg(0).kind() == TermKind::Var)?;
    let text = formula.arg(0).symbol().clone();
    ensure(!text.contains('\\'))?;
    Ok(text)
}

pub fn get_pairs(args: &[Term]) -> Checked<Vec<(Term, Term)>> {
    ensure(args.len().is_multiple_of(2))?;
    Ok(args
        .chunks(2)
        .map(|pair| (pair[0].clone(), pair[1].clone()))
        .collect())
}

pub fn make_natural(count: usize) -> Term {
    let mut result = variable("0");
    for _ in 0..count {
        result = fapply(&variable("TLA.Succ"), &result);
    }
    result
}
