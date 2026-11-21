//! tlapm's `ptl_to_trp` (`translate/` of tlapm), run as `ptl_to_trp -i file`: it reads a PTL
//! formula and prints the clause set LS4 decides, through negation normal form, the DSNF renaming
//! of temporal subformulas, skolemization and conjunctive normal form. Where its lexer or parser
//! stops, or the translation raises on an operator it has no rule for, it prints no clause set.
//!
//! Its grammar is LALR with precedence declarations, read here by precedence climbing: a binary
//! operator takes the formula to its right as far as operators that bind tighter, left to right
//! among equals, and a prefix operator's operand ends before any binary operator, except
//! `alwaysp` and `sometimep`, which have no declared precedence and so take the whole formula.

use std::fmt::Write;

#[derive(Clone, PartialEq, Eq, Debug)]
enum Arg {
    Variable(String),
    Constant(String),
    Skolem(String, Vec<String>),
}

#[derive(Clone, PartialEq, Eq, Debug)]
enum Expr {
    True,
    False,
    Atom(String, Vec<Arg>),
    NotAtom(String, Vec<Arg>),
    And(Box<Expr>, Box<Expr>),
    Or(Box<Expr>, Box<Expr>),
    Implies(Box<Expr>, Box<Expr>),
    Not(Box<Expr>),
    Forall(Vec<String>, Box<Expr>),
    Exists(Vec<String>, Box<Expr>),
    Always(Box<Expr>),
    AlwaysP(Box<Expr>),
    Sometime(Box<Expr>),
    SometimeP(Box<Expr>),
    Next(Box<Expr>),
    Until(Box<Expr>, Box<Expr>),
    Unless(Box<Expr>, Box<Expr>),
}

use Expr::*;

fn and(left: Expr, right: Expr) -> Expr {
    And(Box::new(left), Box::new(right))
}

fn or(left: Expr, right: Expr) -> Expr {
    Or(Box::new(left), Box::new(right))
}

fn implies(left: Expr, right: Expr) -> Expr {
    Implies(Box::new(left), Box::new(right))
}

fn always(body: Expr) -> Expr {
    Always(Box::new(body))
}

fn next(body: Expr) -> Expr {
    Next(Box::new(body))
}

fn sometime(body: Expr) -> Expr {
    Sometime(Box::new(body))
}

fn until(left: Expr, right: Expr) -> Expr {
    Until(Box::new(left), Box::new(right))
}

fn unless(left: Expr, right: Expr) -> Expr {
    Unless(Box::new(left), Box::new(right))
}

#[derive(Clone, PartialEq, Eq, Debug)]
enum Token {
    Eof,
    Ident(String),
    LPar,
    RPar,
    LBracket,
    RBracket,
    Not,
    Conj,
    Disj,
    Impl,
    Equiv,
    Comma,
    Forall,
    Exists,
    Always,
    AlwaysP,
    Sometime,
    SometimeP,
    Next,
    Until,
    Unless,
    True,
    False,
}

/// `folex.mll`: the rule that matches the longest text wins, the earlier among equals. None where
/// the text has a character or a reserved word no rule takes.
fn tokenize(text: &[u8]) -> Option<Vec<Token>> {
    let mut tokens = Vec::new();
    let mut index = 0;
    while index < text.len() {
        let rest = &text[index..];
        let token = match rest[0] {
            b' ' | b'\t' | b'\r' | b'\n' => {
                index += 1;
                continue;
            }
            b';' => {
                index += rest
                    .iter()
                    .position(|&byte| byte == b'\n')
                    .unwrap_or(rest.len());
                continue;
            }
            b'(' => Token::LPar,
            b')' => Token::RPar,
            b'[' => Token::LBracket,
            b']' => Token::RBracket,
            b'~' => Token::Not,
            b'&' => Token::Conj,
            b'|' => Token::Disj,
            b',' => Token::Comma,
            b'!' => Token::Forall,
            b'?' => Token::Exists,
            _ if rest.starts_with(b"<=>") || rest.starts_with(b"<->") => {
                index += 3;
                tokens.push(Token::Equiv);
                continue;
            }
            _ if rest.starts_with(b"=>") || rest.starts_with(b"->") => {
                index += 2;
                tokens.push(Token::Impl);
                continue;
            }
            byte if byte.is_ascii_alphabetic() => {
                let length = rest
                    .iter()
                    .take_while(|&&byte| byte.is_ascii_alphanumeric() || byte == b'_')
                    .count();
                let word = std::str::from_utf8(&rest[..length]).expect("ASCII");
                index += length;
                tokens.push(match word {
                    "not" => Token::Not,
                    "always" => Token::Always,
                    "alwaysp" => Token::AlwaysP,
                    "sometime" => Token::Sometime,
                    "sometimep" => Token::SometimeP,
                    "next" => Token::Next,
                    "until" => Token::Until,
                    "unless" => Token::Unless,
                    "True" => Token::True,
                    "False" => Token::False,
                    "skolem" | "hidden" | "constant" => return None,
                    _ if word.starts_with("NV_V") || word.starts_with("NVV") => return None,
                    _ => Token::Ident(word.to_owned()),
                });
                continue;
            }
            _ => return None,
        };
        index += 1;
        tokens.push(token);
    }
    tokens.push(Token::Eof);
    Some(tokens)
}

/// The precedence `foyacc.mly` declares, higher binding tighter; the prefix operators' are those
/// of their rules.
const UNTIL: u8 = 1;
const UNLESS: u8 = 2;
const EQUIV: u8 = 3;
const DISJ: u8 = 4;
const IMPL: u8 = 5;
const CONJ: u8 = 6;
const NOT: u8 = 7;
const SOMETIME: u8 = 8;
const ALWAYS: u8 = 9;
const NEXT: u8 = 10;

struct Parser {
    tokens: Vec<Token>,
    position: usize,
}

impl Parser {
    fn peek(&self) -> &Token {
        &self.tokens[self.position]
    }

    fn next(&mut self) -> Token {
        let token = self.tokens[self.position].clone();
        if token != Token::Eof {
            self.position += 1;
        }
        token
    }

    fn expect(&mut self, token: Token) -> Option<()> {
        (self.next() == token).then_some(())
    }

    fn ident(&mut self) -> Option<String> {
        match self.next() {
            Token::Ident(name) => Some(name),
            _ => None,
        }
    }

    /// A formula whose binary operators bind at least as tightly as `min`.
    fn formula(&mut self, min: u8) -> Option<Expr> {
        let mut left = self.prefix()?;
        loop {
            let precedence = match self.peek() {
                Token::Until => UNTIL,
                Token::Unless => UNLESS,
                Token::Equiv => EQUIV,
                Token::Disj => DISJ,
                Token::Impl => IMPL,
                Token::Conj => CONJ,
                _ => break,
            };
            if precedence < min {
                break;
            }
            let operator = self.next();
            let right = self.formula(precedence + 1)?;
            left = match operator {
                Token::Until => until(left, right),
                Token::Unless => unless(left, right),
                Token::Equiv => and(implies(left.clone(), right.clone()), implies(right, left)),
                Token::Disj => or(left, right),
                Token::Impl => implies(left, right),
                _ => and(left, right),
            };
        }
        Some(left)
    }

    fn prefix(&mut self) -> Option<Expr> {
        Some(match self.next() {
            Token::True => True,
            Token::False => False,
            Token::LPar => {
                let inner = self.formula(UNTIL)?;
                self.expect(Token::RPar)?;
                inner
            }
            Token::Ident(name) => {
                let mut args = Vec::new();
                if *self.peek() == Token::LPar {
                    self.next();
                    loop {
                        args.push(Arg::Constant(self.ident()?));
                        match self.next() {
                            Token::Comma => {}
                            Token::RPar => break,
                            _ => return None,
                        }
                    }
                }
                Atom(name, args)
            }
            Token::Not => Not(Box::new(self.formula(NOT + 1)?)),
            Token::Always => always(self.formula(ALWAYS + 1)?),
            Token::Sometime => sometime(self.formula(SOMETIME + 1)?),
            Token::Next => next(self.formula(NEXT + 1)?),
            Token::AlwaysP => AlwaysP(Box::new(self.formula(UNTIL)?)),
            Token::SometimeP => SometimeP(Box::new(self.formula(UNTIL)?)),
            quantifier @ (Token::Forall | Token::Exists) => {
                self.expect(Token::LBracket)?;
                let mut variables = Vec::new();
                loop {
                    let name = self.ident()?;
                    if !name.starts_with(|char: char| char.is_ascii_uppercase()) {
                        return None;
                    }
                    variables.push(name);
                    match self.next() {
                        Token::Comma => {}
                        Token::RBracket => break,
                        _ => return None,
                    }
                }
                let mut body = self.formula(NOT + 1)?;
                for variable in &variables {
                    body = subst(
                        &body,
                        &Arg::Constant(variable.clone()),
                        &Arg::Variable(variable.clone()),
                    );
                }
                if quantifier == Token::Forall {
                    Forall(variables, Box::new(body))
                } else {
                    Exists(variables, Box::new(body))
                }
            }
            _ => return None,
        })
    }
}

fn parse(text: &[u8]) -> Option<Expr> {
    let mut parser = Parser {
        tokens: tokenize(text)?,
        position: 0,
    };
    let formula = parser.formula(UNTIL)?;
    parser.expect(Token::Eof)?;
    Some(formula)
}

/// OCaml's `=` on formulas, as `union` and the renaming memo compare them.
fn union<T: PartialEq + Clone>(left: &[T], right: &[T]) -> Vec<T> {
    let mut result: Vec<T> = left
        .iter()
        .filter(|item| !right.contains(item))
        .cloned()
        .collect();
    result.extend(right.iter().cloned());
    result
}

fn except_all(exceptions: &[String], list: &[String]) -> Vec<String> {
    let mut result = list.to_vec();
    for exception in exceptions.iter().rev() {
        if let Some(position) = result.iter().position(|item| item == exception) {
            result.remove(position);
        }
    }
    result
}

fn is_literal(expr: &Expr) -> bool {
    matches!(expr, Atom(..) | NotAtom(..))
}

fn is_temporal_literal(expr: &Expr) -> bool {
    match expr {
        Next(body) => is_literal(body),
        _ => is_literal(expr),
    }
}

fn is_disjunctive(expr: &Expr) -> bool {
    match expr {
        True | False | Atom(..) | NotAtom(..) => true,
        Or(left, right) => is_disjunctive(left) && is_disjunctive(right),
        Forall(_, body) | Exists(_, body) => is_disjunctive(body),
        _ => false,
    }
}

fn is_temporal_free(expr: &Expr) -> bool {
    match expr {
        Always(_) | AlwaysP(_) | Sometime(_) | SometimeP(_) | Next(_) | Until(..) | Unless(..) => {
            false
        }
        Not(body) | Forall(_, body) | Exists(_, body) => is_temporal_free(body),
        And(left, right) | Or(left, right) | Implies(left, right) => {
            is_temporal_free(left) && is_temporal_free(right)
        }
        _ => true,
    }
}

/// The names `select` picks from the arguments of the formula's literals, each once, in order of
/// first occurrence from the right (`process`).
fn collect(expr: &Expr, select: &dyn Fn(&Arg) -> Option<&String>) -> Vec<String> {
    match expr {
        True | False => Vec::new(),
        Atom(_, args) | NotAtom(_, args) => args.iter().filter_map(select).cloned().collect(),
        And(left, right)
        | Or(left, right)
        | Implies(left, right)
        | Until(left, right)
        | Unless(left, right) => union(&collect(left, select), &collect(right, select)),
        Not(body) | Always(body) | Sometime(body) | AlwaysP(body) | SometimeP(body)
        | Next(body) => collect(body, select),
        Forall(variables, body) | Exists(variables, body) => {
            except_all(variables, &collect(body, select))
        }
    }
}

fn free_vars(expr: &Expr) -> Vec<String> {
    collect(expr, &|arg| match arg {
        Arg::Variable(name) => Some(name),
        _ => None,
    })
}

fn subst_args(args: &[Arg], from: &Arg, to: &Arg) -> Vec<Arg> {
    args.iter()
        .map(|arg| if arg == from { to.clone() } else { arg.clone() })
        .collect()
}

fn subst(expr: &Expr, from: &Arg, to: &Arg) -> Expr {
    let sub = |body: &Expr| Box::new(subst(body, from, to));
    match expr {
        True => True,
        False => False,
        Atom(name, args) => Atom(name.clone(), subst_args(args, from, to)),
        NotAtom(name, args) => NotAtom(name.clone(), subst_args(args, from, to)),
        And(left, right) => And(sub(left), sub(right)),
        Or(left, right) => Or(sub(left), sub(right)),
        Implies(left, right) => Implies(sub(left), sub(right)),
        Not(body) => Not(sub(body)),
        Forall(variables, body) => Forall(variables.clone(), sub(body)),
        Exists(variables, body) => Exists(variables.clone(), sub(body)),
        Always(body) => Always(sub(body)),
        Sometime(body) => Sometime(sub(body)),
        AlwaysP(body) => AlwaysP(sub(body)),
        SometimeP(body) => SometimeP(sub(body)),
        Next(body) => Next(sub(body)),
        Until(left, right) => Until(sub(left), sub(right)),
        Unless(left, right) => Unless(sub(left), sub(right)),
    }
}

fn nnf(expr: &Expr) -> Expr {
    let sub = |body: &Expr| Box::new(nnf(body));
    match expr {
        True => True,
        False => False,
        Atom(..) | NotAtom(..) => expr.clone(),
        And(left, right) => And(sub(left), sub(right)),
        Or(left, right) => Or(sub(left), sub(right)),
        Implies(left, right) => or(negate(left), nnf(right)),
        Not(body) => negate(body),
        Forall(variables, body) => Forall(variables.clone(), sub(body)),
        Exists(variables, body) => Exists(variables.clone(), sub(body)),
        Always(body) => Always(sub(body)),
        Sometime(body) => Sometime(sub(body)),
        AlwaysP(body) => AlwaysP(sub(body)),
        SometimeP(body) => SometimeP(sub(body)),
        Next(body) => Next(sub(body)),
        Until(left, right) => Until(sub(left), sub(right)),
        Unless(left, right) => Unless(sub(left), sub(right)),
    }
}

fn negate(expr: &Expr) -> Expr {
    let neg = |body: &Expr| Box::new(negate(body));
    match expr {
        True => False,
        False => True,
        Atom(name, args) => NotAtom(name.clone(), args.clone()),
        NotAtom(name, args) => Atom(name.clone(), args.clone()),
        And(left, right) => Or(neg(left), neg(right)),
        Or(left, right) => And(neg(left), neg(right)),
        Implies(left, right) => and(nnf(left), negate(right)),
        Not(body) => nnf(body),
        Forall(variables, body) => Exists(variables.clone(), neg(body)),
        Exists(variables, body) => Forall(variables.clone(), neg(body)),
        Always(body) => Sometime(neg(body)),
        Sometime(body) => Always(neg(body)),
        AlwaysP(body) => SometimeP(neg(body)),
        SometimeP(body) => AlwaysP(neg(body)),
        Next(body) => Next(neg(body)),
        Until(left, right) => unless(negate(right), and(negate(left), negate(right))),
        Unless(left, right) => until(negate(right), and(negate(left), negate(right))),
    }
}

/// The initial formula and the universal, step and eventuality formulas of a DSNF.
type Dsnf = (Expr, Vec<Expr>, Vec<Expr>, Vec<Expr>);

/// The names ptl_to_trp makes up, numbered from one across both kinds, and the subformulas it has
/// renamed, newest first.
#[derive(Default)]
struct Names {
    count: usize,
    seen: Vec<(Expr, Expr)>,
}

impl Names {
    fn new_var(&mut self, name: &str) -> String {
        self.count += 1;
        format!("{name}{}", self.count)
    }

    fn new_literal(&mut self, variables: &[String]) -> Expr {
        let args = variables
            .iter()
            .map(|variable| Arg::Variable(variable.clone()))
            .collect();
        Atom(self.new_var("NVV"), args)
    }

    fn get_seen(&self, expr: &Expr) -> Option<&Expr> {
        self.seen
            .iter()
            .rev()
            .find(|(seen, _)| seen == expr)
            .map(|(_, name)| name)
    }

    fn set_seen(&mut self, expr: Expr, name: Expr) {
        self.seen.push((expr, name));
    }

    /// `always (proposition => formula)`, quantified over the formula's free variables. ptl_to_trp
    /// asserts that the proposition has the same, in the same order.
    fn rename(&self, proposition: &Expr, formula: Expr) -> Option<Expr> {
        let variables = free_vars(&formula);
        if free_vars(proposition) != variables {
            return None;
        }
        let body = or(negate(proposition), formula);
        Some(if variables.is_empty() {
            always(body)
        } else {
            always(Forall(variables, Box::new(body)))
        })
    }

    fn dsnf_wrap(&mut self, expr: &Expr) -> Option<Dsnf> {
        if is_temporal_free(expr) {
            return Some((expr.clone(), Vec::new(), Vec::new(), Vec::new()));
        }
        match expr {
            And(left, right) => {
                let (first, universal1, step1, eventual1) = self.dsnf_wrap(left)?;
                let (second, universal2, step2, eventual2) = self.dsnf_wrap(right)?;
                Some((
                    and(first, second),
                    union(&universal1, &universal2),
                    union(&step1, &step2),
                    union(&eventual1, &eventual2),
                ))
            }
            Always(body) if is_temporal_free(body) => {
                Some((True, vec![(**body).clone()], Vec::new(), Vec::new()))
            }
            Always(body) => match &**body {
                Or(left, right) if is_temporal_literal(left) && is_temporal_literal(right) => {
                    Some((True, Vec::new(), vec![expr.clone()], Vec::new()))
                }
                Forall(_, inner) => match &**inner {
                    Or(left, right) if is_temporal_literal(left) && is_temporal_literal(right) => {
                        Some((
                            True,
                            Vec::new(),
                            vec![always((**inner).clone())],
                            Vec::new(),
                        ))
                    }
                    _ => self.dsnf(expr),
                },
                _ => self.dsnf(expr),
            },
            _ => self.dsnf(expr),
        }
    }

    /// None where ptl_to_trp raises: on a past operator, which its translation has no rule for,
    /// or on a renaming whose free variables differ.
    fn dsnf(&mut self, expr: &Expr) -> Option<Dsnf> {
        if let Some(name) = self.get_seen(expr) {
            return Some((name.clone(), Vec::new(), Vec::new(), Vec::new()));
        }
        if is_disjunctive(expr) {
            return Some((expr.clone(), Vec::new(), Vec::new(), Vec::new()));
        }
        Some(match expr {
            Not(body) => {
                let (initial, universal, step, eventual) = self.dsnf(body)?;
                (Not(Box::new(initial)), universal, step, eventual)
            }
            And(left, right) | Or(left, right) => {
                let (first, universal1, step1, eventual1) = self.dsnf(left)?;
                let (second, universal2, step2, eventual2) = self.dsnf(right)?;
                let initial = if matches!(expr, And(..)) {
                    and(first, second)
                } else {
                    or(first, second)
                };
                (
                    initial,
                    union(&universal1, &universal2),
                    union(&step1, &step2),
                    union(&eventual1, &eventual2),
                )
            }
            Implies(..) => return None,
            Forall(variables, body) | Exists(variables, body) => {
                let (initial, universal, step, eventual) = self.dsnf(body)?;
                let initial = if matches!(expr, Forall(..)) {
                    Forall(variables.clone(), Box::new(initial))
                } else {
                    Exists(variables.clone(), Box::new(initial))
                };
                (initial, universal, step, eventual)
            }
            Always(body) => {
                let name = self.new_literal(&free_vars(body));
                let (initial, mut universal, mut step, eventual) = self.dsnf(body)?;
                self.set_seen(expr.clone(), name.clone());
                universal.insert(0, self.rename(&name, initial)?);
                step.insert(0, self.rename(&name, next(name.clone()))?);
                (name, universal, step, eventual)
            }
            Next(body) => {
                let name = self.new_literal(&free_vars(body));
                let inner = if is_literal(body) {
                    (**body).clone()
                } else {
                    self.new_literal(&free_vars(body))
                };
                let (initial, mut universal, mut step, eventual) = self.dsnf(body)?;
                self.set_seen(expr.clone(), name.clone());
                if !is_literal(body) {
                    universal.insert(0, self.rename(&inner, initial)?);
                }
                step.insert(0, self.rename(&name, next(inner))?);
                (name, universal, step, eventual)
            }
            Sometime(body) => {
                let name = self.new_literal(&free_vars(body));
                let inner = self.new_literal(&free_vars(body));
                let (initial, mut universal, step, mut eventual) = self.dsnf(body)?;
                self.set_seen(expr.clone(), name.clone());
                universal.insert(0, self.rename(&inner, initial)?);
                eventual.insert(0, self.rename(&name, sometime(inner))?);
                (name, universal, step, eventual)
            }
            Until(left, right) | Unless(left, right) => {
                let is_until = matches!(expr, Until(..));
                let make = |left: Expr, right: Expr| {
                    if is_until {
                        until(left, right)
                    } else {
                        unless(left, right)
                    }
                };
                if !is_literal(left) || !is_literal(right) {
                    let name = self.new_literal(&free_vars(expr));
                    let (renamed, other) = if is_literal(left) {
                        (make((**left).clone(), name.clone()), right)
                    } else {
                        (make(name.clone(), (**right).clone()), left)
                    };
                    let (initial, universal, step, eventual) = self.dsnf(&renamed)?;
                    let (initial2, universal2, step2, eventual2) = self.dsnf(other)?;
                    let mut universal = [universal, universal2].concat();
                    universal.insert(0, self.rename(&name, initial2)?);
                    return Some((
                        initial,
                        universal,
                        [step, step2].concat(),
                        [eventual, eventual2].concat(),
                    ));
                }
                let name = self.new_literal(&free_vars(expr));
                let inner = self.new_literal(&free_vars(expr));
                let (_, universal1, step1, eventual1) = self.dsnf(left)?;
                let (_, universal2, step2, eventual2) = self.dsnf(right)?;
                self.set_seen(expr.clone(), name.clone());
                let (left, right) = ((**left).clone(), (**right).clone());
                let universal = [
                    vec![
                        self.rename(&name, or(left.clone(), right.clone()))?,
                        self.rename(&name, or(right.clone(), inner.clone()))?,
                    ],
                    union(&universal1, &universal2),
                ]
                .concat();
                let step = [
                    vec![
                        self.rename(&inner, next(or(left, right.clone())))?,
                        self.rename(&inner, next(or(inner.clone(), right.clone())))?,
                    ],
                    union(&step1, &step2),
                ]
                .concat();
                let mut eventual = union(&eventual1, &eventual2);
                if is_until {
                    eventual.insert(0, self.rename(&name, sometime(right))?);
                }
                (name, universal, step, eventual)
            }
            _ => return None,
        })
    }

    /// Skolemizes the existential variables and drops the universal ones. None where a formula
    /// ptl_to_trp's rule doesn't cover remains.
    fn eliminate_quantifiers(&mut self, expr: &Expr, free: &[String]) -> Option<Expr> {
        Some(match expr {
            True | False | Atom(..) | NotAtom(..) => expr.clone(),
            And(left, right) => and(
                self.eliminate_quantifiers(left, free)?,
                self.eliminate_quantifiers(right, free)?,
            ),
            Or(left, right) => or(
                self.eliminate_quantifiers(left, free)?,
                self.eliminate_quantifiers(right, free)?,
            ),
            Forall(variables, body) => self.eliminate_quantifiers(body, &union(variables, free))?,
            Exists(variables, body) => {
                let body = self.eliminate_quantifiers(body, free)?;
                self.introduce_skolems(variables, body, free)
            }
            Next(body) => next(self.eliminate_quantifiers(body, free)?),
            Sometime(body) => sometime(self.eliminate_quantifiers(body, free)?),
            Always(body) => always(self.eliminate_quantifiers(body, free)?),
            _ => return None,
        })
    }

    fn introduce_skolems(&mut self, variables: &[String], expr: Expr, free: &[String]) -> Expr {
        let Some((variable, rest)) = variables.split_first() else {
            return expr;
        };
        let skolem = Arg::Skolem(self.new_var("skolem"), free.to_vec());
        let inner = self.introduce_skolems(rest, expr, free);
        subst(&inner, &Arg::Variable(variable.clone()), &skolem)
    }
}

fn cnf(expr: &Expr) -> Expr {
    match expr {
        Or(left, right) => cnf_distribute(or(cnf(left), cnf(right))),
        And(left, right) => and(cnf(left), cnf(right)),
        Always(body) => always(cnf(body)),
        _ => expr.clone(),
    }
}

fn cnf_distribute(expr: Expr) -> Expr {
    match expr {
        Or(left, right) => match (*left, *right) {
            (left, And(inner_left, inner_right)) => and(
                cnf_distribute(or(left.clone(), *inner_left)),
                cnf_distribute(or(left, *inner_right)),
            ),
            (And(inner_left, inner_right), right) => and(
                cnf_distribute(or(*inner_left, right.clone())),
                cnf_distribute(or(*inner_right, right)),
            ),
            (left, right) => or(left, right),
        },
        _ => expr,
    }
}

type Clause = Vec<Expr>;

/// None where a formula ptl_to_trp's rule doesn't cover remains.
fn clausify(expr: &Expr) -> Option<Vec<Clause>> {
    Some(match expr {
        Always(body) => clausify(body)?,
        And(left, right) => union(&clausify(left)?, &clausify(right)?),
        Or(..) => vec![clausify_disjunction(expr)],
        True => Vec::new(),
        False => vec![Vec::new()],
        Atom(..) | NotAtom(..) => vec![vec![expr.clone()]],
        _ => return None,
    })
}

fn clausify_disjunction(expr: &Expr) -> Clause {
    match expr {
        Next(body) => clausify_next(body),
        Or(left, right) => union(&clausify_disjunction(left), &clausify_disjunction(right)),
        _ => vec![expr.clone()],
    }
}

fn clausify_next(expr: &Expr) -> Clause {
    match expr {
        Or(left, right) => union(&clausify_next(left), &clausify_next(right)),
        _ => vec![next(expr.clone())],
    }
}

fn clausify_all(exprs: &[Expr]) -> Option<Vec<Clause>> {
    let mut clauses = Vec::new();
    for expr in exprs.iter().rev() {
        clauses = union(&clausify(expr)?, &clauses);
    }
    Some(clauses)
}

fn write_args(out: &mut String, args: &[Arg]) {
    for (index, arg) in args.iter().enumerate() {
        if index > 0 {
            out.push_str(", ");
        }
        match arg {
            Arg::Variable(name) | Arg::Constant(name) => out.push_str(name),
            Arg::Skolem(name, variables) => {
                out.push_str(name);
                if !variables.is_empty() {
                    write!(out, "({})", variables.join(", ")).expect("a string");
                }
            }
        }
    }
}

fn write_expr(out: &mut String, expr: &Expr) {
    match expr {
        True => out.push_str("True"),
        False => out.push_str("False"),
        Atom(name, args) | NotAtom(name, args) => {
            if matches!(expr, NotAtom(..)) {
                out.push_str("not ");
            }
            out.push_str(name);
            if !args.is_empty() {
                out.push('(');
                write_args(out, args);
                out.push(')');
            }
        }
        And(left, right)
        | Or(left, right)
        | Implies(left, right)
        | Until(left, right)
        | Unless(left, right) => {
            let operator = match expr {
                And(..) => " & ",
                Or(..) => " | ",
                Implies(..) => " => ",
                Until(..) => " until ",
                _ => " unless ",
            };
            out.push('(');
            write_expr(out, left);
            out.push_str(operator);
            write_expr(out, right);
            out.push(')');
        }
        Not(body) => {
            out.push_str("not (");
            write_expr(out, body);
            out.push(')');
        }
        Forall(variables, body) | Exists(variables, body) => {
            let quantifier = if matches!(expr, Forall(..)) { '!' } else { '?' };
            write!(out, "{quantifier}[{}](", variables.join(", ")).expect("a string");
            write_expr(out, body);
            out.push(')');
        }
        Always(body) | AlwaysP(body) | Sometime(body) | SometimeP(body) | Next(body) => {
            let operator = match expr {
                Always(_) => "always",
                AlwaysP(_) => "alwaysp",
                Sometime(_) => "sometime",
                SometimeP(_) => "sometimep",
                _ => "next",
            };
            out.push_str(operator);
            out.push('(');
            write_expr(out, body);
            out.push(')');
        }
    }
}

fn write_clauses(clauses: &[Clause], prefix: &str, suffix: &str) -> String {
    let mut out = String::new();
    for (index, clause) in clauses.iter().enumerate() {
        if index > 0 {
            out.push_str(", \n");
        }
        out.push_str(prefix);
        for (position, literal) in clause.iter().enumerate() {
            if position > 0 {
                out.push_str(", ");
            }
            write_expr(&mut out, literal);
        }
        out.push_str(suffix);
    }
    out
}

/// What `ptl_to_trp -i file` prints for the text, or None where it prints no clause set: its
/// lexer or parser stops, or its translation raises.
pub fn translate(text: &[u8]) -> Option<String> {
    let formula = nnf(&parse(text)?);
    let mut names = Names::default();
    let (initial, universal, step, eventual) = names.dsnf_wrap(&formula)?;
    let initial = cnf(&names.eliminate_quantifiers(&initial, &[])?);
    let mut eliminated = |exprs: &[Expr]| -> Option<Vec<Expr>> {
        exprs
            .iter()
            .map(|expr| names.eliminate_quantifiers(expr, &[]))
            .collect()
    };
    let universal: Vec<Expr> = eliminated(&universal)?.iter().map(cnf).collect();
    let step = eliminated(&step)?;
    let eventual = eliminated(&eventual)?;
    let initial_text = write_clauses(&clausify(&initial)?, "or([", "])");
    let universal_text = write_clauses(&clausify_all(&universal)?, "always(or([", "]))");
    let step_text = write_clauses(&clausify_all(&step)?, "always(or([", "]))");
    let eventual_text = write_clauses(&clausify_all(&eventual)?, "always(or([", "]))");
    let mut out = String::from("and([\n");
    out.push_str(&initial_text);
    if !universal_text.is_empty() && !initial_text.is_empty() {
        out.push_str(",\n");
    }
    out.push_str(&universal_text);
    if !step_text.is_empty() && !(universal_text.is_empty() && initial_text.is_empty()) {
        out.push_str(",\n");
    }
    out.push_str(&step_text);
    if !eventual_text.is_empty() {
        out.push_str(",\n");
    }
    out.push_str(&eventual_text);
    out.push_str("]).\n\n");
    Some(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reads_the_grammar_with_its_precedences() {
        let text = |text: &str| {
            let mut out = String::new();
            write_expr(&mut out, &parse(text.as_bytes()).expect("a formula"));
            out
        };
        assert_eq!(text("a | b -> c"), "(a | (b => c))");
        assert_eq!(text("a -> b -> c"), "((a => b) => c)");
        assert_eq!(text("~ p & q"), "(not (p) & q)");
        assert_eq!(text("always p & q"), "(always(p) & q)");
        assert_eq!(text("p until q & r"), "(p until (q & r))");
        assert_eq!(text("alwaysp p & ~p"), "alwaysp((p & not (p)))");
        assert_eq!(text("p <=> q"), "((p => q) & (q => p))");
        assert_eq!(text("! [X] p(X) & q"), "(![X](p(X)) & q)");
        assert_eq!(text("p(a, b) ; a comment\n& True"), "(p(a, b) & True)");
    }

    #[test]
    fn stops_where_ptl_to_trp_stops() {
        for text in [
            "(p & ~p",
            "[]p",
            "skolem & ~skolem",
            "NVV1",
            "! [x] p(x)",
            "p (q & r)",
            "p q",
            "",
            "p \u{a0} q",
        ] {
            assert_eq!(parse(text.as_bytes()), None, "{text}");
        }
        assert_eq!(translate(b"alwaysp p & ~p"), None);
        assert_eq!(translate(b"sometimep p"), None);
    }

    #[test]
    fn prints_the_clause_set_ptl_to_trp_prints() {
        assert_eq!(
            translate(b"sometime False").expect("a clause set"),
            "and([\nor([NVV1]),\nalways(or([not NVV2, False])),\nalways(or([not NVV1, sometime(NVV2)]))]).\n\n"
        );
        assert_eq!(
            translate(b"False").expect("a clause set"),
            "and([\nor([])]).\n\n"
        );
        assert_eq!(translate(b"True").expect("a clause set"), "and([\n]).\n\n");
        assert_eq!(
            translate(b"always (p | next q)").expect("a clause set"),
            "and([\nalways(or([p, next(q)]))]).\n\n"
        );
        assert_eq!(
            translate(b"? [X] p(X)").expect("a clause set"),
            "and([\nor([p(skolem1)])]).\n\n"
        );
    }
}
