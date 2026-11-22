//! A port of tlapm's `translate` (`ptl_to_trp`, `translate/` at b91fb6c), which turns the formula
//! tlapm writes for LS4 into the clauses LS4 reads: the lexer (`folex.mll`), the grammar
//! (`foyacc.mly`, with ocamlyacc's precedences) and the translation (`fofunctions.ml`, `main.ml`) as
//! `ptl_to_trp -i file` runs it: no simplification, no renaming to CNF, and no first-order
//! treatment of constants, which only the `fo` names get.

use std::fmt::Write;

/// An atom's argument (`Fotypes.arg`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Arg {
    Variable(String),
    Constant(String),
    Skolem(String, Vec<String>),
}

/// `Fotypes.formula`, with a literal's two cases as variants of their own.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Formula {
    True,
    False,
    Atom(String, Vec<Arg>),
    NotAtom(String, Vec<Arg>),
    And(Box<Formula>, Box<Formula>),
    Or(Box<Formula>, Box<Formula>),
    Implies(Box<Formula>, Box<Formula>),
    Not(Box<Formula>),
    Forall(Vec<String>, Box<Formula>),
    Exists(Vec<String>, Box<Formula>),
    Always(Box<Formula>),
    AlwaysP(Box<Formula>),
    Sometime(Box<Formula>),
    SometimeP(Box<Formula>),
    Next(Box<Formula>),
    Until(Box<Formula>, Box<Formula>),
    Unless(Box<Formula>, Box<Formula>),
}

use Formula::*;

/// Why `ptl_to_trp` writes LS4 no clauses: a parse error, which `main.ml` catches and prints in
/// the clauses' place, or an exception it doesn't catch, which ends it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Failure(pub String);

/// The clause sets `main.ml` prints, each clause a list of literals, which may be `next` or
/// `sometime` of one, or a constant printed as its name.
#[derive(Debug, Default, PartialEq, Eq)]
pub struct Clauses {
    pub initial: Vec<Vec<Formula>>,
    pub universal: Vec<Vec<Formula>>,
    pub step: Vec<Vec<Formula>>,
    pub eventuality: Vec<Vec<Formula>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Token {
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
    Ident(String),
    Eof,
}

fn parse_error(message: &str) -> Failure {
    Failure(format!("Parse error: {message}"))
}

/// `folex.mll`: a keyword wins over the identifier of the same text, and a longer identifier over
/// a keyword it starts with. Anything the rules don't name, such as a digit or `=` alone, is an
/// error, as is a reserved word.
fn tokenize(text: &str) -> Result<Vec<Token>, Failure> {
    let bytes = text.as_bytes();
    let mut tokens = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        let byte = bytes[i];
        let token = match byte {
            b' ' | b'\t' | b'\r' | b'\n' => {
                i += 1;
                continue;
            }
            b';' => {
                while i < bytes.len() && bytes[i] != b'\n' {
                    i += 1;
                }
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
            b'=' | b'-' if bytes.get(i + 1) == Some(&b'>') => {
                i += 1;
                Token::Impl
            }
            b'<' if matches!(bytes.get(i + 1), Some(b'=' | b'-'))
                && bytes.get(i + 2) == Some(&b'>') =>
            {
                i += 2;
                Token::Equiv
            }
            _ if byte.is_ascii_alphabetic() => {
                let start = i;
                while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                    i += 1;
                }
                let word = &text[start..i];
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
                    "skolem" | "hidden" | "constant" => {
                        return Err(parse_error(&format!("{word} is a reserved word")));
                    }
                    _ if word.starts_with("NV_V") || word.starts_with("NVV") => {
                        return Err(parse_error(&format!(
                            "{word} cannot start any word: reserved"
                        )));
                    }
                    _ => Token::Ident(word.to_owned()),
                });
                continue;
            }
            _ => {
                return Err(parse_error(&format!(
                    "unexpected character {:?}",
                    byte as char
                )));
            }
        };
        tokens.push(token);
        i += 1;
    }
    tokens.push(Token::Eof);
    Ok(tokens)
}

/// `foyacc.mly`, as ocamlyacc parses it: the binary operators left associative at the levels
/// `%left` declares (`until` below `unless`, `<->`, `|`, `->` and `&`), each prefix operator and
/// quantifier above them, except `alwaysp` and `sometimep`, which have no precedence, so their
/// body extends as far as it can, since ocamlyacc shifts on the conflict.
struct Parser {
    tokens: Vec<Token>,
    position: usize,
}

impl Parser {
    fn peek(&self) -> &Token {
        &self.tokens[self.position]
    }

    fn take(&mut self) -> Token {
        let token = self.tokens[self.position].clone();
        if self.position + 1 < self.tokens.len() {
            self.position += 1;
        }
        token
    }

    fn expect(&mut self, token: Token) -> Result<(), Failure> {
        if *self.peek() == token {
            self.take();
            Ok(())
        } else {
            Err(parse_error(&format!(
                "expected {token:?}, found {:?}",
                self.peek()
            )))
        }
    }

    fn ident(&mut self) -> Result<String, Failure> {
        match self.take() {
            Token::Ident(name) => Ok(name),
            token => Err(parse_error(&format!(
                "expected an identifier, found {token:?}"
            ))),
        }
    }

    fn binary_level(token: &Token) -> Option<u8> {
        Some(match token {
            Token::Until => 1,
            Token::Unless => 2,
            Token::Equiv => 3,
            Token::Disj => 4,
            Token::Impl => 5,
            Token::Conj => 6,
            _ => return None,
        })
    }

    fn formula(&mut self, min_level: u8) -> Result<Formula, Failure> {
        let mut left = self.prefix()?;
        while let Some(level) = Self::binary_level(self.peek()).filter(|&level| level >= min_level)
        {
            let operator = self.take();
            let right = self.formula(level + 1)?;
            let (left_box, right_box) = (Box::new(left), Box::new(right));
            left = match operator {
                Token::Until => Until(left_box, right_box),
                Token::Unless => Unless(left_box, right_box),
                Token::Equiv => And(
                    Box::new(Implies(left_box.clone(), right_box.clone())),
                    Box::new(Implies(right_box, left_box)),
                ),
                Token::Disj => Or(left_box, right_box),
                Token::Impl => Implies(left_box, right_box),
                _ => And(left_box, right_box),
            };
        }
        Ok(left)
    }

    fn prefix(&mut self) -> Result<Formula, Failure> {
        Ok(match self.take() {
            Token::Ident(name) => {
                let mut args = Vec::new();
                if *self.peek() == Token::LPar {
                    self.take();
                    loop {
                        args.push(Arg::Constant(self.ident()?));
                        if *self.peek() != Token::Comma {
                            break;
                        }
                        self.take();
                    }
                    self.expect(Token::RPar)?;
                }
                Atom(name, args)
            }
            Token::True => True,
            Token::False => False,
            Token::Not => Not(Box::new(self.prefix()?)),
            Token::Always => Always(Box::new(self.prefix()?)),
            Token::Sometime => Sometime(Box::new(self.prefix()?)),
            Token::Next => Next(Box::new(self.prefix()?)),
            Token::AlwaysP => AlwaysP(Box::new(self.formula(1)?)),
            Token::SometimeP => SometimeP(Box::new(self.formula(1)?)),
            quantifier @ (Token::Forall | Token::Exists) => {
                self.expect(Token::LBracket)?;
                let mut names = vec![self.ident()?];
                while *self.peek() == Token::Comma {
                    self.take();
                    names.push(self.ident()?);
                }
                // The grammar checks the case of the list's last name only.
                let last = names.last().expect("a name");
                if !last.starts_with(|c: char| c.is_ascii_uppercase()) {
                    return Err(parse_error(&format!("{last} is not uppercase")));
                }
                self.expect(Token::RBracket)?;
                let mut body = self.prefix()?;
                for name in &names {
                    body = subst(
                        &body,
                        &Arg::Constant(name.clone()),
                        &Arg::Variable(name.clone()),
                    );
                }
                if quantifier == Token::Forall {
                    Forall(names, Box::new(body))
                } else {
                    Exists(names, Box::new(body))
                }
            }
            Token::LPar => {
                let inner = self.formula(1)?;
                self.expect(Token::RPar)?;
                inner
            }
            token => return Err(parse_error(&format!("unexpected {token:?}"))),
        })
    }
}

fn parse(text: &str) -> Result<Formula, Failure> {
    let mut parser = Parser {
        tokens: tokenize(text)?,
        position: 0,
    };
    let formula = parser.formula(1)?;
    parser.expect(Token::Eof)?;
    Ok(formula)
}

fn subst_args(args: &[Arg], var: &Arg, sk: &Arg) -> Vec<Arg> {
    args.iter()
        .map(|arg| if arg == var { sk.clone() } else { arg.clone() })
        .collect()
}

/// `Fofunctions.subst`: the argument `var` replaced by `sk` in every atom.
fn subst(f: &Formula, var: &Arg, sk: &Arg) -> Formula {
    let go = |g: &Formula| Box::new(subst(g, var, sk));
    match f {
        True => True,
        False => False,
        Atom(a, args) => Atom(a.clone(), subst_args(args, var, sk)),
        NotAtom(a, args) => NotAtom(a.clone(), subst_args(args, var, sk)),
        And(f, g) => And(go(f), go(g)),
        Or(f, g) => Or(go(f), go(g)),
        Implies(f, g) => Implies(go(f), go(g)),
        Not(f) => Not(go(f)),
        Forall(v, f) => Forall(v.clone(), go(f)),
        Exists(v, f) => Exists(v.clone(), go(f)),
        Always(f) => Always(go(f)),
        AlwaysP(f) => AlwaysP(go(f)),
        Sometime(f) => Sometime(go(f)),
        SometimeP(f) => SometimeP(go(f)),
        Next(f) => Next(go(f)),
        Until(f, g) => Until(go(f), go(g)),
        Unless(f, g) => Unless(go(f), go(g)),
    }
}

/// `Fofunctions.union`: the elements of `l1` not in `l2`, in order, before `l2`.
fn union<T: PartialEq + Clone>(l1: &[T], l2: &[T]) -> Vec<T> {
    let mut result: Vec<T> = l1.iter().filter(|e| !l2.contains(e)).cloned().collect();
    result.extend(l2.iter().cloned());
    result
}

fn except_all<T: PartialEq + Clone>(exceptions: &[T], list: &[T]) -> Vec<T> {
    // `exceptL` removes each exception's first occurrence, innermost first.
    let mut result = list.to_vec();
    for e in exceptions.iter().rev() {
        if let Some(position) = result.iter().position(|x| x == e) {
            result.remove(position);
        }
    }
    result
}

/// `Fofunctions.freeVars`: the variables of the atoms' arguments, less the bound ones.
fn free_vars(f: &Formula) -> Vec<String> {
    match f {
        True | False => Vec::new(),
        Atom(_, args) | NotAtom(_, args) => args
            .iter()
            .filter_map(|arg| match arg {
                Arg::Variable(x) => Some(x.clone()),
                _ => None,
            })
            .collect(),
        And(f, g) | Or(f, g) | Implies(f, g) | Until(f, g) | Unless(f, g) => {
            union(&free_vars(f), &free_vars(g))
        }
        Not(f) | Always(f) | Sometime(f) | AlwaysP(f) | SometimeP(f) | Next(f) => free_vars(f),
        Forall(v, f) | Exists(v, f) => except_all(v, &free_vars(f)),
    }
}

fn is_literal(f: &Formula) -> bool {
    matches!(f, Atom(..) | NotAtom(..))
}

fn is_temporal_literal(f: &Formula) -> bool {
    match f {
        Next(inner) => is_literal(inner),
        _ => is_literal(f),
    }
}

/// `isDisjunctive`: a truth constant, a literal, or a disjunction of such, under quantifiers.
fn is_disjunctive(f: &Formula) -> bool {
    match f {
        True | False => true,
        Or(f, g) => is_disjunctive(f) && is_disjunctive(g),
        Forall(_, f) | Exists(_, f) => is_disjunctive(f),
        _ => is_literal(f),
    }
}

fn is_temporal(f: &Formula) -> bool {
    matches!(
        f,
        Always(_) | AlwaysP(_) | Sometime(_) | SometimeP(_) | Next(_) | Until(..) | Unless(..)
    )
}

fn is_temporal_free(f: &Formula) -> bool {
    if is_temporal(f) {
        return false;
    }
    match f {
        Not(f) | Forall(_, f) | Exists(_, f) => is_temporal_free(f),
        And(f, g) | Or(f, g) | Implies(f, g) => is_temporal_free(f) && is_temporal_free(g),
        _ => true,
    }
}

/// `Fofunctions.nnf`: implications and negations pushed to the literals.
fn nnf(f: &Formula) -> Formula {
    let go = |g: &Formula| Box::new(nnf(g));
    match f {
        True | False | Atom(..) | NotAtom(..) => f.clone(),
        And(f, g) => And(go(f), go(g)),
        Or(f, g) => Or(go(f), go(g)),
        Implies(f, g) => Or(Box::new(negate(f)), go(g)),
        Not(f) => negate(f),
        Forall(v, f) => Forall(v.clone(), go(f)),
        Exists(v, f) => Exists(v.clone(), go(f)),
        Always(f) => Always(go(f)),
        Sometime(f) => Sometime(go(f)),
        AlwaysP(f) => AlwaysP(go(f)),
        SometimeP(f) => SometimeP(go(f)),
        Next(f) => Next(go(f)),
        Until(f, g) => Until(go(f), go(g)),
        Unless(f, g) => Unless(go(f), go(g)),
    }
}

fn negate(f: &Formula) -> Formula {
    let neg = |g: &Formula| Box::new(negate(g));
    match f {
        True => False,
        False => True,
        Atom(a, args) => NotAtom(a.clone(), args.clone()),
        NotAtom(a, args) => Atom(a.clone(), args.clone()),
        And(f, g) => Or(neg(f), neg(g)),
        Or(f, g) => And(neg(f), neg(g)),
        Implies(f, g) => And(Box::new(nnf(f)), neg(g)),
        Not(f) => nnf(f),
        Forall(v, f) => Exists(v.clone(), neg(f)),
        Exists(v, f) => Forall(v.clone(), neg(f)),
        Always(f) => Sometime(neg(f)),
        Sometime(f) => Always(neg(f)),
        AlwaysP(f) => SometimeP(neg(f)),
        SometimeP(f) => AlwaysP(neg(f)),
        Next(f) => Next(neg(f)),
        Until(f, g) => Unless(neg(g), Box::new(And(neg(f), neg(g)))),
        Unless(f, g) => Until(neg(g), Box::new(And(neg(f), neg(g)))),
    }
}

/// The initial part, the universal, step and eventuality parts of a formula's DSNF.
type Dsnf = (Formula, Vec<Formula>, Vec<Formula>, Vec<Formula>);

/// The translation's state: the counter new names take, and the formulas renamed so far with
/// their names (`seenList`), so that the same subformula is named once.
#[derive(Default)]
struct Translator {
    count: u32,
    seen: Vec<(Formula, Formula)>,
}

impl Translator {
    fn new_var(&mut self, name: &str) -> String {
        self.count += 1;
        format!("{name}{}", self.count)
    }

    fn new_literal(&mut self, vars: &[String]) -> Formula {
        let name = self.new_var("NVV");
        Atom(
            name,
            vars.iter().map(|v| Arg::Variable(v.clone())).collect(),
        )
    }

    fn get_seen(&self, f: &Formula) -> Option<Formula> {
        self.seen
            .iter()
            .find(|(seen, _)| seen == f)
            .map(|(_, name)| name.clone())
    }

    fn set_seen(&mut self, f: Formula, name: Formula) {
        self.seen.insert(0, (f, name));
    }

    /// `rename`: `always (proposition => formula)`, universally quantified over the free variables.
    fn rename(proposition: &Formula, formula: &Formula) -> Formula {
        let vars = free_vars(formula);
        let body = Or(Box::new(negate(proposition)), Box::new(formula.clone()));
        if vars.is_empty() {
            Always(Box::new(body))
        } else {
            Always(Box::new(Forall(vars, Box::new(body))))
        }
    }

    fn dsnf_wrap(&mut self, form: &Formula) -> Result<Dsnf, Failure> {
        if is_temporal_free(form) {
            return Ok((form.clone(), Vec::new(), Vec::new(), Vec::new()));
        }
        match form {
            And(x, y) => {
                let (ip1, up1, sp1, ep1) = self.dsnf_wrap(x)?;
                let (ip2, up2, sp2, ep2) = self.dsnf_wrap(y)?;
                Ok((
                    And(Box::new(ip1), Box::new(ip2)),
                    union(&up1, &up2),
                    union(&sp1, &sp2),
                    union(&ep1, &ep2),
                ))
            }
            Always(f) if is_temporal_free(f) => {
                Ok((True, vec![(**f).clone()], Vec::new(), Vec::new()))
            }
            // A step clause in the input is kept as one.
            Always(f) => {
                let clause = match &**f {
                    Or(lhs, rhs) => Some((lhs, rhs)),
                    Forall(_, inner) => match &**inner {
                        Or(lhs, rhs) => Some((lhs, rhs)),
                        _ => None,
                    },
                    _ => None,
                };
                match clause {
                    Some((lhs, rhs)) if is_temporal_literal(lhs) && is_temporal_literal(rhs) => {
                        Ok((
                            True,
                            Vec::new(),
                            vec![Always(Box::new(Or(lhs.clone(), rhs.clone())))],
                            Vec::new(),
                        ))
                    }
                    _ => self.dsnf(form),
                }
            }
            _ => self.dsnf(form),
        }
    }

    fn dsnf(&mut self, form: &Formula) -> Result<Dsnf, Failure> {
        if let Some(name) = self.get_seen(form) {
            return Ok((name, Vec::new(), Vec::new(), Vec::new()));
        }
        if is_disjunctive(form) {
            return Ok((form.clone(), Vec::new(), Vec::new(), Vec::new()));
        }
        match form {
            Not(x) => {
                let (ip, up, sp, ep) = self.dsnf(x)?;
                Ok((Not(Box::new(ip)), up, sp, ep))
            }
            And(x, y) => {
                let (ip1, up1, sp1, ep1) = self.dsnf(x)?;
                let (ip2, up2, sp2, ep2) = self.dsnf(y)?;
                Ok((
                    And(Box::new(ip1), Box::new(ip2)),
                    union(&up1, &up2),
                    union(&sp1, &sp2),
                    union(&ep1, &ep2),
                ))
            }
            Or(f, g) => {
                let (ip1, up1, sp1, ep1) = self.dsnf(f)?;
                let (ip2, up2, sp2, ep2) = self.dsnf(g)?;
                Ok((
                    Or(Box::new(ip1), Box::new(ip2)),
                    union(&up1, &up2),
                    union(&sp1, &sp2),
                    union(&ep1, &ep2),
                ))
            }
            Implies(..) => Err(Failure("Fofunctions.Illegal7".into())),
            Forall(v, y) => {
                let (ip, up, sp, ep) = self.dsnf(y)?;
                Ok((Forall(v.clone(), Box::new(ip)), up, sp, ep))
            }
            Exists(v, y) => {
                let (ip, up, sp, ep) = self.dsnf(y)?;
                Ok((Exists(v.clone(), Box::new(ip)), up, sp, ep))
            }
            Always(f) => {
                let new_p = self.new_literal(&free_vars(f));
                let (ip, mut up, mut sp, ep) = self.dsnf(f)?;
                self.set_seen(form.clone(), new_p.clone());
                up.insert(0, Self::rename(&new_p, &ip));
                sp.insert(0, Self::rename(&new_p, &Next(Box::new(new_p.clone()))));
                Ok((new_p, up, sp, ep))
            }
            Next(f) => {
                let new_p = self.new_literal(&free_vars(f));
                let new_q = if is_literal(f) {
                    (**f).clone()
                } else {
                    self.new_literal(&free_vars(f))
                };
                let (ip, mut up, mut sp, ep) = self.dsnf(f)?;
                self.set_seen(form.clone(), new_p.clone());
                if !is_literal(f) {
                    up.insert(0, Self::rename(&new_q, &ip));
                }
                sp.insert(0, Self::rename(&new_p, &Next(Box::new(new_q))));
                Ok((new_p, up, sp, ep))
            }
            Sometime(f) => {
                let new_p = self.new_literal(&free_vars(f));
                let new_q = self.new_literal(&free_vars(f));
                let (ip, mut up, sp, mut ep) = self.dsnf(f)?;
                self.set_seen(form.clone(), new_p.clone());
                up.insert(0, Self::rename(&new_q, &ip));
                ep.insert(0, Self::rename(&new_p, &Sometime(Box::new(new_q))));
                Ok((new_p, up, sp, ep))
            }
            Until(f, g) | Unless(f, g) => {
                let is_until = matches!(form, Until(..));
                let make = |f: Formula, g: Formula| {
                    if is_until {
                        Until(Box::new(f), Box::new(g))
                    } else {
                        Unless(Box::new(f), Box::new(g))
                    }
                };
                if !is_literal(f) {
                    let new_p = self.new_literal(&free_vars(form));
                    let (ip, up, sp, ep) = self.dsnf(&make(new_p.clone(), (**g).clone()))?;
                    let (ip2, up2, sp2, ep2) = self.dsnf(f)?;
                    let mut universal = vec![Self::rename(&new_p, &ip2)];
                    universal.extend(up);
                    universal.extend(up2);
                    return Ok((ip, universal, [sp, sp2].concat(), [ep, ep2].concat()));
                }
                if !is_literal(g) {
                    let new_q = self.new_literal(&free_vars(form));
                    let (ip, up, sp, ep) = self.dsnf(&make((**f).clone(), new_q.clone()))?;
                    let (ip2, up2, sp2, ep2) = self.dsnf(g)?;
                    let mut universal = vec![Self::rename(&new_q, &ip2)];
                    universal.extend(up);
                    universal.extend(up2);
                    return Ok((ip, universal, [sp, sp2].concat(), [ep, ep2].concat()));
                }
                let new_p = self.new_literal(&free_vars(form));
                let new_q = self.new_literal(&free_vars(form));
                let (_, up1, sp1, ep1) = self.dsnf(f)?;
                let (_, up2, sp2, ep2) = self.dsnf(g)?;
                self.set_seen(form.clone(), new_p.clone());
                let f_or_g = Or(f.clone(), g.clone());
                let mut universal = vec![
                    Self::rename(&new_p, &f_or_g),
                    Self::rename(&new_p, &Or(g.clone(), Box::new(new_q.clone()))),
                ];
                universal.extend(union(&up1, &up2));
                let mut step = vec![
                    Self::rename(&new_q, &Next(Box::new(f_or_g))),
                    Self::rename(
                        &new_q,
                        &Next(Box::new(Or(Box::new(new_q.clone()), g.clone()))),
                    ),
                ];
                step.extend(union(&sp1, &sp2));
                let mut eventuality = union(&ep1, &ep2);
                if is_until {
                    eventuality.insert(0, Self::rename(&new_p, &Sometime(g.clone())));
                }
                Ok((new_p, universal, step, eventuality))
            }
            _ => Err(Failure("Fofunctions.Illegal1".into())),
        }
    }

    /// `eliminateQ`: universal quantifiers dropped, existential ones Skolemized over the free
    /// variables, on a formula in NNF.
    fn eliminate_quantifiers(
        &mut self,
        form: &Formula,
        free: &[String],
    ) -> Result<Formula, Failure> {
        Ok(match form {
            True | False | Atom(..) | NotAtom(..) => form.clone(),
            And(f, g) => And(
                Box::new(self.eliminate_quantifiers(f, free)?),
                Box::new(self.eliminate_quantifiers(g, free)?),
            ),
            Or(f, g) => Or(
                Box::new(self.eliminate_quantifiers(f, free)?),
                Box::new(self.eliminate_quantifiers(g, free)?),
            ),
            Forall(v, f) => self.eliminate_quantifiers(f, &union(v, free))?,
            Exists(v, f) => {
                let inner = self.eliminate_quantifiers(f, free)?;
                self.introduce_skolem(v, inner, free)
            }
            Next(f) => Next(Box::new(self.eliminate_quantifiers(f, free)?)),
            Sometime(f) => Sometime(Box::new(self.eliminate_quantifiers(f, free)?)),
            Always(f) => Always(Box::new(self.eliminate_quantifiers(f, free)?)),
            _ => return Err(Failure("Fofunctions.Illegal2".into())),
        })
    }

    fn introduce_skolem(&mut self, vars: &[String], form: Formula, free: &[String]) -> Formula {
        let Some((v, rest)) = vars.split_first() else {
            return form;
        };
        let skolem = Arg::Skolem(self.new_var("skolem"), free.to_vec());
        let inner = self.introduce_skolem(rest, form, free);
        subst(&inner, &Arg::Variable(v.clone()), &skolem)
    }
}

/// `cnf`: disjunctions distributed over conjunctions, under a leading `always`.
fn cnf(f: &Formula) -> Formula {
    match f {
        Or(f, g) => cnf_aux(Or(Box::new(cnf(f)), Box::new(cnf(g)))),
        And(f, g) => And(Box::new(cnf(f)), Box::new(cnf(g))),
        Always(f) => Always(Box::new(cnf(f))),
        _ => f.clone(),
    }
}

fn cnf_aux(f: Formula) -> Formula {
    match f {
        Or(f, g) => match (*f, *g) {
            (f, And(g, h)) => And(
                Box::new(cnf_aux(Or(Box::new(f.clone()), g))),
                Box::new(cnf_aux(Or(Box::new(f), h))),
            ),
            (And(f, g), h) => And(
                Box::new(cnf_aux(Or(f, Box::new(h.clone())))),
                Box::new(cnf_aux(Or(g, Box::new(h)))),
            ),
            (f, g) => Or(Box::new(f), Box::new(g)),
        },
        other => other,
    }
}

/// `clausify`: a formula in CNF as its clauses, each a list of literals.
fn clausify(f: &Formula) -> Result<Vec<Vec<Formula>>, Failure> {
    Ok(match f {
        Always(f) => clausify(f)?,
        And(f, g) => union(&clausify(f)?, &clausify(g)?),
        Or(..) => vec![clausify_aux(f)],
        True => Vec::new(),
        False => vec![Vec::new()],
        Atom(..) | NotAtom(..) => vec![vec![f.clone()]],
        _ => return Err(Failure("Fofunctions.Illegal3".into())),
    })
}

fn clausify_aux(f: &Formula) -> Vec<Formula> {
    match f {
        Next(f) => clausify_aux2(f),
        Or(f, g) => union(&clausify_aux(f), &clausify_aux(g)),
        _ => vec![f.clone()],
    }
}

fn clausify_aux2(f: &Formula) -> Vec<Formula> {
    match f {
        Or(f, g) => union(&clausify_aux2(f), &clausify_aux2(g)),
        _ => vec![Next(Box::new(f.clone()))],
    }
}

fn clausify_all(formulas: &[Formula]) -> Result<Vec<Vec<Formula>>, Failure> {
    let mut clauses = Vec::new();
    for f in formulas.iter().rev() {
        clauses = union(&clausify(f)?, &clauses);
    }
    Ok(clauses)
}

/// The clauses `ptl_to_trp` writes for the text, or why it writes none.
pub fn translate(text: &str) -> Result<Clauses, Failure> {
    let formula = parse(text)?;
    let mut translator = Translator::default();
    let (ip, up, sp, ep) = translator.dsnf_wrap(&nnf(&formula))?;
    let ip = translator.eliminate_quantifiers(&ip, &[])?;
    let mut eliminate = |formulas: &[Formula]| -> Result<Vec<Formula>, Failure> {
        formulas
            .iter()
            .map(|f| translator.eliminate_quantifiers(f, &[]))
            .collect()
    };
    let up = eliminate(&up)?;
    let sp = eliminate(&sp)?;
    let ep = eliminate(&ep)?;
    let up: Vec<Formula> = up.iter().map(cnf).collect();
    Ok(Clauses {
        initial: clausify(&cnf(&ip))?,
        universal: clausify_all(&up)?,
        step: clausify_all(&sp)?,
        eventuality: clausify_all(&ep)?,
    })
}

fn write_args(out: &mut String, args: &[Arg]) {
    for (i, arg) in args.iter().enumerate() {
        if i > 0 {
            out.push_str(", ");
        }
        match arg {
            Arg::Variable(name) | Arg::Constant(name) => out.push_str(name),
            Arg::Skolem(name, vars) => {
                out.push_str(name);
                if !vars.is_empty() {
                    let _ = write!(out, "({})", vars.join(", "));
                }
            }
        }
    }
}

/// `string_of_formula`.
pub fn write_formula(out: &mut String, f: &Formula) {
    let binary = |out: &mut String, f: &Formula, op: &str, g: &Formula| {
        out.push('(');
        write_formula(out, f);
        out.push_str(op);
        write_formula(out, g);
        out.push(')');
    };
    let unary = |out: &mut String, name: &str, f: &Formula| {
        out.push_str(name);
        out.push('(');
        write_formula(out, f);
        out.push(')');
    };
    match f {
        True => out.push_str("True"),
        False => out.push_str("False"),
        Atom(a, args) | NotAtom(a, args) => {
            if matches!(f, NotAtom(..)) {
                out.push_str("not ");
            }
            out.push_str(a);
            if !args.is_empty() {
                out.push('(');
                write_args(out, args);
                out.push(')');
            }
        }
        And(f, g) => binary(out, f, " & ", g),
        Or(f, g) => binary(out, f, " | ", g),
        Implies(f, g) => binary(out, f, " => ", g),
        Not(f) => unary(out, "not ", f),
        Forall(v, body) | Exists(v, body) => {
            let quantifier = if matches!(f, Forall(..)) { "!" } else { "?" };
            let _ = write!(out, "{quantifier}[{}](", v.join(", "));
            write_formula(out, body);
            out.push(')');
        }
        Always(f) => unary(out, "always", f),
        AlwaysP(f) => unary(out, "alwaysp", f),
        Sometime(f) => unary(out, "sometime", f),
        SometimeP(f) => unary(out, "sometimep", f),
        Next(f) => unary(out, "next", f),
        Until(f, g) => binary(out, f, " until ", g),
        Unless(f, g) => binary(out, f, " unless ", g),
    }
}

fn write_clauses(clauses: &[Vec<Formula>], is_always: bool) -> String {
    let mut out = String::new();
    for (i, clause) in clauses.iter().enumerate() {
        if i > 0 {
            out.push_str(", \n");
        }
        out.push_str(if is_always { "always(or([" } else { "or([" });
        for (j, literal) in clause.iter().enumerate() {
            if j > 0 {
                out.push_str(", ");
            }
            write_formula(&mut out, literal);
        }
        out.push_str(if is_always { "]))" } else { "])" });
    }
    out
}

impl Clauses {
    /// The text `main.ml` prints, commas and all.
    pub fn text(&self) -> String {
        let ic = write_clauses(&self.initial, false);
        let uc = write_clauses(&self.universal, true);
        let sc = write_clauses(&self.step, true);
        let ec = write_clauses(&self.eventuality, true);
        let ic_joined = if uc.is_empty() || ic.is_empty() {
            ic.clone()
        } else {
            format!("{ic},\n")
        };
        let uc_joined = if sc.is_empty() || uc.len() + ic.len() == 0 {
            uc.clone()
        } else {
            format!("{uc},\n")
        };
        let sc_joined = if ec.is_empty() {
            sc
        } else {
            format!("{sc},\n")
        };
        format!("and([\n{ic_joined}{uc_joined}{sc_joined}{ec}]).\n\n")
    }
}
