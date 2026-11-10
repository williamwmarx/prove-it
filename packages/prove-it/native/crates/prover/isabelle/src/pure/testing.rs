//! Helpers for the kernel's tests, whose expectations in `testdata/kernel` are recorded from the
//! TypeScript by a script that renders and parses terms exactly as this module does.
//!
//! The text form: types are `name`, `name(arg,...)`, `'a` (TFree) and `?'a.0` (TVar), all with
//! the empty sort; terms are `name::T` (Const), `name:T` (Free), `?name.0:T` (Var), `B0`
//! (Bound), `(%name:T body)` (Abs) and `(f a)` (App).
//!
//! A test file is a list of problems, each a line `> kind<TAB>field<TAB>...` followed by the
//! lines the TypeScript printed for it.

use crate::error::{Error, Res};

use super::envir::{Envir, TEnv};
use super::table::table_entries;
use super::term::{
    Term, TermNode, Typ, TypNode, empty_sort, mk_abs, mk_app, mk_bound, mk_const, mk_free,
    mk_tfree, mk_tvar, mk_type, mk_var,
};
use super::types::TyEnv;

pub(crate) fn show_typ(ty: &Typ) -> String {
    match &**ty {
        TypNode::Type { name, args, .. } if args.is_empty() => name.to_string(),
        TypNode::Type { name, args, .. } => format!(
            "{name}({})",
            args.iter().map(show_typ).collect::<Vec<_>>().join(",")
        ),
        TypNode::TFree { name, sort } => {
            assert!(sort.is_empty(), "a sorted type");
            name.to_string()
        }
        TypNode::TVar { name, index, sort } => {
            assert!(sort.is_empty(), "a sorted type");
            format!("?{name}.{index}")
        }
    }
}

pub(crate) fn show(term: &Term) -> String {
    match &**term {
        TermNode::Const { name, ty } => format!("{name}::{}", show_typ(ty)),
        TermNode::Free { name, ty } => format!("{name}:{}", show_typ(ty)),
        TermNode::Var { name, index, ty } => format!("?{name}.{index}:{}", show_typ(ty)),
        TermNode::Bound { index } => format!("B{index}"),
        TermNode::Abs { name, ty, body, .. } => {
            format!("(%{name}:{} {})", show_typ(ty), show(body))
        }
        TermNode::App { fun, arg, .. } => format!("({} {})", show(fun), show(arg)),
    }
}

struct Parser<'a> {
    text: &'a [u8],
    position: usize,
}

impl Parser<'_> {
    fn peek(&self) -> Option<u8> {
        self.text.get(self.position).copied()
    }

    fn expect(&mut self, char: u8) {
        assert_eq!(
            self.peek(),
            Some(char),
            "expected {} at {}",
            char as char,
            self.position
        );
        self.position += 1;
    }

    fn name(&mut self) -> String {
        let start = self.position;
        while self
            .peek()
            .is_some_and(|char| char.is_ascii_alphanumeric() || b"_.'?".contains(&char))
        {
            self.position += 1;
        }
        String::from_utf8(self.text[start..self.position].to_vec()).unwrap()
    }

    fn indexed(token: &str) -> (String, i32) {
        let dot = token.rfind('.').unwrap();
        (token[1..dot].to_string(), token[dot + 1..].parse().unwrap())
    }

    fn typ(&mut self) -> Typ {
        let token = self.name();
        if token.starts_with('?') {
            let (name, index) = Self::indexed(&token);
            return mk_tvar(name, index, empty_sort());
        }
        if token.starts_with('\'') {
            return mk_tfree(token, empty_sort());
        }
        if self.peek() != Some(b'(') {
            return mk_type(token, Vec::new());
        }
        self.position += 1;
        let mut args = vec![self.typ()];
        while self.peek() == Some(b',') {
            self.position += 1;
            args.push(self.typ());
        }
        self.expect(b')');
        mk_type(token, args)
    }

    fn term(&mut self) -> Term {
        if self.peek() == Some(b'(') {
            self.position += 1;
            if self.peek() == Some(b'%') {
                self.position += 1;
                let name = self.name();
                self.expect(b':');
                let ty = self.typ();
                self.expect(b' ');
                let body = self.term();
                self.expect(b')');
                return mk_abs(name, ty, body);
            }
            let fun = self.term();
            self.expect(b' ');
            let arg = self.term();
            self.expect(b')');
            return mk_app(fun, arg);
        }
        let token = self.name();
        if self.peek() != Some(b':') {
            let index = token.strip_prefix('B').and_then(|index| index.parse().ok());
            return mk_bound(index.unwrap_or_else(|| panic!("bad atom {token}")));
        }
        self.position += 1;
        if self.peek() == Some(b':') {
            self.position += 1;
            return mk_const(token, self.typ());
        }
        let ty = self.typ();
        if token.starts_with('?') {
            let (name, index) = Self::indexed(&token);
            return mk_var(name, index, ty);
        }
        mk_free(token, ty)
    }
}

pub(crate) fn parse_term(text: &str) -> Term {
    let mut parser = Parser {
        text: text.as_bytes(),
        position: 0,
    };
    let term = parser.term();
    assert_eq!(parser.position, text.len(), "trailing text in {text}");
    term
}

pub(crate) fn parse_typ(text: &str) -> Typ {
    let mut parser = Parser {
        text: text.as_bytes(),
        position: 0,
    };
    let ty = parser.typ();
    assert_eq!(parser.position, text.len(), "trailing text in {text}");
    ty
}

/// An exception as the script prints it: `error EXCEPTION: message`, or the local class.
pub(crate) fn show_error(error: &Error) -> String {
    match error {
        Error::Isabelle(exception, message) => format!("error {}: {message}", exception.name()),
        Error::Unif
        | Error::NotPattern
        | Error::Match
        | Error::CantUnify
        | Error::ChangeFail
        | Error::Compose
        | Error::MatchFailure
        | Error::NoMatch
        | Error::EqVar => format!("error {error:?}"),
        _ => panic!("unexpected {error:?}"),
    }
}

/// Runs a computation that prints lines, ending at the first exception, which it prints.
pub(crate) fn attempt(lines: &mut Vec<String>, run: impl FnOnce(&mut Vec<String>) -> Res<()>) {
    if let Err(error) = run(lines) {
        lines.push(show_error(&error));
    }
}

pub(crate) fn show_tables(tyenv: &TyEnv, tenv: &TEnv) -> Vec<String> {
    table_entries(tenv)
        .iter()
        .map(|(key, binding)| {
            format!(
                "tenv ?{}.{}:{} := {}",
                key.name,
                key.index,
                show_typ(&binding.ty),
                show(&binding.term)
            )
        })
        .chain(
            table_entries(tyenv)
                .iter()
                .map(|(key, ty)| format!("tyenv ?{}.{} := {}", key.name, key.index, show_typ(ty))),
        )
        .collect()
}

pub(crate) fn show_envir(envir: &Envir) -> Vec<String> {
    let mut lines = vec![format!("maxidx {}", envir.maxidx)];
    lines.extend(show_tables(&envir.tyenv, &envir.tenv));
    lines
}

/// Solves each problem of a test file, and checks that it prints what the TypeScript printed.
pub(crate) fn check_problems(text: &str, mut solve: impl FnMut(&str, &[&str]) -> Vec<String>) {
    let mut problems: Vec<(&str, Vec<&str>)> = Vec::new();
    for line in text.lines() {
        match line.strip_prefix("> ") {
            Some(problem) => problems.push((problem, Vec::new())),
            None => problems
                .last_mut()
                .expect("a problem before its expectations")
                .1
                .push(line),
        }
    }
    assert!(!problems.is_empty());
    let mut failures = Vec::new();
    for (problem, expected) in &problems {
        let fields: Vec<&str> = problem.split('\t').collect();
        let actual = solve(fields[0], &fields[1..]);
        if actual != *expected {
            failures.push(format!(
                "> {problem}\nexpected:\n{}\nactual:\n{}",
                expected.join("\n"),
                actual.join("\n")
            ));
        }
    }
    assert!(
        failures.is_empty(),
        "{} of {} problems differ; the first:\n{}",
        failures.len(),
        problems.len(),
        failures[0]
    );
}
