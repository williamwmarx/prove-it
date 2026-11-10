//! ctx.ml and backend/smtlib.ml's naming: each name is salted past the names in scope. A port of
//! `src/prover/smt/context.ts`.

use std::collections::{HashMap, HashSet};

use crate::errors::{ObligationError, Result};
use crate::smt::format::{format_name, is_js_space};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Identifier {
    pub base: String,
    pub salt: usize,
    pub name: String,
}

fn get_salted_name(base: &str, salt: usize) -> String {
    if salt == 0 {
        base.to_string()
    } else {
        format!("{base}_{salt}")
    }
}

/// How to take an identifier out of scope again: the closure `enter` returns in the TypeScript.
#[derive(Clone, Debug)]
pub struct ContextExit {
    name: String,
    base: String,
    previous: Option<usize>,
}

/// The context `createContext` returns. `names` is looked up only, never iterated.
#[derive(Debug, Default)]
pub struct Context {
    salts: HashMap<String, usize>,
    pub names: HashSet<String>,
}

// Ctx.maybe_adj: a name is its formatted base, salted past the last one with that base and past
// every name in scope.
pub fn create_context() -> Context {
    Context::default()
}

impl Context {
    pub fn adjoin(&self, raw: &str) -> Identifier {
        let base = format_name(raw);
        let start = self.salts.get(&base).map_or(0, |salt| salt + 1);
        let salt = (start..start + self.names.len() + 1)
            .find(|candidate| !self.names.contains(&get_salted_name(&base, *candidate)))
            .unwrap_or(start);
        let name = get_salted_name(&base, salt);
        Identifier { base, salt, name }
    }

    // Brings an identifier into scope and returns how to take it out again.
    pub fn enter(&mut self, identifier: &Identifier) -> ContextExit {
        let previous = self.salts.insert(identifier.base.clone(), identifier.salt);
        self.names.insert(identifier.name.clone());
        ContextExit {
            name: identifier.name.clone(),
            base: identifier.base.clone(),
            previous,
        }
    }

    pub fn exit(&mut self, exit: ContextExit) {
        self.names.remove(&exit.name);
        match exit.previous {
            None => self.salts.remove(&exit.base),
            Some(previous) => self.salts.insert(exit.base, previous),
        };
    }
}

/// One of a quantifier scope's exits: an identifier's, or restoring a raw name's renames.
enum Exit {
    Context(ContextExit),
    Renames { raw: String, stack: Vec<String> },
}

// A quantifier's variables, in scope until the quantifier's closing parenthesis.
struct QuantifierScope {
    depth: i64,
    exits: Vec<Exit>,
}

/// The printer `createPrinter` returns.
pub struct Printer<'declared> {
    declared: &'declared HashMap<String, Identifier>,
    context: Context,
}

// Smtlib.pp_print_obligation names each declaration for the rest of the obligation, and each
// quantifier's variables within it, so a variable's name depends on the names in scope.
pub fn create_printer(declared: &HashMap<String, Identifier>) -> Printer<'_> {
    Printer {
        declared,
        context: create_context(),
    }
}

/// `/\|[^|]*\||[()]|[^\s()|]+/g`: each token's offset and text.
fn get_tokens(line: &str) -> Vec<(usize, &str)> {
    let mut tokens = Vec::new();
    let mut index = 0;
    while let Some(character) = line.get(index..).and_then(|tail| tail.chars().next()) {
        let tail = &line[index..];
        let length = if character == '|' {
            tail[1..].find('|').map(|close| close + 2)
        } else if character == '(' || character == ')' {
            Some(1)
        } else if is_js_space(character) {
            None
        } else {
            Some(
                tail.find(|other: char| is_js_space(other) || matches!(other, '(' | ')' | '|'))
                    .unwrap_or(tail.len()),
            )
        };
        match length {
            Some(length) => {
                tokens.push((index, &tail[..length]));
                index += length;
            }
            None => index += character.len_utf8(),
        }
    }
    tokens
}

/// `raw.replace(/#\d+$/, "")`.
fn remove_depth(raw: &str) -> &str {
    let digits = raw.len()
        - raw
            .trim_end_matches(|other: char| other.is_ascii_digit())
            .len();
    let stem = &raw[..raw.len() - digits];
    match stem.strip_suffix('#') {
        Some(name) if digits > 0 => name,
        _ => raw,
    }
}

impl Printer<'_> {
    pub fn resolve(&mut self, line: &str) -> Result<String> {
        if let Some(rest) = line.strip_prefix("(declare-fun ") {
            let declaration = &rest[..rest.find(is_js_space).unwrap_or(rest.len())];
            if !declaration.is_empty() {
                match self.declared.get(declaration) {
                    Some(identifier) => {
                        self.context.enter(identifier);
                    }
                    None => {
                        self.context.names.insert(declaration.to_string());
                    }
                }
                return Ok(line.to_string());
            }
        }
        let tokens = get_tokens(line);
        let token_at = |index: usize| tokens.get(index).map(|token| token.1);
        let mut replacements: HashMap<usize, String> = HashMap::new();
        let mut renames: HashMap<String, Vec<String>> = HashMap::new();
        let mut scopes: Vec<QuantifierScope> = Vec::new();
        let mut index = 0;
        let mut depth = 0i64;
        while index < tokens.len() {
            let token = tokens[index].1;
            let is_quantifier = token == "("
                && matches!(token_at(index + 1), Some("forall" | "exists"))
                && token_at(index + 2) == Some("(");
            if is_quantifier {
                depth += 1;
                let mut scope = QuantifierScope {
                    depth,
                    exits: Vec::new(),
                };
                index += 3;
                while token_at(index) == Some("(") {
                    // The TypeScript reads a binder's name past the end of the line as a TypeError.
                    let raw = token_at(index + 1).ok_or_else(ObligationError::assert_failure)?;
                    let identifier = self.context.adjoin(remove_depth(raw));
                    let stack = renames.get(raw).cloned().unwrap_or_default();
                    let mut renamed = stack.clone();
                    renamed.push(identifier.name.clone());
                    renames.insert(raw.to_string(), renamed);
                    scope
                        .exits
                        .push(Exit::Context(self.context.enter(&identifier)));
                    scope.exits.push(Exit::Renames {
                        raw: raw.to_string(),
                        stack,
                    });
                    replacements.insert(index + 1, identifier.name);
                    index += 4;
                }
                scopes.push(scope);
                index += 1;
                continue;
            }
            if token == "(" {
                depth += 1;
            }
            if token == ")" {
                if scopes.last().map(|scope| scope.depth) == Some(depth)
                    && let Some(scope) = scopes.pop()
                {
                    for exit in scope.exits.into_iter().rev() {
                        match exit {
                            Exit::Context(exit) => self.context.exit(exit),
                            Exit::Renames { raw, stack } => {
                                renames.insert(raw, stack);
                            }
                        }
                    }
                }
                depth -= 1;
            }
            if let Some(name) = renames.get(token).and_then(|stack| stack.last()) {
                replacements.insert(index, name.clone());
            }
            index += 1;
        }
        let mut resolved = String::with_capacity(line.len());
        for (position, token) in tokens.iter().enumerate() {
            let end = tokens.get(position + 1).map_or(line.len(), |next| next.0);
            resolved.push_str(replacements.get(&position).map_or(token.1, String::as_str));
            resolved.push_str(&line[token.0 + token.1.len()..end]);
        }
        Ok(resolved)
    }
}

// Expected values from running the TypeScript.
#[cfg(test)]
mod tests {
    use super::*;

    fn show(identifier: &Identifier) -> String {
        format!(
            "{}/{}/{}",
            identifier.base, identifier.salt, identifier.name
        )
    }

    #[test]
    fn adjoins_names() {
        assert_eq!(
            {
                let mut context = create_context();
                let first = context.adjoin("x");
                let exit_first = context.enter(&first);
                let second = context.adjoin("x");
                let exit_second = context.enter(&second);
                let third = context.adjoin("x");
                context.exit(exit_second);
                let fourth = context.adjoin("x");
                context.exit(exit_first);
                let fifth = context.adjoin("x");
                context.names.insert("smt__y".to_string());
                let sixth = context.adjoin("y");
                let seventh = context.adjoin("a b");
                [first, second, third, fourth, fifth, sixth, seventh]
                    .iter()
                    .map(show)
                    .collect::<Vec<_>>()
                    .join(";")
            },
            "smt__x/0/smt__x;smt__x/1/smt__x_1;smt__x/2/smt__x_2;smt__x/1/smt__x_1;smt__x/0/smt__x;smt__y/1/smt__y_1;smt__aspace__b/0/smt__aspace__b"
        );
    }

    #[test]
    fn prints_lines() {
        assert_eq!(
            {
                let declared = HashMap::from([(
                    "smt__y".to_string(),
                    Identifier {
                        base: "smt__y".to_string(),
                        salt: 1,
                        name: "smt__y_1".to_string(),
                    },
                )]);
                let mut printer = create_printer(&declared);
                ["(declare-fun smt__x () Idv)", "(declare-fun smt__y () Idv)", "(assert (forall ((x#0 Idv) (y#1 Idv)) (! (= x#0 y#1) :pattern ((f x#0)))))", "(assert (forall ((x#0 Idv)) (and (P x#0) (forall ((x#1 Idv)) (Q x#0 x#1)) (exists ((x#0 Int)) (R x#0)) (S x#0))))", "(assert (! (forall ((x#0 Idv)) x#0) :named |Goal x#0 (|))", "  (a  b)\t", "", "(a |b c)", "(declare-fun  z)", "(assert (forall ((smt__y#2 Idv)) (= smt__y#2 smt__y)))", "(forall ((\u{e9}#3 Idv)) (p \u{e9}#3))\u{a0}x", "(forall ((x#0 Idv)) (p x#0))) (q x#0)"].iter().map(|line| printer.resolve(line).unwrap_or_else(|error| format!("ERR {}: {}", error.name(), error.message()))).collect::<Vec<_>>().join("\n")
            },
            "(declare-fun smt__x () Idv)\n(declare-fun smt__y () Idv)\n(assert (forall ((smt__x_1 Idv) (smt__y_2 Idv)) (! (= smt__x_1 smt__y_2) :pattern ((f smt__x_1)))))\n(assert (forall ((smt__x_1 Idv)) (and (P smt__x_1) (forall ((smt__x_2 Idv)) (Q smt__x_1 smt__x_2)) (exists ((smt__x_2 Int)) (R smt__x_2)) (S smt__x_1))))\n(assert (! (forall ((smt__x_1 Idv)) smt__x_1) :named |Goal x#0 (|))\n(a  b)\t\n\n(a |b c)\n(declare-fun  z)\n(assert (forall ((smt__smt____y Idv)) (= smt__smt____y smt__y)))\n(forall ((smt__\u{e9} Idv)) (p smt__\u{e9}))\u{a0}x\n(forall ((smt__x_1 Idv)) (p smt__x_1))) (q x#0)"
        );
        assert!(
            create_printer(&HashMap::new())
                .resolve("(forall ((")
                .is_err()
        );
    }
}
