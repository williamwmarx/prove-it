// Ported from Zenon's phrase.ml, as shipped in tlapm. Copyright 2004 INRIA, see LICENSE.
//! Splits the input into definitions and hypotheses. A hypothesis that defines a symbol, such as
//! x = e or \A a, b : f(a, b) <=> e, becomes a definition that the prover unfolds.

use std::rc::Rc;

use crate::expr::{Expr, Kind};
use crate::parse::{Definition, Phrase};

#[derive(Clone, Debug)]
pub struct Hypothesis {
    pub formula: Expr,
    pub goalness: i64,
}

fn has_name(env: &[Expr], name: &str) -> bool {
    env.iter().any(|variable| &*variable.symbol == name)
}

/// The names sorted as JavaScript's `sort()` sorts strings, by UTF-16 code units.
fn sort_names<'a>(names: impl Iterator<Item = &'a str>) -> Vec<&'a str> {
    let mut names: Vec<&str> = names.collect();
    names.sort_by(|left, right| crate::expr::compare_utf16(left, right));
    names
}

/// Zenon's check_args: the arguments are variables, and exactly the quantified ones.
fn is_parameter_list(env: &[Expr], args: &[Expr]) -> bool {
    if !args.iter().all(|arg| arg.kind == Kind::Var) {
        return false;
    }
    let env_names = sort_names(env.iter().map(|variable| &*variable.symbol));
    let arg_names = sort_names(args.iter().map(|arg| &*arg.symbol));
    env_names == arg_names && env_names.windows(2).all(|pair| pair[0] != pair[1])
}

fn is_body_of(env: &[Expr], symbol: &str, expression: &Expr) -> bool {
    match expression.kind {
        Kind::Var => &*expression.symbol != symbol || has_name(env, &expression.symbol),
        Kind::App => {
            &*expression.symbol != symbol
                && expression
                    .args
                    .iter()
                    .all(|inner| is_body_of(env, symbol, inner))
        }
        kind if kind.is_binder() => is_body_of(
            &[&[expression.args[0].clone()], env].concat(),
            symbol,
            &expression.args[1],
        ),
        _ => expression
            .args
            .iter()
            .all(|inner| is_body_of(env, symbol, inner)),
    }
}

struct Shape {
    symbol: String,
    params: Option<Vec<Expr>>,
    body: Expr,
}

/// The ways a formula can define a symbol, in the order Zenon tries them: a definiendum that is an
/// application with its parameters, or a constant.
fn get_shapes(expression: &Expr) -> Vec<Shape> {
    let is_definition = expression.kind == Kind::Equiv || expression.is_app("=");
    if !is_definition || expression.args.len() != 2 {
        return Vec::new();
    }
    let to_shape = |definiendum: &Expr, body: &Expr| match definiendum.kind {
        Kind::App => Some(Shape {
            symbol: definiendum.symbol.to_string(),
            params: Some(definiendum.args.clone()),
            body: body.clone(),
        }),
        Kind::Var => Some(Shape {
            symbol: definiendum.symbol.to_string(),
            params: None,
            body: body.clone(),
        }),
        _ => None,
    };
    let left = &expression.args[0];
    let right = &expression.args[1];
    let shapes: Vec<Shape> = to_shape(left, right)
        .into_iter()
        .chain(to_shape(right, left))
        .collect();
    let (applications, constants): (Vec<Shape>, Vec<Shape>) =
        shapes.into_iter().partition(|shape| shape.params.is_some());
    if expression.kind == Kind::Equiv {
        applications.into_iter().chain(constants).collect()
    } else {
        constants.into_iter().chain(applications).collect()
    }
}

fn strip_forall(expression: &Expr, mut env: Vec<Expr>) -> (Vec<Expr>, Expr) {
    let mut body = expression.clone();
    while body.kind == Kind::All {
        env.insert(0, body.args[0].clone());
        body = body.args[1].clone();
    }
    (env, body)
}

/// Zenon's is_def, then make_def. The two try the shapes with different conditions, so the shape
/// that defines the symbol can differ from the one that qualifies the formula.
fn get_definition(predefined: &[&str], hypothesis: &Hypothesis) -> Option<Definition> {
    let (env, body) = strip_forall(&hypothesis.formula, Vec::new());
    let shapes = get_shapes(&body);
    let qualifying = shapes
        .iter()
        .find(|candidate| !predefined.contains(&candidate.symbol.as_str()))?;
    let are_params_valid = match &qualifying.params {
        None => env.is_empty(),
        Some(params) => is_parameter_list(&env, params),
    };
    if !are_params_valid || !is_body_of(&[], &qualifying.symbol, &qualifying.body) {
        return None;
    }
    let shape = shapes.into_iter().find(|candidate| {
        !predefined.contains(&candidate.symbol.as_str())
            && candidate
                .params
                .as_ref()
                .is_none_or(|params| is_parameter_list(&env, params))
    })?;
    Some(Definition::Pseudo {
        origin: hypothesis.formula.clone(),
        goalness: hypothesis.goalness,
        symbol: shape.symbol,
        params: shape.params.unwrap_or_default(),
        body: shape.body,
    })
}

fn get_free_symbols(env: &[Expr], accumulator: Vec<String>, expression: &Expr) -> Vec<String> {
    match expression.kind {
        Kind::Var => {
            if has_name(env, &expression.symbol) {
                accumulator
            } else {
                let mut symbols = vec![expression.symbol.to_string()];
                symbols.extend(accumulator);
                symbols
            }
        }
        Kind::App => {
            let mut symbols = vec![expression.symbol.to_string()];
            symbols.extend(accumulator);
            expression.args.iter().fold(symbols, |symbols, inner| {
                get_free_symbols(env, symbols, inner)
            })
        }
        kind if kind.is_binder() => get_free_symbols(
            &[&[expression.args[0].clone()], env].concat(),
            accumulator,
            &expression.args[1],
        ),
        _ => expression.args.iter().fold(accumulator, |symbols, inner| {
            get_free_symbols(env, symbols, inner)
        }),
    }
}

type Dependency = (String, Vec<String>);

fn follow_dependencies(symbols: &[String], dependencies: &[Dependency]) -> Vec<String> {
    symbols
        .iter()
        .flat_map(|symbol| {
            dependencies
                .iter()
                .find(|dependency| dependency.0 == *symbol)
                .map(|dependency| dependency.1.clone())
                .unwrap_or_default()
        })
        .collect()
}

fn is_looping(symbol: &str, symbols: &[String], dependencies: &[Dependency]) -> bool {
    !symbols.is_empty()
        && (symbols.iter().any(|inner| inner == symbol)
            || is_looping(
                symbol,
                &follow_dependencies(symbols, dependencies),
                dependencies,
            ))
}

pub struct Separated {
    pub definitions: Vec<Rc<Definition>>,
    pub hypotheses: Vec<Hypothesis>,
}

/// Zenon's separate. Definitions come before hypotheses, each in input order, except where a
/// symbol is defined twice: then neither formula defines it.
pub fn separate(predefined: &[&str], phrases: &[Phrase]) -> Separated {
    let mut dependencies: Vec<Dependency> = Vec::new();
    let mut multiple: Vec<String> = Vec::new();
    let mut definitions: Vec<Rc<Definition>> = Vec::new();
    let mut hypotheses: Vec<Hypothesis> = Vec::new();
    for phrase in phrases {
        let (formula, goalness) = match phrase {
            Phrase::Def(definition) => {
                definitions.insert(0, definition.clone());
                continue;
            }
            Phrase::Hyp {
                formula, goalness, ..
            } => (formula, *goalness),
        };
        let hypothesis = Hypothesis {
            formula: formula.clone(),
            goalness,
        };
        let Some(definition) = get_definition(predefined, &hypothesis) else {
            hypotheses.insert(0, hypothesis);
            continue;
        };
        let symbol = definition.symbol().to_owned();
        let dependency: Dependency = (
            symbol.clone(),
            get_free_symbols(definition.params(), Vec::new(), definition.body()),
        );
        // The lists are reversed, as in Zenon, so a definition's index 0 is the latest.
        let previous = definitions.iter().position(|existing| {
            matches!(&**existing, Definition::Pseudo { .. }) && existing.symbol() == symbol
        });
        if multiple.contains(&symbol) || is_looping(&symbol, &dependency.1, &dependencies) {
            hypotheses.insert(0, hypothesis);
        } else if let Some(previous) = previous {
            let Definition::Pseudo {
                origin, goalness, ..
            } = &*definitions[previous]
            else {
                unreachable!("found as a pseudo-definition");
            };
            let removed = Hypothesis {
                formula: origin.clone(),
                goalness: *goalness,
            };
            // Zenon's remove_def reverses the definitions after the old one.
            let after = definitions.split_off(previous + 1);
            definitions.pop();
            definitions.reverse();
            definitions.extend(after);
            if let Some(index) = dependencies
                .iter()
                .position(|candidate| candidate.0 == symbol)
            {
                dependencies.remove(index);
            }
            multiple.insert(0, symbol);
            hypotheses.splice(0..0, [hypothesis, removed]);
        } else {
            dependencies.insert(0, dependency);
            definitions.insert(0, Rc::new(definition));
        }
    }
    definitions.reverse();
    hypotheses.reverse();
    Separated {
        definitions,
        hypotheses,
    }
}
