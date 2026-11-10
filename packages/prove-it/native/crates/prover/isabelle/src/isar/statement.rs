//! Ported from the statement handling of Isabelle2025's Pure/Isar/expression.ML
//! (prep_full_context_statement). Copyright (c) 1986-2025 University of Cambridge, Technische
//! Universitaet Muenchen, and contributors, see LICENSE.
//!
//! Reads a lemma's fixes, assumes and shows: each proposition is parsed with the variables fixed
//! before it, and all of them are type checked together.

use std::collections::HashSet;
use std::rc::Rc;

use crate::error::Res;
use crate::isar::inner_syntax::{parse_prop, parse_type};
use crate::isar::theory::{StatementElement, TheoryText};
use crate::isar::type_check::{NameScope, PropToCheck, check_props};
use crate::pure::consts::typargs_of;
use crate::pure::term::{Name, Term};
use crate::tla::logic::{ConstInfo, TlaLogic};

pub struct Statement {
    pub assumptions: Vec<Term>,
    pub conclusion: Term,
}

pub fn read_statement(logic: &TlaLogic, theory: &TheoryText) -> Res<Statement> {
    let theory_consts = theory
        .consts
        .iter()
        .map(|constant| {
            Ok((
                Name::from(&*constant.name),
                Name::from(format!("{}.{}", theory.name, constant.name)),
                parse_type(&constant.ty)?,
            ))
        })
        .collect::<Res<Vec<_>>>()?;
    let mut scope = NameScope {
        consts: logic.consts.clone(),
        const_names: logic.const_names.clone(),
    };
    for (base, name, ty) in theory_consts {
        let info = ConstInfo {
            typargs: typargs_of(&ty).into(),
            ty,
            abbreviation: None,
        };
        scope.consts.insert(name.clone(), info);
        scope.const_names.insert(base, name);
    }
    let mut fixed = Rc::new(HashSet::new());
    let mut props = Vec::new();
    for element in &theory.elements {
        match element {
            StatementElement::Fixes { names } => {
                let mut extended = (*fixed).clone();
                extended.extend(names.iter().map(|name| Name::from(&**name)));
                fixed = Rc::new(extended);
            }
            StatementElement::Assumes { prop, .. } => props.push(PropToCheck {
                ast: parse_prop(prop)?,
                fixed: fixed.clone(),
            }),
        }
    }
    props.push(PropToCheck {
        ast: parse_prop(&theory.shows)?,
        fixed,
    });
    let mut checked = check_props(&scope, &props)?;
    let conclusion = checked.pop().expect("the shows is checked");
    Ok(Statement {
        assumptions: checked,
        conclusion,
    })
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::*;
    use crate::error::Error;
    use crate::isar::theory::parse_theory;
    use crate::pure::logic::tests::show;
    use crate::pure::term::{empty_sort, mk_tfree, mk_type};
    use crate::tla::logic::load_logic;

    // The expectations in testdata/statement are what statement.ts and type-check.ts produce,
    // rendered alike.

    macro_rules! fixtures {
        ($($name:literal),* $(,)?) => {
            [$((
                $name,
                include_str!(concat!("../../../../../../tests/fixtures/isabelle/", $name, ".thy")),
                include_str!(concat!("../../testdata/statement/", $name, ".txt")),
            )),*]
        };
    }

    fn unescape(text: &str) -> String {
        let mut result = String::new();
        let mut chars = text.chars();
        while let Some(char) = chars.next() {
            result.push(if char == '\\' {
                match chars.next() {
                    Some('n') => '\n',
                    Some('t') => '\t',
                    Some('r') => '\r',
                    Some(other) => other,
                    None => panic!("escape at end of {text}"),
                }
            } else {
                char
            });
        }
        result
    }

    fn outcome(result: Res<Vec<String>>) -> Vec<String> {
        result.unwrap_or_else(|error| match error {
            Error::Isabelle(exception, message) => vec![format!("{}: {message}", exception.name())],
            other => panic!("not an Isabelle error: {other:?}"),
        })
    }

    fn render(text: &str) -> Vec<String> {
        outcome((|| {
            let theory = parse_theory(text)?;
            let statement = read_statement(&load_logic(), &theory)?;
            let assumes: Vec<_> = theory
                .elements
                .iter()
                .filter_map(|element| match element {
                    StatementElement::Assumes { name, .. } => Some(name),
                    StatementElement::Fixes { .. } => None,
                })
                .collect();
            let elements = theory.elements.iter().map(|element| match element {
                StatementElement::Fixes { names } => format!("fixes {}", names.join(" ")),
                StatementElement::Assumes { name, .. } => format!("assumes {name}"),
            });
            let assumptions = statement
                .assumptions
                .iter()
                .zip(&assumes)
                .map(|(term, name)| format!("assumption {name}: {}", show(term)));
            Ok(elements
                .chain(assumptions)
                .chain([format!("conclusion: {}", show(&statement.conclusion))])
                .collect())
        })())
    }

    #[test]
    fn reads_the_fixture_statements() {
        for (name, theory, expected) in fixtures!(
            "AllocatorImplementation_proof-127",
            "AllocatorImplementation_proof-33",
            "AtomicBakeryWithoutSMT-465",
            "AtomicBakeryWithoutSMT-6",
            "FiniteSetTheorems_proofs-453",
            "Level_test-1",
            "NaturalsInduction_proofs-1",
            "Paxos-109",
            "Sets-183",
            "TLAPS-2",
            "constantfcn_test-1",
            "function_except_tuple_soundness_gh201_test-1",
        ) {
            assert_eq!(
                render(theory),
                expected.lines().collect::<Vec<_>>(),
                "statement of {name}"
            );
        }
    }

    /// The scope the `check` cases use: Trueprop, a declared T.g :: 'a => 'a, and f standing for
    /// the undeclared T.f.
    fn check_scope() -> NameScope {
        let trueprop = load_logic().consts["PredicateLogic.Trueprop"].clone();
        let a = mk_tfree("'a", empty_sort());
        let g = ConstInfo {
            ty: mk_type("fun", vec![a.clone(), a]),
            typargs: Rc::new([]),
            abbreviation: None,
        };
        NameScope {
            consts: HashMap::from([
                ("PredicateLogic.Trueprop".into(), trueprop),
                ("T.g".into(), g),
            ]),
            const_names: HashMap::from([("f".into(), "T.f".into()), ("g".into(), "T.g".into())]),
        }
    }

    #[test]
    fn reads_and_checks_the_cases() {
        let mut cases: Vec<(&str, String, Vec<&str>)> = Vec::new();
        for line in include_str!("../../testdata/statement/cases.txt").lines() {
            match line.split_once('\t') {
                Some((kind, text)) => cases.push((kind, unescape(text), Vec::new())),
                None => cases.last_mut().expect("a case first").2.push(line),
            }
        }
        assert!(cases.len() > 20);
        for (kind, text, expected) in cases {
            let actual = match kind {
                "theory" => render(&text),
                "check" => outcome((|| {
                    let props = [PropToCheck {
                        ast: parse_prop(&text)?,
                        fixed: Rc::new(HashSet::new()),
                    }];
                    Ok(check_props(&check_scope(), &props)?
                        .iter()
                        .map(show)
                        .collect())
                })()),
                _ => panic!("unknown case kind {kind}"),
            };
            assert_eq!(actual, expected, "{kind} {text}");
        }
    }
}
