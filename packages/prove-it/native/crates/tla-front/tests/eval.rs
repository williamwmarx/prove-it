//! The constant evaluator on small specs. `scripts/front-differential.ts model-full` holds what it
//! unrolls to the TypeScript evaluator's on every corpus model.

use std::rc::Rc;

use tla_front::TlcVersion;
use tla_front::config::{ConfigValue, parse_config};
use tla_front::environment::{EnvironmentOptions, create_environment};
use tla_front::errors::FrontError;
use tla_front::eval::Evaluator;
use tla_front::hash::FastMap;
use tla_front::spec::create_identifier;
use tla_front::values::ValueOrder;

fn try_evaluate(definitions: &str, name: &str) -> Result<ConfigValue, FrontError> {
    try_evaluate_ranked(definitions, name, &[])
}

/// Evaluates with TLC's string order ranking `texts` in turn.
fn try_evaluate_ranked(
    definitions: &str,
    name: &str,
    texts: &[&str],
) -> Result<ConfigValue, FrontError> {
    let source =
        format!("---- MODULE Main ----\nEXTENDS Naturals, FiniteSets\n{definitions}\n====");
    let config = parse_config("", TlcVersion::Master).expect("a configuration");
    let environment = create_environment(&EnvironmentOptions {
        source: &source,
        load_module: &|_| None,
        config: &config,
        is_unconfigured: true,
        version: TlcVersion::Master,
        is_level_checked: false,
    })
    .expect("an environment");
    let ranks: FastMap<Rc<str>, u32> = texts
        .iter()
        .zip(0..)
        .map(|(text, rank)| (Rc::from(*text), rank))
        .collect();
    let evaluator = Evaluator::new(
        &environment,
        ValueOrder { ranks: &ranks },
        TlcVersion::Master,
        true,
    );
    evaluator.evaluate(&create_identifier(name), None)
}

fn evaluate(definitions: &str, name: &str) -> ConfigValue {
    try_evaluate(definitions, name).unwrap_or_else(|error| panic!("{error:?}"))
}

fn numbers(values: &[f64]) -> ConfigValue {
    ConfigValue::Set(
        values
            .iter()
            .map(|value| ConfigValue::Number(*value))
            .collect(),
    )
}

#[test]
fn computes_sets_in_tlc_order() {
    assert_eq!(
        evaluate("S == {3, 1} \\cup 2..4", "S"),
        numbers(&[1.0, 2.0, 3.0, 4.0])
    );
    assert_eq!(
        evaluate("S == {x \\in 1..6 : x % 2 = 0} \\ {4}", "S"),
        numbers(&[2.0, 6.0])
    );
    assert_eq!(
        evaluate("S == {x * x : x \\in {2, 0, 1}}", "S"),
        numbers(&[0.0, 1.0, 4.0])
    );
}

#[test]
fn computes_constant_formulas() {
    assert_eq!(
        evaluate(
            "N == 3\nOk == \\A x \\in 1..N : x \\div 2 < N /\\ Cardinality({x, N}) \\in Nat",
            "Ok"
        ),
        ConfigValue::Boolean(true)
    );
    assert_eq!(
        evaluate("F(a) == IF a > 1 THEN a - 7 \\div 2 ELSE 0\nV == F(5)", "V"),
        ConfigValue::Number(2.0)
    );
}

#[test]
fn computes_powers() {
    assert_eq!(evaluate("N == 2^3 - 1", "N"), ConfigValue::Number(7.0));
    assert_eq!(evaluate("N == 1^40 + 0^2", "N"), ConfigValue::Number(1.0));
}

#[test]
fn fails_as_tlc_does_to_enumerate_functions_of_a_named_set() {
    // IOUtils' IOEnv, which TLC can't compute without its Java override.
    let definitions = "Env == CHOOSE r \\in [STRING -> STRING] : TRUE\nName == CASE \"G\" \\in DOMAIN Env -> 1 [] OTHER -> 2";
    assert_eq!(
        try_evaluate(definitions, "Name"),
        Err(FrontError::Evaluation(
            "Attempted to enumerate a set of the form [D -> R],but the domain D:\nSTRING\ncannot be enumerated.".to_owned()
        ))
    );
    assert_eq!(
        evaluate("Pick == CHOOSE x \\in 1..5 : x > 3", "Pick"),
        ConfigValue::Number(4.0)
    );
}

fn record(fields: &[(&str, ConfigValue)]) -> ConfigValue {
    ConfigValue::Record(
        fields
            .iter()
            .map(|(name, value)| (name.to_string(), value.clone()))
            .collect(),
    )
}

#[test]
fn orders_records_by_size_then_names_then_values() {
    // TLC orders field names by when it interned them: here `b` before `a`.
    let ranked = |definitions: &str| {
        try_evaluate_ranked(definitions, "S", &["b", "a"])
            .unwrap_or_else(|error| panic!("{error:?}"))
    };
    assert_eq!(
        ranked("S == {[a |-> 1, b |-> 2], [b |-> 1, a |-> 2], [a |-> 0]}"),
        ConfigValue::Set(vec![
            record(&[("a", ConfigValue::Number(0.0))]),
            record(&[
                ("b", ConfigValue::Number(1.0)),
                ("a", ConfigValue::Number(2.0))
            ]),
            record(&[
                ("b", ConfigValue::Number(2.0)),
                ("a", ConfigValue::Number(1.0))
            ]),
        ])
    );
    let records = ranked("S == [a : {1, 2}, b : {0}]");
    assert_eq!(
        records,
        ConfigValue::Set(vec![
            record(&[
                ("b", ConfigValue::Number(0.0)),
                ("a", ConfigValue::Number(1.0))
            ]),
            record(&[
                ("b", ConfigValue::Number(0.0)),
                ("a", ConfigValue::Number(2.0))
            ]),
        ])
    );
    assert_eq!(
        ranked("S == {r.a : r \\in [a : {1, 2}, b : {0}]}"),
        numbers(&[1.0, 2.0])
    );
}
