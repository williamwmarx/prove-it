//! The constant evaluator on small specs. `scripts/front-differential.ts model-full` holds what it
//! unrolls to the TypeScript evaluator's on every corpus model.

use std::rc::Rc;

use tla_front::TlcVersion;
use tla_front::config::{ConfigValue, parse_config};
use tla_front::environment::{EnvironmentOptions, create_environment};
use tla_front::eval::Evaluator;
use tla_front::hash::FastMap;
use tla_front::spec::create_identifier;
use tla_front::values::ValueOrder;

fn evaluate(definitions: &str, name: &str) -> ConfigValue {
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
    let ranks: FastMap<Rc<str>, u32> = FastMap::default();
    let evaluator = Evaluator::new(
        &environment,
        ValueOrder { ranks: &ranks },
        TlcVersion::Master,
        true,
    );
    evaluator
        .evaluate(&create_identifier(name), None)
        .unwrap_or_else(|error| panic!("{error:?}"))
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
