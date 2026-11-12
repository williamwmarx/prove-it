//! TLC's Java overrides of a module's operators, on the class `tests/fixtures/overrides` holds,
//! as `tests/unit/overrides.test.ts` checks them in TypeScript.

use std::path::Path;
use std::rc::Rc;

use tla_front::TlcVersion;
use tla_front::config::{ConfigValue, parse_config};
use tla_front::environment::{Environment, EnvironmentOptions, create_environment};
use tla_front::errors::FrontError;
use tla_front::eval::Evaluator;
use tla_front::hash::FastMap;
use tla_front::spec::create_identifier;
use tla_front::values::ValueOrder;

fn link(source: &str) -> Result<Environment, FrontError> {
    link_in("overrides", source)
}

// Links the spec with the classes of the fixture directory `fixture`.
fn link_in(fixture: &str, source: &str) -> Result<Environment, FrontError> {
    let directory = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../../tests/fixtures")
        .join(fixture);
    let config = parse_config("", TlcVersion::Master).expect("a configuration");
    let load_class = |name: &str| std::fs::read(directory.join(format!("{name}.class"))).ok();
    create_environment(&EnvironmentOptions {
        source,
        load_module: &|_| None,
        config: &config,
        is_unconfigured: true,
        version: TlcVersion::Master,
        is_level_checked: false,
        load_class: Some(&load_class),
    })
}

#[test]
fn replaces_each_operator_with_the_method_of_the_same_name_and_arity() {
    let source = std::fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../../tests/fixtures/overrides/Overrides.tla"),
    )
    .expect("the spec");
    let environment = link(&source).expect("an environment");
    let ranks: FastMap<Rc<str>, u32> = FastMap::default();
    let evaluator = Evaluator::new(
        &environment,
        ValueOrder { ranks: &ranks },
        TlcVersion::Master,
        true,
    );
    let evaluate = |name: &str| {
        evaluator
            .evaluate(&create_identifier(name), None)
            .expect("a value")
    };
    assert_eq!(evaluate("Flag"), ConfigValue::Boolean(true));
    assert_eq!(evaluate("Small"), ConfigValue::Number(3.0));
    assert_eq!(evaluate("Large"), ConfigValue::Number(100_000.0));
    assert_eq!(evaluate("Name"), ConfigValue::String("java".to_owned()));
    // Mismatch takes no argument, so the method of one doesn't override it.
    assert_eq!(evaluate("Mismatch"), ConfigValue::Boolean(true));
    let matched: Vec<(&str, bool)> = environment
        .java_overrides
        .iter()
        .map(|java_override| (java_override.operator.as_str(), java_override.is_matched))
        .collect();
    assert_eq!(
        matched,
        [
            ("Flag", true),
            ("Small", true),
            ("Large", true),
            ("Name", true),
            ("Twice", false),
            ("Mismatch", false),
            ("Computed", false),
        ]
    );
    assert_eq!(
        environment.java_overrides[4].signature,
        "public static tlc2.value.impl.Value Overrides.Twice(tlc2.value.impl.Value)"
    );
}

#[test]
fn leaves_an_override_that_computes_its_value_to_java() {
    let error = link("---- MODULE Overrides ----\nComputed == 0\n====\n").err();
    assert!(matches!(error, Some(FrontError::NotYet(_))), "{error:?}");
}

#[test]
fn leaves_an_override_with_parameters_to_java() {
    // TLC evaluates 1 \div 0 before it calls Twice, and reports the division, not -2.
    let error = link(
        "---- MODULE Overrides ----\nEXTENDS Integers\nVARIABLE x\nTwice(n) == 2 * n\nInit == x = Twice(1 \\div 0)\n====\n",
    )
    .err();
    assert!(matches!(error, Some(FrontError::NotYet(_))), "{error:?}");
}

#[test]
fn leaves_an_override_class_it_does_not_read_whole_to_java() {
    // tests/fixtures/override-shapes: in each, TLC runs what the front end can't, or matches
    // otherwise (each P.java says what TLC does).
    for (shape, reason) in [
        ("clinit", "a Java override class with a static initializer"),
        ("field", "a Java override class with fields"),
        ("super", "a Java override class with a superclass"),
        ("overload", "a Java override class with methods of one name"),
        (
            "registry",
            "a Java override of a name TLC maps to an operator's",
        ),
    ] {
        let directory = format!("override-shapes/{shape}");
        let source = std::fs::read_to_string(
            Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../../../tests/fixtures")
                .join(&directory)
                .join("P.tla"),
        )
        .expect("the spec");
        let error = link_in(&directory, &source).err();
        assert!(
            matches!(&error, Some(FrontError::NotYet(message)) if message == reason),
            "{shape}: {error:?}"
        );
    }
}

#[test]
fn skips_an_annotated_method_and_runs_a_method_that_catches() {
    // tests/fixtures/override-shapes: TLC skips the method annotated @TLAPlusOperator, so K stays
    // 1, and runs the try block of the one that catches, which returns 0.
    for (shape, value) in [("annotation", 1.0), ("trycatch", 0.0)] {
        let directory = format!("override-shapes/{shape}");
        let source = std::fs::read_to_string(
            Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../../../tests/fixtures")
                .join(&directory)
                .join("P.tla"),
        )
        .expect("the spec");
        let environment = link_in(&directory, &source).expect("an environment");
        let ranks: FastMap<Rc<str>, u32> = FastMap::default();
        let evaluator = Evaluator::new(
            &environment,
            ValueOrder { ranks: &ranks },
            TlcVersion::Master,
            true,
        );
        assert_eq!(
            evaluator.evaluate(&create_identifier("K"), None),
            Ok(ConfigValue::Number(value)),
            "{shape}"
        );
    }
}
