//! Linking and name resolution on small specs. `scripts/front-differential.ts resolve` holds the
//! Rust environment to the TypeScript one on every corpus module.

use tla_front::TlcVersion;
use tla_front::ast::{DefinitionKind, Expression, ExpressionKind};
use tla_front::environment::{Environment, EnvironmentOptions, create_environment};
use tla_front::errors::FrontError;

fn link(source: &str, modules: &[(&str, &str)]) -> Result<Environment, FrontError> {
    let load_module = |name: &str| {
        modules
            .iter()
            .find(|module| module.0 == name)
            .map(|module| module.1.to_owned())
    };
    create_environment(&EnvironmentOptions {
        source,
        load_module: &load_module,
        version: TlcVersion::Master,
    })
}

fn keys(environment: &Environment) -> Vec<String> {
    environment
        .definitions
        .keys()
        .map(|key| key.to_string())
        .collect()
}

fn sany_messages(error: FrontError) -> Vec<String> {
    let FrontError::Syntax(error) = error else {
        panic!("a syntax error");
    };
    error
        .sany
        .expect("SANY's errors")
        .errors
        .into_iter()
        .map(|error| format!("{}: {}", error.location, error.message))
        .collect()
}

fn args(expression: &Expression) -> Vec<&Expression> {
    match &expression.kind {
        ExpressionKind::Apply { args, .. } => args.iter().map(|arg| &**arg).collect(),
        _ => Vec::new(),
    }
}

#[test]
fn keys_the_definitions_of_extended_modules_and_resolves_names_to_them() {
    let environment = link(
        "---- MODULE Main ----\nEXTENDS Base, Naturals\nVARIABLE y\nNext == Inc(y)\n====",
        &[(
            "Base",
            "---- MODULE Base ----\nEXTENDS Naturals\nCONSTANT N\nInc(x) == x + N\n====",
        )],
    )
    .expect("an environment");
    assert_eq!(keys(&environment), ["Inc@Base", "Next", "Inc"]);
    let next = environment.definitions.get("Next").expect("Next");
    assert_eq!(next.body.reference().as_deref(), Some("Inc@Base"));
    assert!(!next.body.resolved.is_local.get());
    let increment = environment.definitions.get("Inc@Base").expect("Inc");
    let operands = args(&increment.body);
    assert!(operands[0].resolved.is_local.get());
    assert_eq!(operands[1].reference().as_deref(), Some("N"));
    assert!(environment.builtins.contains_key("+"));
    assert_eq!(
        environment
            .variable_index
            .keys()
            .map(|key| &**key)
            .collect::<Vec<_>>(),
        ["y", "y@ENABLED"]
    );
}

#[test]
fn marks_a_function_that_applies_itself() {
    let environment = link(
        "---- MODULE Main ----\nEXTENDS Naturals\nf[n \\in Nat] == IF n = 0 THEN 1 ELSE n * f[n - 1]\n====",
        &[],
    )
    .expect("an environment");
    let definition = environment.definitions.get("f").expect("f");
    assert!(matches!(definition.kind, DefinitionKind::Function { .. }));
    assert_eq!(definition.is_self_referential.get(), Some(true));
}

#[test]
fn reports_sany_errors_in_the_order_of_the_units() {
    let error = link("---- MODULE Main ----\nA == B\nB == 1 + 2\n====", &[])
        .err()
        .expect("an error");
    assert_eq!(
        sany_messages(error),
        [
            "line 2, col 6 to line 2, col 6 of module Main: Unknown operator: `B'.",
            "line 3, col 8 to line 3, col 8 of module Main: Could not find declaration or definition of symbol '+'.",
            "line 3, col 6 to line 3, col 10 of module Main: Couldn't resolve infix operator symbol `+'.",
        ]
    );
}

#[test]
fn reports_a_missing_module_in_its_importer() {
    let error = link("---- MODULE Main ----\nEXTENDS Missing\n====", &[])
        .err()
        .expect("an error");
    assert_eq!(
        sany_messages(error),
        ["In module Main: Cannot find source file for module Missing imported in module Main."]
    );
}

#[test]
fn leaves_an_instance_for_later() {
    let error = link("---- MODULE Main ----\nI == INSTANCE Naturals\n====", &[])
        .err()
        .expect("an error");
    assert_eq!(error, FrontError::NotYet("an INSTANCE".to_owned()));
}
