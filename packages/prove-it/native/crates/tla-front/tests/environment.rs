//! Linking and name resolution on small specs. `scripts/front-differential.ts resolve` holds the
//! Rust environment to the TypeScript one on every corpus module.

use tla_front::TlcVersion;
use tla_front::ast::{DefinitionKind, Expression, ExpressionKind};
use tla_front::config::parse_config;
use tla_front::environment::{Environment, EnvironmentOptions, create_environment};
use tla_front::errors::{FrontError, describe_range};

fn link(source: &str, modules: &[(&str, &str)]) -> Result<Environment, FrontError> {
    link_model(source, modules, None)
}

fn link_model(
    source: &str,
    modules: &[(&str, &str)],
    config: Option<&str>,
) -> Result<Environment, FrontError> {
    let model = parse_config(config.unwrap_or(""), TlcVersion::Master).expect("a configuration");
    let load_module = |name: &str| {
        modules
            .iter()
            .find(|module| module.0 == name)
            .map(|module| module.1.to_owned())
    };
    create_environment(&EnvironmentOptions {
        source,
        load_module: &load_module,
        config: &model,
        is_unconfigured: config.is_none(),
        version: TlcVersion::Master,
        is_level_checked: false,
        load_class: None,
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
fn sees_a_declaration_only_after_it() {
    let error = link(
        "---- MODULE Main ----\nFoo == x = 1\nVARIABLE x\nP == INSTANCE Counter\nVARIABLE y\n====",
        &[("Counter", "---- MODULE Counter ----\nVARIABLE x, y\n====")],
    )
    .err()
    .expect("an error");
    assert_eq!(
        sany_messages(error),
        [
            "line 2, col 8 to line 2, col 8 of module Main: Unknown operator: `x'.",
            "line 4, col 1 to line 4, col 21 of module Main: Substitution missing for symbol y declared at line 2, col 13 to line 2, col 13 of module Counter \nand instantiated in module Main.",
        ]
    );
}

#[test]
fn copies_the_definitions_an_instance_substitutes_into() {
    let environment = link(
        "---- MODULE Main ----\nVARIABLE y\nC == INSTANCE Counter WITH x <- y\nNext == C!Step\n====",
        &[(
            "Counter",
            "---- MODULE Counter ----\nVARIABLE x\nStep == x' = x\n====",
        )],
    )
    .expect("an environment");
    assert_eq!(
        keys(&environment),
        ["Step@Counter", "Step@Main#1", "Next", "C!Step"]
    );
    let copy = environment
        .definitions
        .get("Step@Main#1")
        .expect("the copy");
    assert!(environment.is_substituted(copy));
    let ExpressionKind::Apply { args, .. } = &copy.body.kind else {
        panic!("an application");
    };
    let ExpressionKind::Prime(primed) = &args[0].kind else {
        panic!("a primed variable");
    };
    assert_eq!(primed.reference().as_deref(), Some("y"));
    let next = environment.definitions.get("Next").expect("Next");
    assert_eq!(next.body.reference().as_deref(), Some("Step@Main#1"));
}

#[test]
fn selects_the_labeled_part_of_a_definition() {
    let environment = link(
        "---- MODULE Main ----\nEXTENDS Naturals\nInv == lab :: 1 + 2\nPart == Inv!lab\n====",
        &[],
    )
    .expect("an environment");
    let part = environment.definitions.get("Part").expect("Part");
    let ExpressionKind::Apply { args, .. } = &part.body.kind else {
        panic!("the selected sum, not {:?}", part.body.kind);
    };
    assert_eq!(args.len(), 2);
    assert_eq!(part.body.reference().as_deref(), Some("+"));
}

#[test]
fn assigns_and_substitutes_the_constants_of_the_configuration() {
    let source = "---- MODULE Main ----\nEXTENDS Naturals\nCONSTANTS N, Op(_)\nM == 3\nDouble(x) == 2 * x\n====";
    let environment =
        link_model(source, &[], Some("CONSTANT N <- M\nOp <- Double")).expect("an environment");
    assert_eq!(
        environment
            .substitutions
            .iter()
            .map(|(key, target)| format!("{key} <- {target}"))
            .collect::<Vec<_>>(),
        ["N <- M", "Op <- Double"]
    );
    let error = link_model(source, &[], Some("CONSTANT N = 1"))
        .err()
        .expect("an error");
    assert_eq!(
        error,
        FrontError::Config(
            "The constant parameter Op is not assigned a value by the configuration file."
                .to_owned()
        )
    );
}

#[test]
fn rejects_a_substitute_that_fails_at_startup() {
    // TLC's etest7 and TLCGetNamedUndefined: TLC evaluates a non-constant substitute at startup.
    let variable = "---- MODULE Main ----\nCONSTANT C\nVARIABLE x\nFoo == x\n====";
    assert_eq!(
        link_model(variable, &[], Some("CONSTANT C <- Foo")).err(),
        Some(FrontError::Config(
            "The configuration file substitutes constant C with non-constant Foo - specifically: In evaluation, the identifier x is either undefined or not an operator.\nline 4, col 8 to line 4, col 8 of module Main".to_owned()
        ))
    );
    let checker =
        "---- MODULE Main ----\nEXTENDS TLC\nCONSTANT A\nqueue == TLCGet(\"queue\")\n====";
    let error = link_model(checker, &[], Some("CONSTANT A <- queue")).err();
    assert!(
        matches!(error, Some(FrontError::Config(message)) if message.ends_with("TLCGet(queue) was undefined."))
    );
}

#[test]
fn lists_the_assumptions_and_startup_definitions_of_a_model() {
    let environment = link_model(
        "---- MODULE Main ----\nEXTENDS Base\nASSUME Two == N > 1\nAXIOM N > 0\nDouble == 2 * N\nInit == TRUE\n====",
        &[(
            "Base",
            "---- MODULE Base ----\nEXTENDS Naturals\nCONSTANT N\nASSUME N \\in Nat\nHalf == N \\div 2\n====",
        )],
        Some("CONSTANT N = 3\nINIT Init\nNEXT Init"),
    )
    .expect("an environment");
    let assumptions: Vec<String> = environment
        .assumptions
        .iter()
        .map(|assumption| describe_range(&assumption.expression))
        .collect();
    assert_eq!(
        assumptions,
        [
            "line 4, col 8 to line 4, col 16 of module Base",
            "line 3, col 15 to line 3, col 19 of module Main",
            "line 4, col 7 to line 4, col 11 of module Main",
        ]
    );
    let startup: Vec<&str> = environment
        .startup_definitions
        .iter()
        .map(|definition| &*definition.name)
        .collect();
    assert!(startup.contains(&"Half") && startup.contains(&"Double"));
}
