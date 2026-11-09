//! SANY's level checks on small specs. `scripts/front-differential.ts levels` holds the Rust checks
//! to the TypeScript ones on every corpus module.

use tla_front::TlcVersion;
use tla_front::config::parse_config;
use tla_front::environment::{EnvironmentOptions, create_environment};
use tla_front::errors::FrontError;

fn get_level_errors(source: &str, modules: &[(&str, &str)]) -> Vec<(String, String)> {
    let config = parse_config("", TlcVersion::Master).expect("a configuration");
    let load_module = |name: &str| {
        modules
            .iter()
            .find(|module| module.0 == name)
            .map(|module| module.1.to_owned())
    };
    let linked = create_environment(&EnvironmentOptions {
        source,
        load_module: &load_module,
        config: &config,
        is_unconfigured: true,
        version: TlcVersion::Master,
        is_level_checked: true,
        load_class: None,
    });
    let Err(FrontError::Syntax(error)) = linked else {
        return Vec::new();
    };
    error
        .sany
        .expect("SANY's errors")
        .errors
        .into_iter()
        .map(|error| (error.location, error.message))
        .collect()
}

#[test]
fn rejects_an_action_under_always() {
    assert_eq!(
        get_level_errors(
            "---- MODULE Main ----\nVARIABLE x\nBad == [](x' = x)\n====",
            &[]
        ),
        [(
            "line 3, col 8 to line 3, col 17 of module Main".to_owned(),
            "[] followed by action not of form [A]_v.".to_owned()
        )]
    );
}

#[test]
fn rejects_an_action_operator_substituted_for_a_constant_operator() {
    let location = "line 4, col 1 to line 4, col 40 of module Main".to_owned();
    assert_eq!(
        get_level_errors(
            "---- MODULE Main ----\nVARIABLE x\nP(a) == a'\nI == INSTANCE Inner WITH Op <- P, y <- x\n====",
            &[(
                "Inner",
                "---- MODULE Inner ----\nCONSTANT Op(_)\nVARIABLE y\nUse == Op(y)\n===="
            )]
        ),
        [
            (
                location.clone(),
                "Level error in instantiating module 'Inner':\nThe level of the expression or operator substituted for 'Op' \nmust be at most 0.".to_owned()
            ),
            (
                location,
                "Error in instantiating module 'Inner':\n A non-Leibniz operator substituted for 'Op'.".to_owned()
            )
        ]
    );
}

#[test]
fn accepts_a_box_action() {
    assert!(
        get_level_errors(
            "---- MODULE Main ----\nEXTENDS Naturals\nVARIABLE x\nSpec == x = 0 /\\ [][x' = x + 1]_x\n====",
            &[]
        )
        .is_empty()
    );
}
