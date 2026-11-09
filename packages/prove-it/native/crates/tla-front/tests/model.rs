//! The checks `createSearch` makes of a model's configuration before `lower_model` lowers it.
//! `scripts/front-differential.ts model-full` holds the model to `check.ts` on every corpus model.

use tla_front::errors::FrontError;
use tla_front::model::{ModelOptions, lower_model};

const SPEC: &str = "---- MODULE Checked ----
EXTENDS Integers
VARIABLE x
CONSTANT Flag
Init == x = 0
Next == x' = x
Small == x < 3
Step == x' = x
Never == 1 > 2
Below == -1 \\in Nat
Spec == Init /\\ [][Next]_x
Boxed == Spec /\\ [](x < 3)
Flagged == Spec /\\ Flag
====
";

fn lower(test: &str, config: &str) -> Result<Vec<u8>, FrontError> {
    let directory =
        std::env::temp_dir().join(format!("tla-front-model-{test}-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    let path = directory.join("Checked.tla");
    std::fs::write(&path, SPEC).expect("the spec");
    let options = ModelOptions {
        libraries: &[],
        version: None,
        is_warning_enabled: true,
    };
    let lowered = lower_model(&path, config, &options);
    std::fs::remove_dir_all(&directory).expect("removed");
    lowered
}

fn config_error(test: &str, config: &str) -> String {
    match lower(test, config) {
        Err(FrontError::Config(message)) => message,
        other => panic!("a configuration error, not {other:?}"),
    }
}

#[test]
fn rejects_what_the_configuration_names_as_tlc_does() {
    assert_eq!(
        config_error("init", "CONSTANT Flag = TRUE\nNEXT Next\n"),
        "The configuration file did not specify the initial state predicate."
    );
    assert_eq!(
        config_error(
            "constraint",
            "CONSTANT Flag = TRUE\nINIT Init\nNEXT Next\nCONSTRAINT Bound\n"
        ),
        "The constraint Bound specified in the configuration file\nis not defined in the specification."
    );
    assert_eq!(
        config_error(
            "action",
            "CONSTANT Flag = TRUE\nINIT Init\nNEXT Next\nINVARIANT Step\n"
        ),
        "The invariant Step is not a state predicate (one with no primes or temporal operators).\nNote that a bug can cause TLC to incorrectly report this error.\nIf you believe your TLA+ or PlusCal specification to be correct,\nplease check if this bug described in LevelNode.java starting at line 590ff affects you."
    );
    assert_eq!(
        config_error(
            "false",
            "CONSTANT Flag = TRUE\nINIT Init\nNEXT Next\nINVARIANT Never\n"
        ),
        "The invariant of Never is equal to FALSE"
    );
}

#[test]
fn evaluates_a_constant_invariant_with_the_configuration_substitutions() {
    assert!(
        lower(
            "substituted",
            "CONSTANT Flag = TRUE\nCONSTANT Nat <- Int\nINIT Init\nNEXT Next\nINVARIANT Below\n"
        )
        .is_ok()
    );
    assert_eq!(
        config_error(
            "unsubstituted",
            "CONSTANT Flag = TRUE\nINIT Init\nNEXT Next\nINVARIANT Below\n"
        ),
        "The invariant of Below is equal to FALSE"
    );
    assert!(
        lower(
            "state",
            "CONSTANT Flag = TRUE\nINIT Init\nNEXT Next\nINVARIANT Small\nCONSTRAINT Small\n"
        )
        .is_ok()
    );
}

#[test]
fn reads_the_conjuncts_of_the_specification_as_tlc_does() {
    assert_eq!(
        config_error("trivial", "CONSTANT Flag = FALSE\nSPECIFICATION Flagged\n"),
        "The spec is trivially false because Flag is false."
    );
    assert_eq!(
        config_error("number", "CONSTANT Flag = 3\nSPECIFICATION Flagged\n"),
        "The operator Flag, which equals 3,\ncannot be used as a spec"
    );
    assert!(lower("true", "CONSTANT Flag = TRUE\nSPECIFICATION Flagged\n").is_ok());
    assert!(matches!(
        lower("boxed", "CONSTANT Flag = TRUE\nSPECIFICATION Boxed\n"),
        Err(FrontError::Evaluation(message))
            if message == "TLC cannot handle the temporal formula line 12, col 21 to line 12, col 25 of module Checked"
    ));
}
