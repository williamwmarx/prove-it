//! TLC's checks of the invariants a configuration names, which it makes before it reads the
//! specification (`getInvariants` in `search.ts`, `processConfigInvariants` in TLC).

use tla_front::errors::FrontError;
use tla_front::model::{ModelOptions, lower_model};

// TLC's test-model/testinvalidinvariant.tla.
const SPEC: &str = "------------------ MODULE testinvalidinvariant --------------------
EXTENDS Integers

VARIABLES x
Init == /\\ x = 1
Next == /\\ x'= x + 1
Spec == Init /\\ [][Next]_<<x>>

\\* Primed variable is invalid.
Invariant == x' \\in Nat
Holds == x \\in Nat
==================================================================
";

fn lower(test: &str, config: &str) -> Result<Vec<u8>, FrontError> {
    let directory = std::env::temp_dir().join(format!(
        "tla-front-invariants-{test}-{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&directory).expect("a directory");
    let path = directory.join("testinvalidinvariant.tla");
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

#[test]
fn reports_an_invariant_that_is_no_state_predicate_before_an_undefined_property() {
    let error = lower(
        "level",
        "SPECIFICATION Spec\nPROPERTY Property\nINVARIANT Invariant\n",
    )
    .expect_err("TLC rejects the invariant");
    let coded = error.get_coded(false).expect("a coded error");
    assert_eq!(
        (coded.code, coded.text.as_str(), coded.exit_code),
        (
            2146,
            "The invariant Invariant is not a state predicate (one with no primes or temporal operators).",
            76,
        )
    );
}

#[test]
fn takes_a_state_predicate_as_an_invariant() {
    lower("state", "SPECIFICATION Spec\nINVARIANT Holds\n").expect("a model it lowers");
}
