//! TLC's errors for a property that is an action, from its test-model/ActionLevelProp.tla and the
//! ActionLevelProp*Test cases.

use std::path::Path;

use tla_front::errors::FrontError;
use tla_front::model::{ModelOptions, lower_model};

const SPEC: &str = "---- MODULE ActionLevelProp ----
EXTENDS Naturals

VARIABLE x
vars == x

Init ==
    x = 0

Next ==
    /\\ x < 5
    /\\ x' = x + 1

Spec ==
    Init /\\ [][Next]_vars

------

ActionLivePropA ==
    x' > x

ActionLivePropB ==
\tNext

ActionLivePropC ==
    Next \\/ UNCHANGED vars

ActionLivePropD ==
    [Next]_vars

ActionLivePropE ==
    <<Next>>_vars

=============================================================================
";

const ACTION_LEVEL: &str = "is an action-level formula (i.e., it contains no temporal operators). Only temporal-level (or state-level) formulas are allowed under PROPERTY or PROPERTIES.";

fn lower(property: &str) -> FrontError {
    let directory = std::env::temp_dir().join(format!(
        "tla-front-properties-{property}-{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&directory).expect("a directory");
    let path = directory.join("ActionLevelProp.tla");
    std::fs::write(&path, SPEC).expect("the spec");
    let options = ModelOptions {
        libraries: &[],
        version: None,
        is_warning_enabled: true,
        is_spec_described: false,
        random_seed: 0,
        root_extendees: &[],
    };
    let config = format!("SPECIFICATION Spec\nPROPERTY {property}\n");
    let lowered = lower_model(&path, &config, &options);
    std::fs::remove_dir_all(&directory).expect("removed");
    lowered.expect_err("TLC rejects the property")
}

fn coded(property: &str) -> (u32, String, i32) {
    let coded = lower(property).get_coded(false).expect("a coded error");
    (coded.code, coded.text, coded.exit_code)
}

#[test]
fn rewrites_an_action_as_always_it_in_a_subscript() {
    let at = "line 20, col 5 to line 20, col 10 of module ActionLevelProp";
    assert_eq!(
        coded("ActionLivePropA"),
        (
            2272,
            format!(
                "The formula ActionLivePropA at {at} {ACTION_LEVEL} To check that action ActionLivePropA holds in *every* step of the behavior, define a temporal property: Let A be the formula at {at}; rewrite A as [][A]_v, where v is a state function (typically the tuple of variables) (compare page 90 of Specifying Systems at https://lamport.azurewebsites.net/tla/book.html)."
            ),
            151,
        )
    );
}

#[test]
fn names_a_conjunct_of_an_action_by_its_location() {
    let at = "line 12, col 8 to line 12, col 17 of module ActionLevelProp";
    let (code, text, _) = coded("ActionLivePropB");
    assert_eq!(code, 2272);
    assert!(text.starts_with(&format!("The formula {at} at {at} {ACTION_LEVEL}")));
}

#[test]
fn applies_always_to_a_box_action_and_always_eventually_to_an_angle_action() {
    let box_at = "line 29, col 5 to line 29, col 15 of module ActionLevelProp";
    assert_eq!(
        coded("ActionLivePropD"),
        (
            2273,
            format!(
                "The formula ActionLivePropD at {box_at} {ACTION_LEVEL} To check that action ActionLivePropD holds in *every* step of the behavior, define a temporal property by applying the \"always\" temporal operator ([]) to the formula at {box_at} (compare page 90 of Specifying Systems at https://lamport.azurewebsites.net/tla/book.html)."
            ),
            151,
        )
    );
    let angle_at = "line 32, col 5 to line 32, col 17 of module ActionLevelProp";
    assert_eq!(
        coded("ActionLivePropE"),
        (
            2274,
            format!(
                "The formula ActionLivePropE at {angle_at} {ACTION_LEVEL} To check that infinitely many ActionLivePropE steps occur, define a temporal property by applying the \"always eventually\" temporal operator combination ([]<>) to the formula at {angle_at} (compare page 91 of Specifying Systems at https://lamport.azurewebsites.net/tla/book.html)."
            ),
            151,
        )
    );
    assert_eq!(coded("ActionLivePropC").0, 2272);
}

// The names of the invariants a property asserts, as the model holds them for TLC's reports.
fn get_property_invariant_names(config: &str) -> Vec<String> {
    let fixtures =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../tests/fixtures/instance-property");
    let options = ModelOptions {
        libraries: &[],
        version: None,
        is_warning_enabled: true,
        is_spec_described: false,
        random_seed: 0,
        root_extendees: &[],
    };
    let config = std::fs::read_to_string(fixtures.join(config)).expect("the configuration");
    let ir = lower_model(&fixtures.join("Main.tla"), &config, &options).expect("the model");
    let ir = tla_ir::decode(&ir).expect("an IR that decodes");
    ir.model
        .property_invariant_names
        .iter()
        .map(|&name| ir.texts[name as usize].to_string())
        .collect()
}

#[test]
fn names_a_property_an_instance_exports_as_written() {
    // `opNode.getName()`: PSafe == A!Safe names A!Safe, but A!Safe2 == Safe names Safe.
    assert_eq!(get_property_invariant_names("Main.cfg"), ["A!Safe"]);
    assert_eq!(get_property_invariant_names("Inner.cfg"), ["Safe"]);
}
