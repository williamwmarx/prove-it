//! The liveness checker's atoms, formula and properties in a model's IR, as `lowerToIr` writes
//! them from `createLivenessChecker`.

use tla_front::errors::{FrontError, UNEXPECTED_EXCEPTION};
use tla_front::model::{ModelOptions, lower_model};
use tla_ir::{AtomKind, EnabledActions, LiveTerm};

const SPEC: &str = "---- MODULE Live ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = (x + 1) % 3
Spec == Init /\\ [][Next]_x /\\ WF_x(Next)
Returns == []<>(x = 0)
Visits == \\E v \\in {0, 1} : []<>(x = v)
Chosen == IF 1 > 0 THEN []<>(x = 0) ELSE <>(x = 1)
Enumerated == (CHOOSE f \\in [STRING -> {0}] : TRUE) = 0 => []<>(x = 0)
====
";

fn try_lower(test: &str, config: &str) -> Result<Vec<u8>, FrontError> {
    let directory =
        std::env::temp_dir().join(format!("tla-front-live-{test}-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    let path = directory.join("Live.tla");
    std::fs::write(&path, SPEC).expect("the spec");
    let options = ModelOptions {
        libraries: &[],
        version: None,
        is_warning_enabled: true,
        is_spec_described: false,
    };
    let lowered = lower_model(&path, config, &options);
    std::fs::remove_dir_all(&directory).expect("removed");
    lowered
}

fn lower(test: &str, config: &str) -> tla_ir::Model {
    let bytes = try_lower(test, config).expect("a model the front end lowers");
    tla_ir::decode(&bytes).expect("an IR that decodes").model
}

#[test]
fn reports_a_constant_part_that_fails_as_an_exception_tlc_did_not_expect() {
    // TLC's enumerateSet throws a RuntimeException, which the liveness checker doesn't catch.
    let error = try_lower("enumerated", "SPECIFICATION Spec\nPROPERTY Enumerated\n")
        .expect_err("a failure");
    assert_eq!(
        error,
        FrontError::Evaluation(format!(
            "{UNEXPECTED_EXCEPTION}Attempted to enumerate a set of the form [D -> R],but the domain D:\nSTRING\ncannot be enumerated."
        ))
    );
}

#[test]
fn writes_the_fairness_and_the_negated_property_with_their_atoms() {
    let model = lower("property", "SPECIFICATION Spec\nPROPERTY Returns\n");
    assert!(model.is_recording_graph);
    // The checker asks of WF's ENABLED and the property's predicate first, then of the action,
    // whose ENABLED is the first atom.
    let kinds: Vec<&AtomKind> = model.atoms.iter().map(|atom| &atom.kind).collect();
    assert!(matches!(
        kinds[..],
        [
            AtomKind::Enabled {
                actions: EnabledActions::Unknown
            },
            AtomKind::State,
            AtomKind::Action {
                unchanged: Some(_),
                enabled: Some(0)
            },
        ]
    ));
    assert_eq!(
        model.live_formula,
        [
            LiveTerm::And(2),
            LiveTerm::Always,
            LiveTerm::Eventually,
            LiveTerm::Or(2),
            LiveTerm::Not,
            LiveTerm::Enabled(0),
            LiveTerm::Action {
                atom: 2,
                enabled: Some(0)
            },
            LiveTerm::Not,
            LiveTerm::Always,
            LiveTerm::Eventually,
            LiveTerm::State(1),
        ]
    );
    assert_eq!(model.live_properties.len(), 1);
    assert_eq!(
        model.live_properties[0].formula,
        [LiveTerm::Always, LiveTerm::Eventually, LiveTerm::State(1)]
    );
}

#[test]
fn checks_nothing_of_fairness_without_a_temporal_property() {
    let model = lower("fairness", "SPECIFICATION Spec\n");
    assert!(!model.is_recording_graph);
    assert!(model.atoms.is_empty() && model.live_formula.is_empty());
}

#[test]
fn expands_a_quantifier_over_a_constant_set_and_chooses_a_constant_branch() {
    let model = lower("constant", "SPECIFICATION Spec\nPROPERTIES Visits Chosen\n");
    assert_eq!(model.live_properties.len(), 2);
    let visits = &model.live_properties[0].formula;
    assert!(matches!(
        visits[..],
        [
            LiveTerm::Or(2),
            LiveTerm::Always,
            LiveTerm::Eventually,
            LiveTerm::State(first),
            LiveTerm::Always,
            LiveTerm::Eventually,
            LiveTerm::State(second),
        ] if first != second
    ));
    assert!(matches!(
        model.live_properties[1].formula[..],
        [LiveTerm::Always, LiveTerm::Eventually, LiveTerm::State(_)]
    ));
}
