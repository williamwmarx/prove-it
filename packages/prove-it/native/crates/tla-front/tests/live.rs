//! The liveness checker's atoms, formula and properties in a model's IR, as `lowerToIr` writes
//! them from `createLivenessChecker`.

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
====
";

fn lower(test: &str, config: &str) -> tla_ir::Model {
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
    let bytes = lower_model(&path, config, &options).expect("a model the front end lowers");
    std::fs::remove_dir_all(&directory).expect("removed");
    tla_ir::decode(&bytes).expect("an IR that decodes").model
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
