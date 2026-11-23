//! The liveness checker's atoms, formula and properties in a model's IR, as `lowerToIr` writes
//! them from `createLivenessChecker`.

use tla_front::errors::{FrontError, UNEXPECTED_EXCEPTION};
use tla_front::model::{LoweredModel, ModelOptions, lower_front};
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
Constant == 1 + 1 = 2
Zero == x = 0
Enumerated == (CHOOSE f \\in [STRING -> {0}] : TRUE) = 0 => []<>(x = 0)
Redefined == x \\in {0, 1} /\\ Init
Fair == WF_x(Next)
FairAlias == Fair
NamedSpec == Init /\\ [][Next]_x /\\ FairAlias
ExtraSpec == NamedSpec /\\ SF_x(Next)
OtherFair == SF_x(Next)
====
";

fn try_lower(test: &str, config: &str) -> Result<Vec<u8>, FrontError> {
    try_lower_front(test, config, true).map(|lowered| lowered.ir)
}

fn try_lower_front(
    test: &str,
    config: &str,
    is_warning_enabled: bool,
) -> Result<LoweredModel, FrontError> {
    let directory =
        std::env::temp_dir().join(format!("tla-front-live-{test}-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    let path = directory.join("Live.tla");
    std::fs::write(&path, SPEC).expect("the spec");
    let options = ModelOptions {
        libraries: &[],
        version: None,
        is_warning_enabled,
        is_spec_described: false,
        random_seed: 0,
        root_extendees: &[],
    };
    let lowered = lower_front(&path, config, &options);
    std::fs::remove_dir_all(&directory).expect("removed");
    lowered
}

fn lower(test: &str, config: &str) -> tla_ir::Model {
    let bytes = try_lower(test, config).expect("a model the front end lowers");
    tla_ir::decode(&bytes).expect("an IR that decodes").model
}

#[test]
fn overflows_on_an_initial_predicate_the_configuration_redefines_by_itself() {
    // The shape of TLC's CyclicRedefineVars: Init <- Redefined, whose body names Init. TLC
    // overflows its stack as it reads the specification.
    let error = try_lower("cyclic", "SPECIFICATION Spec\nCONSTANT Init <- Redefined\n")
        .expect_err("TLC overflows its stack");
    assert!(matches!(error, FrontError::StackOverflow), "{error:?}");
}

#[test]
fn reports_a_constant_part_that_fails_as_an_exception_tlc_did_not_expect() {
    // TLC's enumerateSet throws a RuntimeException, which the liveness checker doesn't catch.
    // Without a symmetry or warnings about the spec, TLC warns of nothing before.
    let error = try_lower("enumerated", "SPECIFICATION Spec\nPROPERTY Enumerated\n")
        .expect_err("a failure");
    assert_eq!(
        error,
        FrontError::Warned(
            Vec::new(),
            Box::new(FrontError::Evaluation(format!(
                "{UNEXPECTED_EXCEPTION}Attempted to enumerate a set of the form [D -> R],but the domain D:\nSTRING\ncannot be enumerated."
            )))
        )
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

fn startup_messages(config: &str, is_warning_enabled: bool) -> Vec<(u32, bool, String)> {
    try_lower_front("startup", config, is_warning_enabled)
        .expect("a model the front end lowers")
        .startup_messages
        .expect("the startup messages")
        .into_iter()
        .map(|message| (message.code, message.is_warning, message.text))
        .collect()
}

#[test]
fn writes_what_tlc_prints_as_it_starts() {
    let config = "SPECIFICATION Spec\nINVARIANT Constant\nPROPERTY Zero Returns\n";
    let messages = startup_messages(config, true);
    let codes: Vec<(u32, bool)> = messages
        .iter()
        .map(|(code, is_warning, _)| (*code, *is_warning))
        .collect();
    assert_eq!(codes, [(2149, true), (2255, true), (2212, false)]);
    assert!(
        messages[0]
            .2
            .starts_with("The invariant Constant is a constant-level formula")
    );
    assert!(
        messages[1]
            .2
            .starts_with("The formula Zero is a state-level formula")
    );
    assert_eq!(
        messages[2].2,
        "Implied-temporal checking--satisfiability problem has 1 branches."
    );
    // -nowarning drops TLC's warnings.
    let codes: Vec<u32> = startup_messages(config, false)
        .iter()
        .map(|(code, _, _)| *code)
        .collect();
    assert_eq!(codes, [2212]);
    assert!(startup_messages("SPECIFICATION Spec\n", true).is_empty());
}

#[test]
fn warns_when_one_named_property_contains_all_specification_temporals() {
    let model = try_lower_front(
        "fairness-tautology",
        "SPECIFICATION NamedSpec\nPROPERTY Fair\n",
        true,
    )
    .expect("a lowered model");
    let warnings = model.startup_messages.expect("startup messages");
    assert_eq!(
        warnings
            .iter()
            .filter(|message| message.code == 2258)
            .count(),
        1
    );
    let warning = warnings
        .iter()
        .find(|message| message.code == 2258)
        .unwrap();
    assert!(warning.is_warning);
    assert!(
        warning
            .text
            .contains("The temporal formula Fair at line 14, col 1")
    );
    assert!(warning.text.ends_with(
        "checking whether NamedSpec => Fair using TLC will never result in a violation of Fair."
    ));
    for (name, config, enabled) in [
        ("extra", "SPECIFICATION ExtraSpec\nPROPERTY Fair\n", true),
        (
            "two",
            "SPECIFICATION NamedSpec\nPROPERTIES Fair FairAlias\n",
            true,
        ),
        ("same-formula", "SPECIFICATION Spec\nPROPERTY Fair\n", true),
        (
            "disabled",
            "SPECIFICATION NamedSpec\nPROPERTY Fair\n",
            false,
        ),
    ] {
        let lowered = try_lower_front(name, config, enabled).expect("a lowered model");
        assert!(
            !lowered
                .startup_messages
                .expect("startup messages")
                .iter()
                .any(|message| message.code == 2258),
            "{name}"
        );
    }
}

#[test]
fn fairness_warning_names_the_configured_property_at_its_override_location() {
    let model = try_lower_front(
        "fairness-override",
        "SPECIFICATION NamedSpec\nPROPERTY Fair\nCONSTANT Fair <- OtherFair\n",
        true,
    )
    .expect("a lowered model");
    let warnings = model.startup_messages.expect("startup messages");
    let warning = warnings
        .iter()
        .find(|message| message.code == 2258)
        .expect("fairness warning");
    assert!(
        warning
            .text
            .contains("The temporal formula Fair at line 18, col 1")
    );
}

fn try_lower_spec(name: &str, spec: &str, config: &str) -> Result<LoweredModel, FrontError> {
    let directory =
        std::env::temp_dir().join(format!("tla-front-live-{name}-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    let path = directory.join(format!("{name}.tla"));
    std::fs::write(&path, spec).expect("the spec");
    let options = ModelOptions {
        libraries: &[],
        version: None,
        is_warning_enabled: true,
        is_spec_described: false,
        random_seed: 0,
        root_extendees: &[],
    };
    let lowered = lower_front(&path, config, &options);
    std::fs::remove_dir_all(&directory).expect("removed");
    lowered
}

// A property through a chain of `count` definitions, each conjoining one more.
fn lower_definition_chain(count: usize) -> Result<LoweredModel, FrontError> {
    let mut spec = String::from(
        "---- MODULE Chain ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x' = (x + 1) % 3\nSpec == Init /\\ [][Next]_x /\\ WF_x(Next)\n",
    );
    spec.push_str(&format!("D{count} == [](x # 5)\n"));
    for index in (1..count).rev() {
        spec.push_str(&format!("D{index} == [](x # 5) /\\ D{}\n", index + 1));
    }
    spec.push_str("Prop == D1\n====\n");
    try_lower_spec("Chain", &spec, "SPECIFICATION Spec\nPROPERTY Prop\n")
}

#[test]
fn follows_a_recursion_whose_argument_becomes_a_constant() {
    // The outer IF reads the state, but F(0)'s guard is constant and chooses the base case, so
    // TLC's translation ends there; TLC's output, with four branches and a time, is no fixture's.
    let lowered = try_lower_spec(
        "StateToConstant",
        "---- MODULE StateToConstant ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x' = x\nSpec == Init /\\ [][Next]_x\nRECURSIVE F(_)\nF(n) == IF n = 0 THEN <>(x = 0) ELSE F(0)\nProp == F(x)\n====\n",
        "SPECIFICATION Spec\nPROPERTY Prop\n",
    );
    assert!(lowered.is_ok(), "{:?}", lowered.err());
}

#[test]
fn overflows_on_a_recursion_whose_guard_reads_only_the_state() {
    let lowered = try_lower_spec(
        "Reach",
        "---- MODULE Reach ----\nEXTENDS Naturals\nVARIABLE x\nNext == x < 2 /\\ x' = x + 1\nSpec == x = 0 /\\ [][Next]_x /\\ WF_x(Next)\nRECURSIVE Reach(_)\nReach(n) == IF x = 0 THEN <>(x = 2) ELSE Reach(n + 1)\nProp == <>(x = 2) /\\ Reach(1)\n====\n",
        "SPECIFICATION Spec\nPROPERTY Prop\nCHECK_DEADLOCK FALSE\n",
    );
    let Err(error) = lowered else {
        panic!("TLC overflows its stack");
    };
    let error = match error {
        FrontError::Warned(_, error) => *error,
        error => error,
    };
    assert!(matches!(error, FrontError::StackOverflow), "{error:?}");
}

#[test]
fn declines_a_property_through_definitions_nested_past_tlc_stack() {
    // At the corpus's -Xss2m TLC's expansion of the property completes through 2,250 definitions
    // and overflows from 2,300 to 2,450 from run to run. The front end's analysis of such a chain
    // recurses deeper than a test thread's stack holds.
    let lowered = std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(|| {
            (
                lower_definition_chain(2250).map(|lowered| lowered.ir.len()),
                lower_definition_chain(2251).map(|lowered| lowered.ir.len()),
            )
        })
        .expect("a thread")
        .join()
        .expect("the lowering");
    assert!(lowered.0.is_ok(), "{:?}", lowered.0);
    assert!(
        matches!(&lowered.1, Err(FrontError::NotYet(reason)) if reason == "a temporal formula through definitions nested more deeply than TLC's stack may hold"),
        "{:?}",
        lowered.1
    );
}
