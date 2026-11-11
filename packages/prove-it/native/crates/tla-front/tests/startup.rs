//! TLC's startup decision (`tla_front::startup`) on small specs: which 0-ary definitions TLC
//! computes as it starts (`processConstantDefns`), by which rule, and what `defns` then holds.
//! `front-dump startup` reports it against the front end's marks over a corpus.

use tla_front::TlcVersion;
use tla_front::config::parse_config;
use tla_front::environment::{Environment, EnvironmentOptions, create_environment};
use tla_front::startup::{Read, Rule, get_startup_model};

const MODULE_N: &str =
    "---- MODULE N ----\nEXTENDS Naturals\nOp(x) == {n \\in Nat : n > x}\n====\n";

fn create(definitions: &str, config: &str) -> Environment {
    create_extending("Naturals, TLC", definitions, config)
}

fn create_extending(extends: &str, definitions: &str, config: &str) -> Environment {
    let source = format!(
        "---- MODULE M ----\nEXTENDS {extends}\nCONSTANT C\nVARIABLE x\n{definitions}\nInit == x = 0\nNext == x' = x\n====\n"
    );
    let config = parse_config(
        &format!("CONSTANT C = 1\nINIT Init\nNEXT Next\n{config}"),
        TlcVersion::Master,
    )
    .expect("a configuration");
    create_environment(&EnvironmentOptions {
        source: &source,
        load_module: &|name| (name == "N").then(|| MODULE_N.to_owned()),
        config: &config,
        is_unconfigured: false,
        version: TlcVersion::Master,
        is_level_checked: false,
        load_class: None,
    })
    .expect("an environment")
}

// The read of the definition named `name`, with whether `defns` holds its value and the rule TLC
// attempts it by.
fn decide(definitions: &str, config: &str, name: &str) -> (Read, bool, Option<Rule>) {
    decide_in(&create(definitions, config), name)
}

fn decide_in(environment: &Environment, name: &str) -> (Read, bool, Option<Rule>) {
    let model = get_startup_model(environment);
    let definition = environment
        .definitions
        .get(name)
        .unwrap_or_else(|| panic!("a definition {name}"));
    let rule = model
        .attempted
        .iter()
        .find(|(attempted, _)| std::rc::Rc::ptr_eq(attempted, definition))
        .map(|(_, rule)| *rule);
    (
        model.read(definition),
        model.is_held_in_defns(definition),
        rule,
    )
}

#[test]
fn attempts_a_definition_of_constant_level() {
    assert_eq!(
        decide("D == {3, 1, 2}", "", "D"),
        (Read::Attempted, true, Some(Rule::Constant))
    );
}

#[test]
fn leaves_a_definition_reading_a_variable() {
    assert_eq!(decide("D == x + 1", "", "D"), (Read::Operator, false, None));
}

#[test]
fn counts_an_operator_argument_of_level_zero_whatever_it_reads() {
    let apply = "F(G(_)) == [i \\in Nat |-> G(i)]\n";
    assert_eq!(
        decide(&format!("{apply}D == F(LAMBDA i : i + x)"), "", "D"),
        (Read::Attempted, true, Some(Rule::Constant))
    );
    assert_eq!(
        decide(&format!("{apply}G(k) == k + x\nD == F(G)"), "", "D"),
        (Read::Attempted, true, Some(Rule::Constant))
    );
}

#[test]
fn counts_an_action_inside_an_operator_argument_of_level_zero() {
    assert_eq!(
        decide("A(F(_)) == F(1)\nD == A(LAMBDA i : x' = i)", "", "D"),
        (Read::Attempted, true, Some(Rule::Constant))
    );
}

#[test]
fn counts_a_name_spelled_as_a_variable_of_level_one() {
    assert_eq!(
        decide("I == INSTANCE N\nD == I!Op(1)", "", "D"),
        (Read::Operator, false, None)
    );
}

#[test]
fn counts_the_java_methods_of_a_level_above_constant() {
    assert_eq!(
        decide("D == TLCGet(\"level\")", "", "D"),
        (Read::Operator, false, None)
    );
    // TLCGet passed as an operator is an argument, of level 0.
    assert_eq!(
        decide("A(F(_)) == F(\"level\")\nD == A(TLCGet)", "", "D"),
        (Read::Attempted, true, Some(Rule::Constant))
    );
}

#[test]
fn holds_a_literal_without_computing_it() {
    assert_eq!(decide("D == 3", "", "D"), (Read::Literal, false, None));
    assert_eq!(decide("D == \"a\"", "", "D"), (Read::Literal, false, None));
}

#[test]
fn attempts_a_substitute_for_a_constant_at_any_level_without_its_defns_entry() {
    let source = "CONSTANT K\nD == IF FALSE THEN x ELSE {3, 1, 2}";
    let environment = {
        let source = format!(
            "---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\n{source}\nInit == x = 0\nNext == x' = x\n====\n"
        );
        let config = parse_config(
            "CONSTANT K <- D\nINIT Init\nNEXT Next\n",
            TlcVersion::Master,
        )
        .expect("a configuration");
        create_environment(&EnvironmentOptions {
            source: &source,
            load_module: &|_| None,
            config: &config,
            is_unconfigured: false,
            version: TlcVersion::Master,
            is_level_checked: false,
            load_class: None,
        })
        .expect("an environment")
    };
    let model = get_startup_model(&environment);
    let definition = environment.definitions.get("D").expect("D");
    assert_eq!(model.read(definition), Read::Attempted);
    assert!(!model.is_held_in_defns(definition));
    assert_eq!(
        model
            .attempted
            .iter()
            .filter(|(attempted, _)| std::rc::Rc::ptr_eq(attempted, definition))
            .map(|(_, rule)| *rule)
            .collect::<Vec<_>>(),
        [Rule::Substitute]
    );
}

#[test]
fn attempts_the_definition_another_definition_is_substituted_by() {
    let (read, is_held, rule) = decide(
        "Ballot == Nat\nMCBallot == 0..1\nB == Ballot",
        "CONSTANT Ballot <- MCBallot\n",
        "MCBallot",
    );
    assert_eq!(
        (read, is_held, rule),
        (Read::Attempted, true, Some(Rule::Constant))
    );
}

#[test]
fn leaves_a_definition_the_configuration_gives_a_value() {
    assert_eq!(
        decide("D == {3, 1, 2}", "CONSTANT D = 4\n", "D"),
        (Read::Operator, false, None)
    );
}

// TLC sets a Java method on the body of the operator the module of its class defines, which no
// operator of another module spelled the same reads (`processModuleOverrides`, `lookup`).
#[test]
fn reads_an_override_only_through_the_operator_its_module_defines() {
    let print = "Print(a, b) == x\nD == <<{3, 1, 2}, Print(1, 2)>>";
    assert_eq!(
        decide_in(
            &create_extending("Naturals", &format!("J == INSTANCE TLC\n{print}"), ""),
            "D"
        ),
        (Read::Operator, false, None)
    );
    assert_eq!(
        decide_in(&create_extending("Naturals", print, ""), "D"),
        (Read::Operator, false, None)
    );
    // TLC's own Print, extended, is a method of level 0.
    assert_eq!(
        decide("D == <<{3, 1, 2}, Print(1, 2)>>", "", "D"),
        (Read::Attempted, true, Some(Rule::Constant))
    );
    // TLC's TLCGet through a named instance of its module is the method, of level 1.
    assert_eq!(
        decide_in(
            &create_extending(
                "Naturals",
                "J == INSTANCE TLC\nD == J!TLCGet(\"level\")",
                ""
            ),
            "D"
        ),
        (Read::Operator, false, None)
    );
}
