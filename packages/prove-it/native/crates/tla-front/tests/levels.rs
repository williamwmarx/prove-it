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

#[test]
fn rejects_a_primed_argument_of_a_recursive_operator() {
    // As TLC reports it, in a module and in a LET.
    let module = "---- MODULE Rec ----\nEXTENDS Naturals\nVARIABLE x\nRECURSIVE Up(_, _)\nUp(v, n) == IF n = 0 THEN v' = v ELSE Up(v, n - 1)\n====";
    assert_eq!(
        get_level_errors(module, &[]),
        [(
            "line 5, col 1 to line 5, col 50 of module Rec".to_owned(),
            "Argument 1 of recursive operator Up is primed".to_owned()
        )]
    );
    let in_let = "---- MODULE InLet ----\nEXTENDS Naturals\nVARIABLE x\nOp == LET RECURSIVE Up(_, _)\n          Up(v, n) == IF n = 0 THEN v' = v ELSE Up(v, n - 1)\n      IN Up(x, 2)\n====";
    assert_eq!(
        get_level_errors(in_let, &[]),
        [(
            "line 5, col 11 to line 5, col 60 of module InLet".to_owned(),
            "Argument 1 of recursive operator Up is primed".to_owned()
        )]
    );
    // A recursion over a number takes its argument at any level.
    let plain = "---- MODULE Plain ----\nEXTENDS Naturals\nRECURSIVE Sum(_)\nSum(n) == IF n = 0 THEN 0 ELSE n + Sum(n - 1)\n====";
    assert!(get_level_errors(plain, &[]).is_empty());
}

#[test]
fn rejects_an_assumption_above_constant_level() {
    // TLC's tla2sany error corpus, E4206_Test.
    assert_eq!(
        get_level_errors(
            "---- MODULE E4206_Test ----\nVARIABLE v\nASSUME v\n====",
            &[]
        ),
        [(
            "line 3, col 1 to line 3, col 8 of module E4206_Test".to_owned(),
            "Level error: assumptions must be level 0 (Constant), \nbut this one has level 1."
                .to_owned()
        )]
    );
}

#[test]
fn rejects_an_at_outside_an_except_value() {
    // TLC's tla2sany error corpus, E4261_Test.
    assert_eq!(
        get_level_errors("---- MODULE E4261_Test ----\nop == @\n====", &[]),
        [(
            "line 2, col 7 to line 2, col 7 of module E4261_Test".to_owned(),
            "@ used where its meaning is not defined.".to_owned()
        )]
    );
    assert!(
        get_level_errors(
            "---- MODULE At ----\nf == [i \\in {1} |-> i]\nop == [f EXCEPT ![1] = LET g == @ IN g]\n====",
            &[]
        )
        .is_empty()
    );
}

#[test]
fn rejects_what_comes_between_a_recursive_declaration_and_its_definition() {
    // TLC's tla2sany error corpus, E4294_Constant_Test and E4294_Use_or_Hide_Test.
    assert_eq!(
        get_level_errors(
            "---- MODULE E4294_Constant_Test ----\nRECURSIVE op\nCONSTANT c\nop == 0\n====",
            &[]
        ),
        [(
            "line 3, col 1 to line 3, col 10 of module E4294_Constant_Test".to_owned(),
            "A declaration may not appear within a recursive definition section.".to_owned()
        )]
    );
    assert_eq!(
        get_level_errors(
            "---- MODULE E4294_Use_or_Hide_Test ----\nRECURSIVE op\nUSE op\nop == 0\n====",
            &[]
        ),
        [(
            "line 3, col 1 to line 3, col 6 of module E4294_Use_or_Hide_Test".to_owned(),
            "A USE or HIDE may not appear within a recursive definition section.".to_owned()
        )]
    );
}

#[test]
fn rejects_a_function_declared_recursive_with_operator_arguments() {
    // TLC's tla2sany error corpus, E4292_Function_Test: the declaration stays undefined.
    assert_eq!(
        get_level_errors(
            "---- MODULE E4292_Function_Test ----\nRECURSIVE F(_)\nF[x \\in {}] == 0\n====",
            &[]
        ),
        [
            (
                "line 3, col 1 to line 3, col 16 of module E4292_Function_Test".to_owned(),
                "Function F has operator arguments in its RECURSIVE declaration.".to_owned()
            ),
            (
                "line 2, col 11 to line 2, col 14 of module E4292_Function_Test".to_owned(),
                "Symbol F declared in RECURSIVE statement but not defined.".to_owned()
            ),
        ]
    );
}

#[test]
fn takes_the_at_of_a_step_that_continues_an_infix_step() {
    let steps = "---- MODULE Steps ----\nEXTENDS Naturals\nTHEOREM 1 + 1 = 2\n<1>1. 1 + 1 = 1 + 1 OBVIOUS\n<1>2. @ = 2 OBVIOUS\n<1>3. QED BY <1>1, <1>2\n====";
    assert!(get_level_errors(steps, &[]).is_empty());
    let first =
        "---- MODULE First ----\nTHEOREM 2 = 2\n<1>1. @ = 2 OBVIOUS\n<1>2. QED BY <1>1\n====";
    assert_eq!(
        get_level_errors(first, &[]),
        [(
            "line 3, col 7 to line 3, col 7 of module First".to_owned(),
            "@ used where its meaning is not defined.".to_owned()
        )]
    );
}
