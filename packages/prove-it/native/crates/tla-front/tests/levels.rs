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

#[test]
fn words_level_errors_of_operator_arguments_and_bounds_as_sany_does() {
    // TLC's tla2sany error corpus, E4272_Test, E4313_ConjList_Test and E4315_Existential_Test.
    assert_eq!(
        get_level_errors(
            "---- MODULE E4272_Test ----\nVARIABLE v\nop(F(_)) == F(v')\nop2 == op(')\n====",
            &[]
        ),
        [(
            "line 4, col 8 to line 4, col 12 of module E4272_Test".to_owned(),
            "Level error in applying operator op:\nThe permitted level of argument 1 of the operator argument 1 \nmust be at least 2.".to_owned()
        )]
    );
    assert_eq!(
        get_level_errors(
            "---- MODULE E4313_ConjList_Test ----\nVARIABLE v\nop ==\n  /\\ v'\n  /\\ []v\n====",
            &[]
        ),
        [(
            "line 4, col 3 to line 5, col 8 of module E4313_ConjList_Test".to_owned(),
            "Conjunction list has both temporal formula and action as arguments.".to_owned()
        )]
    );
    assert_eq!(
        get_level_errors(
            "---- MODULE E4315_Existential_Test ----\nVARIABLE v\nop == \\E x \\in []v : TRUE\n====",
            &[]
        ),
        [(
            "line 3, col 7 to line 3, col 25 of module E4315_Existential_Test".to_owned(),
            "Level error in applying operator $BoundedExists:\nThe level of the range for the bounded variable line 3, col 10 to line 3, col 10 of module E4315_Existential_Test \nexceeds the maximum level allowed by the operator.".to_owned()
        )]
    );
}

#[test]
fn rejects_a_temporal_formula_a_new_symbol_ranges_over() {
    // TLC's tla2sany error corpus, E4356_Test.
    assert_eq!(
        get_level_errors(
            "---- MODULE E4356_Test ----\nVARIABLE v\nTHEOREM\n  ASSUME NEW x \\in []v\n  PROVE TRUE\n====",
            &[]
        ),
        [(
            "line 4, col 10 to line 4, col 22 of module E4356_Test".to_owned(),
            "Level error:\nTemporal formula used as set.".to_owned()
        )]
    );
}

fn is_not_yet(source: &str) -> bool {
    let config = parse_config("", TlcVersion::Master).expect("a configuration");
    matches!(
        create_environment(&EnvironmentOptions {
            source,
            load_module: &|_| None,
            config: &config,
            is_unconfigured: true,
            version: TlcVersion::Master,
            is_level_checked: true,
            load_class: None,
        }),
        Err(FrontError::NotYet(_))
    )
}

#[test]
fn rejects_what_sanys_selectors_reject_and_takes_a_theorem_named_as_an_expression() {
    // TLC's tla2sany error corpus: E4203_Test, E4355_Test and E4351_Test, and a DEF entry that
    // names nothing (E4200_Use_Test), which `tests/report.rs` words.
    for source in [
        "---- MODULE E4203_Test ----\nimport == INSTANCE Naturals\nop == import\n====",
        "---- MODULE E4355_Test ----\nTHEOREM thm == ASSUME TRUE PROVE TRUE\nop == thm\n====",
        "---- MODULE E4351_Test ----\nop(x) == x\nTHEOREM TRUE\nPROOF\n<1>a TRUE\n<1>b HAVE TRUE\n<1>c op(<1>a)\n<1>d op(<1>b)\n<1> QED\n====",
        "---- MODULE E4200_Use_Test ----\nUSE DEF DoesNotExist\n====",
    ] {
        assert!(!is_not_yet(source), "{source}");
        assert!(!get_level_errors(source, &[]).is_empty(), "{source}");
    }
    // SANY takes a theorem whose statement is an expression as one.
    let source = "---- MODULE Main ----\nTHEOREM thm == TRUE\nop == thm\n====";
    assert!(!is_not_yet(source));
    assert!(get_level_errors(source, &[]).is_empty());
}

#[test]
fn rejects_a_function_applied_to_another_number_of_arguments() {
    // TLC's tla2sany error corpus, E4260_1_Expected_2_Provided_Test, and as TLC reports a
    // function a LET defines; one argument may be a tuple of the parameters.
    let message = |count: usize| {
        format!("Function 'f' is defined with 1 parameters, but is applied to {count} arguments.")
    };
    assert_eq!(
        get_level_errors(
            "---- MODULE Main ----\nf[x \\in {}] == 0\nop == f[0, 0]\ntuple == f[<<0, 0>>]\n====",
            &[]
        ),
        [(
            "line 3, col 7 to line 3, col 13 of module Main".to_owned(),
            message(2)
        )]
    );
    assert_eq!(
        get_level_errors(
            "---- MODULE Fl ----\nop == LET f[x \\in {1}] == 0 IN f[1, 2]\n====",
            &[]
        ),
        [(
            "line 2, col 32 to line 2, col 38 of module Fl".to_owned(),
            message(2)
        )]
    );
}

#[test]
fn leaves_a_recursive_declaration_an_enclosing_let_leaves_undefined_not_native() {
    // SANY adds the inner declaration of F as a second one, which the front end doesn't follow.
    assert!(is_not_yet(
        "---- MODULE Main ----\nA == LET RECURSIVE F\n         G == LET RECURSIVE F\n                  F == 1\n              IN F\n     IN 0\n===="
    ));
}
