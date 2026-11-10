//! What SANY prints for a small spec. `scripts/front-differential.ts sany-text` holds the Rust text
//! to the TypeScript one on every corpus spec.

use std::path::Path;

use tla_front::TlcVersion;
use tla_front::errors::FrontError;
use tla_front::report::{ReportOptions, SanyText, get_sany_text};

/// What SANY prints for the root module `source`, named Main, with no other files.
fn get_text(name: &str, source: &str) -> String {
    get_report(name, source).expect("a text").text
}

fn get_report(name: &str, source: &str) -> Result<SanyText, FrontError> {
    let directory =
        std::env::temp_dir().join(format!("tla-front-report-{name}-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    let spec_path = directory.join("Main.tla");
    std::fs::write(&spec_path, source).expect("a spec");
    let text = get_sany_text(
        &spec_path,
        &ReportOptions {
            version: TlcVersion::Master,
            file_name: None,
            load_module: &|_| None,
            describe_file: &|name, origin| format!("{name} {origin:?}"),
        },
    );
    std::fs::remove_dir_all(&directory).expect("a removed directory");
    text
}

// tests/fixtures/recursive-shapes: RECURSIVE declarations at module level, in a LET and in a LET
// within a definition of another, against everything else that can bind or name what they declare
// (src/recursive.rs). The front end writes SANY's report of these, and declines the rest.
#[test]
fn reports_only_the_recursive_shapes_it_follows() {
    let reported = [
        "RLetDefined",
        "RLetDefinedZero",
        "RLetExtendsOther",
        "RLetExtendsUndefined",
        "RLetFunction",
        "RLetInfix",
        "RLetMutual",
        "RLetPrimed",
        "RLetUndefined",
        "RLetUndefinedTwo",
        "RLetWrongLevel",
        "RLetWrongLevelDeeper",
        "RLetWrongLevelFunction",
        "RModuleArityLess",
        "RModuleArityMore",
        "RModuleArityZero",
        "RModuleAssumeInSection",
        "RModuleBodyLevelRecursive",
        "RModuleDefined",
        "RModuleDefinedZero",
        "RModuleExtendsOther",
        "RModuleExtendsUndefined",
        "RModuleFunction",
        "RModuleFunctionArity",
        "RModuleFunctionArityUndefined",
        "RModuleInfix",
        "RModuleInnerRecursive",
        "RModuleInnerRecursiveUndefined",
        "RModuleInnerUndefinedOuterUndefined",
        "RModuleInstanceAfter",
        "RModuleLocalDefinition",
        "RModuleModuleAfter",
        "RModuleModuleInSection",
        "RModuleModuleInSectionUsed",
        "RModuleMutual",
        "RModuleOtherConstantInSection",
        "RModulePrimed",
        "RModuleSiblingLets",
        "RModuleSiblingLetsSameName",
        "RModuleTheoremInSection",
        "RModuleTheoremUses",
        "RModuleUndefined",
        "RModuleUndefinedTwo",
        "RModuleUseInSection",
        "RModuleVariableInSection",
        "RNestedDefined",
        "RNestedDefinedZero",
        "RNestedFunction",
        "RNestedInfix",
        "RNestedMutual",
        "RNestedPrimed",
        "RNestedUndefined",
        "RNestedUndefinedTwo",
        "RNestedWrongLevel",
        "RNestedWrongLevelDeeper",
        "RNestedWrongLevelFunction",
        "RecursiveHelper",
    ];
    let directory =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../tests/fixtures/recursive-shapes");
    let mut paths: Vec<_> = std::fs::read_dir(&directory)
        .expect("the grid")
        .map(|entry| entry.expect("an entry").path())
        .collect();
    paths.sort();
    for path in paths {
        let name = path.file_stem().and_then(|stem| stem.to_str()).expect("a name");
        let report = get_sany_text(
            &path,
            &ReportOptions {
                version: TlcVersion::Master,
                file_name: None,
                load_module: &|module| {
                    std::fs::read_to_string(directory.join(format!("{module}.tla"))).ok()
                },
                describe_file: &|name, origin| format!("{name} {origin:?}"),
            },
        );
        match report {
            Ok(_) => assert!(reported.contains(&name), "{name} is reported"),
            Err(FrontError::NotYet(_)) => assert!(!reported.contains(&name), "{name} declines"),
            Err(error) => panic!("{name}: {error:?}"),
        }
    }
}

#[test]
fn reports_a_missing_module_in_the_module_that_names_it() {
    assert_eq!(
        get_text("missing", "---- MODULE Main ----\nEXTENDS Gone\n====\n"),
        "Parsing file Main File\n\nFatal errors while parsing TLA+ spec in file Main\n\nIn module Main\n\nCannot find source file for module Gone imported in module Main.\n*** Errors: 1\n\nIn module Main\n\nCannot find source file for module Gone imported in module Main.\n\n\n\n"
    );
}

#[test]
fn reprints_every_error_so_far_after_each_module() {
    assert_eq!(
        get_text(
            "errors",
            "---- MODULE Main ----\nEXTENDS Lib\nAlso == Missing\n====\n---- MODULE Lib ----\nFoo == Undefined\n====\n"
        ),
        "Parsing file Main File\nParsing file Lib RootFile\nSemantic processing of module Lib\nSemantic errors:\n\n*** Errors: 1\n\nline 2, col 8 to line 2, col 16 of module Lib\n\nUnknown operator: `Undefined'.\n\n\nSemantic processing of module Main\nSemantic errors:\n\n*** Errors: 2\n\nline 2, col 8 to line 2, col 16 of module Lib\n\nUnknown operator: `Undefined'.\n\n\nline 3, col 9 to line 3, col 15 of module Main\n\nUnknown operator: `Missing'.\n\n\n"
    );
}

#[test]
fn warns_of_a_field_named_like_a_declaration_unless_a_field_is_built_from_one() {
    assert_eq!(
        get_text(
            "lint",
            "---- MODULE Main ----\nVARIABLE x, y\nA == [x |-> 1]\nB == [y |-> y, z |-> 2]\n====\n"
        ),
        "Parsing file Main File\nSemantic processing of module Main\nLinting of module Main\nline 3, col 7 to line 3, col 7 of module Main\n\nThe field name \"x\" in the record constructor is identical to the existing definition or declaration\nnamed x, located at line 2, col 10 to line 2, col 10 of module Main.\nThe field in the record will not take the value of the x definition or declaration.\nIn TLA+, field names in records are strings, regardless of any similarly named declarations or definitions.\nTherefore, DOMAIN [x |-> ...] = {\"x\"} holds true.\n\n\n\n"
    );
}

#[test]
fn names_each_module_sany_parses_analyzes_and_lints() {
    assert_eq!(
        get_text(
            "accepted",
            "---- MODULE Main ----\nEXTENDS Naturals\nC == INSTANCE Counter\nx == C!y + 1\n====\n---- MODULE Counter ----\ny == 2\n====\n"
        ),
        "Parsing file Main File\nParsing file Naturals Standard\nParsing file Counter RootFile\nSemantic processing of module Naturals\nSemantic processing of module Counter\nSemantic processing of module Main\nLinting of module Counter\nLinting of module Main\n"
    );
}

#[test]
fn reports_the_arity_of_an_operator_substituted_explicitly_and_implicitly() {
    // TLC's tla2sany error corpus, E4243_1_Required_0_Provided_Test: SANY's selector rejects an
    // explicit substitute, so it reports the substitution in the builtins' module; an implicit
    // one it reports at the INSTANCE, as TLC at d8fb231 does.
    let inner = "---- MODULE Inner ----\nCONSTANT F(_)\n====\n";
    let explicit = get_text(
        "explicit",
        &format!("---- MODULE Main ----\n{inner}op == 0\nINSTANCE Inner WITH F <- op\n====\n"),
    );
    assert!(
        explicit.ends_with("*** Errors: 2\n\nline 6, col 26 to line 6, col 27 of module Main\n\nExpected arity 1 but found operator of arity 0.\n\n\nIn module --TLA+ BUILTINS--\n\nAn operator must be substituted for symbol 'F', and it must have arity 1.\n\n\n"),
        "{explicit}"
    );
    let implicit = get_text(
        "implicit",
        &format!("---- MODULE Main ----\n{inner}F == 0\nINSTANCE Inner\n====\n"),
    );
    assert!(
        implicit.ends_with("*** Errors: 1\n\nline 6, col 1 to line 6, col 14 of module Main\n\nAn operator must be substituted for symbol 'F', and it must have arity 1.\n\n\n"),
        "{implicit}"
    );
}

#[test]
fn reports_a_named_step_of_an_implicit_level_as_a_semantic_error() {
    // TLC's tla2sany error corpus, E4350_Plus_Test.
    let text = get_text(
        "named",
        "---- MODULE Main ----\nTHEOREM TRUE\nPROOF\n<+>a. QED\n====\n",
    );
    assert!(
        text.ends_with("Semantic errors:\n\n*** Errors: 1\n\nline 4, col 1 to line 4, col 5 of module Main\n\n<*> and <+> cannot be used for a named step.\n\n\n"),
        "{text}"
    );
}

#[test]
fn declines_a_module_that_sany_parses_and_the_front_end_does_not() {
    // TLC's tla2sany corpus, AssumeProveTest: a labeled ASSUME/PROVE among the assumptions.
    let report = get_report(
        "unparsed",
        "---- MODULE Main ----\nTHEOREM ASSUME inner :: ASSUME TRUE PROVE TRUE PROVE TRUE\n====\n",
    );
    assert!(matches!(report, Err(FrontError::NotYet(_))));
}

#[test]
fn declines_a_module_of_the_community_modules_tlc_bundles() {
    // TLC's jar finds IOUtils in its CommunityModules, which the front end doesn't have; another
    // module it can't find is SANY's error.
    let bundled = get_report("bundled", "---- MODULE Main ----\nEXTENDS IOUtils\n====\n");
    assert!(matches!(bundled, Err(FrontError::NotYet(_))));
    let missing = get_text(
        "unbundled",
        "---- MODULE Main ----\nEXTENDS NoSuchModule\n====\n",
    );
    assert!(
        missing
            .contains("Cannot find source file for module NoSuchModule imported in module Main."),
        "{missing}"
    );
}

// SANY's error corpus E4203 and E4204: `selectorToNode` checks an INSTANCE's arguments, then that
// the name selects an operator of it.
#[test]
fn reports_an_instance_named_as_an_expression() {
    assert_eq!(
        get_text(
            "instance",
            "---- MODULE Main ----\nI == INSTANCE Naturals\nJ(x) == INSTANCE Naturals\nA == I\nB == J(1, 2)\nC == J\n====\n"
        ),
        "Parsing file Main File\nParsing file Naturals Standard\nSemantic processing of module Naturals\nSemantic processing of module Main\nSemantic errors:\n\n*** Errors: 3\n\nline 4, col 6 to line 4, col 6 of module Main\n\nOperator name I is incomplete.\n\n\nline 5, col 7 to line 5, col 12 of module Main\n\nThe operator J requires 1 arguments.\n\n\nline 6, col 6 to line 6, col 6 of module Main\n\nThe operator J requires 1 arguments.\n\n\n"
    );
}

// E4351 and E4355: an ASSUME/PROVE, or a step that asserts no expression, used as an expression.
#[test]
fn reports_a_theorem_or_step_that_asserts_no_expression_named_as_one() {
    assert_eq!(
        get_text(
            "selected",
            "---- MODULE Main ----\nop(x) == x\nTHEOREM T == ASSUME TRUE PROVE TRUE\nA == T\nTHEOREM TRUE\n<1>a HAVE TRUE\n<1>b SUFFICES TRUE\n<1>c ASSUME TRUE PROVE TRUE\n<1>d CASE TRUE\n<1>e op(<1>a) /\\ op(<1>b) /\\ op(<1>c) /\\ op(<1>d)\n<1> QED\n====\n"
        ),
        "Parsing file Main File\nSemantic processing of module Main\nSemantic errors:\n\n*** Errors: 5\n\nline 4, col 6 to line 4, col 6 of module Main\n\nASSUME/PROVE used where an expression is required.\n\n\nline 10, col 9 to line 10, col 12 of module Main\n\nHAVE proof step selected instead of expression.\n\n\nline 10, col 21 to line 10, col 24 of module Main\n\nSUFFICES proof step selected instead of expression.\n\n\nline 10, col 33 to line 10, col 36 of module Main\n\nASSUME/PROVE used where an expression is required.\n\n\nline 10, col 45 to line 10, col 48 of module Main\n\nCASE proof step selected instead of expression.\n\n\n"
    );
}

// E4293: a definition at a deeper LET of an operator or function a LET declares RECURSIVE, and at
// the end of each LET that leaves one undefined, every one of its level so far, each once.
#[test]
fn reports_operators_a_let_declares_recursive_and_leaves_undefined() {
    assert_eq!(
        get_text(
            "recursive",
            "---- MODULE Main ----\nA == LET RECURSIVE F(_)\n     IN 1\nB == LET RECURSIVE G\n         H == LET G == 2 IN 0\n     IN 0\nE == LET RECURSIVE K IN 3\nC == LET RECURSIVE R\n         D == LET R[x \\in {}] == 0 IN 0\n     IN 0\n====\n"
        ),
        "Parsing file Main File\nSemantic processing of module Main\n*** Warnings: 1\n\nline 5, col 19 to line 5, col 24 of module Main\n\nMultiple declarations or definitions for symbol G.  \nThis duplicates the one at line 4, col 20 to line 4, col 20 of module Main.\n\n\n\nSemantic errors:\n\n*** Errors: 6\n\nline 2, col 20 to line 2, col 23 of module Main\n\nSymbol F declared in RECURSIVE statement but not defined.\n\n\nline 5, col 19 to line 5, col 24 of module Main\n\nRecursive operator G defined at wrong LET/IN level.\n\n\nline 4, col 20 to line 4, col 20 of module Main\n\nSymbol G declared in RECURSIVE statement but not defined.\n\n\nline 7, col 20 to line 7, col 20 of module Main\n\nSymbol K declared in RECURSIVE statement but not defined.\n\n\nline 9, col 19 to line 9, col 34 of module Main\n\nRecursive function R defined at wrong LET/IN level.\n\n\nline 8, col 20 to line 8, col 20 of module Main\n\nSymbol R declared in RECURSIVE statement but not defined.\n\n\n"
    );
}

// E4200: an unknown name, a constant, a variable or a parameter as a DEF entry, and a USE, HIDE or
// BY that keeps nothing.
#[test]
fn reports_def_entries_that_name_no_defined_operator() {
    assert_eq!(
        get_text(
            "defs",
            "---- MODULE Main ----\nCONSTANT C\nVARIABLE v\nop == 1\nUSE DEF Missing\nUSE DEF C, v\nUSE DEF op, Nope\nTHEOREM TRUE\n<1>1 HIDE DEF C\n<1> QED BY DEF Gone\n====\n"
        ),
        "Parsing file Main File\nSemantic processing of module Main\nSemantic errors:\n\n*** Errors: 13\n\nline 5, col 9 to line 5, col 15 of module Main\n\nUnknown operator: `Missing'.\n\n\nline 5, col 9 to line 5, col 15 of module Main\n\nDEF clause entry should describe a defined operator.\n\n\nline 5, col 1 to line 5, col 15 of module Main\n\nEmpty USE or HIDE statement.\n\n\nline 6, col 9 to line 6, col 9 of module Main\n\nDEF clause entry should describe a defined operator.\n\n\nline 6, col 12 to line 6, col 12 of module Main\n\nDEF clause entry should describe a defined operator.\n\n\nline 6, col 1 to line 6, col 12 of module Main\n\nEmpty USE or HIDE statement.\n\n\nline 7, col 13 to line 7, col 16 of module Main\n\nUnknown operator: `Nope'.\n\n\nline 7, col 13 to line 7, col 16 of module Main\n\nDEF clause entry should describe a defined operator.\n\n\nline 9, col 15 to line 9, col 15 of module Main\n\nDEF clause entry should describe a defined operator.\n\n\nline 9, col 6 to line 9, col 15 of module Main\n\nEmpty USE or HIDE statement.\n\n\nline 10, col 16 to line 10, col 19 of module Main\n\nUnknown operator: `Gone'.\n\n\nline 10, col 16 to line 10, col 19 of module Main\n\nDEF clause entry should describe a defined operator.\n\n\nline 10, col 9 to line 10, col 19 of module Main\n\nEmpty BY\n\n\n"
    );
}

// E4223: a nested module named like a module SANY has already read.
#[test]
fn reports_a_nested_module_named_like_a_standard_module_it_extends() {
    assert_eq!(
        get_text(
            "module",
            "---- MODULE Main ----\nEXTENDS Naturals\n---- MODULE Naturals ----\n====\nINSTANCE Naturals\n====\n"
        ),
        "Parsing file Main File\nParsing file Naturals Standard\nSemantic processing of module Naturals\nSemantic processing of module Main\nSemantic errors:\n\n*** Errors: 1\n\nline 3, col 1 to line 4, col 4 of module Main\n\nMultiply-defined module 'Naturals': this definition or declaration conflicts \nwith the one at line 1, col 1 to line 36, col 77 of module Naturals.\n\n\n"
    );
}

// E4294_Module: a nested module ends the recursive section's count, so the definition after it
// makes SANY's generator throw (`endOpDefNode`), which `SANY.parse` prints after the module's
// "Semantic processing" line, with no messages.
#[test]
fn ends_with_the_exception_sanys_generator_throws_for_a_module_in_a_recursive_section() {
    let report = get_report(
        "exception",
        "---- MODULE Main ----\nRECURSIVE op\n---- MODULE Inner ----\n====\nop == 0\n====\n",
    )
    .expect("a text");
    let exception = "util.WrongInvocationException: Defined more recursive operators than were declared in RECURSIVE statements.";
    assert!(report.is_failed);
    assert_eq!(report.exception.as_deref(), Some(exception));
    assert_eq!(
        report.text,
        format!("Parsing file Main File\nSemantic processing of module Main\n{exception}\n")
    );
    // Without a definition after the module nothing throws, and the count SANY is left with
    // isn't followed.
    assert!(matches!(
        get_report(
            "exception-undefined",
            "---- MODULE Main ----\nRECURSIVE op\n---- MODULE Inner ----\n====\n====\n",
        ),
        Err(FrontError::NotYet(_))
    ));
}

#[test]
fn leaves_a_recursive_function_with_operator_arguments_after_a_module_not_native() {
    // `processFunction` leaves F undefined, so its definition doesn't make the generator throw.
    assert!(matches!(
        get_report(
            "exception-function",
            "---- MODULE Main ----\nRECURSIVE F(_)\n---- MODULE Inner ----\n====\nF[x \\in {}] == 0\n====\n",
        ),
        Err(FrontError::NotYet(_))
    ));
}

#[test]
fn leaves_a_recursive_section_after_a_module_whose_declaration_sany_rejects_not_native() {
    // SANY rejects the declaration of the constant's name, so F == 0 doesn't count down.
    assert!(matches!(
        get_report(
            "exception-constant",
            "---- MODULE Main ----\nCONSTANT F\nRECURSIVE F\n---- MODULE Inner ----\n====\nF == 0\n====\n",
        ),
        Err(FrontError::NotYet(_))
    ));
}

#[test]
fn leaves_a_let_whose_recursive_definitions_are_shaped_otherwise_not_native() {
    // SANY gives a declared operator parameters of arity zero until its definition sets them, and
    // an INSTANCE binds where it appears.
    for source in [
        "---- MODULE Main ----\nA == LET RECURSIVE F(_)\n         F[x \\in {}] == 0\n     IN 0\n====\n",
        "---- MODULE Main ----\nA == LET RECURSIVE G(_)\n         G == 1\n     IN 0\n====\n",
        "---- MODULE Main ----\nA == LET RECURSIVE F(_), K\n         G == F(0)\n         F(H(_)) == 0\n     IN 0\n====\n",
        "---- MODULE Main ----\nA == LET I == INSTANCE Naturals\n         RECURSIVE I, K\n     IN I\n====\n",
    ] {
        assert!(
            matches!(get_report("reshaped", source), Err(FrontError::NotYet(_))),
            "{source}"
        );
    }
}
