//! What SANY prints for a small spec. `scripts/front-differential.ts sany-text` holds the Rust text
//! to the TypeScript one on every corpus spec.

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
