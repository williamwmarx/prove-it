//! What SANY prints for a small spec. `scripts/front-differential.ts sany-text` holds the Rust text
//! to the TypeScript one on every corpus spec.

use std::collections::BTreeMap;
use std::path::Path;

use tla_front::TlcVersion;
use tla_front::errors::FrontError;
use tla_front::report::{ModuleOrigin, ReportOptions, SanyText, get_sany_text};

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
            is_xml_export: false,
        },
    );
    std::fs::remove_dir_all(&directory).expect("a removed directory");
    text
}

// tests/recursive-shapes: RECURSIVE declarations at module level, in a LET and in a LET
// within a definition of another, against everything else that can bind or name what they declare.
// The front end writes SANY's report of each: linking derives the messages of the shapes
// src/recursive.rs follows, and SANY's generator those of the others. `grid.json` records what
// TLC at d8fb231 prints for each.
#[test]
fn reports_every_recursive_shape_as_sany_does() {
    let directory = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/recursive-shapes");
    let recordings = get_recordings(include_str!(
        "../../../../tests/conformance/sany-stdout/grid.json"
    ));
    let mut paths: Vec<_> = std::fs::read_dir(&directory)
        .expect("the grid")
        .map(|entry| entry.expect("an entry").path())
        .collect();
    paths.sort();
    assert_eq!(paths.len(), recordings.len());
    for path in paths {
        let name = path
            .file_stem()
            .and_then(|stem| stem.to_str())
            .expect("a name");
        let report = get_sany_text(
            &path,
            &ReportOptions {
                version: TlcVersion::Master,
                file_name: None,
                load_module: &|module| {
                    std::fs::read_to_string(directory.join(format!("{module}.tla"))).ok()
                },
                describe_file: &|module, origin| match origin {
                    ModuleOrigin::Standard => format!("/tmp/tlc-_/{module}.tla"),
                    ModuleOrigin::File | ModuleOrigin::RootFile => format!("{module}.tla"),
                },
                is_xml_export: false,
            },
        )
        .unwrap_or_else(|error| panic!("{name}: {error:?}"));
        let recording = &recordings[&format!("recursive-shapes/{name}")];
        let sany_lines: Vec<&str> = recording
            .lines()
            .skip_while(|line| !line.starts_with("Running "))
            .skip(1)
            .take_while(|line| !line.starts_with("Starting... ") && !line.starts_with("Error: "))
            .collect();
        assert_eq!(
            report.text,
            format!("{}\n", sany_lines.join("\n")),
            "{name}"
        );
        assert_eq!(
            report.is_failed,
            recording.starts_with("exit 150\n"),
            "{name}"
        );
    }
}

/// The recorded output of each spec in a JSON object of strings, as `sany-corpus.ts` writes it.
fn get_recordings(json: &str) -> BTreeMap<String, String> {
    let mut strings = Vec::new();
    let mut characters = json.chars();
    while let Some(character) = characters.next() {
        if character != '"' {
            continue;
        }
        let mut string = String::new();
        while let Some(character) = characters.next() {
            match character {
                '"' => break,
                '\\' => match characters.next().expect("an escape") {
                    'n' => string.push('\n'),
                    't' => string.push('\t'),
                    'u' => {
                        let code: String = characters.by_ref().take(4).collect();
                        let unit = u32::from_str_radix(&code, 16).expect("a code unit");
                        string.push(char::from_u32(unit).expect("a character"));
                    }
                    other => string.push(other),
                },
                other => string.push(other),
            }
        }
        strings.push(string);
    }
    strings
        .chunks(2)
        .map(|pair| (pair[0].clone(), pair[1].clone()))
        .collect()
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
    // With as many arguments as it takes, SANY generates them before it finds the name incomplete.
    assert_eq!(
        get_text(
            "instance-arguments",
            "---- MODULE Main ----\nJ(x) == INSTANCE Naturals\nA == J(Missing)\n====\n",
        ),
        "Parsing file Main File\nParsing file Naturals Standard\nSemantic processing of module Naturals\nSemantic processing of module Main\nSemantic errors:\n\n*** Errors: 2\n\nline 3, col 8 to line 3, col 14 of module Main\n\nUnknown operator: `Missing'.\n\n\nline 3, col 6 to line 3, col 6 of module Main\n\nOperator name J is incomplete.\n\n\n"
    );
}

// SANY's corpus ProofsTest: `processTheorem` adds a theorem whose statement is an expression to the
// symbol table before its proof, which may name it as one.
#[test]
fn reads_a_theorem_named_as_an_expression_in_its_own_proof() {
    assert_eq!(
        get_text(
            "own-proof",
            "---- MODULE Main ----\nOp(x) == x\nTHEOREM T == TRUE\n<1> QED BY Op(T)\n====\n"
        ),
        "Parsing file Main File\nSemantic processing of module Main\nLinting of module Main\n"
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
    // Where an operator is required, SANY checks the expected arity first.
    assert!(matches!(
        get_report(
            "selected-argument",
            "---- MODULE Main ----\nTHEOREM T == ASSUME TRUE PROVE TRUE\nOp(F(_)) == 0\nA == Op(T)\n====\n",
        ),
        Err(FrontError::NotYet(_))
    ));
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
    // An operator symbol is kept where a module defines it, and otherwise not followed.
    assert_eq!(
        get_text(
            "defs-symbol",
            "---- MODULE Main ----\nEXTENDS Naturals\nUSE DEF +\n====\n"
        ),
        "Parsing file Main File\nParsing file Naturals Standard\nSemantic processing of module Naturals\nSemantic processing of module Main\nLinting of module Main\n"
    );
    // A DEFINE step and a selection of a definition are kept; another step, a selection of
    // nothing, and a module named in a fact or DEF clause are not followed.
    assert_eq!(
        get_text(
            "defs-kept",
            "---- MODULE Main ----\n---- MODULE Inner ----\nH == 0\n====\nV == INSTANCE Inner\nTHEOREM TRUE\n<1>1 DEFINE G == 2\n<1> QED BY DEF <1>1, V!H\n====\n"
        ),
        "Parsing file Main File\nSemantic processing of module Main\nLinting of module Main\n"
    );
    for (name, source) in [
        (
            "defs-step",
            "---- MODULE Main ----\nTHEOREM TRUE\n<1>1 TRUE\n<1> QED BY DEF <1>1\n====\n",
        ),
        (
            "defs-selection",
            "---- MODULE Main ----\n---- MODULE Inner ----\nH == 0\n====\nV == INSTANCE Inner\nUSE DEF V!Missing\n====\n",
        ),
        (
            "defs-module",
            "---- MODULE Main ----\nUSE DEF Nope, MODULE Gone\n====\n",
        ),
        (
            "defs-parenthesized",
            "---- MODULE Main ----\nUSE DEF (Missing)\n====\n",
        ),
        (
            "facts-module",
            "---- MODULE Main ----\nUSE MODULE Gone\n====\n",
        ),
    ] {
        assert!(
            matches!(get_report(name, source), Err(FrontError::NotYet(_))),
            "{name}"
        );
    }
    assert!(matches!(
        get_report(
            "defs-unknown-symbol",
            "---- MODULE Main ----\nUSE DEF Missing, +\n====\n",
        ),
        Err(FrontError::NotYet(_))
    ));
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
