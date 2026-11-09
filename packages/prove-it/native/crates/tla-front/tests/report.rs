//! What SANY prints for a small spec. `scripts/front-differential.ts sany-text` holds the Rust text
//! to the TypeScript one on every corpus spec.

use tla_front::TlcVersion;
use tla_front::report::{ReportOptions, get_sany_text};

/// What SANY prints for the root module `source`, named Main, with no other files.
fn get_text(name: &str, source: &str) -> String {
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
    text.expect("a text").text
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
