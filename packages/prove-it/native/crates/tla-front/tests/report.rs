//! What SANY prints for a small spec. `scripts/front-differential.ts sany-text` holds the Rust text
//! to the TypeScript one on every corpus spec.

use tla_front::TlcVersion;
use tla_front::report::{ReportOptions, get_sany_text};

#[test]
fn names_each_module_sany_parses_analyzes_and_lints() {
    let directory = std::env::temp_dir().join(format!("tla-front-report-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    let spec_path = directory.join("Main.tla");
    std::fs::write(
        &spec_path,
        "---- MODULE Main ----\nEXTENDS Naturals\nC == INSTANCE Counter\nx == C!y + 1\n====\n---- MODULE Counter ----\ny == 2\n====\n",
    )
    .expect("a spec");
    let text = get_sany_text(
        &spec_path,
        &ReportOptions {
            version: TlcVersion::Master,
            load_module: &|_| None,
            describe_file: &|name, origin| format!("{name} {origin:?}"),
        },
    );
    std::fs::remove_dir_all(&directory).expect("a removed directory");
    assert_eq!(
        text.expect("a text"),
        "Parsing file Main File\nParsing file Naturals Standard\nParsing file Counter RootFile\nSemantic processing of module Naturals\nSemantic processing of module Counter\nSemantic processing of module Main\nLinting of module Counter\nLinting of module Main\n"
    );
}
