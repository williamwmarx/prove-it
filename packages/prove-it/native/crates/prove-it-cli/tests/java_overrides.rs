//! The binary's Java overrides of an operator a module declares RECURSIVE and defines LOCAL, which
//! SANY doesn't hide (`Generator.processRecursive`), so TLC loads the method of a class beside the
//! spec in its place, as Hanoi's Bits.class overrides And in tlaplus/Examples.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

// Copies the fixture `tests/java-overrides/<fixture>` to a directory of its own and checks M there
// as TLC's command line does.
fn run_fixture(fixture: &str) -> (Output, PathBuf) {
    let source = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/java-overrides")
        .join(fixture);
    let directory = std::env::temp_dir().join(format!(
        "prove-it-java-overrides-{fixture}-{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&directory).expect("a directory");
    for name in ["M.tla", "M.cfg", "Ext.tla", "Ext.class"] {
        std::fs::copy(source.join(name), directory.join(name)).expect("a fixture file");
    }
    let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .args([
            "-workers",
            "1",
            "-nowarning",
            "-noGenerateSpecTE",
            "-config",
            "M.cfg",
            "M.tla",
        ])
        .current_dir(&directory)
        .output()
        .expect("the binary runs");
    (output, directory)
}

// What TLC built at d8fb231 prints but its version, the machine, times and the standard modules'
// paths, with the fixture's directory in place of `{directory}`.
fn get_untimed_lines(text: &str, directory: &str) -> String {
    text.lines()
        .filter(|line| {
            ![
                "TLC2 Version",
                "Running breadth-first",
                "Starting...",
                "Finished in",
            ]
            .iter()
            .any(|timed| line.starts_with(timed))
                && !line
                    .strip_prefix("Parsing file ")
                    .is_some_and(|path| !path.starts_with(directory))
        })
        .map(|line| format!("{}\n", line.replace(directory, "{directory}")))
        .collect()
}

#[test]
fn loads_the_override_of_a_recursive_local_operator_as_tlc() {
    let (output, directory) = run_fixture("recursive");
    let path = directory.to_str().expect("a path");
    let text = String::from_utf8_lossy(&output.stdout);
    assert_eq!(output.status.code(), Some(12), "{text}");
    assert_eq!(
        get_untimed_lines(&text, path),
        concat!(
            "Parsing file {directory}/M.tla\n",
            "Parsing file {directory}/Ext.tla\n",
            "Semantic processing of module Ext\n",
            "Semantic processing of module Naturals\n",
            "Semantic processing of module M\n",
            "Linting of module Ext\n",
            "Linting of module M\n",
            "Loading Op operator override from file:{directory}/Ext.class with signature: <Java Method: public static tlc2.value.impl.Value Ext.Op()>.\n",
            "Computing initial states...\n",
            "Error: Invariant Inv is violated by the initial state:\n",
            "v = 101\n",
            "\n",
        )
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

// TLC runs the method of a recursive local operator with parameters, as it runs Bits.And, which
// the binary can't.
#[test]
fn declines_the_override_of_a_recursive_local_operator_with_parameters() {
    let (output, directory) = run_fixture("parameters");
    assert_eq!(output.status.code(), Some(1));
    assert_eq!(
        String::from_utf8_lossy(&output.stderr),
        "prove-it: not native yet: a Java override with parameters, whose arguments TLC evaluates\n"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}
