//! TLC's verdict where SANY's level of a formula differs from TLC's level bound of it: an operator
//! application takes the levels of the arguments its body reads, and a LET its body's level, where
//! the bound counts every argument and every definition. `processConfigProps` sorts a property by
//! the bound, and the liveness checker and `_POSSIBLE` take SANY's level.
//! Full outputs were recorded with TLC d8fb231 and JDK 21.0.13+9.

use std::process::Command;

const VARYING: &[&str] = &[
    "TLC2 Version",
    "Running ",
    "Parsing file",
    "Semantic processing",
    "Linting of module",
    "Starting...",
    "Computing initial states",
    "Finished computing initial states",
    "Finished in",
    "Picked up JAVA_TOOL_OPTIONS",
];

fn fixed(text: &str) -> String {
    text.lines()
        .filter(|line| !VARYING.iter().any(|prefix| line.starts_with(prefix)))
        .collect::<Vec<_>>()
        .join("\n")
        .trim_end()
        .to_owned()
}

#[test]
fn levels_a_property_as_sany_and_tlc_do() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/level-params");
    let mut cases: Vec<_> = std::fs::read_dir(&root)
        .expect("the fixtures")
        .map(|entry| entry.expect("an entry").path())
        .collect();
    cases.sort();
    assert_eq!(cases.len(), 21);
    for fixture in cases {
        let name = fixture
            .file_name()
            .expect("a name")
            .to_string_lossy()
            .into_owned();
        let directory = std::env::temp_dir().join(format!(
            "prove-it-level-params-{name}-{}",
            std::process::id()
        ));
        std::fs::create_dir_all(&directory).expect("a fixture directory");
        for file in ["M.tla", "M.cfg"] {
            std::fs::copy(fixture.join(file), directory.join(file)).expect("a fixture file");
        }
        let reference = std::fs::read_to_string(fixture.join("tlc.txt"))
            .expect("the pinned Jar's complete output");
        let reference_exit: i32 = std::fs::read_to_string(fixture.join("tlc.exit"))
            .expect("the pinned Jar's exit code")
            .trim()
            .parse()
            .expect("an exit code");
        let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
            .args([
                "-fp",
                "0",
                "-seed",
                "4",
                "-lncheck",
                "final",
                "-noGenerateSpecTE",
                "-config",
                "M.cfg",
                "M.tla",
            ])
            .current_dir(&directory)
            .output()
            .expect("the binary runs");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(output.status.code(), Some(reference_exit), "{name}");
        assert_eq!(
            fixed(&format!("{stdout}{stderr}")),
            fixed(&reference),
            "{name}"
        );
        std::fs::remove_dir_all(directory).expect("removed fixtures");
    }
}
