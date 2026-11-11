//! What the front end computes of a spec's constants and its Java overrides before the search,
//! against TLC built at d8fb231. Each directory of `tests/front_constants` holds a spec with its
//! configuration, which names it, and the files beside it, and either `tlc.out`, TLC's exit code
//! and output with `-fp 0 -nowarning -noGenerateSpecTE` but the lines that depend on the time or
//! the machine, with the directory's path as `{directory}`, or `declined`, the reason the binary
//! gives for a spec it leaves to TLC. Each runs on one thread and with every level shared between
//! four.

use std::path::Path;
use std::process::Command;

// The lines whose text depends on the time, the machine or where TLC's jar keeps its modules.
const VARYING: &[&str] = &[
    "TLC2 Version",
    "Running breadth-first search",
    "Parsing file",
    "Starting...",
    "Finished computing initial states",
    "Finished in",
    "calculated (optimistic)",
    "Progress(",
    "Checking temporal properties",
    "Finished checking temporal properties",
];

fn get_untimed_lines(text: &str, directory: &str) -> String {
    text.lines()
        .filter(|line| !VARYING.iter().any(|varying| line.starts_with(varying)))
        .map(|line| format!("{}\n", line.replace(directory, "{directory}")))
        .collect()
}

#[test]
fn computes_constants_and_overrides_as_tlc() {
    let fixtures = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/front_constants");
    let mut names: Vec<_> = std::fs::read_dir(&fixtures)
        .expect("the fixtures")
        .map(|entry| entry.expect("an entry").file_name())
        .collect();
    names.sort();
    assert!(!names.is_empty());
    let mut differences = Vec::new();
    for name in &names {
        let source = fixtures.join(name);
        let directory = std::env::temp_dir().join(format!(
            "prove-it-front-constants-{}-{}",
            name.to_string_lossy(),
            std::process::id()
        ));
        std::fs::create_dir_all(&directory).expect("a directory");
        let mut spec = None;
        for entry in std::fs::read_dir(&source).expect("a fixture") {
            let file = Path::new(&entry.expect("an entry").file_name()).to_owned();
            if file.extension().is_some_and(|extension| extension == "cfg") {
                spec = file.file_stem().map(|stem| stem.to_owned());
            }
            if file != Path::new("tlc.out") && file != Path::new("declined") {
                std::fs::copy(source.join(&file), directory.join(&file)).expect("a copy");
            }
        }
        let spec = spec.expect("a configuration");
        let expected = std::fs::read_to_string(source.join("tlc.out")).ok();
        let declined = std::fs::read_to_string(source.join("declined")).ok();
        for workers in ["1", "4"] {
            let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
                .args([
                    "-workers",
                    workers,
                    "-fp",
                    "0",
                    "-nowarning",
                    "-noGenerateSpecTE",
                ])
                .arg(&spec)
                .current_dir(&directory)
                .output()
                .expect("the binary runs");
            let path = directory.to_str().expect("a path");
            let actual = format!(
                "exit {}\n{}",
                output.status.code().unwrap_or(-1),
                get_untimed_lines(&String::from_utf8_lossy(&output.stdout), path)
            );
            let stderr = String::from_utf8_lossy(&output.stderr);
            let is_same = match (&expected, &declined) {
                (Some(expected), None) => actual == *expected,
                (None, Some(reason)) => {
                    stderr == format!("prove-it: not native yet: {reason}")
                        && output.status.code() == Some(1)
                }
                _ => panic!("{name:?} holds neither tlc.out nor declined"),
            };
            if !is_same {
                differences.push(format!(
                    "{name:?} at {workers} workers:\n{actual}{stderr}\nexpected:\n{}",
                    expected
                        .as_deref()
                        .or(declined.as_deref())
                        .unwrap_or_default()
                ));
            }
        }
        std::fs::remove_dir_all(&directory).expect("removed");
    }
    assert!(differences.is_empty(), "{}", differences.join("\n"));
}
