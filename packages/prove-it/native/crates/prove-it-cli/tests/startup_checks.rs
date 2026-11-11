//! What TLC checks of a model as it starts, and how it fails there, against TLC built at d8fb231:
//! the configuration's errors that show a value, the symmetry's definition, the invariants it
//! computes and the conjuncts of the specification it drops, and a trace whose successor it fails
//! to find again. Each directory of `tests/startup_checks` holds a spec with its configuration,
//! which names it, the files beside it, `args`, options of TLC's command line to add, one a line,
//! if any, and either `tlc.out`, TLC's exit code and output with `-fp 0 -nowarning
//! -noGenerateSpecTE` but the lines that depend on the time or the machine, with the directory's
//! path as `{directory}`, or `declined`, the reason the binary gives for a spec it leaves to TLC.
//! Each runs on one thread and on four.

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
fn checks_models_at_startup_as_tlc() {
    let fixtures = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/startup_checks");
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
            "prove-it-startup-checks-{}-{}",
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
            if !["tlc.out", "declined", "args"].contains(&file.to_str().unwrap_or_default()) {
                std::fs::copy(source.join(&file), directory.join(&file)).expect("a copy");
            }
        }
        let spec = spec.expect("a configuration");
        let expected = std::fs::read_to_string(source.join("tlc.out")).ok();
        let declined = std::fs::read_to_string(source.join("declined")).ok();
        let options = std::fs::read_to_string(source.join("args")).unwrap_or_default();
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
                .args(options.lines())
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
