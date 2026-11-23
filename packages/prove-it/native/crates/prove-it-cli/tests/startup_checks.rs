//! What TLC checks of a model as it starts, and how it fails there, against TLC built at d8fb231:
//! the configuration's errors that show a value, what a constant definition prints as TLC computes
//! it, the symmetry's definition, the invariants it computes and the conjuncts of the
//! specification it drops, and a trace whose successor it fails to find again. Each directory of
//! `tests/startup_checks` holds a spec with its configuration, which names it, the files beside
//! it, `args`, options of TLC's command line to add, one a line, if any, and either `tlc.out`,
//! TLC's exit code and output with `-fp 0 -noGenerateSpecTE` but the lines that depend on the time
//! or the machine, with the directory's path as `{directory}`, or `declined`, the reason the
//! binary gives for a spec it leaves to TLC, with TLC's output beside it as `jar.out` where it
//! was recorded. A `declined-4` holds a four-worker-only decline.
//! Each runs on one thread and on four.

mod common;

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

/// The line that starts checking the temporal properties of several branches, which ends with
/// the time TLC starts at, as `at ({time})` in a fixture: its count of branches is TLC's.
fn get_untimed_line(line: &str) -> String {
    match line.rfind(" at (") {
        Some(at)
            if line.starts_with("Checking ")
                && line.contains(" branches of temporal properties ")
                && line.ends_with(')') =>
        {
            format!("{} at ({{time}})", &line[..at])
        }
        _ => line.to_owned(),
    }
}

fn get_untimed_lines(text: &str, directory: &str) -> String {
    text.lines()
        .filter(|line| !VARYING.iter().any(|varying| line.starts_with(varying)))
        .map(|line| {
            format!(
                "{}\n",
                get_untimed_line(line).replace(directory, "{directory}")
            )
        })
        .collect()
}

fn copy_fixture_entry(source: &Path, destination: &Path) {
    if source.is_dir() {
        std::fs::create_dir_all(destination).expect("an auxiliary directory");
        for entry in std::fs::read_dir(source).expect("auxiliary files") {
            let entry = entry.expect("an auxiliary entry");
            copy_fixture_entry(&entry.path(), &destination.join(entry.file_name()));
        }
    } else {
        std::fs::copy(source, destination).expect("a copy");
    }
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
            // TLC's output is kept only under the two names the module's doc gives.
            assert!(
                file.extension().is_none_or(|extension| extension != "out")
                    || ["tlc.out", "jar.out"].contains(&file.to_str().unwrap_or_default()),
                "{}: {} names no output the harness reads or leaves out",
                name.to_string_lossy(),
                file.display()
            );
            if !["tlc.out", "jar.out", "declined", "declined-4", "args"]
                .contains(&file.to_str().unwrap_or_default())
            {
                copy_fixture_entry(&source.join(&file), &directory.join(&file));
            }
        }
        let spec = spec.expect("a configuration");
        let expected = std::fs::read_to_string(source.join("tlc.out")).ok();
        let declined = std::fs::read_to_string(source.join("declined")).ok();
        let declined_four = std::fs::read_to_string(source.join("declined-4")).ok();
        let options = std::fs::read_to_string(source.join("args")).unwrap_or_default();
        for workers in ["1", "4"] {
            let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
                .args(["-workers", workers, "-fp", "0", "-noGenerateSpecTE"])
                .args(options.lines())
                .arg(&spec)
                .current_dir(&directory)
                .output()
                .expect("the binary runs");
            let working = common::get_working_path(&directory);
            let path = working.to_str().expect("a path");
            let actual = format!(
                "exit {}\n{}",
                output.status.code().unwrap_or(-1),
                get_untimed_lines(&String::from_utf8_lossy(&output.stdout), path)
            );
            let stderr = String::from_utf8_lossy(&output.stderr);
            let expected = if workers == "4" && declined_four.is_some() {
                None
            } else {
                expected.as_ref()
            };
            let declined = if workers == "4" {
                declined_four.as_ref().or(declined.as_ref())
            } else {
                declined.as_ref()
            };
            // A path TLC prints differently on Windows the binary declines there.
            let is_declined_on_windows = cfg!(windows)
                && output.status.code() == Some(1)
                && [
                    common::DECLINED_FILE_URL,
                    common::DECLINED_ROOT_FILE,
                    common::DECLINED_JAR,
                    common::DECLINED_CLASS_URL,
                    common::DECLINED_TRACE_SPEC,
                ]
                .iter()
                .any(|reason| stderr.starts_with(&format!("prove-it: not native yet: {reason}")));
            let is_same = is_declined_on_windows
                || match (expected, declined) {
                    (Some(expected), None) => actual == *expected,
                    (None, Some(reason)) => {
                        stderr == format!("prove-it: not native yet: {reason}")
                            && output.status.code() == Some(1)
                            && output.stdout.is_empty()
                    }
                    _ => panic!("{name:?} holds neither tlc.out nor declined"),
                };
            if !is_same {
                let raw_stdout_bytes = output.stdout.len();
                differences.push(format!(
                    "{name:?} at {workers} workers ({raw_stdout_bytes} raw stdout bytes):\n{actual}{stderr}\nexpected:\n{}",
                    expected
                        .map(String::as_str)
                        .or(declined.map(String::as_str))
                        .unwrap_or_default()
                ));
            }
        }
        std::fs::remove_dir_all(&directory).expect("removed");
    }
    assert!(differences.is_empty(), "{}", differences.join("\n"));
}
