//! The trace exploration spec TLC writes in its default mode after an error trace, against what
//! TLC at d8fb231 wrote for the same specs (tests/te-spec, each with the `.tla` TLC wrote). TLC
//! names the file by the second its run started and dates it as it writes it; the binary runs with
//! its clock fixed by PROVE_IT_TEST_NOW, and the test puts the binary's second and date in place of
//! TLC's.

mod common;

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

// 2026-11-11 04:26:40 UTC, which `java.util.Date.toString` writes as below.
const NOW_MILLISECONDS: &str = "1794371200000";
const NOW_SECONDS: &str = "1794371200";
const NOW_DATE: &str = "Wed Nov 11 04:26:40 UTC 2026";

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/te-spec")
        .join(name)
}

// Copies the fixture's spec and configuration to a directory of the test's and checks the spec
// there, as TLC does by default.
fn run(test: &str, name: &str, module: &str, args: &[&str]) -> (Output, PathBuf) {
    let directory = std::env::temp_dir().join(format!(
        "prove-it-te-spec-{test}-{name}-{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&directory).expect("a directory");
    for extension in ["tla", "cfg"] {
        let file = format!("{module}.{extension}");
        std::fs::copy(fixture(name).join(&file), directory.join(&file)).expect("the fixture");
    }
    let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .args(["-workers", "1"].iter().chain(args).chain([&module]))
        .env("PROVE_IT_TEST_NOW", NOW_MILLISECONDS)
        .env_remove("TZ")
        .current_dir(&directory)
        .output()
        .expect("the binary runs");
    (output, directory)
}

// The spec TLC wrote, with the binary's second and date in place of TLC's.
fn get_expected_spec(name: &str, module: &str) -> String {
    let path = std::fs::read_dir(fixture(name))
        .expect("the fixture")
        .map(|entry| entry.expect("an entry").path())
        .find(|path| {
            path.file_name().is_some_and(|file| {
                file.to_string_lossy()
                    .starts_with(&format!("{module}_TTrace_"))
            })
        })
        .expect("the spec TLC wrote");
    let stem = path
        .file_stem()
        .expect("a stem")
        .to_string_lossy()
        .into_owned();
    let second = stem.rsplit('_').next().expect("the second").to_string();
    let text = std::fs::read_to_string(&path).expect("the spec");
    let (body, generated) = text
        .rsplit_once("\\* Generated on ")
        .expect("the date TLC wrote");
    assert!(!generated.contains('\n'));
    format!("{body}\\* Generated on {NOW_DATE}").replace(&second, NOW_SECONDS)
}

#[test]
fn writes_the_trace_exploration_spec_after_an_error_trace_as_tlc() {
    // An Assert that fails in an action, and an invariant that fails to evaluate: TLC writes the
    // spec of the behavior up to the error, and no trace file, since the counterexample is empty.
    for (name, exit) in [("assert", 14), ("evalinv", 76)] {
        let (output, directory) = run("written", name, "Stop", &[]);
        if cfg!(windows) {
            common::assert_declined(&output, common::DECLINED_TRACE_SPEC, name);
            std::fs::remove_dir_all(directory).expect("removed");
            continue;
        }
        let text = String::from_utf8_lossy(&output.stdout);
        assert_eq!(output.status.code(), Some(exit), "{name}: {text}");
        let path = format!("Stop_TTrace_{NOW_SECONDS}.tla");
        assert!(
            text.ends_with(&format!("Trace exploration spec path: ./{path}\n")),
            "{name}: {text}"
        );
        let written = std::fs::read_to_string(directory.join(&path)).expect("the spec");
        assert_eq!(written, get_expected_spec(name, "Stop"), "{name}");
        let files: Vec<String> = std::fs::read_dir(&directory)
            .expect("the directory")
            .map(|entry| {
                entry
                    .expect("an entry")
                    .file_name()
                    .to_string_lossy()
                    .into_owned()
            })
            .filter(|file| file.contains("_TTrace_"))
            .collect();
        assert_eq!(files, [path], "{name}");
        std::fs::remove_dir_all(directory).expect("removed");
    }
}

#[test]
fn writes_no_trace_exploration_spec_where_tlc_writes_none() {
    // With -noTE, TLC writes neither file, and the binary prints the error trace without the path.
    let (output, directory) = run("unwritten", "assert", "Stop", &["-noTE"]);
    let text = String::from_utf8_lossy(&output.stdout);
    assert_eq!(output.status.code(), Some(14), "{text}");
    assert!(!text.contains("Trace exploration spec path"), "{text}");
    assert!(
        std::fs::read_dir(&directory)
            .expect("the directory")
            .all(|entry| !entry
                .expect("an entry")
                .file_name()
                .to_string_lossy()
                .contains("_TTrace_"))
    );
    std::fs::remove_dir_all(directory).expect("removed");
}
