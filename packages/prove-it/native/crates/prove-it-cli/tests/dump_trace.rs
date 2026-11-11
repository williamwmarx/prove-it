//! `-dumpTrace tlc <file>` and `-dumpTrace json <file>`, against what TLC built at d8fb231 printed
//! and wrote for the specs in tests/dump-trace: `<Spec>.tool.out` with `-tool -modelcheck
//! -dumpTrace tlc <Spec>.bin -dumpTrace json <Spec>.json`, and `<Spec>.out` with `-noTE -dumpTrace
//! json <Spec>.first.json -dumpTrace tlc <Spec>.first.bin`. The JSON is compared byte for byte, the
//! `.bin` but for the tokens of its strings, which no two runs share.

#[path = "../../tla-trace/tests/dump/payload.rs"]
mod payload;

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use payload::compare_dumps;

fn fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/dump-trace")
        .join(name)
}

fn read_fixture(name: &str) -> String {
    std::fs::read_to_string(fixture(name)).expect("a fixture")
}

// Copies the spec and its configuration to a directory of their own and runs the binary there
// with TLC's command line.
fn run(test: &str, spec: &str, args: &[&str]) -> (Output, PathBuf) {
    let directory =
        std::env::temp_dir().join(format!("prove-it-dump-trace-{test}-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    for extension in ["tla", "cfg"] {
        let name = format!("{spec}.{extension}");
        std::fs::copy(fixture(&name), directory.join(&name)).expect("the spec");
    }
    let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .args(["tlc2.TLC"].iter().chain(args).chain([&spec]))
        .current_dir(&directory)
        .output()
        .expect("the binary runs");
    (output, directory)
}

// What a run prints but its times, its machine, where the files it parses are, and its progress,
// which comes once a minute.
fn normalize(text: &str) -> String {
    let mut lines = Vec::new();
    for line in text.lines() {
        if line.starts_with("Progress(") || line.contains("MSG 2200") {
            continue;
        }
        let timed = [
            "TLC2 Version ",
            "Running breadth-first search ",
            "Starting... ",
            "Finished in ",
            "Finished checking temporal properties ",
        ]
        .into_iter()
        .find(|prefix| line.starts_with(prefix));
        let line = match (timed, line.strip_prefix("Parsing file ")) {
            (Some(prefix), _) => prefix.to_owned(),
            (None, Some(path)) => {
                let path = path.split(' ').next().unwrap_or(path);
                format!("Parsing file {}", path.rsplit('/').next().unwrap_or(path))
            }
            _ if line.starts_with("Finished computing initial states")
                || line.starts_with("Checking temporal properties ") =>
            {
                line.rsplit_once(" at ")
                    .map_or(line, |(head, _)| head)
                    .to_owned()
            }
            _ => line.to_owned(),
        };
        lines.push(line);
    }
    lines.join("\n")
}

fn check_files(spec: &str, directory: &Path, bin: &str, json: &str) {
    let actual = std::fs::read(directory.join(bin)).expect("the tlc dump");
    let expected = std::fs::read(fixture(bin)).expect("TLC's dump");
    if let Err(difference) = compare_dumps(&expected, &actual) {
        panic!("{spec}: {bin}: {difference}");
    }
    let actual = std::fs::read_to_string(directory.join(json)).expect("the JSON dump");
    assert_eq!(actual, read_fixture(json), "{spec}: {json}");
}

// Each spec with the exit code TLC ends it with, and whether TLC finds a counterexample to dump.
const SPECS: [(&str, i32, bool); 5] = [
    ("DumpInvariant", 12, true),
    ("DumpDeadlock", 11, true),
    ("DumpLasso", 13, true),
    ("DumpInitial", 12, true),
    ("DumpSuccess", 0, false),
];

#[test]
fn dumps_counterexamples_as_tlc_with_tool() {
    // An invariant violation, with model values; a deadlock; a lasso, its step back into the
    // cycle closing it; an initial state's violation; and a run without a counterexample, which
    // writes and prints nothing more. Each prints `CounterExample written: <file>` as PrintT does
    // as TLC checks the postconditions, after the trace.
    for (spec, code, is_dumped) in SPECS {
        let (bin, json) = (format!("{spec}.bin"), format!("{spec}.json"));
        let (output, directory) = run(
            &format!("tool-{spec}"),
            spec,
            &[
                "-tool",
                "-modelcheck",
                "-dumpTrace",
                "tlc",
                &bin,
                "-dumpTrace",
                "json",
                &json,
            ],
        );
        let text = String::from_utf8_lossy(&output.stdout);
        assert_eq!(output.status.code(), Some(code), "{spec}: {text}");
        assert_eq!(
            normalize(&text),
            normalize(&read_fixture(&format!("{spec}.tool.out"))),
            "{spec}"
        );
        if is_dumped {
            check_files(spec, &directory, &bin, &json);
        } else {
            assert!(!directory.join(&bin).exists() && !directory.join(&json).exists());
        }
        std::fs::remove_dir_all(directory).expect("removed");
    }
}

#[test]
fn dumps_counterexamples_as_tlc_without_tool_json_first() {
    // The JSON, written before the tlc dump sorts the counterexample, holds its records and
    // functions in the order they were made.
    for (spec, code, is_dumped) in SPECS {
        let (bin, json) = (format!("{spec}.first.bin"), format!("{spec}.first.json"));
        let (output, directory) = run(
            &format!("plain-{spec}"),
            spec,
            &[
                "-noTE",
                "-dumpTrace",
                "json",
                &json,
                "-dumpTrace",
                "tlc",
                &bin,
            ],
        );
        let text = String::from_utf8_lossy(&output.stdout);
        assert_eq!(output.status.code(), Some(code), "{spec}: {text}");
        assert_eq!(
            normalize(&text),
            normalize(&read_fixture(&format!("{spec}.out"))),
            "{spec}"
        );
        if is_dumped {
            check_files(spec, &directory, &bin, &json);
        } else {
            assert!(!directory.join(&bin).exists() && !directory.join(&json).exists());
        }
        std::fs::remove_dir_all(directory).expect("removed");
    }
}

#[test]
fn dumps_into_the_file_the_last_option_of_a_format_names() {
    // TLC gives `_TLCTrace`'s constant the file of each -dumpTrace tlc in turn, so both
    // postconditions write and name the last (`processConstantsForModule`, TLC at d8fb231).
    let (output, directory) = run(
        "shared-constant",
        "DumpInvariant",
        &[
            "-tool",
            "-dumpTrace",
            "tlc",
            "first.bin",
            "-dumpTrace",
            "tlc",
            "DumpInvariant.bin",
        ],
    );
    let text = String::from_utf8_lossy(&output.stdout);
    assert_eq!(output.status.code(), Some(12), "{text}");
    assert!(
        text.contains("\n\"CounterExample written: DumpInvariant.bin\"\n\"CounterExample written: DumpInvariant.bin\"\n@!@!@STARTMSG 2200:0 @!@!@\n"),
        "{text}"
    );
    assert!(!directory.join("first.bin").exists());
    let actual = std::fs::read(directory.join("DumpInvariant.bin")).expect("the tlc dump");
    let expected = std::fs::read(fixture("DumpInvariant.bin")).expect("TLC's dump");
    assert_eq!(compare_dumps(&expected, &actual), Ok(()));
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn parses_the_trace_modules_where_tlc_records_the_trace() {
    // By default TLC adds the trace exploration spec's `_TLCTrace` after the command line's
    // modules, and SANY parses them all with the spec.
    let (output, directory) = run(
        "default",
        "DumpSuccess",
        &[
            "-dumpTrace",
            "tlc",
            "DumpSuccess.bin",
            "-dumpTrace",
            "json",
            "DumpSuccess.json",
        ],
    );
    let text = String::from_utf8_lossy(&output.stdout);
    assert_eq!(output.status.code(), Some(0), "{text}");
    assert_eq!(
        normalize(&text),
        normalize(&read_fixture("DumpSuccess.default.out"))
    );
    std::fs::remove_dir_all(directory).expect("removed");
    // A counterexample makes the trace exploration spec's postcondition write its own file to the
    // constant the command line's `tlc` dump shares, which the binary doesn't yet.
    let (output, directory) = run(
        "default-violation",
        "DumpInvariant",
        &["-dumpTrace", "json", "DumpInvariant.json"],
    );
    let text = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        text.contains("prove-it: not native yet: -dumpTrace with the trace exploration spec"),
        "{text}"
    );
    assert!(!directory.join("DumpInvariant.json").exists());
    std::fs::remove_dir_all(directory).expect("removed");
}

// Writes the files to a directory of their own and runs the binary there with TLC's command line.
fn run_files(test: &str, files: &[(&str, &str)], args: &[&str]) -> (String, PathBuf) {
    let directory =
        std::env::temp_dir().join(format!("prove-it-dump-trace-{test}-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    for (name, text) in files {
        std::fs::write(directory.join(name), text).expect("a file");
    }
    let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .args(["tlc2.TLC"].iter().chain(args))
        .current_dir(&directory)
        .output()
        .expect("the binary runs");
    let text = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    (text, directory)
}

#[test]
fn declines_a_module_of_the_users_that_a_trace_module_uses() {
    // SANY analyzes `_JsonTrace` with the spec, and a Json beside the spec in place of the
    // standard one fails TLC's run, though the spec doesn't use it (TLC at d8fb231 reports
    // "Unknown operator: `JsonSerialize'." in _JsonTrace).
    let (text, directory) = run_files(
        "users-json",
        &[
            (
                "M.tla",
                "---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x < 2 /\\ x' = x + 1\nInv == x < 2\n====\n",
            ),
            ("M.cfg", "INIT Init\nNEXT Next\nINVARIANT Inv\n"),
            ("Json.tla", "---- MODULE Json ----\nFoo == 1\n====\n"),
        ],
        &["-tool", "-modelcheck", "-dumpTrace", "json", "M.json", "M"],
    );
    assert!(
        text.contains("not native yet: SANY's report of a module of the user's that the trace exploration spec uses"),
        "{text}"
    );
    assert!(!directory.join("M.json").exists());
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn loads_the_integers_methods_a_trace_module_loads() {
    // `_JsonTrace` loads TLCExt, which loads Integers, so TLC divides with Integers' method
    // though the spec extends only Naturals (TLC at d8fb231).
    let (text, directory) = run_files(
        "integers",
        &[
            (
                "M.tla",
                "---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLE x\nASSUME PrintT((0 - 2147483647 - 1) \\div (0 - 1))\nInit == x = 0\nNext == x' = x\n====\n",
            ),
            ("M.cfg", "INIT Init\nNEXT Next\n"),
        ],
        &["-tool", "-modelcheck", "-dumpTrace", "json", "M.json", "M"],
    );
    assert!(
        text.contains("Overflow when computing -2147483648 \\div -1"),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn declines_a_postcondition_tlc_rejects() {
    // TLC collects the postconditions, -dumpTrace's and the configuration's, before it evaluates
    // any, and fails on one that takes an argument: it prints the trace and writes no file
    // (TLC at d8fb231).
    let (text, directory) = run_files(
        "rejected",
        &[
            (
                "R.tla",
                "---- MODULE R ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x' = x + 1\nInv == x < 2\nP(y) == TRUE\n====\n",
            ),
            (
                "R.cfg",
                "INIT Init\nNEXT Next\nINVARIANT Inv\nPOSTCONDITION P\n",
            ),
        ],
        &["-tool", "-modelcheck", "-dumpTrace", "json", "R.json", "R"],
    );
    assert!(
        text.contains("not native yet: the engine stopped")
            && text.contains("-dumpTrace with a POSTCONDITION TLC rejects"),
        "{text}"
    );
    assert!(!text.contains("CounterExample written"), "{text}");
    assert!(!directory.join("R.json").exists());
    std::fs::remove_dir_all(directory).expect("removed");
}
