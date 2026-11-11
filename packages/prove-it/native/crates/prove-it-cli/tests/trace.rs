//! The binary as TLC runs by default, recording the trace for its trace exploration spec,
//! against TLC built at d8fb231.

use std::path::PathBuf;
use std::process::{Command, Output};

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

// Writes the spec and its configuration to a directory of their own and checks them with TLC's
// command line and the arguments, without -noTE.
fn run_spec(test: &str, spec: &str, config: &str, args: &[&str]) -> (Output, PathBuf) {
    let directory =
        std::env::temp_dir().join(format!("prove-it-trace-{test}-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    let name = spec
        .split_whitespace()
        .nth(2)
        .expect("the module's name")
        .to_string();
    std::fs::write(directory.join(format!("{name}.tla")), spec).expect("the spec");
    std::fs::write(directory.join(format!("{name}.cfg")), config).expect("the configuration");
    let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .args(args.iter().chain([&name.as_str()]))
        .current_dir(&directory)
        .output()
        .expect("the binary runs");
    (output, directory)
}

#[test]
fn checks_as_tlc_does_by_default_where_it_records_the_trace() {
    // TLC's default records the trace for its trace exploration spec: SANY parses _TLCTrace and
    // the modules it uses with the spec, and TLC loads Integers' methods over Naturals', so
    // -1 \\div 2 is -1 and >= names itself (TLC at d8fb231).
    let spec = "---- MODULE Succ ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x < 3 /\\ x' = x + 1\nInv == x <= 3\n====\n";
    let (output, directory) = run_spec(
        "trace-default",
        spec,
        "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n",
        &[],
    );
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(0), "{text}");
    let parsed: Vec<&str> = text
        .lines()
        .filter_map(|line| line.strip_prefix("Parsing file "))
        .map(|path| {
            let file = path.rsplit('/').next().unwrap_or(path);
            file.strip_suffix(".tla").unwrap_or(file)
        })
        .collect();
    assert_eq!(
        parsed,
        [
            "Succ",
            "Naturals",
            "_TLCTrace",
            "TLC",
            "TLCExt",
            "Sequences",
            "FiniteSets",
            "Integers"
        ],
        "{text}"
    );
    assert!(
        text.contains("Semantic processing of module Naturals\nSemantic processing of module Sequences\nSemantic processing of module FiniteSets\nSemantic processing of module TLC\nSemantic processing of module Integers\nSemantic processing of module TLCExt\nSemantic processing of module _TLCTrace\nSemantic processing of module Succ\nLinting of module TLCExt\nLinting of module _TLCTrace\nLinting of module Succ\nStarting... ("),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
    for (test, assumption, expected) in [
        (
            "trace-divide",
            "ASSUME PrintT((0 - 1) \\div 2)\nASSUME PrintT((0 - 2147483647 - 1) \\div (0 - 1))",
            "\n-1\nError: Evaluating assumption line 7, col 8 to line 7, col 48 of module Arith failed.\nOverflow when computing -2147483648 \\div -1\n",
        ),
        (
            "trace-geq",
            "ASSUME TRUE\nASSUME \"a\" >= 1",
            "\nError: Evaluating assumption line 7, col 8 to line 7, col 15 of module Arith failed.\nThe first argument of >= should be an integer, but instead it is:\n\"a\"\n",
        ),
    ] {
        let spec = format!(
            "---- MODULE Arith ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == x' = x\n{assumption}\n====\n"
        );
        let (output, directory) = run_spec(test, &spec, "INIT Init\nNEXT Next\n", &[]);
        let text = stdout(&output);
        assert_eq!(output.status.code(), Some(10), "{text}");
        assert!(text.contains(expected), "{text}");
        std::fs::remove_dir_all(directory).expect("removed");
    }
}

#[test]
fn declines_a_counterexample_where_tlc_records_the_trace() {
    // TLC writes the trace's file for any counterexample, compressed with Java's Deflater, which
    // the binary doesn't yet.
    let spec = "---- MODULE Viol ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x' = x + 1\nInv == x > 0\n====\n";
    let (output, directory) = run_spec(
        "trace-counterexample",
        spec,
        "INIT Init\nNEXT Next\nINVARIANT Inv\n",
        &[],
    );
    let text = format!(
        "{}{}",
        stdout(&output),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        text.contains(
            "prove-it: not native yet: the trace file of the trace exploration spec, which TLC compresses with Java's Deflater"
        ),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn writes_the_spec_after_an_error_after_a_behavior_where_tlc_records_the_trace() {
    // TLC records the behavior it prints before any error, so it writes the trace exploration
    // spec for an Assert that fails in an action (exit 14) and for an invariant that fails to
    // evaluate (exit 76) as for a counterexample: at d8fb231, Stop_TTrace_<epoch>.tla and its path
    // after both, and no trace file. tests/te_spec.rs checks the spec's text.
    for (name, spec, config, exit) in [
        (
            "trace-assert",
            "---- MODULE Stop ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == x' = x + 1 /\\ Assert(x < 1, \"x is one\")\n====\n",
            "INIT Init\nNEXT Next\n",
            14,
        ),
        (
            "trace-invariant",
            "---- MODULE Stop ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x' = x + 1\nInv == IF x = 1 THEN 1 ELSE TRUE\n====\n",
            "INIT Init\nNEXT Next\nINVARIANT Inv\n",
            76,
        ),
    ] {
        let (output, directory) = run_spec(name, spec, config, &[]);
        let text = stdout(&output);
        assert_eq!(output.status.code(), Some(exit), "{name}: {text}");
        let line = text.lines().last().unwrap_or_default();
        let path = line
            .strip_prefix("Trace exploration spec path: ./")
            .unwrap_or_else(|| panic!("{name}: {text}"));
        assert!(directory.join(path).exists(), "{name}: {path}");
        let files = std::fs::read_dir(&directory)
            .expect("the directory")
            .filter(|entry| {
                entry
                    .as_ref()
                    .expect("an entry")
                    .file_name()
                    .to_string_lossy()
                    .contains("_TTrace_")
            })
            .count();
        assert_eq!(files, 1, "{name}");
        std::fs::remove_dir_all(directory).expect("removed");
    }
}

#[test]
fn declines_a_module_of_the_users_that_the_trace_exploration_spec_uses() {
    // SANY analyzes the modules TLC adds for the trace exploration spec with the spec's, so a
    // TLCExt beside the spec that fails its analysis fails TLC's run, though the spec doesn't use
    // it (TLC at d8fb231 reports "Unknown operator: `Unknown'." in TLCExt, then _TLCTrace's own).
    let directory =
        std::env::temp_dir().join(format!("prove-it-trace-users-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    let files = [
        (
            "M.tla",
            "---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x < 2 /\\ x' = x + 1\n====\n",
        ),
        ("M.cfg", "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n"),
        (
            "TLCExt.tla",
            "---- MODULE TLCExt ----\nBad == Unknown\n====\n",
        ),
    ];
    for (name, text) in files {
        std::fs::write(directory.join(name), text).expect("a file");
    }
    let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .arg("M")
        .current_dir(&directory)
        .output()
        .expect("the binary runs");
    let text = format!(
        "{}{}",
        stdout(&output),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        text.contains("not native yet: SANY's report of a module of the user's that the trace exploration spec uses"),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn checks_the_other_specs_after_declining_a_counterexample() {
    // The binary checks each spec it's given in turn, as after any spec it declines.
    let directory =
        std::env::temp_dir().join(format!("prove-it-trace-batch-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    let files = [
        (
            "Viol.tla",
            "---- MODULE Viol ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x' = x + 1\nInv == x > 0\n====\n",
        ),
        ("Viol.cfg", "INIT Init\nNEXT Next\nINVARIANT Inv\n"),
        (
            "Good.tla",
            "---- MODULE Good ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x < 2 /\\ x' = x + 1\n====\n",
        ),
        ("Good.cfg", "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n"),
    ];
    for (name, text) in files {
        std::fs::write(directory.join(name), text).expect("a file");
    }
    let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .args(["Viol", "Good"])
        .current_dir(&directory)
        .output()
        .expect("the binary runs");
    let text = format!(
        "{}{}",
        stdout(&output),
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(output.status.code(), Some(1), "{text}");
    assert!(
        text.contains(
            "not native yet: the trace file of the trace exploration spec, which TLC compresses with Java's Deflater"
        ),
        "{text}"
    );
    assert!(text.contains("Checking Good.tla with Good.cfg\n"), "{text}");
    assert!(
        text.contains("Model checking completed. No error has been found."),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}
