//! The trace evaluator keeps an argument's value once evaluated while it checks an assumption, as
//! TLC's `LazyValue` keeps it there, so an assumption the engine leaves to it costs what it costs
//! TLC and prints once what TLC prints once. In a replay it evaluates an argument again at each
//! use, as before: each spec in `trace-kept` is one that a replay keeping values got wrong, or
//! could, with TLC's output.

mod common;

use std::path::Path;

use common::{run, run_spec, stderr, stdout};

// The engine leaves the assumption to the trace evaluator: it binds a tuple pattern to a set of
// functions. Each call names its argument twice, so evaluating an argument again at each use
// would double the work at each of the 60 calls.
#[test]
fn checks_an_assumption_naming_each_argument_twice_as_tlc_does() {
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals\nRECURSIVE Doubled(_, _)\nDoubled(n, S) == IF n = 0 THEN S ELSE Doubled(n - 1, S \\cup S)\nASSUME {<<s, t>> \\in {f \\in [1..2 -> Doubled(60, {1})] : TRUE} : TRUE} # {}\n====\n";
    let (output, directory) = run_spec("trace-kept", spec, "");
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(0), "{text}{}", stderr(&output));
    assert!(
        text.contains(
            "Model checking completed. No error has been found.\n  Estimates of the probability that TLC did not check all reachable states\n  because two distinct states had the same fingerprint:\n  calculated (optimistic):  val = 0.0\n0 states generated, 0 distinct states found, 0 states left on queue.\nThe depth of the complete state graph search is 0.\n"
        ),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

// An argument that builds a lazy function holds the states it was built in, so the walk keeps its
// value only for those states: TLC's `LazyValue` keeps it per state, and each successor the walk
// tries applies the function to its own x'.
#[test]
fn applies_an_argument_built_lazy_in_each_successor_as_tlc_does() {
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nP(F) == /\\ x' \\in {1, 2} /\\ F[0] = x'\nNext == P([i \\in Nat |-> x'])\nInv == x # 2\n====\n";
    let (output, directory) = run_spec(
        "trace-kept-lazy",
        spec,
        "INIT Init\nNEXT Next\nINVARIANT Inv\n",
    );
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(12), "{text}{}", stderr(&output));
    assert!(
        text.contains(
            "Error: Invariant Inv is violated.\nError: The behavior up to this point is:\nState 1: <Initial predicate>\nx = 0\n\nState 2: <P line 6, col 9 to line 6, col 29 of module Stop>\nx = 2\n\n3 states generated, 3 distinct states found, 1 states left on queue.\n"
        ),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

// An argument whose value is another's, holding the states, holds them too: Q's B is F's value,
// kept for the states F was built in.
#[test]
fn applies_an_argument_passed_on_lazy_in_each_successor_as_tlc_does() {
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nQ(A, B) == /\\ x' \\in {1, 2} /\\ A[0] = x' /\\ B[0] = x'\nP(F) == Q(F, F)\nNext == P([i \\in Nat |-> x'])\nInv == x # 2\n====\n";
    let (output, directory) = run_spec(
        "trace-kept-passed",
        spec,
        "INIT Init\nNEXT Next\nINVARIANT Inv\n",
    );
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(12), "{text}{}", stderr(&output));
    assert!(
        text.contains(
            "Error: Invariant Inv is violated.\nError: The behavior up to this point is:\nState 1: <Initial predicate>\nx = 0\n\nState 2: <P line 7, col 9 to line 7, col 29 of module Stop>\nx = 2\n\n3 states generated, 3 distinct states found, 1 states left on queue.\n"
        ),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

// A definition that builds a lazy function of x' holds the states, so it isn't the same value in
// each successor, though it reads none as it is built.
#[test]
fn applies_a_definition_built_lazy_in_each_successor_as_tlc_does() {
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nD == [i \\in Nat |-> x']\nNext == x' \\in {1, 2} /\\ D[0] = x'\nInv == x # 2\n====\n";
    let (output, directory) = run_spec(
        "trace-kept-definition",
        spec,
        "INIT Init\nNEXT Next\nINVARIANT Inv\n",
    );
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(12), "{text}{}", stderr(&output));
    assert!(
        text.contains(
            "Error: Invariant Inv is violated.\nError: The behavior up to this point is:\nState 1: <Initial predicate>\nx = 0\n\nState 2: <Next line 6, col 9 to line 6, col 34 of module Stop>\nx = 2\n\n3 states generated, 3 distinct states found, 1 states left on queue.\n"
        ),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

fn get_untimed(text: &str) -> String {
    const DROPPED: [&str; 8] = [
        "Picked up JAVA_TOOL_OPTIONS",
        "TLC2 Version",
        "Running breadth-first",
        "Parsing file",
        "Starting...",
        "Finished in",
        "Warning: Please run the Java VM",
        "(Use the -nowarning",
    ];
    text.lines()
        .filter(|line| !DROPPED.iter().any(|dropped| line.starts_with(dropped)))
        .map(|line| {
            let line = if line.starts_with("Finished computing initial states:") {
                line.rsplit_once(" at ").map_or(line, |(kept, _)| kept)
            } else {
                line
            };
            format!("{line}\n")
        })
        .collect()
}

// Each spec in `trace-kept` passes through the trace evaluator a value that a kept argument could
// get wrong: one passed through operators, a recursive one or a LAMBDA, held by a filter or a
// CHOOSE, of x, x' or the level, and one that prints, draws or fails, in an assumption the engine
// leaves to it. Each prints what TLC prints (`tlc.out`, recorded from TLC at d8fb231), on one
// thread and on four.
#[test]
fn keeps_an_argument_only_where_tlc_does() {
    let cases = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/trace-kept");
    let mut names: Vec<_> = std::fs::read_dir(&cases)
        .expect("the cases")
        .map(|entry| entry.expect("a case").file_name())
        .collect();
    names.sort();
    let mut differences = Vec::new();
    for name in names {
        let case = cases.join(&name);
        let directory = std::env::temp_dir().join(format!(
            "prove-it-cli-trace-kept-{}-{}",
            name.to_string_lossy(),
            std::process::id()
        ));
        std::fs::create_dir_all(&directory).expect("a directory");
        for file in ["M.tla", "M.cfg"] {
            std::fs::copy(case.join(file), directory.join(file)).expect("the spec");
        }
        let expected = std::fs::read_to_string(case.join("tlc.out")).expect("TLC's output");
        for workers in ["1", "4"] {
            let output = run(&directory, &["-noGenerateSpecTE", "-workers", workers, "M"]);
            let text = get_untimed(&stdout(&output));
            if text != expected {
                differences.push(format!(
                    "{} on {workers}:\n{text}{}",
                    name.to_string_lossy(),
                    stderr(&output)
                ));
            }
        }
        std::fs::remove_dir_all(directory).expect("removed");
    }
    assert!(differences.is_empty(), "{}", differences.join("\n"));
}
