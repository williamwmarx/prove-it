//! The trace evaluator evaluates an operator's argument again at each use, where TLC keeps its value
//! (`LazyValue`). Each spec here is one that a trace evaluator keeping values got wrong, with TLC's
//! output, and the definitions it caches only where they are the same value in any states.

mod common;

use std::path::Path;

use common::{run, run_spec, stderr, stdout};

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

// Each spec in `trace-kept` is one that a version of the trace evaluator keeping an argument's value
// printed another message for than TLC, in a replay, ENABLED, UNCHANGED, a subscript or an
// assumption. Each prints what TLC prints (`tlc.out`, recorded from TLC at d8fb231), on one thread
// and on four.
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
            // On four workers TLC's others race a stop that leaves a state on the queue: the Jar
            // prints 5 states generated, 3 distinct and none left for `choose`, `direct`,
            // `filter`, `lambda`, `recursive` and `through3` in each of six runs and more, where
            // one worker prints 3, 3 and 1 left, and 9, 6 and none or 8, 5 and none for
            // `next-definition-lambda-of-x`, where one worker prints 7, 5 and 1. Those decline.
            let is_raced = workers == "4"
                && stderr(&output).ends_with("a stop several workers race to\n")
                && [
                    "choose",
                    "direct",
                    "filter",
                    "lambda",
                    "recursive",
                    "through3",
                    "next-definition-lambda-of-x",
                ]
                .contains(&&*name.to_string_lossy());
            if text != expected && !is_raced {
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

// TLC holds a recursive function, and a LET's function its LazyValue keeps, as one object whose
// body it evaluates only as it uses it (`FcnLambdaValue.apply`, `toFcnRcd` once, `getDomain` and
// `deepNormalize` not at all). The trace evaluator builds such a function at each use, so where its
// body or domain prints, an ALIAS printed the prints again or out of TLC's order, which main
// declines: each declines, on one thread and on four.
#[test]
fn declines_the_effects_of_a_function_tlc_keeps_lazy() {
    let header = "---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == x = 0 /\\ x' = 1\n";
    let recursive = "LET RECURSIVE F, G, H, R\n  F[n \\in 1..1] == IF n = 0 THEN F[n] ELSE Print(\"F\", 1)\n  G[n \\in 1..1] == IF n = 0 THEN G[n] ELSE Print(\"G\", 2)\n  H[n \\in 1..1] == IF n = 0 THEN H[n] ELSE Print(\"H\", 3)\n  R[k \\in {F, G}] == IF x = 99 THEN R[k] ELSE 0\nIN ";
    let cases = [
        (
            "except-function",
            format!("{recursive}PrintT([R EXCEPT ![F] = H])"),
            "effects in the body of a function TLC keeps lazy",
        ),
        (
            "except-set",
            format!("{recursive}PrintT([R EXCEPT ![F] = {{H, G}}])"),
            "effects in the body of a function TLC keeps lazy",
        ),
        (
            "built-twice",
            "LET F[n \\in 1..2] == Print(n, n) IN IF x = 99 THEN 0 ELSE (F = F)".to_string(),
            "a function a LET defines, used again",
        ),
        (
            "built-then-applied",
            "LET F[n \\in 1..2] == Print(n, n) IN IF x = 99 THEN 0 ELSE <<F, F[1]>>".to_string(),
            "a function a LET defines, used again",
        ),
        // `CombineFcn` forces the lazy left operand after the right one printed.
        (
            "merge-printed-right",
            "IF x = 99 THEN 0 ELSE ([s \\in SUBSET {1} |-> Print(<<\"L\", s>>, 0)] @@ Print(\"X\", <<>>))"
                .to_string(),
            "effects in the body of a function TLC keeps lazy",
        ),
        (
            "merge-merged-right",
            "IF x = 99 THEN 0 ELSE ([s \\in SUBSET {1} |-> Print(<<\"L\", s>>, 0)] @@ ([t \\in SUBSET {2} |-> Print(\"R\", t)] @@ <<>>))"
                .to_string(),
            "effects in the body of a function TLC keeps lazy",
        ),
        (
            "domain-applied-twice",
            "LET F[n \\in {1, Print(\"D\", 2)}] == n IN IF x = 99 THEN 0 ELSE <<F[1], F[1]>>"
                .to_string(),
            "a function a LET defines, used again",
        ),
    ];
    let mut differences = Vec::new();
    for (name, probe, reason) in cases {
        let directory = std::env::temp_dir().join(format!(
            "prove-it-cli-lazy-effects-{name}-{}",
            std::process::id()
        ));
        std::fs::create_dir_all(&directory).expect("a directory");
        std::fs::write(
            directory.join("M.tla"),
            format!("{header}Probe == {probe}\nAlias == [x |-> x, p |-> Probe]\n====\n"),
        )
        .expect("a spec");
        std::fs::write(
            directory.join("M.cfg"),
            "INIT Init\nNEXT Next\nALIAS Alias\n",
        )
        .expect("a configuration");
        for workers in ["1", "4"] {
            let output = run(&directory, &["-noGenerateSpecTE", "-workers", workers, "M"]);
            let error = stderr(&output);
            if output.status.code() != Some(1)
                || !error.starts_with("prove-it: not native yet: rebuilding a trace: ")
                || !error.contains(reason)
            {
                differences.push(format!("{name} on {workers}:\n{}{error}", stdout(&output)));
            }
        }
        std::fs::remove_dir_all(directory).expect("removed");
    }
    assert!(differences.is_empty(), "{}", differences.join("\n"));
}
