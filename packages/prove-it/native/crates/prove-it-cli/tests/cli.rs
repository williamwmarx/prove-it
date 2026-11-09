//! Runs the binary as a user would, on TCommit's engine IR as a recorded front.

use std::path::PathBuf;
use std::process::{Command, Output};

const COMMIT_IR: &[u8] = include_bytes!(
    "../../../../tests/conformance/ir/examples/specifications/transaction_commit/TCommit.ir"
);

fn run(directory: &PathBuf, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .args(args)
        .current_dir(directory)
        .env("PROVE_IT_FRONT", directory)
        .output()
        .expect("the binary runs")
}

fn commit_directory(name: &str) -> PathBuf {
    commit_directory_with(name, COMMIT_IR)
}

fn commit_directory_with(name: &str, ir: &[u8]) -> PathBuf {
    let directory =
        std::env::temp_dir().join(format!("prove-it-cli-{name}-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    for (file, contents) in [
        ("TCommit.tla", &b""[..]),
        ("TCommit.cfg", b""),
        ("TCommit.ir", ir),
        ("TCommit.front", b"Starting... (2026-11-09 00:00:00)\n"),
    ] {
        std::fs::write(directory.join(file), contents).expect("a file");
    }
    directory
}

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

#[test]
fn checks_commit_as_tlc_prints_it() {
    let directory = commit_directory("default");
    let output = run(&directory, &["-workers", "1", "-noTE", "TCommit"]);
    let text = stdout(&output);
    let lines: Vec<&str> = text.lines().collect();
    assert_eq!(output.status.code(), Some(0), "{text}");
    assert!(lines[0].starts_with("TLC2 Version "));
    assert!(lines[1].starts_with(
        "Running breadth-first search Model-Checking with fp 0 and seed 0 with 1 worker on "
    ));
    assert_eq!(lines[2], "Starting... (2026-11-09 00:00:00)");
    assert_eq!(lines[3], "Computing initial states...");
    assert!(
        lines[4].starts_with("Finished computing initial states: 1 distinct state generated at ")
    );
    assert_eq!(
        lines[5..lines.len() - 1].join("\n"),
        "Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states
  because two distinct states had the same fingerprint:
  calculated (optimistic):  val = 1.1E-16
94 states generated, 34 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 7.
The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 6 and the 95th percentile is 4)."
    );
    assert!(lines[lines.len() - 1].starts_with("Finished in 00s at ("));
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn marks_messages_with_tool() {
    let directory = commit_directory("tool");
    let output = run(&directory, &["-tool", "-seed", "+12", "TCommit.tla"]);
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(0), "{text}");
    assert!(text.starts_with("@!@!@STARTMSG 2262:0 @!@!@\nTLC2 Version "));
    assert!(text.contains("and seed 12 with 1 worker"));
    assert!(text.contains(
        "@!@!@STARTMSG 2199:0 @!@!@\n94 states generated, 34 distinct states found, 0 states left on queue.\n@!@!@ENDMSG 2199 @!@!@\n"
    ));
    assert!(text.contains("@!@!@STARTMSG 2200:0 @!@!@\nProgress(7) at "));
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn reports_what_tlc_reports_before_the_search() {
    let directory = commit_directory("errors");
    let seed = run(&directory, &["-seed", "x", "TCommit"]);
    assert_eq!(seed.status.code(), Some(1));
    assert!(stdout(&seed).ends_with(
        "Error: Error: An integer for seed required. But encountered x\nUsage: java tlc2.TLC [-help] [-option] inputfile\n"
    ));
    let config = run(&directory, &["Missing.tla"]);
    assert_eq!(config.status.code(), Some(151));
    assert!(stdout(&config).ends_with(
        "Error: TLC encountered the following error when trying to read the configuration file Missing.cfg:\nFile not found.\n"
    ));
    let usage = run(&directory, &[]);
    assert_eq!(usage.status.code(), Some(1));
    assert!(String::from_utf8_lossy(&usage.stderr).starts_with("Usage: tla-ts "));
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn prints_a_deadlock_unless_deadlock_turns_it_off() {
    // TCommit's configuration turns deadlock checking off; with it on, its final states deadlock.
    let mut ir = tla_ir::decode(COMMIT_IR).expect("an IR");
    ir.model.check_deadlock = true;
    let directory = commit_directory_with("deadlock", &tla_ir::encode(&ir));
    let checked = run(&directory, &["TCommit"]);
    let text = stdout(&checked);
    assert_eq!(checked.status.code(), Some(11), "{text}");
    assert!(
        text.contains(concat!(
            "Error: Deadlock reached.\n",
            "Error: The behavior up to this point is:\n",
            "State 1: <Initial predicate>\n",
            "rmState = (r1 :> \"working\" @@ r2 :> \"working\" @@ r3 :> \"working\")\n\n",
            "State 2: <Decide(r1) line 37, col 19 to line 39, col 66 of module TCommit>\n",
            "rmState = (r1 :> \"aborted\" @@ r2 :> \"working\" @@ r3 :> \"working\")\n\n",
            "State 3: <Decide(r2) line 37, col 19 to line 39, col 66 of module TCommit>\n",
            "rmState = (r1 :> \"aborted\" @@ r2 :> \"aborted\" @@ r3 :> \"working\")\n\n",
            "State 4: <Decide(r3) line 37, col 19 to line 39, col 66 of module TCommit>\n",
            "rmState = (r1 :> \"aborted\" @@ r2 :> \"aborted\" @@ r3 :> \"aborted\")\n\n",
            "85 states generated, 30 distinct states found, 3 states left on queue.\n",
            "The depth of the complete state graph search is 5.\n",
            "Finished in ",
        )),
        "{text}"
    );
    let tool = run(&directory, &["-tool", "TCommit"]);
    let text = stdout(&tool);
    assert_eq!(tool.status.code(), Some(11), "{text}");
    assert!(text.contains(concat!(
        "@!@!@STARTMSG 2114:1 @!@!@\nDeadlock reached.\n@!@!@ENDMSG 2114 @!@!@\n",
        "@!@!@STARTMSG 2121:1 @!@!@\nThe behavior up to this point is:\n@!@!@ENDMSG 2121 @!@!@\n",
        "@!@!@STARTMSG 2217:4 @!@!@\n1: <Initial predicate>\n",
    )), "{text}");
    let unchecked = run(&directory, &["-deadlock", "TCommit"]);
    assert_eq!(unchecked.status.code(), Some(0));
    assert!(stdout(&unchecked).contains("94 states generated, 34 distinct states found"));
    std::fs::remove_dir_all(directory).expect("removed");
}

// Runs the binary on a golden model's IR as the recorded front of a spec of that name, with no
// output before the search and the given configuration, in a directory of the test's own.
fn run_golden(test: &str, ir: &[u8], name: &str, config: &str, args: &[&str]) -> (Output, PathBuf) {
    let directory =
        std::env::temp_dir().join(format!("prove-it-cli-{test}-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    for (extension, contents) in [
        ("tla", &b""[..]),
        ("cfg", config.as_bytes()),
        ("ir", ir),
        ("front", b""),
    ] {
        std::fs::write(directory.join(format!("{name}.{extension}")), contents).expect("a file");
    }
    let mut all = args.to_vec();
    all.push(name);
    (run(&directory, &all), directory)
}

const TEST57_IR: &[u8] = include_bytes!(
    "../../../../tests/conformance/ir/tlc/tlatools/org.lamport.tlatools/test-model/suite/test57.ir"
);

#[test]
fn prints_an_invariant_an_initial_state_violates() {
    let (output, directory) = run_golden("initial", TEST57_IR, "test57", "", &[]);
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(12), "{text}");
    // A state of one variable isn't a conjunction, and TLC prints no statistics.
    assert!(text.contains(
        "Computing initial states...\nError: Invariant Invariant1 is violated by the initial state:\nx = 1\n\nFinished in "
    ), "{text}");
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn marks_the_initial_violation_with_tool() {
    let (output, directory) = run_golden("initial-tool", TEST57_IR, "test57", "", &["-tool"]);
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(12), "{text}");
    assert!(text.contains(
        "@!@!@STARTMSG 2107:1 @!@!@\nInvariant Invariant1 is violated by the initial state:\nx = 1\n\n@!@!@ENDMSG 2107 @!@!@\n"
    ), "{text}");
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn prints_a_state_through_the_alias() {
    let ir = include_bytes!(
        "../../../../tests/conformance/ir/tlc/tlatools/org.lamport.tlatools/test-model/Github746.ir"
    );
    let (output, directory) = run_golden(
        "alias",
        ir,
        "Github746",
        "SPECIFICATION Spec\nINVARIANT Inv\nALIAS Alias\n",
        &[],
    );
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(12), "{text}");
    // TLC prints the record the alias gives in place of the state's variables.
    assert!(
        text.contains(
            "Error: Invariant Inv is violated by the initial state:\n/\\ i = 1\n/\\ foo = \"bar\"\n/\\ j = TRUE\n"
        ),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn checks_temporal_properties_that_hold() {
    let ir = include_bytes!(
        "../../../../tests/conformance/ir/examples/specifications/glowingRaccoon/stages.ir"
    );
    let config = "CONSTANTS\n  DNA = 5\n  PRIMER = 5\nINVARIANT TypeOK\nSPECIFICATION Spec\nPROPERTIES cleanSpec primerDepleted\nCHECK_DEADLOCK FALSE\n";
    let (output, directory) = run_golden("liveness", ir, "stages", config, &[]);
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(0), "{text}");
    // TLC reports how far the search got, without rates, before it checks the complete graph.
    assert!(text.contains(": 93 states generated, 83 distinct states found, 0 states left on queue.\nChecking temporal properties for the complete state space with 83 total distinct states at ("), "{text}");
    assert!(
        text.contains("Finished checking temporal properties in 00s at "),
        "{text}"
    );
    assert!(
        text.contains("\nModel checking completed. No error has been found."),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn prints_a_violation_the_behavior_graphs_dont_stop_before() {
    // TLC adds each state to the behavior graphs as it searches, and would stop first at a tableau
    // node that accepts every behavior; none does here, so it reports the invariant.
    let ir = include_bytes!(
        "../../../../tests/conformance/ir/examples/specifications/acp/ACP_NB_WRONG_TLC.ir"
    );
    let config = "CONSTANTS\n  participants = { p0, p1 }\n  waiting = waiting\n  notsent = notsent\n  undecided = undecided\n  commit = commit\n  abort = abort\n  yes = yes\n  timeout = timeout\n  no = no\nSPECIFICATION SpecNB\nPROPERTIES AC1\nCHECK_DEADLOCK FALSE\n";
    let (output, directory) = run_golden("graph-invariant", ir, "ACP_NB_WRONG_TLC", config, &[]);
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(12), "{text}");
    assert!(
        text.contains("Error: Invariant AC1 is violated.\n"),
        "{text}"
    );
    assert!(
        text.contains("59286 states generated, 11852 distinct states found, 1248 states left on queue.\nThe depth of the complete state graph search is 13.\n"),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn prints_a_node_that_accepts_every_behavior() {
    let ir = include_bytes!(
        "../../../../tests/conformance/ir/tlc/tlatools/org.lamport.tlatools/test-model/Github1389Counting.ir"
    );
    // TLC's configuration but its POSTCONDITION, which TLC doesn't reach.
    let config = "SPECIFICATION Spec\nCHECK_DEADLOCK FALSE\nPROPERTIES CountAtMostFour\n";
    let (output, directory) = run_golden("accepted", ir, "Github1389Counting", config, &[]);
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(12), "{text}");
    // TLC stops as it adds the second state, and prints the path to the node through the
    // behavior graph, which passes through each state many times, with the counts by then.
    let label = "Next line 24, col 9 to line 24, col 22 of module Github1389Counting";
    let mut trace = String::from("State 1: <Initial predicate>\nx = FALSE\n\n");
    for position in 2..=10 {
        let value = if position % 2 == 0 { "TRUE" } else { "FALSE" };
        trace.push_str(&format!("State {position}: <{label}>\nx = {value}\n\n"));
    }
    assert!(
        text.contains(&format!(
            "Error: Temporal property CountAtMostFour was violated.\n\nError: The following behavior constitutes a counter-example:\n\n{trace}5 states generated, 2 distinct states found, 0 states left on queue.\nThe depth of the complete state graph search is 2.\n"
        )),
        "{text}"
    );
    assert!(!text.contains("Checking temporal properties"), "{text}");
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn prints_a_lasso_it_rebuilds_under_a_view() {
    let ir = include_bytes!(
        "../../../../tests/conformance/ir/tlc/tlatools/org.lamport.tlatools/test-model/examples/FiniteMonotonic/MCDistributedReplicatedLog.ir"
    );
    let config = "SPECIFICATION Spec\nCONSTANTS\n    Servers = {n1, n2, n3}\n    Values = {v}\n    Lag = 3\nINVARIANTS TypeOK BoundedLag\nPROPERTIES AllExtending InSync\nVIEW DropCommonPrefix\nCHECK_DEADLOCK TRUE\n";
    let (output, directory) =
        run_golden("view-lasso", ir, "MCDistributedReplicatedLog", config, &[]);
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(13), "{text}");
    // TLC rebuilds the lasso from the states it stored, the step back into the cycle with it,
    // and names the one of the two properties the rebuilt lasso violates.
    let module = "of module DistributedReplicatedLog";
    let extend = format!("Extend(n2) line 35, col 5 to line 38, col 49 {module}");
    let copy = |server: &str| format!("Copy({server}) line 26, col 9 to line 32, col 96 {module}");
    let lasso = format!(
        "Error: Temporal property InSync was violated.\n\nError: The following behavior constitutes a counter-example:\n\nState 1: <Initial predicate>\ncLogs = (n1 :> <<>> @@ n2 :> <<>> @@ n3 :> <<>>)\n\nState 2: <{extend}>\ncLogs = (n1 :> <<>> @@ n2 :> <<v, v, v>> @@ n3 :> <<>>)\n\nState 3: <{}>\ncLogs = (n1 :> <<>> @@ n2 :> <<v, v, v>> @@ n3 :> <<v, v, v>>)\n\nState 4: <{}>\ncLogs = (n1 :> <<v, v>> @@ n2 :> <<v, v, v>> @@ n3 :> <<v, v, v>>)\n\nState 5: <{extend}>\ncLogs = (n1 :> <<v, v>> @@ n2 :> <<v, v, v, v, v>> @@ n3 :> <<v, v, v>>)\n\nState 6: <{}>\ncLogs = (n1 :> <<v, v, v>> @@ n2 :> <<v, v, v, v, v>> @@ n3 :> <<v, v, v>>)\n\nBack to state 2: <{extend}>\n\nFinished checking temporal properties in ",
        copy("n3"),
        copy("n1"),
        copy("n1")
    );
    assert!(text.contains(&lasso), "{text}");
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn warns_of_a_stuttering_counterexample_without_fairness() {
    // No recorded IR, so tla-front lowers the model, and TLC prints its warnings.
    let directory =
        std::env::temp_dir().join(format!("prove-it-cli-stuttering-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    for (file, contents) in [
        (
            "Stutter.tla",
            "---- MODULE Stutter ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x' = 1 - x\nSpec == Init /\\ [][Next]_x\nLive == []<>(x = 1)\n====\n",
        ),
        ("Stutter.cfg", "SPECIFICATION Spec\nPROPERTY Live\n"),
        ("Stutter.front", ""),
    ] {
        std::fs::write(directory.join(file), contents).expect("a file");
    }
    let output = run(&directory, &["Stutter"]);
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(13), "{text}");
    assert!(
        text.contains("State 2: Stuttering\nWarning: The stuttering counterexample above may be caused by the absence of a fairness constraint in the behavior specification Spec defined at line 6, col 1 to line 6, col 26 of module Stutter. To rule out such counterexamples, conjoin a suitable fairness constraint to Spec (compare Chapter 8, page 87ff of Specifying Systems at https://lamport.azurewebsites.net/tla/book.html).\n"),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn overflows_translating_a_temporal_operator_that_recurses_forever() {
    // TLC's Github1389StateGuard: the guard reads x, so the translation of op(x) never ends,
    // and TLC overflows its stack before it computes the initial states.
    let directory =
        std::env::temp_dir().join(format!("prove-it-cli-recursion-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    for (file, contents) in [
        (
            "Guard.tla",
            "---- MODULE Guard ----\nEXTENDS Naturals\nVARIABLE x\nRECURSIVE op(_)\nop(n) == IF n = 0 THEN <>(x = 0) ELSE op(n - 1)\nInit == x = 0\nNext == x' \\in 0..3\nSpec == Init /\\ [][Next]_x\nProp == op(x)\n====\n",
        ),
        (
            "Guard.cfg",
            "SPECIFICATION Spec\nCHECK_DEADLOCK FALSE\nPROPERTY Prop\n",
        ),
    ] {
        std::fs::write(directory.join(file), contents).expect("a file");
    }
    let output = run(&directory, &["Guard"]);
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(255), "{text}");
    assert!(
        text.contains("\nError: This was a Java StackOverflowError. It was probably the result\n"),
        "{text}"
    );
    assert!(!text.contains("Computing initial states"), "{text}");
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn prints_a_temporal_propertys_lasso() {
    let ir = include_bytes!(
        "../../../../tests/conformance/ir/tlc/tlatools/org.lamport.tlatools/test-model/Github1389ViolatedB.ir"
    );
    let config = "SPECIFICATION Spec\nCHECK_DEADLOCK FALSE\nPROPERTY PropViolated\n";
    let (output, directory) = run_golden("lasso", ir, "Github1389ViolatedB", config, &[]);
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(13), "{text}");
    // TLC names the property, prints the lasso's states and the step back into its cycle, and
    // then finishes checking the temporal properties.
    let label = "Next line 10, col 9 to line 10, col 18 of module Github1389ViolatedB";
    let lasso = format!(
        "Error: Temporal property PropViolated was violated.\n\nError: The following behavior constitutes a counter-example:\n\nState 1: <Initial predicate>\nx = 0\n\nState 2: <{label}>\nx = 1\n\nBack to state 1: <{label}>\n\nFinished checking temporal properties in "
    );
    assert!(text.contains(&lasso), "{text}");
    assert!(
        text.contains("3 states generated, 2 distinct states found, 0 states left on queue.\nThe depth of the complete state graph search is 2.\n"),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn checks_temporal_properties_part_way_through_the_search() {
    let ir = include_bytes!(
        "../../../../tests/conformance/ir/examples/specifications/glowingRaccoon/stages.ir"
    );
    let config = "CONSTANTS\n  DNA = 5\n  PRIMER = 5\nINVARIANT TypeOK\nSPECIFICATION Spec\nPROPERTIES cleanSpec primerDepleted\nCHECK_DEADLOCK FALSE\n";
    let (output, directory) = run_golden("periodic", ir, "stages", config, &["-lncheck", "final"]);
    assert_eq!(output.status.code(), Some(0));
    let current = "Checking temporal properties for the current state space with 10 total distinct states at (";
    // PROVE_IT_TEST_LIVE_CHECK_AT has the first check made after 10 states are expanded, which
    // -lncheck final leaves to the end.
    let periodic = Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .arg("stages")
        .current_dir(&directory)
        .env("PROVE_IT_FRONT", &directory)
        .env("PROVE_IT_TEST_LIVE_CHECK_AT", "10")
        .output()
        .expect("the binary runs");
    let text = stdout(&periodic);
    assert_eq!(periodic.status.code(), Some(0), "{text}");
    assert!(text.contains(current), "{text}");
    assert!(
        text.contains("Finished checking temporal properties in 00s at "),
        "{text}"
    );
    assert!(!stdout(&output).contains("current state space"));
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn lowers_a_model_without_a_recorded_ir() {
    let directory = std::env::temp_dir().join(format!("prove-it-cli-lower-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    let spec = "---- MODULE Count ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x < 3 /\\ x' = x + 1\n====\n";
    for (file, contents) in [
        ("Count.tla", spec),
        ("Count.cfg", "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n"),
        ("Count.front", ""),
    ] {
        std::fs::write(directory.join(file), contents).expect("a file");
    }
    let output = run(&directory, &["Count"]);
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(0), "{text}");
    assert!(
        text.contains("4 states generated, 4 distinct states found, 0 states left on queue."),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn reports_a_postcondition_that_is_false() {
    let directory = std::env::temp_dir().join(format!("prove-it-cli-post-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    let spec = "---- MODULE Post ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == x < 3 /\\ x' = x + 1\nEnough == TLCGet(\"stats\").distinct = 5\n====\n";
    for (file, contents) in [
        ("Post.tla", spec),
        (
            "Post.cfg",
            "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\nPOSTCONDITION Enough\n",
        ),
        ("Post.front", ""),
    ] {
        std::fs::write(directory.join(file), contents).expect("a file");
    }
    let output = run(&directory, &["Post"]);
    let text = stdout(&output);
    // TLC reports the postcondition, named with where its body is written, in place of the
    // success, and exits as for an assumption.
    assert_eq!(output.status.code(), Some(10), "{text}");
    assert!(
        text.contains("Error: Postcondition Enough at line 6, col 11 to line 6, col 38 of module Post is false.\n4 states generated, 4 distinct states found, 0 states left on queue.\n"),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

const EVALUATING_VALUE_IR: &[u8] = include_bytes!(
    "../../../../tests/conformance/ir/tlc/tlatools/org.lamport.tlatools/test-model/EvaluatingValueTest.ir"
);

#[test]
fn prints_an_invariant_that_fails_to_evaluate() {
    let (output, directory) = run_golden(
        "invariant-failure",
        EVALUATING_VALUE_IR,
        "EvaluatingValueTest",
        "",
        &[],
    );
    let text = stdout(&output);
    // TLC prints the trace to the state it failed on, no call stack, and the outdegree of the
    // state graph with the failing state counted.
    assert_eq!(output.status.code(), Some(76), "{text}");
    assert!(
        text.contains("Error: Evaluating invariant Inv failed.\nAttempted to check if the value:\nFALSE\nis an element of Nat.\nError: The behavior up to this point is:\nState 1: <Initial predicate>\nx = 1\n\nState 2: <A line 8, col 6 to line 8, col 15 of module EvaluatingValueTest>\nx = FALSE\n\n2 states generated, 2 distinct states found, 0 states left on queue.\nThe depth of the complete state graph search is 2.\nThe average outdegree of the complete state graph is 1 (minimum is 1, the maximum 1 and the 95th percentile is 1).\nFinished in "),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

const INIT_EVAL_EXCEPTION_IR: &[u8] = include_bytes!(
    "../../../../tests/conformance/ir/tlc/tlatools/org.lamport.tlatools/test-model/DoInitFunctor/DoInitFunctorEvalException.ir"
);

#[test]
fn prints_a_constraint_that_fails_on_an_initial_state() {
    let (output, directory) = run_golden(
        "initial-constraint",
        INIT_EVAL_EXCEPTION_IR,
        "DoInitFunctorEvalException",
        "",
        &[],
    );
    let text = stdout(&output);
    // TLC reports the state it was checking with the error, and the call stack of the initial
    // predicate that found it, which the constraint's evaluation leaves.
    assert_eq!(output.status.code(), Some(75), "{text}");
    assert!(
        text.contains("Computing initial states...\nError: TLC expected a boolean value, but did not find one. line 15, col 15 to line 15, col 18 of module DoInitFunctorEvalException\nWhile working on the initial state:\nx = 1\n\nError: The error occurred when TLC was evaluating the nested\nexpressions at the following positions:\n0. Line 7, column 9 to line 7, column 19 in DoInitFunctorEvalException\n\n\n1 states generated, 0 distinct states found, 0 states left on queue.\nThe depth of the complete state graph search is 1.\nFinished in "),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

const ETEST14_IR: &[u8] = include_bytes!(
    "../../../../tests/conformance/ir/tlc/tlatools/org.lamport.tlatools/test-model/suite/etest14.ir"
);

#[test]
fn prints_an_assumption_that_fails_to_evaluate() {
    for (args, expected) in [
        (
            &[][..],
            "Error: Evaluating assumption line 5, col 3 to line 5, col 56 of module etest14 failed.\nAttempted to compute the value of an expression of form\nCHOOSE x \\in S: P, but no element of S satisfied P.\nline 5, col 7 to line 5, col 28 of module etest14\nFinished in ",
        ),
        (
            &["-tool"][..],
            "@!@!@STARTMSG 2105:1 @!@!@\nEvaluating assumption line 5, col 3 to line 5, col 56 of module etest14 failed.\nAttempted to compute the value of an expression of form\nCHOOSE x \\in S: P, but no element of S satisfied P.\nline 5, col 7 to line 5, col 28 of module etest14\n@!@!@ENDMSG 2105 @!@!@\n@!@!@STARTMSG 2186:0 @!@!@\nFinished in ",
        ),
    ] {
        let (output, directory) = run_golden("assumption-failure", ETEST14_IR, "etest14", "", args);
        let text = stdout(&output);
        // TLC reports the assumption by where it is written, and no statistics.
        assert_eq!(output.status.code(), Some(10), "{text}");
        assert!(text.contains(expected), "{text}");
        std::fs::remove_dir_all(directory).expect("removed");
    }
}

const CDOT_IR: &[u8] = include_bytes!(
    "../../../../tests/conformance/ir/tlc/tlatools/org.lamport.tlatools/test-model/cdot/CdotWithContextA.ir"
);

#[test]
fn prints_action_composition_as_tlc_refuses_it() {
    let (output, directory) = run_golden("cdot", CDOT_IR, "CdotWithContextA", "", &[]);
    let text = stdout(&output);
    // TLC fails on \cdot unless a Java property enables it, as an exception it didn't expect in
    // the next states, with the call stack down to the composition.
    assert_eq!(output.status.code(), Some(75), "{text}");
    assert!(text.contains("Error: TLC threw an unexpected exception.\nThis was probably caused by an error in the spec or model.\nSee the User Output or TLC Console for clues to what happened.\nThe exception was a java.lang.RuntimeException\n: The current version of TLC does not support action composition.  An incomplete implementation can be enabled via the tlc2.tool.impl.Tool.cdot=true java property.\nError: The behavior up to this point is:\nState 1: <Initial predicate>\n/\\ S = {1, 2}\n/\\ x = 0\n\nError: The error occurred when TLC was evaluating the nested\nexpressions at the following positions:\n0. Line 19, column 9 to line 22, column 28 in CdotWithContextA\n1. Line 19, column 9 to line 19, column 16 in CdotWithContextA\n2. Line 19, column 12 to line 19, column 16 in CdotWithContextA\n3. Line 20, column 8 to line 22, column 28 in CdotWithContextA\n4. Line 21, column 11 to line 22, column 28 in CdotWithContextA\n5. Line 21, column 14 to line 21, column 20 in CdotWithContextA\n6. Line 22, column 14 to line 22, column 28 in CdotWithContextA\n\n\n1 states generated, 1 distinct states found, 0 states left on queue.\nThe depth of the complete state graph search is 1.\n"), "{text}");
    std::fs::remove_dir_all(directory).expect("removed");
}

const OPERATOR_TABLE_IR: &[u8] = include_bytes!(
    "../../../../tests/conformance/ir/tlc/tlatools/org.lamport.tlatools/test-model/ConstantOperatorConfiguration.ir"
);

#[test]
fn rebuilds_a_trace_through_an_operator_the_configuration_defines() {
    let (output, directory) = run_golden(
        "operator-table",
        OPERATOR_TABLE_IR,
        "ConstantOperatorConfiguration",
        "",
        &[],
    );
    let text = stdout(&output);
    // F(0) = 1, F(1) = 2 in the configuration take x from 0 to 2, which Inv forbids.
    assert_eq!(output.status.code(), Some(12), "{text}");
    assert!(text.contains("Error: Invariant Inv is violated.\nError: The behavior up to this point is:\nState 1: <Initial predicate>\nx = 0\n\nState 2: <Next line 7, col 9 to line 7, col 17 of module ConstantOperatorConfiguration>\nx = 1\n\nState 3: <Next line 7, col 9 to line 7, col 17 of module ConstantOperatorConfiguration>\nx = 2\n\n3 states generated, 3 distinct states found, 0 states left on queue.\nThe depth of the complete state graph search is 3.\n"), "{text}");
    std::fs::remove_dir_all(directory).expect("removed");
}

// Runs the binary on a spec of the test's own, with no recorded front.
fn run_unrecorded(test: &str, spec: &str, config: &str) -> (Output, PathBuf) {
    let directory =
        std::env::temp_dir().join(format!("prove-it-cli-{test}-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    std::fs::write(directory.join("Stop.tla"), spec).expect("a spec");
    std::fs::write(directory.join("Stop.cfg"), config).expect("a configuration");
    (run(&directory, &["Stop"]), directory)
}

#[test]
fn reports_a_constant_the_configuration_leaves_unassigned() {
    let spec =
        "---- MODULE Stop ----\nCONSTANT N\nVARIABLE x\nInit == x = N\nNext == x' = x\n====\n";
    let (output, directory) = run_unrecorded("unassigned", spec, "INIT Init\nNEXT Next\n");
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(151), "{text}");
    assert!(
        text.contains("Linting of module Stop\nStarting... ("),
        "{text}"
    );
    assert!(
        text.contains(")\nError: The constant parameter N is not assigned a value by the configuration file.\nFinished in "),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn reports_a_spec_sany_rejects() {
    let spec = "---- MODULE Stop ----\nVARIABLE x\nInit == x =\n====\n";
    let (output, directory) = run_unrecorded("rejected", spec, "INIT Init\n");
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(150), "{text}");
    assert!(
        text.contains(")\nError: Parsing or semantic analysis failed.\nFinished in "),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

// Runs the binary on a spec of the test's own, which tla-front lowers, as TLC prints nothing
// before the search for it.
fn run_lowered(test: &str, spec: &str, config: &str) -> (Output, PathBuf) {
    let directory =
        std::env::temp_dir().join(format!("prove-it-cli-{test}-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    std::fs::write(directory.join("Stop.front"), "").expect("a front");
    run_unrecorded(test, spec, config)
}

#[test]
fn reads_and_sets_tlcs_registers() {
    // TLCCache evaluates Counted once, TLCFP is TLC's fingerprint under -fp 0, which the
    // interpreter and TLC print the same, and a Java property TLC hasn't set is its key.
    let spec = "---- MODULE Stop ----\nEXTENDS Integers, TLC, TLCExt\nVARIABLE x\nASSUME TLCSet(1, 0)\nCounted(v) == CASE TLCSet(1, TLCGet(1) + 1) -> v\nCached == TLCCache(Counted(7), {1})\nInit == x = 0 /\\ TLCSet(\"s:steps\", 0)\nNext == x < 3 /\\ x' = x + 1 /\\ Cached = 7 /\\ TLCSet(\"s:steps\", TLCGet(\"s:steps\") + 1)\nCounts == PrintT(<<TLCGet(1), TLCGet(\"s:steps\"), TLCGet(\"all\"), TLCGet(\"all:named\")>>)\nFingerprints == TLCFP(1) = -1504394061 /\\ TLCFP(\"a\") = -1022804895 /\\ TLCGet(\"-Dfoo\") = \"-Dfoo\"\n====\n";
    let (output, directory) = run_lowered(
        "registers",
        spec,
        "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\nINVARIANT Fingerprints\nPOSTCONDITION Counts\n",
    );
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(0), "{text}");
    assert!(
        text.contains(".\n<<1, 3, <<<<1>>>>, (\"s:steps\" :> <<3>>)>>\nModel checking completed."),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn rebuilds_a_trace_that_sets_registers() {
    // TLC rebuilds the trace from the initial predicate, which sets the register again (as on
    // TLC's TLCGetNonDeterminism).
    let spec = "---- MODULE Stop ----\nEXTENDS Integers, TLC\nVARIABLES x, y\nInit == TLCSet(1, 0) /\\ x = 0 /\\ y = TLCGet(1)\nNext == x < 2 /\\ TLCSet(1, TLCGet(1) + 1) /\\ x' = x + 1 /\\ y' = TLCGet(1)\n====\n";
    let (output, directory) = run_lowered("rebuilt", spec, "INIT Init\nNEXT Next\n");
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(11), "{text}");
    assert!(
        text.contains("State 2: <Next line 5, col 9 to line 5, col 73 of module Stop>\n/\\ x = 1\n/\\ y = 1\n\nState 3: <Next line 5, col 9 to line 5, col 73 of module Stop>\n/\\ x = 2\n/\\ y = 2\n\n"),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn reports_an_initial_state_tlc_fails_to_print() {
    // TLC's Github696b: TLC keeps the set as written, then fails to compare its model values as it
    // fingerprints the state and again as it prints it.
    let spec = "---- MODULE Stop ----\nEXTENDS Integers, TLCExt\nVARIABLE v\nInit == v = {TLCModelValue(\"A_a\"), TLCModelValue(\"B_a\")}\nNext == UNCHANGED v\nInv == TLCModelValue(\"B_a\") \\in v\n====\n";
    let directory =
        std::env::temp_dir().join(format!("prove-it-cli-unprintable-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    for (extension, contents) in [
        ("tla", spec),
        ("cfg", "INIT Init\nNEXT Next\nINVARIANT Inv\n"),
        ("front", ""),
    ] {
        std::fs::write(directory.join(format!("Stop.{extension}")), contents).expect("a file");
    }
    let output = run(&directory, &["Stop"]);
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(255), "{text}");
    assert!(
        text.contains("Computing initial states...\nError: TLC threw an unexpected exception.\nThis was probably caused by an error in the spec or model.\nSee the User Output or TLC Console for clues to what happened.\nThe exception was a java.lang.RuntimeException\n: Attempted to compare the differently-typed model values B_a and A_a\nFinished in "),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

const ETCDRAFT_IR: &[u8] =
    include_bytes!("../../../../tests/conformance/ir/etcd-raft/tla/etcdraft.ir");

#[test]
fn rebuilds_a_trace_of_bags_as_tlc_builds_them() {
    let (output, directory) = run_golden("bags", ETCDRAFT_IR, "etcdraft", "", &[]);
    let text = stdout(&output);
    // The messages are bags, which (+) and (-) build and SetToBag starts, and applying the empty
    // bag fails as applying TLC's empty function does.
    assert_eq!(output.status.code(), Some(75), "{text}");
    assert!(
        text.contains(include_str!("etcdraft-failure.txt")),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn prints_what_the_expansion_printed_before_its_violation() {
    // TLC checks each successor as it finds it, so it prints what finding the violating one
    // printed before it reports the violation, as TLC 1.8 prints this spec's 1.
    let spec = "---- MODULE Stop ----\nEXTENDS Integers, TLC\nVARIABLE x\nInit == x = 0\nNext == x' \\in {x + 1, x + 2} /\\ PrintT(x')\nInv == x # 1\n====\n";
    let (output, directory) = run_lowered("printed", spec, "INIT Init\nNEXT Next\nINVARIANT Inv\n");
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(12), "{text}");
    assert!(
        text.contains(".\n1\nError: Invariant Inv is violated.\n"),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

const SCHEDULING_ALLOCATOR_IR: &[u8] = include_bytes!(
    "../../../../tests/conformance/ir/tlc/tlatools/org.lamport.tlatools/test-model/examples/allocator/SchedulingAllocator.ir"
);

#[test]
fn rebuilds_a_trace_through_a_recursive_function_tlc_keeps_lazy() {
    let (output, directory) = run_golden(
        "recursive-function",
        SCHEDULING_ALLOCATOR_IR,
        "SchedulingAllocator",
        "",
        &[],
    );
    let text = stdout(&output);
    // The schedule's permutations come from the recursive LET function perms over SUBSET S,
    // which TLC applies to an argument without building it.
    assert_eq!(output.status.code(), Some(13), "{text}");
    assert!(
        text.contains(include_str!("scheduling-allocator.txt")),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn prints_a_deadlock_then_the_property_the_deadlocked_state_violates() {
    let ir = include_bytes!(
        "../../../../tests/conformance/ir/tlc/tlatools/org.lamport.tlatools/test-model/Github710d.ir"
    );
    let config = "SPECIFICATION Spec\nPROPERTY NeverThree\nPROPERTY Tautology\n";
    let (output, directory) = run_golden("deadlock-accepted", ir, "Github710d", config, &[]);
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(11), "{text}");
    // TLC adds the deadlocked state to the behavior graphs after it reports the deadlock, and
    // reports the node that accepts every behavior it reaches there.
    let label = "Step line 7, col 9 to line 7, col 27 of module Github710d";
    let mut trace = String::from("State 1: <Initial predicate>\nx = 0\n\n");
    for position in 2..=4 {
        trace.push_str(&format!(
            "State {position}: <{label}>\nx = {}\n\n",
            position - 1
        ));
    }
    assert!(
        text.contains(&format!(
            "Error: Deadlock reached.\nError: The behavior up to this point is:\n{trace}Error: Temporal property NeverThree was violated.\n\nError: The following behavior constitutes a counter-example:\n\n{trace}4 states generated, 4 distinct states found, 0 states left on queue.\n"
        )),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

const PULL_RAFT_IR: &[u8] =
    include_bytes!("../../../../tests/conformance/ir/raft/specifications/pull-raft/PullRaft.ir");

#[test]
fn rebuilds_a_trace_under_symmetry_through_sets_tlc_streams_in_order() {
    let (output, directory) = run_golden("pull-raft", PULL_RAFT_IR, "PullRaft", "", &[]);
    let text = stdout(&output);
    // Under SYMMETRY, TLC takes the first of the successors in a state's orbit, in the order it
    // streams \E m \in DOMAIN messages, a variable's domain it normalized.
    assert_eq!(output.status.code(), Some(11), "{text}");
    assert!(text.contains(include_str!("pull-raft.txt")), "{text}");
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn checks_the_possible_counts_after_a_deadlock() {
    // TLC's PostConditionsTest: TLC checks the postconditions after the deadlock, with each
    // _POSSIBLE predicate's count as the search left it, so PossibleCounts holds.
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == x < 3 /\\ x' = x + 1\nSpec == Init /\\ [][Next]_x\nAtTwo == x = 2\nLastStep == x = 2 /\\ x' = 3\nPossibleCounts ==\n    LET p == TLCGet(\"all:named\")[\"s:_possible\"][1]\n    IN /\\ p[\"AtTwo\"] = 1\n       /\\ p[\"LastStep\"] = 1\n====\n";
    let directory =
        std::env::temp_dir().join(format!("prove-it-cli-possible-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    for (extension, contents) in [
        ("tla", spec),
        (
            "cfg",
            "SPECIFICATION Spec\nPOSTCONDITIONS PossibleCounts\n_POSSIBLE AtTwo LastStep\n",
        ),
        ("front", ""),
    ] {
        std::fs::write(directory.join(format!("Stop.{extension}")), contents).expect("a file");
    }
    let output = run(&directory, &["Stop"]);
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(11), "{text}");
    assert!(
        text.contains("x = 3\n\n4 states generated, 4 distinct states found, 0 states left on queue.\nThe depth of the complete state graph search is 4.\nFinished in "),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn reports_a_division_by_zero_after_what_the_expansion_printed() {
    let directory =
        std::env::temp_dir().join(format!("prove-it-cli-divide-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    let spec = "---- MODULE D ----\nEXTENDS Integers, TLC\nVARIABLE x\nInit == x = 1\nNext == /\\ PrintT(\"step\") /\\ x' = x \\div 0\n====\n";
    for (file, contents) in [
        ("D.tla", spec),
        ("D.cfg", "INIT Init\nNEXT Next\n"),
        ("D.front", ""),
    ] {
        std::fs::write(directory.join(file), contents).expect("a file");
    }
    let output = run(&directory, &["-workers", "1", "D"]);
    let text = stdout(&output);
    // As TLC prints it: the EvalException's message after the expansion's print, the trace, the
    // replay's print and the call stack.
    assert_eq!(output.status.code(), Some(75), "{text}");
    assert!(
        text.contains("\"step\"\nError: The second argument of \\div is 0.\nError: The behavior up to this point is:\nState 1: <Initial predicate>\nx = 1\n\n\"step\"\nError: The error occurred when TLC was evaluating the nested\nexpressions at the following positions:\n0. Line 5, column 9 to line 5, column 42 in D\n1. Line 5, column 12 to line 5, column 42 in D\n2. Line 5, column 12 to line 5, column 25 in D\n3. Line 5, column 30 to line 5, column 42 in D\n4. Line 5, column 35 to line 5, column 42 in D\n\n\n1 states generated, 1 distinct states found, 0 states left on queue.\n"),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

const LIVE_WRITE_THROUGH_CACHE_IR: &[u8] = include_bytes!(
    "../../../../tests/conformance/ir/tlc/tlatools/org.lamport.tlatools/test-model/examples/SpecifyingSystems/Liveness/MCLiveWriteThroughCache.ir"
);

#[test]
fn checks_a_postcondition_on_a_lasso_stuttering_at_its_initial_state() {
    let (output, directory) = run_golden(
        "stutter-postcondition",
        LIVE_WRITE_THROUGH_CACHE_IR,
        "MCLiveWriteThroughCache",
        "",
        &[],
    );
    let text = stdout(&output);
    // The postcondition is TLC's CounterExample, whose step back into the cycle TLC holds no
    // action for: Action.UNKNOWN, unnamed, at the TLA+ builtins' null location.
    assert_eq!(output.status.code(), Some(13), "{text}");
    assert!(text.contains("State 2: Stuttering\n"), "{text}");
    assert!(!text.contains("Postcondition"), "{text}");
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn rejects_a_constant_invariant_the_front_end_leaves_to_the_startup() {
    // tla-front's evaluator computes no records, so the engine evaluates Bad as TLC starts.
    let source = "---- MODULE Bad ----\nVARIABLE x\nInit == x = 0\nNext == x' = x\nBad == [a |-> 1].a = 2\n====\n";
    let config = "INIT Init\nNEXT Next\nINVARIANT Bad\n";
    let spec = std::env::temp_dir().join(format!("prove-it-cli-bad-{}.tla", std::process::id()));
    std::fs::write(&spec, source).expect("the spec");
    let options = tla_front::model::ModelOptions {
        libraries: &[],
        version: None,
        is_warning_enabled: true,
    };
    let ir = tla_front::model::lower_model(&spec, config, &options).expect("an IR");
    std::fs::remove_file(&spec).expect("removed");
    let (output, directory) = run_golden("constant-invariant", &ir, "Bad", config, &[]);
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(151), "{text}");
    assert!(
        text.contains("Error: The invariant of Bad is equal to FALSE\nFinished in "),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}
