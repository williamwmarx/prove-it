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

// Each output is what TLC at d8fb231 prints for the command line.
#[test]
fn reads_the_command_line_as_tlc() {
    let directory = commit_directory("command-line");
    let usage = "\nUsage: java tlc2.TLC [-help] [-option] inputfile\n";
    for (args, message) in [
        (&["-foo", "TCommit"][..], "unrecognized option: -foo"),
        (
            &["TCommit", "Other"],
            "more than one input files: TCommit and Other",
        ),
        (&["-nowarning"], "Missing input TLA+ module."),
        (
            &["-workers", "0", "TCommit"],
            "at least one worker required.",
        ),
        (
            &["TCommit", "-config"],
            "expect a file name for -config option.",
        ),
    ] {
        let output = run(&directory, &[&["tlc2.TLC"], args].concat());
        assert_eq!(output.status.code(), Some(1), "{args:?}");
        let text = stdout(&output);
        assert!(text.starts_with("TLC2 Version "), "{text}");
        assert!(
            text.ends_with(&format!("\nError: Error: {message}{usage}")),
            "{text}"
        );
    }
    let marked = run(&directory, &["tlc2.TLC", "-tool", "-fp", "131", "TCommit"]);
    assert!(stdout(&marked).ends_with(&format!(
        "@!@!@STARTMSG 1102:1 @!@!@\nError: The number for -fp must be between 0 and 130 (inclusive).{usage}@!@!@ENDMSG 1102 @!@!@\n"
    )));
    // TLC names the configuration file with or without its extension.
    let configured = run(&directory, &["tlc2.TLC", "-config", "TCommit", "TCommit"]);
    assert_eq!(configured.status.code(), Some(0), "{}", stdout(&configured));
    for (args, what) in [
        (&["-difftrace", "TCommit"][..], "the TLC option -difftrace"),
        (&["-simulate", "TCommit"], "the TLC option -simulate"),
        (&["-coverage", "1", "TCommit"], "the TLC option -coverage"),
        (&["-fp", "1", "TCommit"], "-fp 1"),
        (&["TCommit.cfg"], "a module named as a configuration file"),
    ] {
        let output = run(&directory, &[&["tlc2.TLC"], args].concat());
        assert_eq!(output.status.code(), Some(1), "{args:?}");
        assert_eq!(stdout(&output), "", "{args:?}");
        assert_eq!(
            String::from_utf8_lossy(&output.stderr),
            format!("prove-it: not native yet: {what}\n")
        );
    }
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

#[test]
fn prints_what_an_assumption_printed_before_it_failed_once() {
    let spec = "---- MODULE Printed ----\nEXTENDS TLC, Integers\nVARIABLE x\nASSUME PrintT(1)\nASSUME PrintT(3) /\\ PrintT(2) /\\ 1 \\div 0 = 1\nInit == x = 0\nNext == x' = x\n====\n";
    let expected = "\n1\n3\n2\nError: Evaluating assumption line 5, col 8 to line 5, col 45 of module Printed failed.\nThe second argument of \\div is 0.\nFinished in ";
    // tla-front as the whole front end, where the search prints the assumptions as it evaluates
    // them.
    let (output, directory) = run_front("printed-native", spec, "INIT Init\nNEXT Next\n", &[]);
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(10), "{text}");
    assert!(text.contains(expected), "{text}");
    std::fs::remove_dir_all(directory).expect("removed");
    // A recorded front, which holds what TLC printed before the error.
    let directory =
        std::env::temp_dir().join(format!("prove-it-cli-printed-front-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    for (extension, contents) in [
        ("tla", spec),
        ("cfg", "INIT Init\nNEXT Next\n"),
        ("front", "Starting... (2026-11-10 00:00:00)\n1\n3\n2\n"),
    ] {
        std::fs::write(directory.join(format!("Printed.{extension}")), contents).expect("a file");
    }
    let output = run(&directory, &["-noTE", "Printed"]);
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(10), "{text}");
    assert!(text.contains(&format!("00:00:00){expected}")), "{text}");
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn prints_once_what_an_assumption_printed_before_the_engine_left_it() {
    // The search prints the first print, then leaves the assumption to the trace evaluator, which
    // prints it again as it evaluates the assumption whole.
    let spec = "---- MODULE Left ----\nEXTENDS TLC, Naturals\nVARIABLE x\nASSUME PrintT(1)\nASSUME Print(SUBSET (1..10), TRUE) /\\ PrintT(ToString(SUBSET (1..10)))\nInit == x = 0\nNext == x' = x\n====\n";
    let (output, directory) = run_front("left", spec, "INIT Init\nNEXT Next\n", &[]);
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(0), "{text}");
    assert!(
        text.contains(
            ")\n1\nSUBSET (1..10)  TRUE\n\"SUBSET (1..10)\"\nComputing initial states...\n"
        ),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn words_failed_memberships_and_sequence_arguments_as_tlc() {
    for (assumption, error) in [
        (
            "m \\in Seq({1})",
            "Attempted to check if the typed model value A_b is an element of\nSeq({1})",
        ),
        (
            "1 \\in SUBSET Nat",
            "Attempted to check if the non-enumerable value\n1\nis element of\nSUBSET Nat",
        ),
        (
            "{1} \\in Seq(Nat)",
            "Attempted to check if the value:\n{1}\nis an element of Seq(Nat).",
        ),
        (
            "Len(Nat) = 1",
            "The argument of Len should be a sequence, but instead it is:\nNat",
        ),
        (
            "1 \\in <<1, 2>>",
            "Attempted to check set membership in a tuple value.",
        ),
        (
            "{1} \\subseteq 1",
            "Attempted to check if the value:\n1\nis an element of the integer 1",
        ),
        (
            "DOMAIN [a : Nat] = {}",
            "Attempted to apply the operator DOMAIN to a non-function\n(a set of the form [d1 : S1, ... , dN : SN])\nline 5, col 8 to line 5, col 23 of module Member",
        ),
        (
            "Seq(Nat)[1] = 1",
            "A non-function (a special set constant) was applied as a function.\nline 5, col 8 to line 5, col 18 of module Member",
        ),
    ] {
        let spec = format!(
            "---- MODULE Member ----\nEXTENDS Naturals, Sequences\nCONSTANT m\nVARIABLE x\nASSUME {assumption}\nInit == x = 0\nNext == x' = x\n====\n"
        );
        let (output, directory) = run_front(
            "member",
            &spec,
            "CONSTANT m = A_b\nINIT Init\nNEXT Next\n",
            &[],
        );
        let text = stdout(&output);
        assert_eq!(output.status.code(), Some(10), "{text}");
        assert!(
            text.contains(&format!("of module Member failed.\n{error}\n")),
            "{text}"
        );
        std::fs::remove_dir_all(directory).expect("removed");
    }
}

#[test]
fn fails_to_print_a_lazy_set_whose_expansion_fails() {
    // PrintT prints with `toStringUnchecked`, which fails where TLC can't expand a lazy set.
    for (set, error) in [
        (
            "Nat \\cup {-1}",
            "Attempted to enumerate S \\cup T when S:\n{-1}\nand T:\nNat\nare not both enumerable",
        ),
        (
            "UNION {Nat, {1}}",
            "Attempted to compare the set {1} with the value:\nNat",
        ),
        (
            "SUBSET Nat",
            "Attempted to compute the number of elements in the overridden value Nat.",
        ),
    ] {
        let spec = format!(
            "---- MODULE Lazy ----\nEXTENDS TLC, Integers\nVARIABLE x\nASSUME PrintT({set})\nInit == x = 0\nNext == x' = x\n====\n"
        );
        let (output, directory) = run_front("lazy-print", &spec, "INIT Init\nNEXT Next\n", &[]);
        let text = stdout(&output);
        assert_eq!(output.status.code(), Some(10), "{text}");
        assert!(
            text.contains(&format!("of module Lazy failed.\nAttempted to apply the operator overridden by the Java method\npublic static tlc2.value.impl.Value tlc2.module.TLC.PrintT(tlc2.value.impl.Value),\nbut it produced the following error:\n{error}\nFinished in ")),
            "{text}"
        );
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
fn stops_at_initial_states_without_a_next_state_relation() {
    // TLC reports 2115 with no statistics, and a model with no initial states either succeeds.
    let spec = "---- MODULE Stop ----\nVARIABLE x\nInit == x = 0\nNone == x \\in {}\n====\n";
    let (output, directory) = run_lowered("no-next", spec, "INIT Init\n");
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(75), "{text}");
    assert!(
        text.contains("Finished computing initial states: 1 distinct state generated at "),
        "{text}"
    );
    assert!(
        text.contains(".\nError: No next state actions defined to generate successor states from.\nFinished in "),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
    let (output, directory) = run_lowered("no-next-empty", spec, "INIT None\n");
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(0), "{text}");
    assert!(
        text.contains("0 states generated, 0 distinct states found, 0 states left on queue."),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn checks_properties_in_the_scope_of_their_instance() {
    // A property an INSTANCE with substitutions exports reads its names in the instance: the
    // invariant of `[]`, checked on the trace's last state again, and the implied init.
    let inner = "---- MODULE Abs ----\nEXTENDS Naturals\nVARIABLE s\nCONSTANT K\nSafe == [](s < K)\nStart == s = K /\\ [](s >= 0)\nSafe2 == Safe\n====\n";
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals\nVARIABLE t\nA == INSTANCE Abs WITH s <- t * 2, K <- 6\nInit == t = 0\nNext == t' = (t + 1) % 5\nSpec == Init /\\ [][Next]_t\nPStart == A!Start\nPSafe2 == A!Safe2\n====\n";
    let directory =
        std::env::temp_dir().join(format!("prove-it-cli-scoped-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    std::fs::write(directory.join("Abs.tla"), inner).expect("a module");
    let (output, _) = run_lowered("scoped", spec, "SPECIFICATION Spec\nPROPERTY PSafe2\n");
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(12), "{text}");
    assert!(
        text.contains(
            "Error: Invariant Safe is violated.\nError: The behavior up to this point is:\n"
        ),
        "{text}"
    );
    assert!(
        text.contains(
            "t = 3\n\n4 states generated, 4 distinct states found, 0 states left on queue.\n"
        ),
        "{text}"
    );
    let (output, _) = run_lowered("scoped", spec, "SPECIFICATION Spec\nPROPERTY PStart\n");
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(13), "{text}");
    assert!(
        text.contains("Error: Property line 6, col 10 to line 6, col 14 of module Abs is violated by the initial state:\nt = 0\n\nFinished in "),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn prints_what_the_atoms_print_naming_a_lassos_properties() {
    // TLC's UserModuleOverrideAnnotation: the atom prints as TLC adds the state to the behavior
    // graphs, and again as it evaluates the property on the lasso it found.
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = FALSE\nNext == x' = FALSE\nSpec == Init /\\ [][Next]_x\nProp == <>[](Print(x, x = TRUE) /\\ TLCGet(\"diameter\") > 0)\n====\n";
    let (output, directory) = run_lowered(
        "printing-lasso",
        spec,
        "SPECIFICATION Spec\nPROPERTY Prop\n",
    );
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(13), "{text}");
    assert!(text.contains(".\nFALSE  FALSE\nProgress(1) at "), "{text}");
    assert!(
        text.contains(")\nFALSE  FALSE\nError: Temporal property Prop was violated.\n\nError: The following behavior constitutes a counter-example:\n\nState 1: <Initial predicate>\nx = FALSE\n\nState 2: Stuttering\nWarning: "),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn reports_an_atom_that_fails_on_an_initial_state() {
    // TLC's InitialLivenessEvaluationError: TLC adds the initial state to the behavior graphs
    // before it reports the initial states or checks the invariant, and ENABLED of an action
    // that reads a primed variable it never assigns fails there.
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == (x = 0 /\\ x' = 1) \\/ UNCHANGED x\nSpec == Init /\\ [][Next]_x\nInv == x = 0\nProp == <>~ENABLED (x' > x)\n====\n";
    let (output, directory) = run_lowered(
        "initial-atom",
        spec,
        "SPECIFICATION Spec\nINVARIANT Inv\nPROPERTY Prop\n",
    );
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(151), "{text}");
    assert!(
        text.contains("Computing initial states...\nError: In evaluation, the identifier x is either undefined or not an operator.\nline 8, col 21 to line 8, col 21 of module Stop\nWhile working on the initial state:\nx = 0\n\n1 states generated, 1 distinct states found, 1 states left on queue.\nThe depth of the complete state graph search is 1.\nFinished in "),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn prints_a_lasso_a_check_part_way_through_the_search_finds() {
    // Without fairness x stutters, which a check after two states finds with a state left to
    // expand: TLC reports the check's start, the counterexample and the counts so far.
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x' = (x + 1) % 10\nUnfair == Init /\\ [][Next]_x\nReaches == <>(x = 9)\n====\n";
    let directory = std::env::temp_dir().join(format!(
        "prove-it-cli-periodic-lasso-{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&directory).expect("a directory");
    for (file, contents) in [
        ("Stop.tla", spec),
        ("Stop.cfg", "SPECIFICATION Unfair\nPROPERTY Reaches\n"),
        ("Stop.front", ""),
    ] {
        std::fs::write(directory.join(file), contents).expect("a file");
    }
    let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .arg("Stop")
        .current_dir(&directory)
        .env("PROVE_IT_FRONT", &directory)
        .env("PROVE_IT_TEST_LIVE_CHECK_AT", "2")
        .output()
        .expect("the binary runs");
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(13), "{text}");
    assert!(
        text.contains(".\nChecking temporal properties for the current state space with 2 total distinct states at ("),
        "{text}"
    );
    assert!(
        text.contains(")\nError: Temporal property Reaches was violated.\n\nError: The following behavior constitutes a counter-example:\n\nState 1: <Initial predicate>\nx = 0\n\nState 2: <Next line 5, col 9 to line 5, col 25 of module Stop>\nx = 1\n\nState 3: Stuttering\n"),
        "{text}"
    );
    assert!(
        text.contains("\n3 states generated, 3 distinct states found, 1 states left on queue.\nThe depth of the complete state graph search is 3.\n"),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn answers_atoms_that_use_registers_as_the_search_goes() {
    // TLC evaluates the temporal properties' atoms as it adds each state it expanded to the
    // behavior graphs (TLC's Test2 counts them): A mixes each step into register 1 each time TLC
    // evaluates it, in the search and in WF's ENABLED and action, Seen each time TLC checks the
    // property's predicate, and B reads register 1 into register 2, so the registers tell the
    // order of it all.
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals, TLC\nVARIABLES x, y\nASSUME TLCSet(1, 1) /\\ TLCSet(2, 1)\nMix(v) == TLCSet(1, (TLCGet(1) * 31 + v) % 1000003)\nInit == x \\in {0, 3} /\\ y = 0\nA == /\\ x' \\in {(x + 1) % 6, (x * 2) % 6, (x + 3) % 6}\n     /\\ y' = y\n     /\\ Mix(x + 7 * x')\nB == /\\ y' = 1 - y\n     /\\ x' = x\n     /\\ TLCSet(2, (TLCGet(2) * 17 + TLCGet(1) + x + y) % 1000003)\nNext == A \\/ B\nvars == <<x, y>>\nSpec == Init /\\ [][Next]_vars /\\ WF_vars(A) /\\ SF_y(B)\nSeen(p) == Mix(100 + x + 10 * y) /\\ p\nPropA == []<>Seen(y = 1)\nPropB == <>[]Seen(x < 6)\nPropL == <>[]Seen(x = 7)\nPost == PrintT(<<TLCGet(1), TLCGet(2)>>)\n====\n";
    for (property, registers) in [
        ("PropA", "<<575965, 353382>>"),
        ("PropB", "<<261017, 589225>>"),
    ] {
        let (output, directory) = run_lowered(
            "online",
            spec,
            &format!(
                "SPECIFICATION Spec\nPROPERTY {property}\nPOSTCONDITION Post\nCHECK_DEADLOCK FALSE\n"
            ),
        );
        let text = stdout(&output);
        assert_eq!(output.status.code(), Some(0), "{text}");
        assert!(
            text.contains("\nFinished checking temporal properties in 00s at "),
            "{text}"
        );
        assert!(
            text.contains(&format!(
                "\n{registers}\nModel checking completed. No error has been found.\n"
            )),
            "{text}"
        );
        std::fs::remove_dir_all(directory).expect("removed");
    }
    // TLC rebuilds a counterexample before it evaluates the properties on it, which the binary
    // doesn't follow where the atoms use the registers.
    let (output, directory) = run_lowered(
        "online",
        spec,
        "SPECIFICATION Spec\nPROPERTY PropL\nPOSTCONDITION Post\nCHECK_DEADLOCK FALSE\n",
    );
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("a counterexample where the atoms use TLC's registers"),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn reports_an_invariant_violated_before_atoms_the_tables_leave_unanswered() {
    // The shape of TLC's ACP_NB_WRONG_TLC and SDP_Attack_Spec: an invariant violated while the
    // tables of the atoms, answered where the search stopped, leave unanswered what the checker
    // asks of states not yet expanded. TLC evaluates those atoms without failing, so it reports
    // the invariant.
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals\nVARIABLES x, y\nvars == <<x, y>>\nP == {0, 1}\nInit == x = 0 /\\ y = [i \\in P |-> 0]\nA == x < 4 /\\ x' = x + 1 /\\ y' = y\nB(i, j) == x % 2 = 1 /\\ y[j] = 0 /\\ y' = [y EXCEPT ![i] = 1] /\\ x' = x\nC == x = 4 /\\ x' = 0 /\\ y' = y\nNext == A \\/ C \\/ \\E i, j \\in P : B(i, j)\nFair == /\\ \\A i \\in P : WF_vars(\\E j \\in P : B(i, j))\n        /\\ WF_vars(A \\/ C)\nSpec == Init /\\ [][Next]_vars /\\ Fair\nSafe == [] \\A i, j \\in P : y[i] = 0 \\/ y[j] = 0 \\/ x < 3\nLeads == \\A p \\in P : \\A q \\in P : (y[p] = 1) ~> (y[q] = 1)\n====\n";
    let (output, directory) = run_lowered(
        "unanswered-past-a-violation",
        spec,
        "SPECIFICATION Spec\nPROPERTIES\nSafe\nPROPERTY Leads\nCHECK_DEADLOCK FALSE\n",
    );
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(12), "{text}");
    assert!(
        text.contains("Error: Invariant Safe is violated.\nError: The behavior up to this point is:\nState 1: <Initial predicate>\n"),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn rebuilds_a_violations_trace_again_before_the_postconditions() {
    // TLC rebuilds the trace as it prints it and once more for the counterexample the
    // postconditions read, running Next again each time: Next prints and counts in a register
    // both times, before the postcondition reads the register.
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals, TLC\nVARIABLE x\nASSUME TLCSet(2, 0)\nInit == x = 0\nNext == x < 5 /\\ x' = x + 1 /\\ TLCSet(2, TLCGet(2) + 1) /\\ PrintT(<<\"n\", x, TLCGet(2)>>)\nInv == x < 3\nPost == PrintT(<<TLCGet(2)>>)\nShown == [x |-> x, r |-> TLCGet(2)]\n====\n";
    let (output, directory) = run_lowered(
        "rebuilt-twice",
        spec,
        "INIT Init\nNEXT Next\nINVARIANT Inv\nPOSTCONDITION Post\n",
    );
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(12), "{text}");
    assert!(
        text.contains("<<\"n\", 2, 3>>\nError: Invariant Inv is violated.\n<<\"n\", 0, 4>>\nError: The behavior up to this point is:\n"),
        "{text}"
    );
    assert!(
        text.contains("<<\"n\", 2, 6>>\nState 4: <Next line 6, col 9 to line 6, col 88 of module Stop>\nx = 3\n\n<<\"n\", 0, 7>>\n<<\"n\", 1, 8>>\n<<\"n\", 2, 9>>\n<<9>>\n4 states generated, 4 distinct states found, 0 states left on queue.\n"),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
    // TLC evaluates the ALIAS of each state as it prints it, part way through those rebuilds.
    let (output, directory) = run_lowered(
        "rebuilt-twice",
        spec,
        "INIT Init\nNEXT Next\nINVARIANT Inv\nALIAS Shown\n",
    );
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("an ALIAS that uses registers the rebuild of the trace sets"),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn reports_a_bound_tlc_cant_enumerate_in_the_initial_predicate() {
    // The shape of YoYoAllGraphs without the Java overrides: TLC fails computing the initial
    // states, quantifying over Seq(S) in the predicate of a filter it kept lazy until a
    // comparison enumerated it, after it found one state; the model has a temporal property.
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals, Sequences\nVARIABLES x, y\nLinked(S) == {T \\in SUBSET S : \\A m \\in T : \\E p \\in Seq(T) : p # <<>> /\\ p[1] = m}\nInit ==\n    /\\ x = 0\n    /\\ \\E T \\in SUBSET {1, 2} :\n          /\\ Linked(T) = {T}\n          /\\ y = T\nNext == x' = 1 - x /\\ y' = y\nSpec == Init /\\ [][Next]_<<x, y>> /\\ WF_x(Next)\nLive == []<>(x = 1)\n====\n";
    let (output, directory) = run_lowered("seq-bound", spec, "SPECIFICATION Spec\nPROPERTY Live\n");
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(75), "{text}");
    assert!(
        text.contains("Computing initial states...\nError: TLC encountered the non-enumerable quantifier bound\nSeq({1})\nline 4, col 54 to line 4, col 59 of module Stop\nIn TLA+, Seq(S) represents"),
        "{text}"
    );
    assert!(
        text.contains("expressions at the following positions:\n0. Line 6, column 5 to line 9, column 18 in Stop\n1. Line 6, column 8 to line 6, column 12 in Stop\n2. Line 7, column 8 to line 9, column 18 in Stop\n3. Line 8, column 11 to line 9, column 18 in Stop\n4. Line 8, column 14 to line 8, column 28 in Stop\n5. Line 4, column 32 to line 4, column 82 in Stop\n6. Line 4, column 45 to line 4, column 82 in Stop\n\n\n1 states generated, 1 distinct states found, 1 states left on queue.\nThe depth of the complete state graph search is 1.\n"),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn reports_a_constraint_that_fails_in_a_values_method_on_an_initial_state() {
    // The shape of ccf's TraceMultiNodeReads without the Java overrides: the constraint chooses
    // from [STRING -> STRING], which TLC can't enumerate. TLC reports the error with the initial
    // state, then its replay of the initial states ends in a FingerprintException whose call
    // stack holds the initial predicate's frames and the constraint's; the model has a
    // temporal property.
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals\nVARIABLE x\nEnv == CHOOSE r \\in [STRING -> STRING] : TRUE\nInit == x = 0\nNext == x' = (x + 1) % 3\nCon == x < 5 => \"A\" \\in DOMAIN Env\nLive == []<>(x = 1)\n====\n";
    let (output, directory) = run_lowered(
        "constraint-fingerprint",
        spec,
        "INIT Init\nNEXT Next\nCONSTRAINT Con\nPROPERTY Live\n",
    );
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(75), "{text}");
    assert!(
        text.contains("Computing initial states...\nError: Attempted to enumerate a set of the form [D -> R],but the domain D:\nSTRING\ncannot be enumerated.\nWhile working on the initial state:\nx = 0\n\nError: TLC was unable to fingerprint.\n\nFingerprint Stack Trace:\n0. Line 5, column 9 to line 5, column 13 in Stop\n"),
        "{text}"
    );
    assert!(
        text.contains("in Stop\n\n\nReason:\nAttempted to enumerate a set of the form [D -> R],but the domain D:\nSTRING\ncannot be enumerated.\n1 states generated, 0 distinct states found, 0 states left on queue.\nThe depth of the complete state graph search is 1.\n"),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn reports_a_bound_that_filters_a_set_tlc_cant_enumerate() {
    // The shape of MCEWD687a's TreeWithRoot: the bound is an operator whose definition filters
    // Seq(S), which TLC keeps as it is until the quantifier enumerates it. The state that fails
    // is one TLC has seen as it replays the expansion, which then ends quietly.
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals, Sequences\nVARIABLE x\nP(S) == {p \\in Seq(S) : p # <<>>}\nInit == x = 0\nNext == x' = (x + 1) % 3\nInv == x < 1 \\/ \\E p \\in P({1, 2}) : p[1] = 1\n====\n";
    let (output, directory) = run_lowered(
        "filter-bound",
        spec,
        "INIT Init\nNEXT Next\nINVARIANT Inv\n",
    );
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(76), "{text}");
    assert!(
        text.contains("Error: Evaluating invariant Inv failed.\nAttempted to enumerate { x \\in S : p(x) } when S:\nSeq({1, 2})\nis not enumerable\nError: The behavior up to this point is:\nState 1: <Initial predicate>\nx = 0\n\nState 2: <Next line 6, col 9 to line 6, col 24 of module Stop>\nx = 1\n\n2 states generated, 2 distinct states found, 0 states left on queue.\nThe depth of the complete state graph search is 2.\nThe average outdegree of the complete state graph is 1 (minimum is 1, the maximum 1 and the 95th percentile is 1).\n"),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
    // A function over the filter is one TLC keeps lazy and applies by the filter's membership,
    // which holds: TLC finds no error, and the binary doesn't report one.
    let spec = spec.replace(
        "\\E p \\in P({1, 2}) : p[1] = 1",
        "[p \\in P({1}) |-> 1][<<1>>] = 1",
    );
    let (output, directory) = run_lowered(
        "filter-function",
        &spec,
        "INIT Init\nNEXT Next\nINVARIANT Inv\n",
    );
    let text = stdout(&output);
    assert!(!text.contains("Error:"), "{text}");
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn checks_assumptions_that_draw_in_an_argument_and_add_bags() {
    // The shapes of ModuleSemanticsAssume: TLC keeps an argument's value once it has drawn it,
    // so both uses of T are the same subset, and reports a bag's count past an int and a
    // negative count by the messages AssertError compares.
    let spec = "---- MODULE Stop ----\nEXTENDS Bags, Integers, Randomization, TLC, TLCExt\nVARIABLE x\nSame(T) == T = T /\\ \\A y \\in T : y \\in T\nASSUME Same(RandomSubset(1, 1..1000))\nASSUME BagUnion({[y \\in {1} |-> 2], [y \\in {1} |-> 1]}) = [y \\in {1} |-> 3]\nASSUME AssertError(\"Overflow when computing 2147483647+1\", ([y \\in {1} |-> 2147483647] (+) [y \\in {1} |-> 1])[1] > 0)\nASSUME AssertError(\"Overflow when computing 2147483647+2147483647\", BagCardinality([y \\in {1, 2} |-> 2147483647]) > 0)\nASSUME AssertError(\"Attempted to apply the operator overridden by the Java method\\npublic static tlc2.value.impl.Value tlc2.module.Randomization.RandomSubset(tlc2.value.impl.Value,tlc2.value.impl.Value),\\nbut it produced the following error:\\n-1\", RandomSubset(-1, {1, 2}) = {})\nInit == x = 0\nNext == x' = x\n====\n";
    let (output, directory) = run_lowered("drawn-argument", spec, "INIT Init\nNEXT Next\n");
    let text = stdout(&output);
    assert_eq!(
        output.status.code(),
        Some(0),
        "{text}{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        text.contains("Model checking completed. No error has been found."),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
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
fn applies_the_functions_tlc_keeps_lazy() {
    // TLC keeps a function over Nat or Int lazy (`FcnLambdaValue`): applying one evaluates its
    // body, EXCEPT records the key, and a state can't hold one, as TLC can't fingerprint it.
    let spec = "---- MODULE Stop ----\nEXTENDS Integers\nVARIABLE x\nDouble == [n \\in Nat |-> 2 * n]\nPairs == [m, n \\in Int |-> m - n]\nInit == x = 0\nNext == x < 3 /\\ x' = x + 1\nShifted == LET f == [n \\in Nat |-> n + x] IN [f EXCEPT ![1] = @ * 10][1] = 10 + 10 * x /\\ f[2] = 2 + x\nInv == Double[3] = 6 /\\ Pairs[1, 4] = -3 /\\ [Double EXCEPT ![2] = 0][2] = 0 /\\ Shifted\n====\n";
    let (output, directory) = run_lowered(
        "lazy",
        spec,
        "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\nINVARIANT Inv\n",
    );
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(0), "{text}");
    assert!(
        text.contains("4 states generated, 4 distinct states found, 0 states left on queue."),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
    let held = "---- MODULE Stop ----\nEXTENDS Naturals\nVARIABLE f\nInit == f = [n \\in Nat |-> n]\nNext == UNCHANGED f\n====\n";
    let (output, directory) = run_lowered("lazy-held", held, "INIT Init\nNEXT Next\n");
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("unsupported: a state holding a function TLC keeps lazy"),
        "{}",
        String::from_utf8_lossy(&output.stderr)
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
fn tests_membership_in_a_set_tlc_holds_unnormalized_element_by_element() {
    // TLC's test PrintTraceRace: {1..2} stays as written, so TLC asks its element 1..2 whether
    // it equals 1, and checks the invariant without the sources that would make that failure a
    // FingerprintException.
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals, Sequences\nVARIABLE S\nInit == S = [q |-> <<>>, i |-> 1]\nNext == S.i <= 2 /\\ S' = [S EXCEPT !.i = S.i + 1, !.q = Append(S.q, S.i)]\nInv == S \\in [q : Seq({1..2}), i : 0..3]\n====\n";
    let (output, directory) = run_lowered(
        "unnormalized",
        spec,
        "INIT Init\nNEXT Next\nINVARIANT Inv\n",
    );
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(76), "{text}");
    assert!(
        text.contains("Error: Evaluating invariant Inv failed.\nAttempted to check equality of the set {1, 2} with the value:\n1\nError: The behavior up to this point is:\n"),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn reports_a_union_with_an_operand_that_isnt_a_set_as_it_fingerprints_it() {
    // Spectacle's semantic_error1: TLC keeps {6} \cup 0 lazy, calling cup on {6}, and fails to
    // enumerate it as it fingerprints the successor.
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == \\E s \\in {6} : x' = x \\cup {s}\n====\n";
    let (output, directory) = run_lowered("cup", spec, "INIT Init\nNEXT Next\n");
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(75), "{text}");
    let reason =
        "Attempted to enumerate S \\cup T when S:\n{6}\nand T:\n0\nare not both enumerable";
    assert!(
        text.contains(&format!("Error: TLC was unable to fingerprint.\n\nFingerprint Stack Trace:\n0) line 5, col 29 to line 5, col 38 of module Stop\n\nReason:\n{reason}\n")),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn stops_where_an_invariant_sets_exit_as_tlc_does() {
    // TLC's test EWD998Chan: TLCSet("exit", TRUE) finishes the queue, so the worker completes the
    // state it expands and stops. TLC's main thread, woken by the stop, prints its progress or not
    // as the threads race; the binary prints none. TLCGet's key reaches it through an INSTANCE of
    // TLC.
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x' \\in {x + 1, x + 2}\nStop == LET T == INSTANCE TLC IN T!TLCSet(\"exit\", T!TLCGet(\"distinct\") > 4)\n====\n";
    let (output, directory) = run_lowered("exit", spec, "INIT Init\nNEXT Next\nINVARIANT Stop\n");
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(0), "{text}");
    assert!(!text.contains("Progress("), "{text}");
    assert!(
        text.contains("\n7 states generated, 5 distinct states found, 2 states left on queue.\nThe depth of the complete state graph search is 3.\n"),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn declines_a_postcondition_or_alias_tlc_computes_as_it_starts() {
    // TLC computes a definition of constant level as it starts, then rejects it as a
    // POSTCONDITION ("The post condition Post cannot be a constant.") or an ALIAS.
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x' = x\nPost == FALSE\nAl == [y |-> 1]\n====\n";
    for config in ["POSTCONDITION Post\n", "ALIAS Al\n"] {
        let (output, directory) = run_lowered(
            "precomputed",
            spec,
            &format!("INIT Init\nNEXT Next\n{config}"),
        );
        assert!(
            String::from_utf8_lossy(&output.stderr)
                .contains("prove-it: not native yet: a POSTCONDITION or an ALIAS"),
            "{}",
            stdout(&output)
        );
        std::fs::remove_dir_all(directory).expect("removed");
    }
}

#[test]
fn declines_an_alias_that_prints_as_it_fails() {
    // TLC prints what the alias printed before the state whose alias fails, which the binary
    // doesn't place.
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals, TLC\nVARIABLES x\nInit == x = 0\nNext == x' = x + 1\nAl == [x |-> x, z |-> IF x = 0 THEN TRUE ELSE PrintT(\"hello\") /\\ Assert(FALSE, \"boom\")]\nInv == x < 1\n====\n";
    let (output, directory) = run_lowered(
        "alias-prints",
        spec,
        "INIT Init\nNEXT Next\nINVARIANT Inv\nALIAS Al\n",
    );
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("not native yet: an ALIAS that prints"),
        "{}",
        stdout(&output)
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn keeps_the_registers_as_tlc_rebuilds_a_violations_trace() {
    // TLC's first rebuild walks neither the initial predicate of a trace of two states nor the
    // step to the violating state, and no rebuild evaluates the constraints: only the search and
    // the second rebuild, for the postcondition, set the register.
    let post = "Post == PrintT(<<\"post\", TLCGet(1)>>)\n====\n";
    let cases = [
        (
            "Init == /\\ TLCSet(1, TLCGet(1) + 1) /\\ x \\in {0, 1}\nNext == x' = x + 1\nInv == x < 2\n",
            "",
            "<<\"post\", 2>>",
        ),
        (
            "Init == x = 0\nNext == x' = x + 1\nC == TLCSet(1, TLCGet(1) + 1)\nInv == x < 3\n",
            "CONSTRAINT C\n",
            "<<\"post\", 4>>",
        ),
    ];
    for (definitions, constraint, printed) in cases {
        let spec = format!(
            "---- MODULE Stop ----\nEXTENDS Naturals, TLC\nVARIABLE x\nASSUME TLCSet(1, 0)\n{definitions}{post}"
        );
        let config =
            format!("INIT Init\nNEXT Next\nINVARIANT Inv\n{constraint}POSTCONDITION Post\n");
        let (output, directory) = run_lowered("registers", &spec, &config);
        let text = stdout(&output);
        assert!(text.contains(&format!("\n{printed}\n")), "{text}");
        std::fs::remove_dir_all(directory).expect("removed");
    }
}

#[test]
fn prints_the_counterexample_records_in_tlcs_order() {
    // TLC interns the field names of its counterexample's records as RecordValue loads, after the
    // spec's strings and in the order declared, so a name the spec has comes first.
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals, TLC, TLCExt\nVARIABLES x\nInit == x = 0\nA(n) == x' = x + n\nDummy == <<\"parameters\", \"context\", \"endLine\">>\nNext == \\E n \\in {1} : A(n)\nInv == x < 1\nPost == PrintT(CounterExample.action) /\\ TRUE\n====\n";
    let (output, directory) = run_lowered(
        "counterexample",
        spec,
        "INIT Init\nNEXT Next\nINVARIANT Inv\nPOSTCONDITION Post\n",
    );
    let text = stdout(&output);
    assert!(
        text.contains("[ parameters |-> <<\"n\">>,\n       context |-> [n |-> 1],\n       name |-> \"A\",\n       location |->\n           [ endLine |-> 5,\n             beginLine |-> 5,\n             beginColumn |-> 9,\n             endColumn |-> 18,\n             module |-> \"Stop\" ] ]"),
        "{text}"
    );
    // TLC builds the counterexample's states from an ALIAS, which the binary doesn't follow.
    let aliased = spec.replace("Inv ==", "Al == [x |-> x, z |-> 0]\nInv ==");
    let (output, aliased_directory) = run_lowered(
        "counterexample-alias",
        &aliased,
        "INIT Init\nNEXT Next\nINVARIANT Inv\nPOSTCONDITION Post\nALIAS Al\n",
    );
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("reads the counterexample of a model with an ALIAS"),
        "{}",
        stdout(&output)
    );
    std::fs::remove_dir_all(directory).expect("removed");
    std::fs::remove_dir_all(aliased_directory).expect("removed");
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

#[test]
fn reports_a_property_an_initial_state_violates() {
    let directory = std::env::temp_dir().join(format!(
        "prove-it-cli-initial-property-{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&directory).expect("a directory");
    let spec = "---- MODULE P ----\nEXTENDS Integers\nVARIABLE x\nInit == x \\in 1..10\nNext == x' = 0\nSpec == Init /\\ [][Next]_x\nNotNine == x # 9\n====\n";
    for (file, contents) in [
        ("P.tla", spec),
        ("P.cfg", "SPECIFICATION Spec\nPROPERTY NotNine\n"),
        ("P.front", ""),
    ] {
        std::fs::write(directory.join(file), contents).expect("a file");
    }
    let output = run(&directory, &["-workers", "1", "P"]);
    let text = stdout(&output);
    // As TLC's DoInitFunctorProperty: the state in the message, and no statistics.
    assert_eq!(output.status.code(), Some(13), "{text}");
    assert!(
        text.contains(
            "Computed 8 initial states...\nError: Property NotNine is violated by the initial state:\nx = 9\n\nFinished in "
        ),
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
fn checks_a_model_whose_assumption_prints_a_record() {
    // TLC's Github726: TLC prints a record's fields in the order it built them, which the store
    // forgets, but TLC prints the assumption's text in the front the binary records.
    let spec = "---- MODULE Stop ----\nEXTENDS TLC\nVARIABLE x\nASSUME PrintT([dst |-> \"a\"] @@ [data |-> 15])\nInit == x = 0\nNext == x' = x\n====\n";
    let directory =
        std::env::temp_dir().join(format!("prove-it-cli-printed-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    for (extension, contents) in [
        ("tla", spec),
        ("cfg", "INIT Init\nNEXT Next\n"),
        ("front", ""),
    ] {
        std::fs::write(directory.join(format!("Stop.{extension}")), contents).expect("a file");
    }
    let output = run(&directory, &["Stop"]);
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(0), "{text}");
    assert!(
        text.contains("Model checking completed. No error has been found."),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

const CDOT_IMPLIED_INIT_IR: &[u8] = include_bytes!(
    "../../../../tests/conformance/ir/tlc/tlatools/org.lamport.tlatools/test-model/cdot/CdotWithContextB.ir"
);

#[test]
fn reports_an_implied_init_that_fails_on_an_initial_state() {
    let (output, directory) = run_golden(
        "implied-init",
        CDOT_IMPLIED_INIT_IR,
        "CdotWithContextB",
        "",
        &[],
    );
    let text = stdout(&output);
    // ENABLED Next, a property's initial predicate, reaches A(n) \cdot B(n): TLC reports the
    // state, and the call stack from the initial predicate's infix conjunction through ENABLED.
    assert_eq!(output.status.code(), Some(75), "{text}");
    assert!(
        text.contains(include_str!("cdot-implied-init.txt")),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn rejects_a_constant_invariant_the_front_end_leaves_to_the_startup() {
    // tla-front's evaluator computes no tuples, so the engine evaluates Bad as TLC starts.
    let source = "---- MODULE Bad ----\nVARIABLE x\nInit == x = 0\nNext == x' = x\nBad == <<1>>[1] = 2\n====\n";
    let config = "INIT Init\nNEXT Next\nINVARIANT Bad\n";
    let spec = std::env::temp_dir().join(format!("prove-it-cli-bad-{}.tla", std::process::id()));
    std::fs::write(&spec, source).expect("the spec");
    let options = tla_front::model::ModelOptions {
        libraries: &[],
        version: None,
        is_warning_enabled: true,
        is_spec_described: false,
        random_seed: 0,
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

#[test]
fn reports_an_atom_that_fails_as_tlc_adds_a_state_to_the_behavior_graphs() {
    let ir = include_bytes!(
        "../../../../tests/conformance/ir/tlc/tlatools/org.lamport.tlatools/test-model/Github607.ir"
    );
    let config = "SPECIFICATION\n    Spec\nPROPERTIES\n    Prop\n";
    let (output, directory) = run_golden("atom-failure", ir, "Github607", config, &[]);
    let text = stdout(&output);
    // TLC evaluates x = "abc" as it adds the state it expanded, prints the call stack before the
    // exception, and exits as on one it didn't expect.
    assert_eq!(output.status.code(), Some(255), "{text}");
    assert!(
        text.contains("Error: The error occurred when TLC was evaluating the nested\nexpressions at the following positions:\n0. Line 21, column 21 to line 21, column 29 in Github607\n\n\nError: TLC threw an unexpected exception.\nThis was probably caused by an error in the spec or model.\nSee the User Output or TLC Console for clues to what happened.\nThe exception was a java.lang.RuntimeException\n: Attempted to check equality of integer 0 with non-integer:\n\"abc\"\nError: The behavior up to this point is:\nState 1: <Initial predicate>\nx = 0\n\n2 states generated, 1 distinct states found, 0 states left on queue.\nThe depth of the complete state graph search is 1.\nThe average outdegree of the complete state graph is 0 (minimum is 0, the maximum 0 and the 95th percentile is 0).\n"),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn names_the_fairness_condition_whose_action_leaves_a_variable_unassigned() {
    let ir = include_bytes!(
        "../../../../tests/conformance/ir/tla-rs/test_cases/should_error/liveness_error.ir"
    );
    let config = "SPECIFICATION Spec\nPROPERTY FairOnlyX\nCHECK_DEADLOCK FALSE\n";
    let (output, directory) = run_golden("fairness-subscript", ir, "liveness_error", config, &[]);
    let text = stdout(&output);
    // ENABLED <<OnlyX>>_vars reads y' in the successor, which OnlyX doesn't assign; TLC's call
    // stack starts at OnlyX, as it records no node for the <<A>>_v of WF_v(A).
    assert_eq!(output.status.code(), Some(255), "{text}");
    assert!(
        text.contains("Error: The error occurred when TLC was evaluating the nested\nexpressions at the following positions:\n0. Line 9, column 22 to line 9, column 26 in liveness_error\n1. Line 7, column 10 to line 7, column 15 in liveness_error\n2. Line 9, column 17 to line 9, column 20 in liveness_error\n3. Line 4, column 9 to line 4, column 16 in liveness_error\n4. Line 4, column 14 to line 4, column 14 in liveness_error\n\n\nError: TLC threw an unexpected exception.\nThis was probably caused by an error in the spec or model.\nSee the User Output or TLC Console for clues to what happened.\nThe exception was a java.lang.RuntimeException\n: The action formula A appearing in a WF_v(A) or SF_v(A) operator does not specify the primed value of the variable y occurring in the state formula v.\n\nError: The behavior up to this point is:\nState 1: <Initial predicate>\n/\\ x = 0\n/\\ y = 0\n\n2 states generated, 2 distinct states found, 1 states left on queue.\n"),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn records_the_specification_as_the_interpreter_does() {
    // TLCGet("spec"), which tla-front describes and the split gives the actions of, as the
    // interpreter prints it for this spec.
    let spec = "---- MODULE Stop ----\nEXTENDS Integers, TLC\nVARIABLES x, y\nInit == x = 0 /\\ y = 0\nStep(d) == x < 3 /\\ x' = x + d /\\ y' = y\nReset == x >= 3 /\\ x' = 0 /\\ UNCHANGED y\nNext == (\\E d \\in {1, 2} : Step(d)) \\/ Reset\nSpec == Init /\\ [][Next]_<<x, y>> /\\ WF_<<x, y>>(Next)\nSmall == x < 10\nProp == [][x' # x]_<<x, y>> /\\ []<>(x = 0)\nBound == y < 5\nMoves == x' # x \\/ y' = y\nRecorded == PrintT(TLCGet(\"spec\"))\n====\n";
    let (output, directory) = run_lowered(
        "spec",
        spec,
        "SPECIFICATION Spec\nINVARIANT Small\nPROPERTY Prop\nCONSTRAINT Bound\nACTION_CONSTRAINT Moves\nPOSTCONDITION Recorded\n",
    );
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(0), "{text}");
    assert!(text.contains(include_str!("spec-record.txt")), "{text}");
    std::fs::remove_dir_all(directory).expect("removed");
}

const EMPTY_SUBSET_EQ_IR: &[u8] = include_bytes!(
    "../../../../tests/conformance/ir/tlc/tlatools/org.lamport.tlatools/test-model/EmptySubsetEq.ir"
);

#[test]
fn reports_a_fingerprint_failure_tlcs_replay_throws() {
    let (output, directory) = run_golden(
        "replayed-fingerprint",
        EMPTY_SUBSET_EQ_IR,
        "EmptySubsetEq",
        "",
        &[],
    );
    let text = stdout(&output);
    // TLC reports the failure in the next states as it is, then its replay with the call stack,
    // which gives SUBSET (1..3) its source, throws a FingerprintException: TLC prints that call
    // stack, down to the value whose method failed.
    assert_eq!(output.status.code(), Some(75), "{text}");
    assert!(text.contains(include_str!("empty-subset-eq.txt")), "{text}");
    std::fs::remove_dir_all(directory).expect("removed");
}

// Runs the binary on a spec of its own with tla-front as its whole front end.
fn run_front(test: &str, spec: &str, config: &str, args: &[&str]) -> (Output, PathBuf) {
    let directory =
        std::env::temp_dir().join(format!("prove-it-cli-{test}-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    let name = spec
        .split_whitespace()
        .nth(2)
        .expect("the module's name")
        .to_string();
    std::fs::write(directory.join(format!("{name}.tla")), spec).expect("the spec");
    std::fs::write(directory.join(format!("{name}.cfg")), config).expect("the configuration");
    let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .args(["-noTE"].iter().chain(args).chain([&name.as_str()]))
        .current_dir(&directory)
        .env_remove("PROVE_IT_FRONT")
        .output()
        .expect("the binary runs");
    (output, directory)
}

// What a run printed from `Starting...` to computing the initial states.
fn get_startup(text: &str) -> &str {
    let start = text.find("Starting... (").expect("the start");
    let start = start + text[start..].find('\n').expect("a line") + 1;
    let end = text
        .find("Computing initial states...")
        .unwrap_or(text.len());
    &text[start..end]
}

#[test]
fn prints_what_tlc_prints_as_it_starts_without_a_recorded_front() {
    let (output, directory) = run_front(
        "startup",
        "---- MODULE Sym ----\nEXTENDS TLC, Naturals\nCONSTANTS A, B\nVARIABLE x\nPerms == Permutations(A) \\cup Permutations(B)\nShown == Print(\"startup\", TRUE)\nInit == x \\in A /\\ Shown\nNext == x' \\in A\n====\n",
        "CONSTANTS A = {a1} B = {b1, b2}\nINIT Init\nNEXT Next\nSYMMETRY Perms\n",
        &[],
    );
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(0), "{text}");
    assert!(
        text.contains("Semantic processing of module Sym\n"),
        "{text}"
    );
    assert_eq!(
        get_startup(&text),
        "\"startup\"  TRUE\nWarning: The set A has been defined to be a symmetry set but contains less than two elements.\n(Use the -nowarning option to disable this warning.)\n",
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn compares_tlcs_message_in_an_assert_error_assumption() {
    let spec = "---- MODULE AE ----\nEXTENDS TLC, TLCExt, Naturals\nVARIABLE x\nASSUME Print(\"before\", TRUE)\nASSUME AssertError(\"Attempted to check if the value:\\n\\\"d1\\\"\\nis an element of Nat.\", \"d1\" \\in Nat)\nASSUME RandomElement(1..100) \\in 1..100\nASSUME Print(\"after\", TRUE)\nInit == x = 1\nNext == UNCHANGED x\n====\n";
    let (output, directory) = run_front("assert-error", spec, "INIT Init\nNEXT Next\n", &[]);
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(0), "{text}");
    assert_eq!(
        get_startup(&text),
        "\"before\"  TRUE\n\"after\"  TRUE\n",
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
    // Under -tool, the message TLC raises with a code holds the code's markers, so the
    // assumption is false.
    let (output, directory) = run_front(
        "assert-error-tool",
        spec,
        "INIT Init\nNEXT Next\n",
        &["-tool"],
    );
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(10), "{text}");
    assert!(
        text.contains("\"before\"  TRUE\n@!@!@STARTMSG 2104:1 @!@!@\nAssumption line 5, col 8 to line 5, col 99 of module AE is false.\n"),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn prints_a_failures_trace_through_the_alias() {
    // TLC prints the trace to the state it was expanding through the ALIAS, each state with the
    // one after it as its next state and the last with itself (`TLCTrace.printTrace`).
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == IF x < 2 THEN x' = x + 1 ELSE x' = Assert(FALSE, \"boom\")\nAlias == [x |-> x, nxt |-> x', twice |-> 2 * x]\n====\n";
    let (output, directory) =
        run_lowered("alias-failure", spec, "INIT Init\nNEXT Next\nALIAS Alias\n");
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(14), "{text}");
    assert!(
        text.contains("\"boom\"\nError: The behavior up to this point is:\nState 1: <Initial predicate>\n/\\ x = 0\n/\\ nxt = 1\n/\\ twice = 0\n\nState 2: <Next line 5, col 9 to line 5, col 64 of module Stop>\n/\\ x = 1\n/\\ nxt = 2\n/\\ twice = 2\n\nState 3: <Next line 5, col 9 to line 5, col 64 of module Stop>\n/\\ x = 2\n/\\ nxt = 2\n/\\ twice = 4\n\nError: The error occurred when TLC was evaluating the nested\n"),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
    // An initial state TLC was expanding is the whole trace, which TLC prints as it is.
    let alone = spec.replace("IF x < 2 THEN x' = x + 1 ELSE ", "");
    let (output, directory) = run_lowered(
        "alias-failure-alone",
        &alone,
        "INIT Init\nNEXT Next\nALIAS Alias\n",
    );
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(14), "{text}");
    assert!(
        text.contains("Error: The behavior up to this point is:\nState 1: <Initial predicate>\nx = 0\n\nError: The error occurred"),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn prints_a_deadlocked_initial_state_as_it_is_under_an_alias() {
    // TLC evaluates no ALIAS on a trace of an initial state alone (`TLCTrace.printTrace`).
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x < 0 /\\ x' = x + 1\nAlias == [x |-> x, twice |-> 2 * x]\n====\n";
    let (output, directory) = run_lowered(
        "alias-deadlock",
        spec,
        "INIT Init\nNEXT Next\nALIAS Alias\n",
    );
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(11), "{text}");
    assert!(
        text.contains("Error: Deadlock reached.\nError: The behavior up to this point is:\nState 1: <Initial predicate>\nx = 0\n\n1 states generated"),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
    // A longer trace goes through the ALIAS.
    let later = spec.replace("x < 0", "x < 1");
    let (output, directory) = run_lowered(
        "alias-deadlock-later",
        &later,
        "INIT Init\nNEXT Next\nALIAS Alias\n",
    );
    let text = stdout(&output);
    assert!(
        text.contains("State 1: <Initial predicate>\n/\\ x = 0\n/\\ twice = 0\n\nState 2: <Next line 5, col 9 to line 5, col 27 of module Stop>\n/\\ x = 1\n/\\ twice = 2\n\n"),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn checks_the_postconditions_after_a_failure_as_tlcs_deadlock_check_does() {
    // TLC's worker goes on to check a state for deadlock after its next-state relation failed,
    // having generated no successor, and that check evaluates the postconditions (`Worker.run`):
    // between the trace and the call stack, with the registers as the failure left them.
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals, TLC\nVARIABLE x\nASSUME TLCSet(0, 0)\nInit == x = 0\nNext == x' = Assert(FALSE, \"boom\")\nPost == TLCSet(42, TLCGet(\"generated\")) /\\ TLCGet(0) = 63\n====\n";
    let config = "INIT Init\nNEXT Next\nPOSTCONDITION Post\n";
    let (output, directory) = run_lowered("failure-postcondition", spec, config);
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(14), "{text}");
    assert!(
        text.contains("State 1: <Initial predicate>\nx = 0\n\nError: Postcondition Post at line 7, col 9 to line 7, col 57 of module Stop is false.\nError: The error occurred when TLC was evaluating the nested\n"),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
    // Without the deadlock check nothing evaluates them.
    let directory = std::env::temp_dir().join(format!(
        "prove-it-cli-failure-no-postcondition-{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&directory).expect("a directory");
    for (file, contents) in [("Stop.tla", spec), ("Stop.cfg", config), ("Stop.front", "")] {
        std::fs::write(directory.join(file), contents).expect("a file");
    }
    let output = run(&directory, &["-deadlock", "Stop"]);
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(14), "{text}");
    assert!(
        text.contains("State 1: <Initial predicate>\nx = 0\n\nError: The error occurred when TLC was evaluating the nested\n"),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
    // Nor after an invariant fails to evaluate, on a successor the worker had generated.
    let invariant = spec.replace(
        "Next == x' = Assert(FALSE, \"boom\")",
        "Next == x < 3 /\\ x' = x + 1\nInv == x < 1 \\/ Assert(FALSE, \"boom\")",
    );
    let (output, directory) = run_lowered(
        "failure-invariant-postcondition",
        &invariant,
        "INIT Init\nNEXT Next\nPOSTCONDITION Post\nINVARIANT Inv\n",
    );
    let text = stdout(&output);
    assert!(
        text.contains("State 2: <Next line 6, col 9 to line 6, col 27 of module Stop>\nx = 1\n\n2 states generated"),
        "{text}"
    );
    assert!(!text.contains("Postcondition"), "{text}");
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn compares_the_message_of_a_lazy_function_applied_outside_its_domain() {
    // TLC applies a LET's function constructor keeping it lazy, and `FcnLambdaValue.apply` words
    // a key outside its domain with the function as its `FcnRcdValue` prints (TLC's Github696).
    let spec = "---- MODULE AE ----\nEXTENDS TLC, TLCExt, Naturals\nVARIABLE x\nASSUME LET f == [n \\in {1, 3} |-> n + 1] IN AssertError(\"In applying the function\\n(1 :> 2 @@ 3 :> 4),\\nthe first argument is:\\n5\\nwhich is not in its domain.\\n\", f[5])\nInit == x = 1\nNext == UNCHANGED x\n====\n";
    let (output, directory) = run_front("assert-error-lazy", spec, "INIT Init\nNEXT Next\n", &[]);
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(0), "{text}");
    assert!(
        text.contains("1 distinct states found, 0 states left on queue."),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
    // A LET that names the function elsewhere may have built it first, which words the failure
    // otherwise: the replay doesn't follow which, so the run isn't native.
    let twice = spec.replace("IN AssertError(", "IN DOMAIN f = {1, 3} /\\ AssertError(");
    let (output, directory) =
        run_front("assert-error-built", &twice, "INIT Init\nNEXT Next\n", &[]);
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("not native yet"),
        "{}",
        stdout(&output)
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn searches_a_functions_keys_as_tlc_does_where_one_cant_compare() {
    // `FcnRcdValue.select` asks each key of a short function whether it equals the argument, in
    // the order of a function a state holds, which TLC has sorted.
    let spec = "---- MODULE Keys ----\nEXTENDS Integers, TLC\nCONSTANTS M1, M2, K\nVARIABLE v\nInit == v = [m \\in {M1, M2} |-> 1]\nNext == UNCHANGED v\nInv == v[K] = 1\n====\n";
    let config = "CONSTANTS M1 = A_1\nM2 = A_2\nK = B_1\nINIT Init\nNEXT Next\nINVARIANT Inv\n";
    let (output, directory) = run_front("keys-state", spec, config, &[]);
    let text = stdout(&output);
    assert!(
        text.contains("Error: Attempted to check equality of the differently-typed model values A_1 and B_1\nWhile working on the initial state:\nv = (A_1 :> 1 @@ A_2 :> 1)\n"),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
    // TLC searches a function it hasn't sorted in the order it built it, which the replay
    // doesn't keep.
    let built = spec.replace("Inv == v[K] = 1", "Inv == (M2 :> v @@ M1 :> 2)[K] = 1");
    let (output, directory) = run_front("keys-built", &built, config, &[]);
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("not native yet"),
        "{}",
        stdout(&output)
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn prints_an_assumption_value_as_tlc_built_it_without_a_recorded_front() {
    // test-model/SetPredValue: the store forgets how TLC built the set PrintT prints, which the
    // trace evaluator prints as TLC does.
    let spec = "---- MODULE SetPredValue ----\nEXTENDS TLC, FiniteSets, Integers\n\nRange(F) == { F[x] : x \\in DOMAIN F }\nMin(n, m) == IF n < m THEN n ELSE m\n\nLP(S, T, p) == LET ss == { s \\in SUBSET S : Cardinality(s) = p}\n                          IN { e \\in [ T -> ss ] : \n                                Cardinality(Range(e)) = Min(Cardinality(T), Cardinality(ss)) }\n\nASSUME PrintT(LP(1..4, {\"a\",\"b\",\"c\"}, 2))\n\n=============================\n";
    let directory =
        std::env::temp_dir().join(format!("prove-it-cli-assumed-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    std::fs::write(directory.join("SetPredValue.tla"), spec).expect("the spec");
    std::fs::write(directory.join("SetPredValue.cfg"), "").expect("the configuration");
    let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .args(["-noGenerateSpecTE", "SetPredValue"])
        .current_dir(&directory)
        .env_remove("PROVE_IT_FRONT")
        .output()
        .expect("the binary runs");
    let text = stdout(&output);
    assert_eq!(
        output.status.code(),
        Some(0),
        "{text}{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        text.contains(")\n{ [a |-> {1, 2}, b |-> {1, 3}, c |-> {1, 4}],\n  [a |-> {1, 2}, b |-> {1, 3}, c |-> {2, 3}],\n"),
        "{text}"
    );
    assert!(
        text.contains(
            "  [a |-> {3, 4}, b |-> {2, 4}, c |-> {2, 3}] }\nComputing initial states...\n"
        ),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}
