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
fn leaves_a_postcondition_to_the_front_end() {
    let (output, directory) = run_golden(
        "postcondition",
        TEST57_IR,
        "test57",
        "POSTCONDITION Never\n",
        &[],
    );
    assert_eq!(output.status.code(), Some(1));
    assert!(!stdout(&output).contains("violated"));
    assert!(String::from_utf8_lossy(&output.stderr).contains("not native yet: the engine stopped"));
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
