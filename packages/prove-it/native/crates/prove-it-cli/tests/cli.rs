//! Runs the binary as a user would: on specs of the tests' own, which tla-front reads, and on
//! golden engine IRs, such as TCommit's, which PROVE_IT_TEST_IR names in place of a spec's.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const COMMIT_IR: &[u8] = include_bytes!(
    "../../../../tests/conformance/ir/examples/specifications/transaction_commit/TCommit.ir"
);

fn run(directory: &PathBuf, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .args(args)
        .current_dir(directory)
        .output()
        .expect("the binary runs")
}

// Runs the binary on the engine IR `<name>.ir` in the directory, in place of the one tla-front
// lowers.
fn run_ir(directory: &PathBuf, name: &str, args: &[&str]) -> Output {
    run_ir_with(directory, name, args, &[])
}

fn run_ir_with(
    directory: &PathBuf,
    name: &str,
    args: &[&str],
    environment: &[(&str, &str)],
) -> Output {
    Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .args(args)
        .current_dir(directory)
        .env("PROVE_IT_TEST_IR", directory.join(format!("{name}.ir")))
        .envs(environment.iter().copied())
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
    let output = run_ir(
        &directory,
        "TCommit",
        &["-workers", "1", "-noTE", "TCommit"],
    );
    let text = stdout(&output);
    let lines: Vec<&str> = text.lines().collect();
    assert_eq!(output.status.code(), Some(0), "{text}");
    assert!(lines[0].starts_with("TLC2 Version "));
    assert!(lines[1].starts_with(
        "Running breadth-first search Model-Checking with fp 0 and seed 0 with 1 worker on "
    ));
    // With an IR in place of a spec, nothing comes before the search.
    assert_eq!(lines[2], "Computing initial states...");
    assert!(
        lines[3].starts_with("Finished computing initial states: 1 distinct state generated at ")
    );
    assert_eq!(
        lines[4..lines.len() - 1].join("\n"),
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
    let output = run_ir(
        &directory,
        "TCommit",
        &["-tool", "-seed", "+12", "TCommit.tla"],
    );
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
    let seed = run_ir(&directory, "TCommit", &["-seed", "x", "TCommit"]);
    assert_eq!(seed.status.code(), Some(1));
    assert!(stdout(&seed).ends_with(
        "Error: Error: An integer for seed required. But encountered x\nUsage: java tlc2.TLC [-help] [-option] inputfile\n"
    ));
    let config = run_ir(&directory, "TCommit", &["Missing.tla"]);
    assert_eq!(config.status.code(), Some(151));
    assert!(stdout(&config).ends_with(
        "Error: TLC encountered the following error when trying to read the configuration file Missing.cfg:\nFile not found.\n"
    ));
    let usage = run_ir(&directory, "TCommit", &[]);
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
        let output = run_ir(&directory, "TCommit", &[&["tlc2.TLC"], args].concat());
        assert_eq!(output.status.code(), Some(1), "{args:?}");
        let text = stdout(&output);
        assert!(text.starts_with("TLC2 Version "), "{text}");
        assert!(
            text.ends_with(&format!("\nError: Error: {message}{usage}")),
            "{text}"
        );
    }
    let marked = run_ir(
        &directory,
        "TCommit",
        &["tlc2.TLC", "-tool", "-fp", "131", "TCommit"],
    );
    assert!(stdout(&marked).ends_with(&format!(
        "@!@!@STARTMSG 1102:1 @!@!@\nError: The number for -fp must be between 0 and 130 (inclusive).{usage}@!@!@ENDMSG 1102 @!@!@\n"
    )));
    // TLC names the configuration file with or without its extension.
    let configured = run_ir(
        &directory,
        "TCommit",
        &["tlc2.TLC", "-config", "TCommit", "TCommit"],
    );
    assert_eq!(configured.status.code(), Some(0), "{}", stdout(&configured));
    for (args, what) in [
        (&["-difftrace", "TCommit"][..], "the TLC option -difftrace"),
        (&["-simulate", "TCommit"], "the TLC option -simulate"),
        (&["-coverage", "1", "TCommit"], "the TLC option -coverage"),
        (&["-fp", "1", "TCommit"], "-fp 1"),
        (&["-lncheck", "off", "TCommit"], "-lncheck off"),
        (&["TCommit.cfg"], "a module named as a configuration file"),
    ] {
        let output = run_ir(&directory, "TCommit", &[&["tlc2.TLC"], args].concat());
        assert_eq!(output.status.code(), Some(1), "{args:?}");
        assert_eq!(stdout(&output), "", "{args:?}");
        assert_eq!(
            String::from_utf8_lossy(&output.stderr),
            format!("prove-it: not native yet: {what}\n")
        );
    }
    let property = run_ir(
        &directory,
        "TCommit",
        &[
            "-Dtlc2.tool.ModelChecker.BAQueue=true",
            "tlc2.TLC",
            "TCommit",
        ],
    );
    assert_eq!(
        String::from_utf8_lossy(&property.stderr),
        "prove-it: not native yet: the system property tlc2.tool.ModelChecker.BAQueue\n"
    );
    let silent = run_ir(
        &directory,
        "TCommit",
        &["-Dtlc2.TLC.ide=vscode", "tlc2.TLC", "TCommit"],
    );
    assert_eq!(silent.status.code(), Some(0), "{}", stdout(&silent));
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn prints_a_deadlock_unless_deadlock_turns_it_off() {
    // TCommit's configuration turns deadlock checking off; with it on, its final states deadlock.
    let mut ir = tla_ir::decode(COMMIT_IR).expect("an IR");
    ir.model.check_deadlock = true;
    let directory = commit_directory_with("deadlock", &tla_ir::encode(&ir));
    let checked = run_ir(&directory, "TCommit", &["TCommit"]);
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
    let tool = run_ir(&directory, "TCommit", &["-tool", "TCommit"]);
    let text = stdout(&tool);
    assert_eq!(tool.status.code(), Some(11), "{text}");
    assert!(text.contains(concat!(
        "@!@!@STARTMSG 2114:1 @!@!@\nDeadlock reached.\n@!@!@ENDMSG 2114 @!@!@\n",
        "@!@!@STARTMSG 2121:1 @!@!@\nThe behavior up to this point is:\n@!@!@ENDMSG 2121 @!@!@\n",
        "@!@!@STARTMSG 2217:4 @!@!@\n1: <Initial predicate>\n",
    )), "{text}");
    let unchecked = run_ir(&directory, "TCommit", &["-deadlock", "TCommit"]);
    assert_eq!(unchecked.status.code(), Some(0));
    assert!(stdout(&unchecked).contains("94 states generated, 34 distinct states found"));
    std::fs::remove_dir_all(directory).expect("removed");
}

// Runs the binary on a golden model's IR as the IR of a spec of that name, with the given
// configuration, in a directory of the test's own.
fn run_golden(test: &str, ir: &[u8], name: &str, config: &str, args: &[&str]) -> (Output, PathBuf) {
    let directory =
        std::env::temp_dir().join(format!("prove-it-cli-{test}-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    for (extension, contents) in [("tla", &b""[..]), ("cfg", config.as_bytes()), ("ir", ir)] {
        std::fs::write(directory.join(format!("{name}.{extension}")), contents).expect("a file");
    }
    let mut all = args.to_vec();
    all.push(name);
    (run_ir(&directory, name, &all), directory)
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
    // TLC prints its warnings of the model tla-front lowers.
    let directory =
        std::env::temp_dir().join(format!("prove-it-cli-stuttering-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    for (file, contents) in [
        (
            "Stutter.tla",
            "---- MODULE Stutter ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x' = 1 - x\nSpec == Init /\\ [][Next]_x\nLive == []<>(x = 1)\n====\n",
        ),
        ("Stutter.cfg", "SPECIFICATION Spec\nPROPERTY Live\n"),
    ] {
        std::fs::write(directory.join(file), contents).expect("a file");
    }
    let output = run(&directory, &["-noTE", "Stutter"]);
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
        .env("PROVE_IT_TEST_IR", directory.join("stages.ir"))
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
fn checks_a_model_tla_front_lowers() {
    let directory = std::env::temp_dir().join(format!("prove-it-cli-lower-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    let spec = "---- MODULE Count ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x < 3 /\\ x' = x + 1\n====\n";
    for (file, contents) in [
        ("Count.tla", spec),
        ("Count.cfg", "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n"),
    ] {
        std::fs::write(directory.join(file), contents).expect("a file");
    }
    let output = run(&directory, &["-noTE", "Count"]);
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
    ] {
        std::fs::write(directory.join(file), contents).expect("a file");
    }
    let output = run(&directory, &["-noTE", "Post"]);
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
    // The search prints the assumptions as it evaluates them.
    let (output, directory) = run_front("printed-native", spec, "INIT Init\nNEXT Next\n", &[]);
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(10), "{text}");
    assert!(text.contains(expected), "{text}");
    std::fs::remove_dir_all(directory).expect("removed");
}

// SANY's corpus Semantics: `Tool.isValid` fails on an assumption that is no boolean, naming its
// place, and `checkAssumptions` reports it (EC 2215 within 2105).
#[test]
fn reports_an_assumption_that_is_no_boolean() {
    let spec = "---- MODULE NotBool ----\nVARIABLE x\nASSUME \"text\"\nInit == x = 0\nNext == x' = x\n====\n";
    let place = "line 3, col 8 to line 3, col 13 of module NotBool";
    for (test, args, expected) in [
        (
            "not-bool",
            &[][..],
            format!(
                "Error: Evaluating assumption {place} failed.\nTLC expected a boolean value, but did not find one. {place}\nFinished in "
            ),
        ),
        (
            "not-bool-tool",
            &["-tool"][..],
            format!(
                "@!@!@STARTMSG 2105:1 @!@!@\nEvaluating assumption {place} failed.\n@!@!@STARTMSG 2215:0 @!@!@\nTLC expected a boolean value, but did not find one. {place}\n@!@!@ENDMSG 2215 @!@!@\n@!@!@ENDMSG 2105 @!@!@\n"
            ),
        ),
    ] {
        let (output, directory) = run_front(test, spec, "INIT Init\nNEXT Next\n", args);
        let text = stdout(&output);
        assert_eq!(output.status.code(), Some(10), "{text}");
        assert!(text.contains(&expected), "{text}");
        std::fs::remove_dir_all(directory).expect("removed");
    }
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
fn tests_membership_in_a_filter_of_a_finite_set_as_tlc_keeps_it_lazy() {
    // TLC filters only a set enumeration or an interval at once. Over SUBSET {1} it asks the set
    // first and evaluates the predicate only for an element, wording its failure as its own.
    for (assumption, error) in [
        (
            "1 \\in {s \\in SUBSET {1} : 1 \\div 0 = 0}",
            "Attempted to check if the non-enumerable value\n1\nis element of\n{{}, {1}}",
        ),
        (
            "{1} \\in {s \\in SUBSET {1} : 1 \\div 0 = 0}",
            "Cannot decide if element:\n{1}\n is element of:\n{{}, {1}}\nand satisfies the predicate line 4, col 36 to line 4, col 47 of module Filter",
        ),
        (
            "Cardinality({s \\in SUBSET {1} : 1 \\div 0 = 0}) = 1",
            "The second argument of \\div is 0.",
        ),
    ] {
        let spec = format!(
            "---- MODULE Filter ----\nEXTENDS Naturals, FiniteSets\nVARIABLE x\nASSUME {assumption}\nInit == x = 0\nNext == x' = x\n====\n"
        );
        let (output, directory) = run_front("filter", &spec, "INIT Init\nNEXT Next\n", &[]);
        let text = stdout(&output);
        assert_eq!(output.status.code(), Some(10), "{text}");
        assert!(
            text.contains(&format!("of module Filter failed.\n{error}\n")),
            "{text}"
        );
        std::fs::remove_dir_all(directory).expect("removed");
    }
}

// Runs an invariant that fails to evaluate on the second state, after definitions of its own, and
// gives TLC's message for it.
fn get_invariant_failure(test: &str, definitions: &str, invariant: &str) -> String {
    let spec = format!(
        "---- MODULE Inv ----\nEXTENDS Naturals, Sequences, TLC\nVARIABLE v\n{definitions}Init == v = 0\nNext == v' = v + 1 /\\ v < 3\nInv == v < 1 \\/ {invariant}\n====\n"
    );
    let (output, directory) = run_front(test, &spec, "INIT Init\nNEXT Next\nINVARIANT Inv\n", &[]);
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(76), "{text}");
    std::fs::remove_dir_all(directory).expect("removed");
    let start = text
        .find("Error: Evaluating invariant Inv failed.\n")
        .expect("the failure");
    let end = text
        .find("Error: The behavior up to this point is:")
        .expect("the trace");
    text[start..end].to_string()
}

#[test]
fn unites_and_compares_sets_and_functions_by_tlc_classes() {
    // `IntervalValue.cup` tests each element of the other set with its own member.
    assert_eq!(
        get_invariant_failure("cup", "", "3 \\in ((1..2) \\cup {\"a\"})"),
        "Error: Evaluating invariant Inv failed.\nAttempted to check if the value:\n\"a\"\nis in the integer interval 1..2\n"
    );
    // `RecordValue.compareTo` fails on a value it can't take as a record, whatever its size.
    assert!(
        get_invariant_failure(
            "record",
            "f == [r \\in {[a |-> i] : i \\in 1..40} |-> 0]\n",
            "f[<<1>>] = 0"
        )
        .contains("Attempted to compare record:\n[a |-> 20]\nwith non-record\n<<1>>")
    );
    // `FcnRcdValue.compareTo` takes the keys of one over an interval as integers.
    assert_eq!(
        get_invariant_failure(
            "interval",
            "g == [r \\in {(\"a\" :> i @@ \"b\" :> 1) : i \\in 1..40} |-> 0]\n",
            "g[<<1, 2>>] = 0"
        ),
        "Error: Evaluating invariant Inv failed.\nAttempted to compare integer with non-integer\n\"a\".\n"
    );
    // A function TLC keeps lazy is the record or the tuple it builds, which it can't over Nat.
    assert_eq!(
        get_invariant_failure("lambda-record", "", "[n \\in Nat |-> n].a = 1"),
        "Error: Evaluating invariant Inv failed.\nAttempted to compute the number of elements in the overridden value Nat.\n"
    );
    assert_eq!(
        get_invariant_failure("lambda-tuple", "", "[n \\in Nat |-> n] \\in Seq(Nat)"),
        "Error: Evaluating invariant Inv failed.\nTo convert a function of form [x \\in S |-> f(x)] to a tuple, the set S must be enumerable.\n"
    );
}

// TLC holds [i \in 0..1 |-> 1] over an interval, whose keys it compares as integers, failing at a
// model value (`FcnRcdValue.compareToInterval` and `equals`), and [i \in {0, 1} |-> 1] over its
// keys, which it compares with the model value without failing. The store can't tell them apart:
// it stops, and the evaluator reports TLC's failure, or finds none and declines.
#[test]
fn compares_functions_over_intervals_with_functions_over_model_values_as_tlc() {
    let unexpected = "Error: TLC threw an unexpected exception.\nThis was probably caused by an error in the spec or model.\nSee the User Output or TLC Console for clues to what happened.\nThe exception was a java.lang.RuntimeException\n: ";
    for (test, init, failure) in [
        (
            "interval",
            "{[i \\in 0..1 |-> 1], [k \\in {m, 0} |-> 1]}",
            Some(format!(
                "{unexpected}Attempted to compare integer with non-integer\nm.\n"
            )),
        ),
        (
            "interval-equality",
            "([i \\in 0..1 |-> 1] = [k \\in {m, 0} |-> 1])",
            Some("Error: Attempted to compare an integer with non-integer:\nm.\n".to_string()),
        ),
        (
            "enumerated",
            "{[i \\in {0, 1} |-> 1], [k \\in {m, 0} |-> 1]}",
            None,
        ),
        // A membership, which the store answers by id only where no comparison can fail, compares
        // and stops: TLC reports these as a FingerprintException, which the evaluator declines.
        (
            "interval-member",
            "([i \\in 0..1 |-> 1] \\in {[k \\in {m, 0} |-> j] : j \\in 1..40})",
            None,
        ),
        (
            "tuple-member",
            "(<<1, 1>> \\in {[k \\in {m, 0} |-> 1]})",
            None,
        ),
    ] {
        let spec = format!(
            "---- MODULE Keys ----\nEXTENDS Integers\nCONSTANT m\nVARIABLE x\nInit == x = {init}\nNext == UNCHANGED x\n====\n"
        );
        let (output, directory) =
            run_front(test, &spec, "CONSTANT m = m\nINIT Init\nNEXT Next\n", &[]);
        let text = stdout(&output);
        std::fs::remove_dir_all(directory).expect("removed");
        assert!(!text.contains("Model checking completed"), "{test}: {text}");
        match failure {
            Some(failure) => assert!(
                text.contains(&format!("Computing initial states...\n{failure}")),
                "{test}: {text}"
            ),
            None => assert!(
                String::from_utf8_lossy(&output.stderr).contains("not native yet"),
                "{test}: {text}"
            ),
        }
    }
}

#[test]
fn compares_model_values_with_lazy_sets_as_tlc() {
    for (model, assumption, expected) in [
        // `SubsetValue.member` fails on any value it can't enumerate, an untyped model value too.
        (
            "m",
            "m \\in SUBSET {1}",
            "of module Lazy failed.\nAttempted to check if the non-enumerable value\nm\nis element of\n{{}, {1}}\n",
        ),
        // `UserValue.equals` compares, which puts any model value first, a typed one too.
        ("A_b", "Nat = m", ")\nFALSE\n"),
    ] {
        let spec = format!(
            "---- MODULE Lazy ----\nEXTENDS TLC, Naturals\nCONSTANT m\nVARIABLE x\nASSUME PrintT({assumption})\nInit == x = 0\nNext == x' = x\n====\n"
        );
        let (output, directory) = run_front(
            "model-lazy",
            &spec,
            &format!("CONSTANT m = {model}\nINIT Init\nNEXT Next\n"),
            &[],
        );
        let text = stdout(&output);
        assert!(text.contains(expected), "{text}");
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

// Runs the binary on a spec of the test's own, where TLC stops before the search.
fn run_spec(test: &str, spec: &str, config: &str) -> (Output, PathBuf) {
    run_spec_with(test, spec, config, &[])
}

fn run_spec_with(test: &str, spec: &str, config: &str, args: &[&str]) -> (Output, PathBuf) {
    let directory =
        std::env::temp_dir().join(format!("prove-it-cli-{test}-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    std::fs::write(directory.join("Stop.tla"), spec).expect("a spec");
    std::fs::write(directory.join("Stop.cfg"), config).expect("a configuration");
    (
        run(&directory, &[args, &["-noTE", "Stop"]].concat()),
        directory,
    )
}

// A counter with a `_PERIODIC` expression, as TLC's ran at d8fb231 with `-workers 1`: TLC
// evaluates the expression just before it prints its progress, about 3 s in, and not at all in a
// run that ends first. A constant-level expression it evaluates once, at startup.
fn periodic_spec(next: &str, periodic: &str) -> String {
    format!(
        "---- MODULE Stop ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == {next}\nPeriodic == {periodic}\n====\n"
    )
}

const PERIODIC_CONFIG: &str = "INIT Init\nNEXT Next\n_PERIODIC Periodic\nCHECK_DEADLOCK FALSE\n";

#[test]
fn prints_a_constant_periodic_expression_at_startup_as_tlc() {
    let spec = periodic_spec("x < 3 /\\ x' = x + 1", "PrintT(\"periodic\")");
    let (output, directory) = run_spec("periodic-constant", &spec, PERIODIC_CONFIG);
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(0), "{text}");
    assert!(
        text.contains(
            "\n\"periodic\"\nComputing initial states...\nFinished computing initial states: 1 distinct state generated at "
        ),
        "{text}"
    );
    assert!(
        text.contains("Model checking completed. No error has been found."),
        "{text}"
    );
    assert!(
        text.contains("4 states generated, 4 distinct states found, 0 states left on queue.\n"),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn completes_where_tlc_ends_before_it_evaluates_the_periodic_expression() {
    for (test, periodic) in [
        (
            "periodic-print",
            "PrintT(<<\"periodic\", TLCGet(\"distinct\")>>)",
        ),
        ("periodic-false", "TLCGet(\"distinct\") < 0"),
    ] {
        let spec = periodic_spec("x < 3 /\\ x' = x + 1", periodic);
        let (output, directory) = run_spec(test, &spec, PERIODIC_CONFIG);
        let text = stdout(&output);
        assert_eq!(output.status.code(), Some(0), "{test}: {text}");
        assert!(!text.contains("\"periodic\""), "{test}: {text}");
        assert!(
            text.contains("Model checking completed. No error has been found."),
            "{test}: {text}"
        );
        assert!(
            text.contains("4 states generated, 4 distinct states found, 0 states left on queue.\n"),
            "{test}: {text}"
        );
        std::fs::remove_dir_all(directory).expect("removed");
    }
}

#[test]
fn declines_where_tlc_would_evaluate_the_periodic_expression() {
    // A search that runs until TLC's first progress, where TLC prints <<"periodic", n>>.
    let spec = periodic_spec(
        "x' = x + 1",
        "PrintT(<<\"periodic\", TLCGet(\"distinct\")>>)",
    );
    let (output, directory) = run_spec("periodic-long", &spec, PERIODIC_CONFIG);
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(1), "{text}");
    assert_eq!(
        String::from_utf8_lossy(&output.stderr),
        "prove-it: not native yet: _PERIODIC, which TLC evaluates as it prints its progress\n"
    );
    assert!(!text.contains("\"periodic\""), "{text}");
    assert!(!text.contains("Progress("), "{text}");
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn reports_a_constant_the_configuration_leaves_unassigned() {
    let spec =
        "---- MODULE Stop ----\nCONSTANT N\nVARIABLE x\nInit == x = N\nNext == x' = x\n====\n";
    let (output, directory) = run_spec("unassigned", spec, "INIT Init\nNEXT Next\n");
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
    let (output, directory) = run_spec("rejected", spec, "INIT Init\n");
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(150), "{text}");
    assert!(
        text.contains(")\nError: Parsing or semantic analysis failed.\nFinished in "),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn reports_the_exception_sanys_generator_throws_as_a_failed_parse() {
    // TLC's tla2sany error corpus, E4294_Module_Test, as TLC at d8fb231 prints it.
    let spec = "---- MODULE Stop ----\nRECURSIVE op\n---- MODULE Inner ----\n====\nop == 0\n====\n";
    let exception = "util.WrongInvocationException: Defined more recursive operators than were declared in RECURSIVE statements.";
    let (output, directory) = run_spec("exception", spec, "");
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(150), "{text}");
    assert!(
        text.contains(&format!("Semantic processing of module Stop\n{exception}\nError: Parsing or semantic analysis failed.Parsing or semantic analysis failed.{exception}\nFinished in ")),
        "{text}"
    );
    assert!(!text.contains("Starting..."), "{text}");
    let tool = Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .args(["-tool", "Stop"])
        .current_dir(&directory)
        .output()
        .expect("the binary runs");
    let text = stdout(&tool);
    assert_eq!(tool.status.code(), Some(150), "{text}");
    assert!(
        text.contains(&format!("{exception}\n@!@!@STARTMSG 2171:1 @!@!@\nParsing or semantic analysis failed.@!@!@STARTMSG 2171:0 @!@!@\nParsing or semantic analysis failed.{exception}\n@!@!@ENDMSG 2171 @!@!@\n@!@!@ENDMSG 2171 @!@!@\n@!@!@STARTMSG 2186:0 @!@!@\nFinished in ")),
        "{text}"
    );
    assert!(!text.contains("SANY finished."), "{text}");
    std::fs::remove_dir_all(directory).expect("removed");
}

// Runs the binary on a spec of the test's own, which tla-front lowers, without the trace
// exploration spec TLC would parse with it.
fn run_lowered(test: &str, spec: &str, config: &str) -> (Output, PathBuf) {
    run_front(test, spec, config, &[])
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
    ] {
        std::fs::write(directory.join(file), contents).expect("a file");
    }
    let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .args(["-noTE", "Stop"])
        .current_dir(&directory)
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
fn declines_what_the_replay_doesnt_follow_of_a_state_tlc_cant_fingerprint() {
    let declines = |test: &str, spec: &str, config: &str, reason: &str| {
        let (output, directory) = run_lowered(test, spec, config);
        let error = String::from_utf8_lossy(&output.stderr).into_owned();
        assert!(error.contains(reason), "{}{error}", stdout(&output));
        std::fs::remove_dir_all(directory).expect("removed");
    };
    // TLC fingerprints an initial state only where the constraints hold of it, and finds no
    // error here.
    declines(
        "constrained-fingerprint",
        "---- MODULE Stop ----\nEXTENDS Integers\nVARIABLES x, y\nInit == \\/ (x = SUBSET (1..31) /\\ y = 0) \\/ (x = 0 /\\ y = 1)\nNext == UNCHANGED <<x, y>>\nC == y = 1\n====\n",
        "INIT Init\nNEXT Next\nCONSTRAINT C\n",
        "a state TLC fingerprints only where its constraints hold",
    );
    // TLC's replay takes all of the action's successors before it fingerprints one, so it
    // reports the assertion that fails after the successor it can't fingerprint.
    declines(
        "fingerprint-then-failure",
        "---- MODULE Stop ----\nEXTENDS Integers, TLC\nVARIABLE x\nInit == x = 0\nNext == x = 0 /\\ \\E i \\in {1, 2} : x' = IF i = 1 THEN SUBSET (1..31) ELSE Assert(FALSE, \"boom\")\n====\n",
        "INIT Init\nNEXT Next\n",
        "an action that fails or prints after a successor TLC can't fingerprint",
    );
}

#[test]
fn declines_a_trace_through_a_set_tlc_streams_in_an_order_of_its_own() {
    let declines = |test: &str, spec: &str, config: &str, reason: &str| {
        let (output, directory) = run_lowered(test, spec, config);
        let error = String::from_utf8_lossy(&output.stderr).into_owned();
        assert!(error.contains(reason), "{}{error}", stdout(&output));
        std::fs::remove_dir_all(directory).expect("removed");
    };
    // TLC prints 33 first: it streams the union in the union's order, not the normalized one.
    declines(
        "streamed-print",
        "---- MODULE Stop ----\nEXTENDS Integers, FiniteSets, TLC\nVARIABLES x, n\nInit == x = {} /\\ n = 0\nNext == n < 2 /\\ x' \\in ((SUBSET {1, 2}) \\cup {{n + 3}}) /\\ PrintT(IF n + 3 \\in x' THEN 33 ELSE Cardinality(x')) /\\ Cardinality(x') = 1 /\\ n' = n + 1\nInv == n < 1\n====\n",
        "INIT Init\nNEXT Next\nINVARIANT Inv\n",
        "an effect under an assignment from a set TLC streams",
    );
    // Under the VIEW TLC keeps the first state it streams, x = {3}, whether a definition or a
    // variable holds the union: the engine declines the second as it starts.
    let reason = "several states TLC may take for the search's under VIEW or SYMMETRY";
    declines(
        "streamed-definition",
        "---- MODULE Stop ----\nEXTENDS Integers, FiniteSets\nVARIABLES x, n\nS == (SUBSET {1, 2}) \\cup {{3}}\nInit == x = {} /\\ n = 0\nNext == n < 3 /\\ x' \\in S /\\ Cardinality(x') = 1 /\\ n' = n + 1\nInv == n < 2\nV == <<n>>\n====\n",
        "INIT Init\nNEXT Next\nINVARIANT Inv\nVIEW V\n",
        reason,
    );
    declines(
        "streamed-variable",
        "---- MODULE Stop ----\nEXTENDS Integers, FiniteSets\nVARIABLES x, n, s\nInit == x = {} /\\ n = 0 /\\ s = (SUBSET {1, 2}) \\cup {{3}}\nNext == n < 3 /\\ x' \\in s /\\ Cardinality(x') = 1 /\\ n' = n + 1 /\\ s' = s\nInv == n < 2\nV == <<n>>\n====\n",
        "INIT Init\nNEXT Next\nINVARIANT Inv\nVIEW V\n",
        "enumerating a lazy set of the state under a VIEW",
    );
}

#[test]
fn exits_as_tlc_does_where_an_atom_fails_adding_a_state() {
    // TLC exits by the error's own status where an atom of a temporal property fails as it adds
    // a state to the behavior graphs: 255 for an EvalException, 14 for a failed assertion. It
    // records no node for the brackets of <<A>>_v, so the call stack starts at A.
    let run = |test: &str, property: &str| {
        let spec = format!(
            "---- MODULE Stop ----\nEXTENDS Integers, TLC\nVARIABLE x\nInit == x = 0\nNext == x' = (x + 1) % 3\nSpec == Init /\\ [][Next]_x /\\ WF_x(Next)\nP == {property}\n====\n"
        );
        let (output, directory) = run_lowered(test, &spec, "SPECIFICATION Spec\nPROPERTY P\n");
        std::fs::remove_dir_all(directory).expect("removed");
        (output.status.code(), stdout(&output))
    };
    let (status, text) = run("atom-division", "[]<>(3 \\div (x - 1) > 0)");
    assert_eq!(status, Some(255), "{text}");
    assert!(
        text.contains("The second argument of \\div is 0."),
        "{text}"
    );
    let (status, text) = run("atom-assert", "[]<>Assert(x # 1, \"atom\")");
    assert_eq!(status, Some(14), "{text}");
    let (status, text) = run(
        "atom-action",
        "[]<><<3 \\div (x - 1) > 0 /\\ x' = x + 1>>_x",
    );
    assert_eq!(status, Some(255), "{text}");
    assert!(
        text.contains("positions:\n0. Line 7, column 12 to line 7, column 43 in Stop\n1. Line 7, column 12 to line 7, column 29 in Stop\n2. Line 7, column 12 to line 7, column 25 in Stop\n"),
        "{text}"
    );
}

#[test]
fn declines_what_it_doesnt_follow_of_the_behavior_graphs() {
    let declines = |test: &str, body: &str, config: &str, arguments: &[&str], reason: &str| {
        let spec = format!("---- MODULE Stop ----\nEXTENDS Naturals, TLC\n{body}\n====\n");
        let directory =
            std::env::temp_dir().join(format!("prove-it-cli-{test}-{}", std::process::id()));
        std::fs::create_dir_all(&directory).expect("a directory");
        std::fs::write(directory.join("Stop.tla"), spec).expect("the spec");
        std::fs::write(directory.join("Stop.cfg"), config).expect("the configuration");
        let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
            .args(["tlc2.TLC", "-noTE", "-workers", "1", "-lncheck", "final"])
            .args(arguments)
            .arg("Stop")
            .current_dir(&directory)
            .output()
            .expect("the binary runs");
        let error = String::from_utf8_lossy(&output.stderr).into_owned();
        assert!(error.contains(reason), "{}{error}", stdout(&output));
        std::fs::remove_dir_all(directory).expect("removed");
    };
    // TLC runs Next again from a state it adds a tableau node of late, so it prints <<"n", 0>>
    // twice before the deadlock.
    declines(
        "late-stop",
        "VARIABLES x\nInit == x = 0\nNext == x < 2 /\\ x' = x + 1 /\\ PrintT(<<\"n\", x>>)\nSpec == Init /\\ [][Next]_x\nProp == [](x # 1 => [](x # 7))",
        "SPECIFICATION Spec\nPROPERTY Prop\n",
        &[],
        "the engine stopped: deadlock",
    );
    // TLC runs it action by action there, with the atoms of each action's successors between.
    declines(
        "late-order",
        "VARIABLES x\nInit == x = 0\nA == x' = 1 - x /\\ PrintT(<<\"a\", x>>)\nB == x' = (x + 2) % 3 /\\ PrintT(<<\"b\", x>>)\nNext == A \\/ B\nSpec == Init /\\ [][Next]_x /\\ SF_x(A)\nProp == [](x # 1 => [](x # 7))",
        "SPECIFICATION Spec\nPROPERTY Prop\n",
        &["-deadlock"],
        "prints it doesn't place in TLC's order",
    );
    // TLC ends this lasso, whose last state is its cycle's first, with "State 3: Stuttering".
    declines(
        "lasso-end",
        "VARIABLES x, y\nvars == <<x, y>>\nInit == x \\in {0, 1} /\\ y = 0\nA0 == x = 1 /\\ y = 0 /\\ x' = 1 /\\ y' \\in {0, 1}\nA1 == x = 1 /\\ x' = 0 /\\ y' = 1\nA2 == x = 1 /\\ y = 0 /\\ x' = 0 /\\ y' = y\nA3 == x = 0 /\\ x' = 1 /\\ y' \\in {0, 0}\nNext == A0 \\/ A1 \\/ A2 \\/ A3\nSpec == Init /\\ [][Next]_vars /\\ WF_vars(Next)\nP0 == []<>(x # 0)\nP1 == []((x = 0) => <>[](y = 1))",
        "SPECIFICATION Spec\nPROPERTY P0\nPROPERTY P1\n",
        &[],
        "a lasso that ends in the first state of its cycle",
    );
}

#[test]
fn prints_the_statistics_where_an_atom_fails_on_the_initial_state() {
    // TLC reports the error with the initial state, then the statistics, and exits 255.
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals\nVARIABLES x\nInit == x = 0\nNext == x' = (x + 1) % 4\nSpec == Init /\\ [][Next]_x /\\ WF_x(Next)\nProp == <>(x = 0 /\\ x[1] = 3)\n====\n";
    let (output, directory) =
        run_lowered("initial-atom", spec, "SPECIFICATION Spec\nPROPERTY Prop\n");
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(255), "{text}");
    assert!(
        text.contains("Error: A non-function (an integer) was applied as a function.\nline 7, col 21 to line 7, col 24 of module Stop\nWhile working on the initial state:\nx = 0\n\n1 states generated, 1 distinct states found, 1 states left on queue.\nThe depth of the complete state graph search is 1.\n"),
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
fn caches_tlccache_by_its_key_alone_as_tlc() {
    // TLC caches a constant expression by its node and its key for the whole run, so bindings the
    // key doesn't tell apart share the value first cached.
    let spec = "---- MODULE Stop ----\nEXTENDS Integers, TLC, TLCExt\nVARIABLE x\nInit == x = [i \\in {0, 1} |-> TLCCache(i, 0)]\nNext == x' = [i \\in {0, 1} |-> TLCCache(i + 1, i)]\nInv == x \\in {(0 :> 0 @@ 1 :> 0), (0 :> 1 @@ 1 :> 2)}\n====\n";
    let (output, directory) =
        run_lowered("cache-key", spec, "INIT Init\nNEXT Next\nINVARIANT Inv\n");
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(0), "{text}");
    assert!(
        text.contains("3 states generated, 2 distinct states found, 0 states left on queue."),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
    // TLC evaluates the key each time, where it fails; and caches nothing of an expression that
    // reads a variable, which the engine can't tell from a constant one that reads it through an
    // operator's argument.
    for (test, definitions) in [
        (
            "cache-violated",
            "Init == x = [i \\in {0, 1} |-> TLCCache(i, 0)]\nNext == x' = x\nInv == x[1] = 1",
        ),
        (
            "cache-key-fails",
            "Init == x = 0\nNext == x' = x\nInv == TLCCache(TRUE, 1 \\div 0)",
        ),
        (
            "cache-argument",
            "F(p) == TLCCache(p + 1, 0)\nInit == x = 0\nNext == x < 3 /\\ x' = x + 1\nInv == F(x) = x + 1",
        ),
        (
            "cache-variable",
            "Init == x = 0\nNext == x < 3 /\\ x' = x + 1\nInv == \\A i \\in {0, 1}: TLCCache(IF FALSE THEN x ELSE i, 0) = i",
        ),
    ] {
        let spec = format!(
            "---- MODULE Stop ----\nEXTENDS Integers, TLC, TLCExt\nVARIABLE x\n{definitions}\n====\n"
        );
        let (output, directory) = run_lowered(
            test,
            &spec,
            "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n",
        );
        let text = stdout(&output);
        assert!(!text.contains("Model checking completed"), "{text}");
        assert!(
            String::from_utf8_lossy(&output.stderr).contains("not native yet"),
            "{test}: {text}"
        );
        std::fs::remove_dir_all(directory).expect("removed");
    }
}

#[test]
fn declines_what_tlc_fails_to_enumerate_where_it_writes_or_reads_a_value() {
    // TLC fails on a function it keeps lazy, or on Nat, where it writes JSON, tests a bag, or
    // reads a register; and on a tuple as a quantifier's bound.
    for (test, definitions, config) in [
        (
            "json-lazy",
            "Init == JsonSerialize(\"out.json\", <<[i \\in Nat |-> i]>>) /\\ x = 0\nNext == x' = x",
            "",
        ),
        (
            "json-nat",
            "Init == \\E s \\in {Nat} : JsonSerialize(\"out.json\", <<s>>) /\\ x = 0\nNext == x' = x",
            "",
        ),
        (
            "bag-lazy",
            "Init == IsABag([i \\in Nat |-> 1]) = FALSE /\\ x = 0\nNext == x' = x",
            "",
        ),
        (
            "register-lazy",
            "Init == x = 0\nNext == x < 3 /\\ x' = x + 1 /\\ TLCSet(1, [i \\in Nat |-> i])\nPost == 3 \\in DOMAIN TLCGet(1)",
            "POSTCONDITION Post\n",
        ),
        (
            "tuple-bound",
            "Init == \\A i \\in <<1>> : x = i\nNext == x' = x",
            "",
        ),
    ] {
        let spec = format!(
            "---- MODULE Stop ----\nEXTENDS Integers, TLC, TLCExt, Json, Bags\nVARIABLE x\n{definitions}\n====\n"
        );
        let (output, directory) =
            run_lowered(test, &spec, &format!("INIT Init\nNEXT Next\n{config}"));
        let text = stdout(&output);
        assert!(!text.contains("Model checking completed"), "{test}: {text}");
        assert!(!text.contains("Error: "), "{test}: {text}");
        assert!(
            String::from_utf8_lossy(&output.stderr).contains("not native yet"),
            "{test}: {text}"
        );
        assert!(!directory.join("out.json").exists(), "{test}");
        std::fs::remove_dir_all(directory).expect("removed");
    }
}

#[test]
fn writes_json_files_as_tlc() {
    // TLC makes a file's directories before it writes it, and reads {} as an empty record, which
    // it writes back as {} where the store would write [].
    let spec = "---- MODULE Stop ----\nEXTENDS Integers, TLC, Json\nVARIABLE x\nInit == JsonSerialize(\"sub/d/o.json\", <<1, \"a\">>) /\\ ndJsonSerialize(\"sub/e/o.ndjson\", <<1, <<2>>>>) /\\ x = 0\nNext == x' = x\n====\n";
    let (output, directory) = run_lowered("json-directories", spec, "INIT Init\nNEXT Next\n");
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(0), "{text}");
    let read = |path: &str| std::fs::read_to_string(directory.join(path)).expect("a file");
    assert_eq!(read("sub/d/o.json"), "[1,\"a\"]");
    assert_eq!(read("sub/e/o.ndjson"), "1\n[2]\n");
    std::fs::remove_dir_all(directory).expect("removed");
    let spec = "---- MODULE Stop ----\nEXTENDS Integers, TLC, Json\nVARIABLE x\nInit == JsonSerialize(\"o.json\", JsonDeserialize(\"i.json\")) /\\ x = 0\nNext == x' = x\n====\n";
    let directory =
        std::env::temp_dir().join(format!("prove-it-cli-json-empty-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    std::fs::write(directory.join("i.json"), "[{}]").expect("the input");
    let (output, directory) = run_lowered("json-empty", spec, "INIT Init\nNEXT Next\n");
    let text = stdout(&output);
    assert!(!text.contains("Model checking completed"), "{text}");
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("an empty JSON object"),
        "{text}"
    );
    assert!(!directory.join("o.json").exists());
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn evaluates_assert_s_message_and_reads_a_file_as_tlc() {
    // TLC evaluates Assert's message even where the assertion holds, as it does any Java
    // method's arguments, printing it again as it rebuilds the trace.
    let spec = "---- MODULE Stop ----\nEXTENDS Integers, TLC\nVARIABLE x\nInit == x = 0 /\\ Assert(TRUE, PrintT(\"msg\"))\nNext == x < 1 /\\ x' = x + 1\n====\n";
    let (output, directory) = run_lowered("assert-message", spec, "INIT Init\nNEXT Next\n");
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(11), "{text}");
    assert_eq!(text.matches("\"msg\"\n").count(), 3, "{text}");
    std::fs::remove_dir_all(directory).expect("removed");
    // TLC reads the file again at each use where it didn't compute the read at startup, which
    // the engine leaves to its caller rather than reading a value it kept.
    for (test, read) in [
        ("read-again", "JsonDeserialize(\"r.json\")[1]"),
        ("read-let", "LET r == JsonDeserialize(\"r.json\") IN r[1]"),
        ("read-defined", "Read[1]"),
    ] {
        let spec = format!(
            "---- MODULE Stop ----\nEXTENDS Integers, TLC, Json\nVARIABLE x\nRead == JsonDeserialize(\"r.json\")\nInit == JsonSerialize(\"r.json\", <<0>>) /\\ x = 0\nNext == JsonSerialize(\"r.json\", <<x + 1>>) /\\ x' = {read}\nInv == x < 2\n====\n"
        );
        let (output, directory) = run_lowered(test, &spec, "INIT Init\nNEXT Next\nINVARIANT Inv\n");
        let text = stdout(&output);
        assert!(!text.contains("Model checking completed"), "{test}: {text}");
        assert!(
            String::from_utf8_lossy(&output.stderr).contains("not native yet"),
            "{test}: {text}"
        );
        std::fs::remove_dir_all(directory).expect("removed");
    }
}

#[test]
fn declines_to_fingerprint_what_tlc_fails_to() {
    // TLC fails to fingerprint a function over Nat or Int it keeps lazy, and Nat, Int or STRING,
    // at any depth: TLCFP of one fails, and so does a state or a VIEW that holds one.
    for (test, definitions, config) in [
        (
            "fp-lazy",
            "Init == x = TLCFP([i \\in Nat |-> i])\nNext == x' = x\nInv == x = TLCFP(<<>>)",
            "INVARIANT Inv\n",
        ),
        (
            "fp-nested",
            "Init == x = 0\nNext == x' = x\nInv == TLCFP(<<1, [r |-> [i \\in Int |-> i]]>>) = x",
            "INVARIANT Inv\n",
        ),
        (
            "fp-set",
            "Init == x = 0\nNext == x' = x\nInv == TLCFP({Nat}) = x",
            "INVARIANT Inv\n",
        ),
        (
            "fp-view",
            "Init == x \\in 0..1\nNext == x' = x\nV == [i \\in Int |-> x]",
            "VIEW V\n",
        ),
    ] {
        let spec = format!(
            "---- MODULE Stop ----\nEXTENDS Integers, TLC, TLCExt\nVARIABLE x\n{definitions}\n====\n"
        );
        let (output, directory) =
            run_lowered(test, &spec, &format!("INIT Init\nNEXT Next\n{config}"));
        let text = stdout(&output);
        assert!(!text.contains("Model checking completed"), "{text}");
        assert!(!text.contains("is equal to FALSE"), "{text}");
        assert!(
            String::from_utf8_lossy(&output.stderr).contains(
                "unsupported: fingerprinting a function TLC keeps lazy, or Nat, Int or STRING"
            ),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        std::fs::remove_dir_all(directory).expect("removed");
    }
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
fn keeps_the_domain_a_lazy_function_was_built_over() {
    // TLC evaluates the operands of a domain it keeps lazy as it builds the function, so the
    // domains are Seq({0}) and Nat \ {0}, which the register written after doesn't change; the
    // engine stops rather than test them against the register as it is then.
    for (test, function, key) in [
        ("domain-seq", "[i \\in Seq(TLCGet(0)) |-> 1]", "<<1>>"),
        (
            "domain-difference",
            "[i \\in Nat \\ {TLCGet(0) + 0} |-> 1]",
            "0",
        ),
    ] {
        let set = if test == "domain-seq" { "{0}" } else { "0" };
        let written = if test == "domain-seq" { "{1}" } else { "5" };
        let spec = format!(
            "---- MODULE Stop ----\nEXTENDS Integers, Sequences, TLC\nVARIABLE x\nInit == TLCSet(0, {set}) /\\ x = (\\E f \\in {{{function}}} : TLCSet(0, {written}) /\\ f[{key}] = 1)\nNext == x' = x\n====\n"
        );
        let (output, directory) = run_lowered(test, &spec, "INIT Init\nNEXT Next\n");
        assert!(
            !stdout(&output).contains("No error has been found"),
            "{}",
            stdout(&output)
        );
        std::fs::remove_dir_all(directory).expect("removed");
    }
    // The body is evaluated as the function is applied, and reads the register then.
    let spec = "---- MODULE Stop ----\nEXTENDS Integers, TLC\nVARIABLE x\nInit == TLCSet(0, 0) /\\ x = (\\E f \\in {[i \\in Nat |-> TLCGet(0)]} : TLCSet(0, 5) /\\ f[0] = 5)\nNext == x' = x\nInv == x\n====\n";
    let (output, directory) =
        run_lowered("domain-body", spec, "INIT Init\nNEXT Next\nINVARIANT Inv\n");
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(0), "{text}");
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn evaluates_a_lazy_functions_domain_as_tlc_builds_it() {
    // TLC evaluates the domain's parts as it builds the function, applied or not: Seq(S), a
    // difference with Nat, SUBSET Seq(S) and a union with Int fail there. The predicate of a
    // filter of Nat waits until a key is tested, so that function builds.
    for (test, domain) in [
        ("domain-fail-seq", "Seq({1 \\div 0})"),
        ("domain-fail-difference", "Nat \\ {1 \\div 0}"),
        ("domain-fail-subset", "SUBSET Seq({1 \\div 0})"),
        ("domain-fail-union", "Int \\cup {1 \\div 0}"),
    ] {
        let spec = format!(
            "---- MODULE Stop ----\nEXTENDS Integers, Sequences\nVARIABLE x\nInit == x = (\\E f \\in {{[i \\in {domain} |-> 1]}} : TRUE)\nNext == UNCHANGED x\nInv == x\n====\n"
        );
        let (output, directory) = run_lowered(test, &spec, "INIT Init\nNEXT Next\nINVARIANT Inv\n");
        let text = stdout(&output);
        assert_eq!(output.status.code(), Some(75), "{text}");
        assert!(
            text.contains("\nError: The second argument of \\div is 0.\n"),
            "{text}"
        );
        std::fs::remove_dir_all(directory).expect("removed");
    }
    let spec = "---- MODULE Stop ----\nEXTENDS Integers\nVARIABLE x\nInit == x = (\\E f \\in {[i \\in {n \\in Nat : 1 \\div 0 = n} |-> 1]} : TRUE)\nNext == UNCHANGED x\nInv == x\n====\n";
    let (output, directory) = run_lowered(
        "domain-lazy-predicate",
        spec,
        "INIT Init\nNEXT Next\nINVARIANT Inv\n",
    );
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(0), "{text}");
    std::fs::remove_dir_all(directory).expect("removed");
    // A key outside a tuple pattern's domain over Nat \X Nat, which TLC reports without
    // enumerating the product: the run must not word it as an enumeration.
    let spec = "---- MODULE Stop ----\nEXTENDS Integers\nVARIABLE x\nInit == x = [<<i, j>> \\in Nat \\X Nat |-> i - j][<<5, -2>>]\nNext == UNCHANGED x\n====\n";
    let (output, directory) = run_lowered("domain-tuple", spec, "INIT Init\nNEXT Next\n");
    assert!(
        !stdout(&output).contains("Attempted to enumerate"),
        "{}",
        stdout(&output)
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn tests_a_typed_model_value_against_a_lazy_domain_as_tlc_does() {
    // TLC fails to test a typed model value for membership in Nat, in DOMAIN of a function it
    // keeps lazy as anywhere, where an untyped one is simply not in it. The run stops there and
    // must not find x FALSE.
    let spec = "---- MODULE Stop ----\nEXTENDS Integers\nCONSTANTS Ma, Mu\nVARIABLE x\nInit == x = (Ma \\in DOMAIN [i \\in Nat |-> 1])\nNext == UNCHANGED x\n====\n";
    let (output, directory) = run_lowered(
        "typed-domain",
        spec,
        "CONSTANTS Ma = a_a\nCONSTANTS Mu = Mu\nINIT Init\nNEXT Next\n",
    );
    let text = stdout(&output);
    assert!(!text.contains("No error has been found"), "{text}");
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("a mistyped membership in Nat"),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    std::fs::remove_dir_all(directory).expect("removed");
    // A failing test of a domain TLC built of other sets is reported as a value TLC can't
    // fingerprint, which the run declines rather than word otherwise.
    let spec = "---- MODULE Stop ----\nEXTENDS Integers\nVARIABLE x\nInit == x = ([i \\in Nat \\ {0} |-> 1][\"s\"])\nNext == UNCHANGED x\n====\n";
    let (output, directory) = run_lowered("typed-composite", spec, "INIT Init\nNEXT Next\n");
    let text = stdout(&output);
    assert!(
        !text.contains("The error occurred when TLC was evaluating the nested"),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn keeps_a_definitions_value_as_tlc_does() {
    // TLC evaluates a LET definition or an argument once, at its first use, and keeps the value
    // (`LazyValue`), so `a` is 0 both times though TLCSet writes the register between its uses.
    // The engine evaluates it at each use: it stops there, and must not print <<0, TRUE, 7>>.
    let spec = "---- MODULE Stop ----\nEXTENDS TLC\nVARIABLE x\nInit == TLCSet(1, 0) /\\ x = (LET a == TLCGet(1) IN <<a, TLCSet(1, 7), a>>) /\\ PrintT(x)\nNext == x' = x\n====\n";
    let (output, directory) = run_lowered("kept-value", spec, "INIT Init\nNEXT Next\n");
    assert!(
        !stdout(&output).contains("<<0, TRUE, 7>>"),
        "{}",
        stdout(&output)
    );
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("reads a register"),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    std::fs::remove_dir_all(directory).expect("removed");
    // Where nothing writes a register between the uses, each gives TLC's value: Max reads S twice.
    let spec = "---- MODULE Stop ----\nEXTENDS Integers, TLC\nVARIABLE x\nMax(S) == CHOOSE m \\in S : \\A y \\in S : m >= y\nInit == TLCSet(1, 3) /\\ x = Max({1, TLCGet(1)}) /\\ PrintT(x)\nNext == x' = x\n====\n";
    let (output, directory) = run_lowered("kept-alike", spec, "INIT Init\nNEXT Next\n");
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(0), "{text}");
    assert!(text.contains("\n3\n"), "{text}");
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn reports_an_assumption_after_the_registers_the_ones_before_set() {
    // The assumption the engine leaves to the trace evaluator reads the register the first one
    // set, and fails as TLC reports.
    let spec = "---- MODULE Stop ----\nEXTENDS Integers, TLC\nVARIABLE x\nASSUME TLCSet(1, 5)\nASSUME LET a == TLCGet(1) IN a \\div (a - 5) = a\nInit == x = 0\nNext == x' = x\n====\n";
    let (output, directory) = run_lowered("assumed-register", spec, "INIT Init\nNEXT Next\n");
    let text = stdout(&output);
    assert!(
        text.contains("failed.\nThe second argument of \\div is 0.\n"),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn binds_several_bounds_in_tlcs_order() {
    // TLC evaluates each bound's set once, in the order written, then binds the first bound
    // fastest (`Tool.contexts`, `ContextEnumerator`): Inv is FALSE at <<2, 1>> before it fails to
    // evaluate at <<1, 2>>, whichever way the sets are written.
    for (test, bounds) in [
        ("bound-order", "a \\in {1, 2}, b \\in {1, 2 + x}"),
        ("bound-order-shared", "a, b \\in 1..(2 + x)"),
    ] {
        let spec = format!(
            "---- MODULE Stop ----\nEXTENDS Integers\nVARIABLE x\nInit == x = 0\nNext == x' = x\nInv == \\A {bounds} : ~(a = 2 /\\ b = 1) /\\ (a = 1 /\\ b = 2 => 1 \\div 0 = 0)\n====\n"
        );
        let (output, directory) = run_lowered(test, &spec, "INIT Init\nNEXT Next\nINVARIANT Inv\n");
        let text = stdout(&output);
        assert_eq!(output.status.code(), Some(12), "{text}");
        assert!(
            text.contains("Error: Invariant Inv is violated by the initial state:\nx = 0\n"),
            "{text}"
        );
        std::fs::remove_dir_all(directory).expect("removed");
    }
    // The first set sets the register the second reads, so b = 1 and x is TRUE.
    let spec = "---- MODULE Stop ----\nEXTENDS TLC, TLCExt\nVARIABLE x\nInit == /\\ TLCSet(0, {0}) /\\ x = (\\E a \\in {TLCCache(TLCSet(0, {1}), 0)}, b \\in TLCCache(TLCGet(0), 1) : b = 1)\nNext == x' = x\nInv == x = FALSE\n====\n";
    let (output, directory) = run_lowered(
        "bound-register",
        spec,
        "INIT Init\nNEXT Next\nINVARIANT Inv\n",
    );
    let text = stdout(&output);
    assert!(!text.contains("No error has been found"), "{text}");
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn tests_the_domain_of_a_function_tlc_keeps_lazy_as_it_was_built() {
    // TLC tests the domain as it applies the function, in the context the function was built in
    // (`FcnLambdaValue.apply`), where a filter's predicate reads k, and tests Seq(S) and a union
    // with Nat as they are.
    let spec = "---- MODULE Stop ----\nEXTENDS Integers, Sequences\nVARIABLE x\nF == [k \\in {0, 1} |-> [i \\in {n \\in Nat : n < k} |-> i + k]]\nLengths == [s \\in Seq({1}) |-> Len(s)]\nWide == [n \\in Nat \\cup {-1} |-> n]\nInit == x = 0\nNext == x < 2 /\\ x' = x + 1\nInv == F[1][0] = 1 /\\ ~(0 \\in DOMAIN F[0]) /\\ 0 \\in DOMAIN F[1] /\\ Lengths[<<1, 1>>] = 2 /\\ Wide[-1] = -1 /\\ \\A k \\in {1} : LET g == [i \\in {n \\in Nat : n < k + x} |-> i] IN g[x] = x\n====\n";
    let (output, directory) = run_lowered(
        "lazy-domain",
        spec,
        "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\nINVARIANT Inv\n",
    );
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(0), "{text}");
    assert!(
        text.contains("3 states generated, 3 distinct states found, 0 states left on queue."),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
    // Op(3)[0] tests its domain by applying Op(2)[0], whose domain is the same filter with other
    // values of n and k, and then reads n and k again: each application restores them.
    let spec = "---- MODULE Stop ----\nEXTENDS Integers\nVARIABLE x\nRECURSIVE Op(_)\nOp(k) == [i \\in {n \\in Nat : k = 0 \\/ (n < k /\\ Op(k - 1)[n] = n + k - 1)} |-> i + k]\nInit == x = 0\nNext == x' = x\nInv == Op(2)[0] = 2 /\\ Op(3)[0] = 3 /\\ ~(5 \\in DOMAIN Op(2)) /\\ ~(1 \\in DOMAIN Op(1)) /\\ x = 0\n====\n";
    let (output, directory) = run_lowered(
        "lazy-reentered",
        spec,
        "INIT Init\nNEXT Next\nINVARIANT Inv\n",
    );
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(0), "{text}");
    assert!(
        text.contains("2 states generated, 1 distinct states found, 0 states left on queue."),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
    // F[0] has an empty domain, which TLC reports applying; the engine stops there, and TLC fails
    // to compare a lazy function even with itself, or a record that holds one. No run may report
    // success.
    for (test, init, reason) in [
        (
            "lazy-outside",
            "F[0][0]",
            "applied a function outside its domain",
        ),
        (
            "lazy-itself",
            "LET g == F[1] IN g = g",
            "comparing a function TLC keeps lazy",
        ),
        (
            "lazy-record",
            "([a |-> F[1], b |-> 1] = [a |-> F[1], b |-> 2])",
            "comparing a function TLC keeps lazy",
        ),
    ] {
        let spec = format!(
            "---- MODULE Stop ----\nEXTENDS Integers\nVARIABLE x\nF == [k \\in {{0, 1}} |-> [i \\in {{n \\in Nat : n < k}} |-> i]]\nInit == x = {init}\nNext == x' = x\n====\n"
        );
        let (output, directory) = run_lowered(test, &spec, "INIT Init\nNEXT Next\n");
        let text = stdout(&output);
        assert!(!text.contains("No error has been found"), "{text}");
        assert!(
            String::from_utf8_lossy(&output.stderr).contains(reason),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        std::fs::remove_dir_all(directory).expect("removed");
    }
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
    ] {
        std::fs::write(directory.join(format!("Stop.{extension}")), contents).expect("a file");
    }
    let output = run(&directory, &["-noTE", "Stop"]);
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
    // TLC's first rebuild doesn't walk the initial predicate of a trace of two states, and no
    // rebuild evaluates the constraints: only the search and the second rebuild, for the
    // postcondition, set the register there.
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
    // TLC builds a safety violation's counterexample from the ALIAS of each state.
    let aliased = spec
        .replace("Inv ==", "Al == [x |-> x, z |-> 0]\nInv ==")
        .replace("CounterExample.action", "CounterExample.state");
    let (output, aliased_directory) = run_lowered(
        "counterexample-alias",
        &aliased,
        "INIT Init\nNEXT Next\nINVARIANT Inv\nPOSTCONDITION Post\nALIAS Al\n",
    );
    let text = stdout(&output);
    assert!(
        text.contains("{<<1, [x |-> 0, z |-> 0]>>, <<2, [x |-> 1, z |-> 0]>>}\n"),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
    std::fs::remove_dir_all(aliased_directory).expect("removed");
}

#[test]
fn declines_a_postcondition_after_an_initial_states_violation() {
    // TLC checks the postconditions after an initial state violates an invariant, with counts of
    // the initial states the binary doesn't follow (TLC prints <<"post", 2>> here).
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x \\in {0, 1}\nNext == x' = x + 1\nInv == x < 1\nPost == PrintT(<<\"post\", TLCGet(\"distinct\")>>)\n====\n";
    let (output, directory) = run_lowered(
        "initial-post",
        spec,
        "INIT Init\nNEXT Next\nINVARIANT Inv\nPOSTCONDITION Post\n",
    );
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("a POSTCONDITION after an initial state's violation"),
        "{}",
        stdout(&output)
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn exits_by_the_code_of_an_evalexception_in_the_next_states() {
    // TLC's replay of the expansion exits by the EvalException's code: a general error, 255, for
    // a division by zero, after the trace and the call stack.
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x' = (IF x = 1 THEN 1 % 0 ELSE x + 1)\n====\n";
    let (output, directory) = run_lowered("eval-exit", spec, "INIT Init\nNEXT Next\n");
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(255), "{text}");
    assert!(
        text.contains(
            "Error: The behavior up to this point is:\nState 1: <Initial predicate>\nx = 0\n"
        ),
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
    ] {
        std::fs::write(directory.join(format!("Stop.{extension}")), contents).expect("a file");
    }
    let output = run(&directory, &["-noTE", "Stop"]);
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
    for (file, contents) in [("D.tla", spec), ("D.cfg", "INIT Init\nNEXT Next\n")] {
        std::fs::write(directory.join(file), contents).expect("a file");
    }
    let output = run(&directory, &["-noTE", "-workers", "1", "D"]);
    let text = stdout(&output);
    // As TLC prints it: the EvalException's message after the expansion's print, the trace, the
    // replay's print and the call stack, exiting by the EvalException's code (255, as TLC
    // d8fb231 exits).
    assert_eq!(output.status.code(), Some(255), "{text}");
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
    ] {
        std::fs::write(directory.join(file), contents).expect("a file");
    }
    let output = run(&directory, &["-noTE", "-workers", "1", "P"]);
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
    for (extension, contents) in [("tla", spec), ("cfg", "INIT Init\nNEXT Next\n")] {
        std::fs::write(directory.join(format!("Stop.{extension}")), contents).expect("a file");
    }
    let output = run(&directory, &["-noTE", "Stop"]);
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

// Runs the binary on a spec of its own, without the trace exploration spec TLC would parse.
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
        .output()
        .expect("the binary runs");
    (output, directory)
}

// tests/liveness-failures: x' \in S or x' \subseteq S beside x' = a \/ x' = b, where TLC fails
// evaluating WF_x(Next) or WF_x(Alias), Alias == Next, as it adds a state to the behavior graphs.
// Where the subscript's two values fail to compare (`LNAction.eval` compares them outside any
// evaluation), TLC prints no nested expressions; where an element of x' fails S's own `member` in
// `isSubsetEq` and S has a source, TLC throws a FingerprintException, whose message it doesn't
// print, which the engine declines as it does other FingerprintExceptions. TLC's output for each
// at d8fb231 is beside it.
#[test]
fn reports_failures_in_the_temporal_properties_as_tlc() {
    let declined = [
        "MFunctionsSubseteqEmptyWrap",
        "MFunctionsSubseteqWrap",
        "MProductSubseteqEmptyWrap",
        "MRecordsSubseteqEmptyWrap",
    ];
    let directory =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/liveness-failures");
    let mut names: Vec<String> = std::fs::read_dir(&directory)
        .expect("the specs")
        .filter_map(|entry| {
            let path = entry.expect("an entry").path();
            (path.extension()? == "tla").then(|| path.file_stem()?.to_str().map(String::from))?
        })
        .collect();
    names.sort();
    assert_eq!(names.len(), 9);
    for name in names {
        let spec = std::fs::read_to_string(directory.join(format!("{name}.tla"))).expect("a spec");
        let constant = if name.contains("Empty") {
            "{}"
        } else {
            "{1, 3}"
        };
        for (specification, suffix) in [("Weak", ""), ("AliasWeak", ".alias")] {
            let tlc = std::fs::read_to_string(directory.join(format!("{name}{suffix}.txt")))
                .expect("TLC's output");
            for workers in ["1", "4"] {
                let config = format!(
                    "CONSTANT C = {constant}\nSPECIFICATION {specification}\nPROPERTY Live\n"
                );
                let test = format!("failures-{name}-{specification}-{workers}");
                let args = [
                    "-workers",
                    workers,
                    "-nowarning",
                    "-seed",
                    "4",
                    "-fp",
                    "0",
                    "-lncheck",
                    "final",
                ];
                let (output, run) = run_front(&test, &spec, &config, &args);
                let text = stdout(&output);
                let error = String::from_utf8_lossy(&output.stderr).into_owned();
                if declined.contains(&name.as_str()) {
                    assert!(
                        error.contains("prove-it: not native yet: "),
                        "{name} {specification} {workers}: {text}{error}"
                    );
                } else {
                    assert_eq!(
                        get_untimed(&text),
                        tlc,
                        "{name} {specification} {workers}: {error}"
                    );
                }
                std::fs::remove_dir_all(run).expect("removed");
            }
        }
    }
}

// What a run printed from `Starting...` to `Finished in`, but the lines that tell the time.
fn get_untimed(text: &str) -> String {
    let start = text.find("Starting... (").expect("the start");
    let end = text.find("Finished in ").expect("the end");
    text[start..end]
        .lines()
        .skip(1)
        .filter(|line| {
            ![
                "Finished computing initial states",
                "Progress(",
                "Checking ",
                "Finished checking temporal properties",
            ]
            .iter()
            .any(|prefix| line.starts_with(prefix))
        })
        .map(|line| format!("{line}\n"))
        .collect()
}

const NEXT_FAIR: &str = "---- MODULE NextFair ----\nEXTENDS Naturals\nVARIABLE x\nInc == x < 2 /\\ x' = x + 1\nTwice == x = 0 /\\ x' = 1\nBack == x > 0 /\\ x' = 0\nNext == Inc \\/ Twice \\/ Back\nWeak == x = 0 /\\ [][Next]_x /\\ WF_x(Next)\nStrong == x = 0 /\\ [][Next]_x /\\ SF_x(Next)\nReach == <>(x = 2)\nLive == []<>(x = 0)\nStable == <>[](x = 2)\n====\n";

const NEXT_MIXED: &str = "---- MODULE Mixed ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nA == x' = \"a\" /\\ FALSE\nB == x' = (x + 1) % 3\nNext == A \\/ B\nSpec == Init /\\ [][Next]_x /\\ WF_x(Next)\nLive == []<>(x = 2)\n====\n";

const NEXT_PIECES: &str = "---- MODULE Pieces ----\nEXTENDS Naturals\nVARIABLES x, y\nvars == <<x, y>>\nInit == x = 0 /\\ y = 0\nA == x' = (x + 1) % 3 /\\ y' = y\nB == x' = (x + 1) % 3 /\\ UNCHANGED y\nC == y' = 1 - y /\\ UNCHANGED x\nD == x' = 2 /\\ y' = y\nNext == A \\/ B \\/ C\nSubSpec == Init /\\ [][Next]_vars /\\ WF_vars(B)\nOtherSpec == Init /\\ [][Next]_vars /\\ WF_vars(D)\nLive == []<>(x = 2)\n====\n";

#[test]
fn answers_fairness_of_the_next_state_relation_as_tlc() {
    // TLC's output on each, at d8fb231. The engine answers <<Next>>_x of each step from the
    // search's steps, which hold of Next, where no comparison of TLC's predicate evaluation can
    // fail: under WF and SF, with a successor two disjuncts take and a step to a state seen
    // before. Where x' = "a" may be compared with an integer, as TLC does and fails, it evaluates;
    // and an action that is part of Next, or not of it, is evaluated as before.
    let same = NEXT_MIXED
        .replace("MODULE Mixed", "MODULE Same")
        .replace("\"a\"", "7");
    let other = NEXT_PIECES.replace("MODULE Pieces", "MODULE Other");
    let cases = [
        (
            NEXT_FAIR.to_string(),
            "SPECIFICATION Weak\nPROPERTY Live Reach\n",
            include_str!("next-fair-weak.txt"),
        ),
        (
            NEXT_FAIR.replace("MODULE NextFair", "MODULE NextStrong"),
            "SPECIFICATION Strong\nPROPERTY Live Stable\n",
            include_str!("next-fair-strong.txt"),
        ),
        (
            NEXT_MIXED.to_string(),
            "SPECIFICATION Spec\nPROPERTY Live\n",
            include_str!("next-fair-mixed.txt"),
        ),
        (
            same,
            "SPECIFICATION Spec\nPROPERTY Live\n",
            include_str!("next-fair-same.txt"),
        ),
        (
            NEXT_PIECES.to_string(),
            "SPECIFICATION SubSpec\nPROPERTY Live\n",
            include_str!("next-fair-part.txt"),
        ),
        (
            other,
            "SPECIFICATION OtherSpec\nPROPERTY Live\n",
            include_str!("next-fair-other.txt"),
        ),
        // Init assigns from sets the guard doesn't cover, which TLC's predicate evaluation of
        // Next never tests: the steps still answer.
        (
            "---- MODULE InitUncovered ----\nEXTENDS Naturals\nVARIABLE x\nInit == x \\in ([a : {}] \\cup {0}) \\cup {y \\in {1, 2} : y > 1}\nNext == x' = (x + 1) % 3\nSpec == Init /\\ [][Next]_x /\\ WF_x(Next)\nReach == <>(x = 5)\n====\n".to_string(),
            "SPECIFICATION Spec\nPROPERTY Reach\n",
            include_str!("next-fair-init.txt"),
        ),
    ];
    for (position, (spec, config, expected)) in cases.iter().enumerate() {
        for workers in ["1", "4"] {
            let test = format!("next-fair-{position}-{workers}");
            let (output, directory) = run_front(&test, spec, config, &["-workers", workers]);
            let text = stdout(&output);
            assert_eq!(get_untimed(&text), *expected, "{text}");
            std::fs::remove_dir_all(directory).expect("removed");
        }
    }
}

#[test]
fn evaluates_the_next_state_relation_where_a_walk_assigned_from_a_set_it_cant_cover() {
    // TLC fails testing x' \in S of a value as it evaluates WF_x(Next) on a step another disjunct
    // took, where S is empty, as [a : {}] is, or holds an empty part, as [a : {}] \cup {1} and
    // SUBSET [a : {}] do, or is the base of x' \subseteq S: the walk joined no shape TLC tests the
    // value against. So the engine
    // evaluates the action, and leaves TLC's failure to the interpreter. TLC's output at d8fb231.
    let cases = [
        (
            include_str!("empty/EmptyRecords.tla"),
            include_str!("empty/EmptyRecords.cfg"),
            include_str!("empty/EmptyRecords.txt"),
        ),
        (
            include_str!("empty/UnionEmpty.tla"),
            include_str!("empty/UnionEmpty.cfg"),
            include_str!("empty/UnionEmpty.txt"),
        ),
        (
            include_str!("empty/SubsetEmpty.tla"),
            include_str!("empty/SubsetEmpty.cfg"),
            include_str!("empty/SubsetEmpty.txt"),
        ),
        (
            include_str!("empty/SubseteqEmpty.tla"),
            include_str!("empty/SubseteqEmpty.cfg"),
            include_str!("empty/SubseteqEmpty.txt"),
        ),
    ];
    for (spec, config, expected) in cases {
        for workers in ["1", "4"] {
            let name = spec.split_whitespace().nth(2).expect("the module's name");
            let test = format!("empty-{name}-{workers}");
            let args = [
                "-workers",
                workers,
                "-nowarning",
                "-seed",
                "4",
                "-fp",
                "0",
                "-lncheck",
                "final",
            ];
            let (output, directory) = run_front(&test, spec, config, &args);
            let text = stdout(&output);
            let is_declined =
                String::from_utf8_lossy(&output.stderr).contains("prove-it: not native yet: ");
            assert!(is_declined || get_untimed(&text) == expected, "{text}");
            std::fs::remove_dir_all(directory).expect("removed");
        }
    }
}

// tests/membership-grid: x' \in S beside x' = a \/ x' = b, under WF_x(Next), which the engine
// answers from the steps the search took where the guard lets it, and WF_x(Alias) with
// Alias == Next, which it evaluates. S is each of an enumeration, an interval, records, functions,
// a product, SUBSET, a filter, a map, a union, a constant and a definition, with a part empty and
// not, nested in x' \in S, x' \in S \cup {7}, x' \subseteq S, [{1} -> S], [a : S], S \X {1} and a
// filter; a and b are 0 and 1, values of S's elements' kind, or integers in the nesting's shape.
// And Init x \in S \cup {a} for each S, with Next x' = a \/ x' = b: TLC's predicate evaluation of
// Next never tests the sets Init assigns from, so those leave the shortcut on. TLC's output on
// each formulation at d8fb231 is beside it: each run prints it exactly, or both formulations
// decline.
#[test]
fn answers_fairness_of_next_as_tlc_whatever_set_a_walk_assigns_from() {
    let directory = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/membership-grid");
    let mut names: Vec<String> = std::fs::read_dir(&directory)
        .expect("the grid")
        .filter_map(|entry| {
            let path = entry.expect("an entry").path();
            (path.extension()? == "tla").then(|| path.file_stem()?.to_str().map(String::from))?
        })
        .collect();
    names.sort();
    assert_eq!(names.len(), 418);
    for name in names {
        let spec = std::fs::read_to_string(directory.join(format!("{name}.tla"))).expect("a spec");
        let constant = if name.contains("Empty") {
            "{}"
        } else {
            "{1, 3}"
        };
        for workers in ["1", "4"] {
            let mut declines = Vec::new();
            for (specification, suffix) in [("Weak", ""), ("AliasWeak", ".alias")] {
                let tlc = std::fs::read_to_string(directory.join(format!("{name}{suffix}.txt")))
                    .expect("TLC's output");
                let config = format!(
                    "CONSTANT C = {constant}\nSPECIFICATION {specification}\nPROPERTY Live\n"
                );
                let test = format!("grid-{name}-{specification}-{workers}");
                let args = [
                    "-workers",
                    workers,
                    "-nowarning",
                    "-seed",
                    "4",
                    "-fp",
                    "0",
                    "-lncheck",
                    "final",
                ];
                let (output, run) = run_front(&test, &spec, &config, &args);
                let is_declined =
                    String::from_utf8_lossy(&output.stderr).contains("prove-it: not native yet: ");
                if !is_declined {
                    assert_eq!(
                        get_untimed(&stdout(&output)),
                        tlc,
                        "{name} {specification} {workers}"
                    );
                }
                declines.push(is_declined);
                std::fs::remove_dir_all(run).expect("removed");
            }
            assert_eq!(declines[0], declines[1], "{name} at {workers} workers");
        }
    }
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
fn prints_what_tlc_prints_as_it_starts() {
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
    for (file, contents) in [("Stop.tla", spec), ("Stop.cfg", config)] {
        std::fs::write(directory.join(file), contents).expect("a file");
    }
    let output = run(&directory, &["-noTE", "-deadlock", "Stop"]);
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
fn declines_a_search_that_prints_a_value_as_tlc_built_it() {
    // TLC prints 1..2 as written, which the store forgets. The search, which never ends, stops
    // once the print is known to differ, on one thread and on several.
    let spec = "---- MODULE Misprinted ----\nEXTENDS TLC, Naturals\nVARIABLE x\nInit == x = 0\nNext == x' = x + 1 /\\ PrintT(1..2)\n====\n";
    let directory =
        std::env::temp_dir().join(format!("prove-it-cli-misprinted-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    std::fs::write(directory.join("Misprinted.tla"), spec).expect("the spec");
    std::fs::write(directory.join("Misprinted.cfg"), "INIT Init\nNEXT Next\n")
        .expect("the configuration");
    for workers in ["1", "4"] {
        let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
            .args(["-noGenerateSpecTE", "-workers", workers, "Misprinted"])
            .current_dir(&directory)
            .output()
            .expect("the binary runs");
        assert_eq!(output.status.code(), Some(1), "{}", stdout(&output));
        assert_eq!(
            String::from_utf8_lossy(&output.stderr),
            "prove-it: not native yet: printing a value whose text depends on how TLC built it\n"
        );
    }
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn prints_an_assumption_value_as_tlc_built_it() {
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

#[test]
fn labels_a_step_of_a_next_state_relation_that_instantiates_in_a_let() {
    // test-model/CyclicRedefineInstance: TLC splits B!Next, which the LET's INSTANCE defines,
    // into its body, and labels the step of the other disjunct.
    let (output, directory) = run_front(
        "let-instance",
        "---- MODULE CyclicRedefineInstance ----\nEXTENDS Base\n\nReDefNext ==\n\tLET B == INSTANCE Base\n\tIN \\/ B!Next\n\t   \\/ x' = TRUE\n=====\n----- MODULE Base -----\nVARIABLE x\n\nNext ==\n    x' = FALSE\n\nSpec ==\n\tx = FALSE /\\ [][Next]_x\n\nInv ==\n\tx = FALSE\n====\n",
        "SPECIFICATION Spec\nINVARIANT Inv\nCONSTANT\n\tNext <- ReDefNext\n",
        &[],
    );
    let text = stdout(&output);
    assert_eq!(
        output.status.code(),
        Some(12),
        "{text}{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        text.contains("State 2: <ReDefNext line 7, col 15 to line 7, col 23 of module CyclicRedefineInstance>\nx = TRUE\n"),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn ranks_the_strings_the_startup_makes() {
    // test-model/Github696: TLC interns the names ToString and \o make as it computes MVS, which
    // orders the model values the search then compares.
    let (output, directory) = run_front(
        "startup-ranks",
        "---- MODULE Ranked ----\nEXTENDS TLC, TLCExt, Integers, Sequences\nb == TLCModelValue(\"B_a\")\nMVS == { TLCModelValue(\"A_\" \\o ToString(n)) : n \\in 0..63 }\nVARIABLE v\nInit == v = [ mv \\in MVS |-> ToString(mv) ]\nNext == UNCHANGED v\nInv == v = [ v EXCEPT ![b] = 42 ]\n====\n",
        "INIT Init\nNEXT Next\nINVARIANT Inv\n",
        &[],
    );
    let text = stdout(&output);
    assert_eq!(
        output.status.code(),
        Some(75),
        "{text}{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        text.contains("Error: Attempted to compare the differently-typed model values A_31 and B_a\nWhile working on the initial state:\n"),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn ranks_the_startup_of_a_recursive_function_of_two_arguments() {
    // tla-rs function_syntax: building add again for each of its arguments recursed until the
    // stack overflowed, which aborted the binary as it ranked the startup's strings.
    let (output, directory) = run_front(
        "two-argument-function",
        "---- MODULE Add ----\nEXTENDS Naturals\nVARIABLE x\nadd[a \\in 0..3, b \\in 0..3] == IF b = 0 THEN a ELSE add[a, b - 1] + 1\nInit == x = 0\nNext == x' = x\nInv == add[2, 3] = 5\n====\n",
        "INIT Init\nNEXT Next\nINVARIANT Inv\n",
        &["-nowarning"],
    );
    let text = stdout(&output);
    assert_eq!(
        output.status.code(),
        Some(0),
        "{text}{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        text.contains("Model checking completed. No error has been found.\n"),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

// Each output is what TLC at d8fb231 prints for the spec.
#[test]
fn checks_a_successor_in_tlc_s_order() {
    // TLC fingerprints a successor, which evaluates the VIEW, only where the action constraints
    // hold (Worker.addElement).
    let view = "---- MODULE ViewAct ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == x < 3 /\\ x' = x + 1\nV == IF x = 2 THEN Assert(FALSE, \"view\") ELSE x\nAC == x' # 2\n====\n";
    let config = "INIT Init\nNEXT Next\nVIEW V\nACTION_CONSTRAINT AC\nCHECK_DEADLOCK FALSE\n";
    let (output, directory) = run_front("view-order", view, config, &[]);
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(0), "{text}");
    assert!(
        text.contains("\n3 states generated, 2 distinct states found, 0 states left on queue.\n"),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
    // TLC reports a constraint that fails on a successor with the successor in the trace, which
    // the binary doesn't, whatever the next-state relation does after it.
    let constraint = "---- MODULE ConThenNext ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == \\/ x < 3 /\\ x' = x + 1\n        \\/ x < 3 /\\ x' = x + 10\n        \\/ x = 1 /\\ Assert(FALSE, \"next\") /\\ x' = 5\nCon == IF x = 2 THEN Assert(FALSE, \"con\") ELSE TRUE\n====\n";
    let config = "INIT Init\nNEXT Next\nCONSTRAINT Con\nCHECK_DEADLOCK FALSE\n";
    let (output, directory) = run_front("constraint-fails", constraint, config, &[]);
    assert_eq!(output.status.code(), Some(1));
    assert!(
        String::from_utf8_lossy(&output.stderr).contains(
            "not native yet: the engine stopped: a constraint, a VIEW or an action property that fails on a successor"
        ),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn reports_the_progress_of_the_initial_states_tlc_computes_again() {
    let spec = "---- MODULE InitInvErr ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x \\in 1..6\nNext == x' = x\nInv == IF x = 6 THEN Assert(FALSE, \"i\") ELSE TRUE\n====\n";
    let (output, directory) = run_front(
        "init-replay",
        spec,
        "INIT Init\nNEXT Next\nINVARIANT Inv\n",
        &[],
    );
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(75), "{text}");
    let progress = "Computed 2 initial states...\nComputed 4 initial states...\n";
    assert!(
        text.contains(&format!(
            "Computing initial states...\n{progress}Error: The first argument of Assert evaluated to FALSE; the second argument was:\n\"i\"\n{progress}Error: The error occurred when TLC was evaluating the nested\n"
        )),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

// TLC drops a SYMMETRY whose definition has as many arguments as permutations, counting the
// arguments of whatever node SANY made of it, and fails on one that is no application.
#[test]
fn declines_a_symmetry_that_is_no_operator_application() {
    for definition in [
        "IF TRUE THEN Permutations(P) ELSE {}",
        "LET Q == P IN Permutations(Q)",
        "{(a :> b) @@ (b :> a)}",
    ] {
        let spec = format!(
            "---- MODULE Shape ----\nEXTENDS TLC\nCONSTANTS a, b, P\nVARIABLE x\nSym == {definition}\nInit == x \\in P\nNext == x' \\in P\n====\n"
        );
        let config = "CONSTANTS a = a\nb = b\nP = {a, b}\nINIT Init\nNEXT Next\nSYMMETRY Sym\n";
        let (output, directory) = run_front("symmetry-shape", &spec, config, &[]);
        assert_eq!(output.status.code(), Some(1), "{definition}");
        assert!(
            String::from_utf8_lossy(&output.stderr).contains(
                "not native yet: a SYMMETRY definition that isn't an operator applied to its sets"
            ),
            "{definition}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        std::fs::remove_dir_all(directory).expect("removed");
    }
}

// TLC's Json module writes a record's fields in the order TLC holds them, which the store forgets.
#[test]
fn declines_to_serialize_a_record_of_several_fields() {
    let spec = "---- MODULE Fields ----\nEXTENDS Json\nVARIABLE x\nInit == x = 0\nNext == x' = x /\\ JsonSerialize(\"fields.out.json\", <<[b |-> 1, a |-> 2]>>)\n====\n";
    let (output, directory) = run_front("json-fields", spec, "INIT Init\nNEXT Next\n", &[]);
    assert_eq!(output.status.code(), Some(1));
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("a Json operator's record, whose fields TLC writes as it holds them"),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(!directory.join("fields.out.json").exists());
    std::fs::remove_dir_all(directory).expect("removed");
}

// TLC stops at the first state whose tableau node accepts every behavior, before the deadlock
// the search goes on to.
#[test]
fn declines_a_deadlock_past_a_node_that_accepts_every_behavior() {
    let spec = "---- MODULE Past ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x < 3 /\\ x' = x + 1\nSpec == Init /\\ [][Next]_x\nProp == [](x = 1 => [](x # 2))\n====\n";
    let (output, directory) = run_front(
        "deadlock-past",
        spec,
        "SPECIFICATION Spec\nPROPERTY Prop\n",
        &[],
    );
    assert_eq!(output.status.code(), Some(1), "{}", stdout(&output));
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("not native yet: the engine stopped: deadlock"),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn declines_a_trace_tlc_fails_to_rebuild_after_drawing_as_it_starts() {
    // An ASSUME draws as TLC starts, and the initial predicate draws after it. TLC rebuilds a
    // trace from the seed (`TLCTrace.getTrace`), finds no initial state, and throws a
    // NullPointerException; it holds the initial state of a violation of two states instead.
    let spec = "---- MODULE Stop ----\nEXTENDS Integers, TLC, Randomization\nVARIABLES x, y, n\nASSUME PrintT(<<\"s\", RandomElement(1..1000)>>)\nInit == x = RandomElement(1..1000) /\\ y = \"a\" /\\ n = 0\nNext == n < 3 /\\ n' = n + 1 /\\ x' = x /\\ y' = y\nInv == n < 3\nHeld == n < 1\n====\n";
    let (output, directory) = run_lowered(
        "startup-draw",
        spec,
        "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\nINVARIANT Inv\n",
    );
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("prove-it: not native yet: a trace whose initial state TLC fails to rebuild"),
        "{}",
        stdout(&output)
    );
    std::fs::remove_dir_all(directory).expect("removed");
    let (output, directory) = run_lowered(
        "startup-draw-held",
        spec,
        "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\nINVARIANT Held\n",
    );
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(12), "{text}");
    assert!(
        text.contains("Error: Invariant Held is violated.\nError: The behavior up to this point is:\nState 1: <Initial predicate>\n/\\ n = 0\n/\\ x = 241\n/\\ y = \"a\"\n\nState 2: <Next line 6, col 9 to line 6, col 47 of module Stop>\n/\\ n = 1\n/\\ x = 241\n/\\ y = \"a\"\n\n2 states generated, 2 distinct states found, 0 states left on queue.\n"),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn reports_a_constraint_that_fails_on_a_later_initial_state_with_its_frames() {
    // TLC's replay of the initial states evaluates the constraint with its call stack, so the
    // failure has the constraint's frames after the initial predicate's.
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x \\in 1..7\nNext == x' = x\nCon == Assert(x # 6, \"con\")\n====\n";
    let (output, directory) = run_lowered(
        "constraint-frames",
        spec,
        "INIT Init\nNEXT Next\nCONSTRAINT Con\n",
    );
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(75), "{text}");
    assert!(
        text.contains("Error: The error occurred when TLC was evaluating the nested\nexpressions at the following positions:\n0. Line 4, column 9 to line 4, column 18 in Stop\n1. Line 6, column 8 to line 6, column 27 in Stop\n\n\n6 states generated, 5 distinct states found, 5 states left on queue.\n"),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn rebuilds_the_trace_again_only_where_tlc_checks_the_postconditions_after_a_failure() {
    // After a failure in the next-state relation TLC's worker rebuilds the trace again, printing,
    // only where it generated no successor of the state before the failure; after an invariant
    // fails to evaluate, never. Then it prints what its replay of the expansion printed.
    let next = "---- MODULE Stop ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nA == PrintT(<<\"a\", x>>) /\\ x' \\in {x + 1, x + 2, x}\nB == x = 3 /\\ PrintT(<<\"b\", x>>) /\\ x' = 1 \\div (x - 3)\nNext == (x < 4 /\\ A) \\/ B\n====\n";
    let (output, directory) = run_lowered("next-prints", next, "INIT Init\nNEXT Next\n");
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(255), "{text}");
    assert!(
        text.contains("State 3: <Next line 7, col 10 to line 7, col 19 of module Stop>\nx = 3\n\n<<\"a\", 3>>\n<<\"b\", 3>>\nError: The error occurred when TLC was evaluating the nested\n"),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
    let first = next.replace("(x < 4 /\\ A) \\/ B", "B \\/ (x < 4 /\\ A)");
    let (output, directory) = run_lowered("next-prints-first", &first, "INIT Init\nNEXT Next\n");
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(255), "{text}");
    assert!(
        text.contains("State 3: <Next line 7, col 15 to line 7, col 24 of module Stop>\nx = 3\n\n<<\"a\", 0>>\n<<\"a\", 1>>\n<<\"b\", 3>>\nError: The error occurred when TLC was evaluating the nested\n"),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
    let invariant = "---- MODULE Stop ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == PrintT(<<\"n\", x>>) /\\ x' \\in {(x + 1) % 6, (x + 2) % 6, (x+3) % 6}\nInv == IF x = 5 THEN Assert(FALSE, \"inv\") ELSE TRUE\n====\n";
    let (output, directory) = run_lowered(
        "invariant-prints",
        invariant,
        "INIT Init\nNEXT Next\nINVARIANT Inv\n",
    );
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(76), "{text}");
    assert!(
        text.contains("State 3: <Next line 5, col 9 to line 5, col 74 of module Stop>\nx = 5\n\n<<\"n\", 2>>\n10 states generated, 6 distinct states found, 2 states left on queue.\n"),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

// TLCEval makes the set an enumerated one (`TLCEval.convert`), which TLC enumerates in its
// normalized order whatever the union it was.
#[test]
fn enumerates_a_set_tlceval_made_in_its_normalized_order() {
    let spec = "---- MODULE Evaluated ----\nEXTENDS Naturals, TLC\nVARIABLES x, y\nInit == x = 0 /\\ y = 0\nNext == x < 1 /\\ x' = x + 1 /\\ y' \\in TLCEval((SUBSET {1, 2}) \\cup {{3}})\n====\n";
    let (output, directory) = run_front("tlceval-order", spec, "INIT Init\nNEXT Next\n", &[]);
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(11), "{text}");
    assert!(text.contains("\n/\\ x = 1\n/\\ y = {}\n"), "{text}");
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn declines_a_violating_successor_tlc_fails_to_draw_again() {
    // TLC finds the violating successor of an initial state it holds by drawing on from its
    // worker's generator as the search left it (`TLCTrace.printTrace`, `Tool.getState`): where
    // the draw differs it finds none, and throws a NullPointerException.
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals, Integers, Sequences, FiniteSets, TLC, Randomization\nVARIABLE x, y\nInit == x = 0 /\\ y = 0\nNext == x < 4 /\\ x' = x + 1 /\\ y' = RandomElement(1..1000)\nInv == y < 400\n====\n";
    let config = "INIT Init\nNEXT Next\nINVARIANT Inv\n";
    let (output, directory) = run_lowered("held-draw", spec, config);
    assert!(
        String::from_utf8_lossy(&output.stderr).contains(
            "prove-it: not native yet: a violating successor TLC fails to find again from its generator"
        ),
        "{}",
        stdout(&output)
    );
    std::fs::remove_dir_all(directory).expect("removed");
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals, TLC\nVARIABLE x, y\nInit == x = 1 /\\ y = 0\nNext == x < 9 /\\ x' = x + 1 /\\ y' = RandomElement(1..2)\nInv == y < 2\n====\n";
    let (output, directory) = run_lowered("held-draw-found", spec, config);
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(12), "{text}");
    assert!(
        text.contains("Error: Invariant Inv is violated.\nError: The behavior up to this point is:\nState 1: <Initial predicate>\n/\\ x = 1\n/\\ y = 0\n\nState 2: <Next line 5, col 9 to line 5, col 55 of module Stop>\n/\\ x = 2\n/\\ y = 2\n\n2 states generated, 2 distinct states found, 0 states left on queue.\n"),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn declines_a_substitute_with_effects() {
    // TLC evaluates QDef before K and L, and again wherever Q is read, printing "subst" each time.
    let config = "CONSTANTS Q <- QDef\nINIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n";
    let spec = |name: &str, definitions: &str, assumption: &str| {
        format!(
            "---- MODULE {name} ----\nEXTENDS Integers, TLC\nCONSTANTS Q\nVARIABLES f\n{definitions}\nASSUME {assumption}\nInit == f = Q\nNext == f' = f\n====\n"
        )
    };
    let declined = [
        spec(
            "W3",
            "K == PrintT(\"constdef\")\nQDef == IF PrintT(\"subst\") THEN 1 ELSE 2\nL == PrintT(\"constdef2\")",
            "PrintT(\"assume1\") /\\ K /\\ L",
        ),
        spec(
            "W2",
            "QDef == IF PrintT(\"subst\") THEN 1 ELSE 2",
            "PrintT(\"assume1\") /\\ Q = 1 /\\ Q = 1",
        ),
        // TLC keeps a constant TLCEval's value, but prints "subst" before K's "constdef".
        spec(
            "W4",
            "K == PrintT(\"constdef\")\nQDef == TLCEval(IF PrintT(\"subst\") THEN 1 ELSE 2)",
            "PrintT(\"assume1\") /\\ K /\\ Q = 1",
        ),
    ];
    for spec in &declined {
        let (output, directory) = run_front("effectful-substitute", spec, config, &[]);
        assert_eq!(output.status.code(), Some(1), "{}", stdout(&output));
        assert!(
            String::from_utf8_lossy(&output.stderr)
                .contains("not native yet: a configuration substitute with effects"),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        std::fs::remove_dir_all(directory).expect("removed");
    }
    // A constant TLCEval no other constant definition's effects come before prints once.
    let cached = spec(
        "W5",
        "QDef == TLCEval(IF PrintT(\"subst\") THEN 1 ELSE 2)",
        "PrintT(\"assume1\") /\\ Q = 1 /\\ Q = 1",
    );
    let (output, directory) = run_front("cached-substitute", &cached, config, &[]);
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(0), "{text}");
    assert!(
        text.contains("\n\"subst\"\n\"assume1\"\nComputing initial states...\n"),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

// TLCGet("-Dname") reads a Java system property, the key itself where nothing sets it
// (`System.getProperty(name, key)`): TLC at d8fb231 finds x = 1 with -Dfoo=bar and x = 0 without.
#[test]
fn reads_a_system_property_as_tlc_or_declines() {
    let spec = "---- MODULE Property ----\nEXTENDS TLC\nVARIABLE x\nInit == x = IF TLCGet(\"-Dfoo\") = \"bar\" THEN 1 ELSE 0\nNext == x' = x\nInv == x = 0\nSeparator == TLCGet(\"-Dfile.separator\") = \"/\" \\/ TLCGet(\"-Dfile.separator\") = \"\\\\\"\n====\n";
    let directory =
        std::env::temp_dir().join(format!("prove-it-cli-property-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    std::fs::write(directory.join("Property.tla"), spec).expect("the spec");
    std::fs::write(
        directory.join("Property.cfg"),
        "INIT Init\nNEXT Next\nINVARIANT Inv\nINVARIANT Separator\n",
    )
    .expect("the configuration");
    let run_with = |property: &str| {
        Command::new(env!("CARGO_BIN_EXE_prove-it"))
            .args([property, "tlc2.TLC", "-noTE", "Property"])
            .current_dir(&directory)
            .output()
            .expect("the binary runs")
    };
    let unset = run_with("-Dother=bar");
    let text = stdout(&unset);
    assert_eq!(unset.status.code(), Some(0), "{text}");
    assert!(
        text.contains("Model checking completed. No error has been found."),
        "{text}"
    );
    let set = run_with("-Dfoo=bar");
    assert_eq!(set.status.code(), Some(1), "{}", stdout(&set));
    assert!(
        !stdout(&set).contains("Computing initial states"),
        "{}",
        stdout(&set)
    );
    assert_eq!(
        String::from_utf8_lossy(&set.stderr),
        "prove-it: not native yet: TLCGet of the system property foo, which the command line sets\n"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

// What the binary prints but its process id and the times, which differ from run to run.
fn untimed(output: &Output) -> String {
    stdout(output)
        .lines()
        .filter(|line| {
            ![
                "[pid: ",
                "Starting...",
                "Progress(",
                "Finished",
                " at (",
                " at 20",
            ]
            .iter()
            .any(|timed| line.contains(timed))
        })
        .collect::<Vec<_>>()
        .join("\n")
}

#[test]
fn prints_on_four_threads_what_it_prints_on_one() {
    let goldens: [(&str, &[u8], &str, &str); 5] = [
        ("TCommit", COMMIT_IR, "", "a search that finds no error"),
        (
            "ACP_NB_WRONG_TLC",
            include_bytes!(
                "../../../../tests/conformance/ir/examples/specifications/acp/ACP_NB_WRONG_TLC.ir"
            ),
            "CONSTANTS\n  participants = { p0, p1 }\n  waiting = waiting\n  notsent = notsent\n  undecided = undecided\n  commit = commit\n  abort = abort\n  yes = yes\n  timeout = timeout\n  no = no\nSPECIFICATION SpecNB\nPROPERTIES AC1\nCHECK_DEADLOCK FALSE\n",
            "an invariant violated part way through a level",
        ),
        (
            "stages",
            include_bytes!(
                "../../../../tests/conformance/ir/examples/specifications/glowingRaccoon/stages.ir"
            ),
            "CONSTANTS\n  DNA = 5\n  PRIMER = 5\nINVARIANT TypeOK\nSPECIFICATION Spec\nPROPERTIES cleanSpec primerDepleted\nCHECK_DEADLOCK FALSE\n",
            "temporal properties that hold",
        ),
        (
            "MCDistributedReplicatedLog",
            include_bytes!(
                "../../../../tests/conformance/ir/tlc/tlatools/org.lamport.tlatools/test-model/examples/FiniteMonotonic/MCDistributedReplicatedLog.ir"
            ),
            "SPECIFICATION Spec\nCONSTANTS\n    Servers = {n1, n2, n3}\n    Values = {v}\n    Lag = 3\nINVARIANTS TypeOK BoundedLag\nPROPERTIES AllExtending InSync\nVIEW DropCommonPrefix\nCHECK_DEADLOCK TRUE\n",
            "a lasso under a VIEW",
        ),
        (
            "MC",
            include_bytes!(
                "../../../../tests/conformance/ir/examples/specifications/ReadersWriters/MC.ir"
            ),
            "CONSTANT\n    NumActors <- n\nSPECIFICATION\n    Spec\nINVARIANT\n    TypeOK\n    Safety\nPROPERTY\n    Liveness\n",
            "fairness, whose steps the graph labels for ENABLED",
        ),
    ];
    for (name, ir, config, what) in goldens {
        let (one, directory) = run_golden(&format!("threads-{name}"), ir, name, config, &[]);
        // Every level shared, between as many threads as the machine runs, up to four.
        let four = run_ir_with(
            &directory,
            name,
            &[name],
            &[("PROVE_IT_WORKERS", "4"), ("PROVE_IT_SHARED_LEVEL", "1")],
        );
        assert_eq!(four.status.code(), one.status.code(), "{name}: {what}");
        assert_eq!(untimed(&four), untimed(&one), "{name}: {what}");
        std::fs::remove_dir_all(directory).expect("removed");
    }
}

#[test]
fn reads_what_tlc_drew_at_startup_on_every_thread() {
    // TLC's SpanTreeRandom, smaller: Edges draws once, as TLC starts, and the liveness checker's
    // threads read that draw, where drawing again from their own generators finds no violation.
    let directory = std::env::temp_dir().join(format!("prove-it-cli-drawn-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    for (file, contents) in [
        (
            "Drawn.tla",
            "---- MODULE Drawn ----\nEXTENDS Integers, FiniteSets, TLC\nCONSTANTS Nodes, Root, MaxCardinality\nEdges == UNION { {{n, m} : m \\in RandomElement(SUBSET (Nodes \\ {n}))} : n \\in Nodes }\nVARIABLES mom, dist\nvars == <<mom, dist>>\nNbrs(n) == {m \\in Nodes : {m, n} \\in Edges}\nInit == /\\ mom = [n \\in Nodes |-> n]\n        /\\ dist = [n \\in Nodes |-> IF n = Root THEN 0 ELSE MaxCardinality]\nNext == \\E n \\in Nodes : \\E m \\in Nbrs(n) :\n          /\\ dist[m] < 1 + dist[n]\n          /\\ \\E d \\in (dist[m] + 1)..(dist[n] - 1) :\n                /\\ dist' = [dist EXCEPT ![n] = d]\n                /\\ mom' = [mom EXCEPT ![n] = m]\nSpec == Init /\\ [][Next]_vars /\\ WF_vars(Next)\nNextAlwaysEnabled == []<>(ENABLED Next)\n====\n",
        ),
        (
            "Drawn.cfg",
            "CONSTANTS\n  Nodes = {n1, n2, n3, n4, n5}\n  MaxCardinality = 5\n  Root = n1\nSPECIFICATION Spec\nPROPERTY NextAlwaysEnabled\nCHECK_DEADLOCK FALSE\n",
        ),
    ] {
        std::fs::write(directory.join(file), contents).expect("a file");
    }
    let run_with = |threads: &str| {
        Command::new(env!("CARGO_BIN_EXE_prove-it"))
            .args(["-seed", "4", "-lncheck", "final", "-noTE", "Drawn"])
            .current_dir(&directory)
            .env("PROVE_IT_WORKERS", threads)
            .output()
            .expect("the binary runs")
    };
    let one = run_with("1");
    let four = run_with("4");
    assert!(
        stdout(&one).contains("Error: Temporal property NextAlwaysEnabled was violated."),
        "{}",
        stdout(&one)
    );
    assert_eq!(four.status.code(), one.status.code());
    assert_eq!(untimed(&four), untimed(&one));
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn passes_the_elements_a_leading_field_test_rejects_where_tlc_does() {
    // Loops whose body starts with `m.type = c`: an action's \E, \A, ~\E and a set filter, over
    // records whose type is another string, records of which a later one lacks the field, a
    // model value and integers, as TLC at d8fb231 prints them: an element is passed only where the
    // test is FALSE without failing, so a later element still fails where TLC fails, and \A
    // stops at the first element whose test is FALSE.
    let directory =
        std::env::temp_dir().join(format!("prove-it-cli-fields-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    let mut module = String::from(
        "---- MODULE Fields ----\nEXTENDS Integers\nCONSTANT M\nVARIABLE x\n\
         Msgs(c) == CASE c = 1 -> {[type |-> \"a\", v |-> 1], [type |-> \"b\", v |-> 2], [typo |-> \"c\", v |-> 3]}\n\
         \x20            [] c = 2 -> {[type |-> \"b\", v |-> 1], [type |-> \"a\", v |-> 2]}\n\
         \x20            [] c = 3 -> {[type |-> M, v |-> 1]}\n\
         \x20            [] OTHER -> {[type |-> 3, v |-> 1], [type |-> 4, v |-> 2]}\n\
         Init == x = 0\n\
         Act(c) == \\E m \\in Msgs(c) : m.type = \"z\" /\\ x' = m.v\n\
         All(c) == \\A m \\in Msgs(c) : m.type = \"b\" /\\ m.v > 0\n\
         None(c) == ~\\E m \\in Msgs(c) : m.type = \"z\" /\\ m.v = 7\n\
         Kept(c) == {m \\in Msgs(c) : m.type = \"a\" /\\ m.v > 0} # {}\n\
         Stay == UNCHANGED x\n",
    );
    for c in 1..=4 {
        module.push_str(&format!(
            "Next{c} == Act({c})\nInvAll{c} == All({c})\nInvNone{c} == None({c})\nInvKept{c} == Kept({c})\n"
        ));
    }
    module.push_str("====\n");
    std::fs::write(directory.join("Fields.tla"), module).expect("a file");
    let missing = "Attempted to select nonexistent field \"type\" from the record\n[v |-> 3, typo |-> \"c\"]\n";
    let cases: [(&str, &[&str]); 16] = [
        (
            "NEXT Next1",
            &[
                missing,
                "line 10, col 30 to line 10, col 35 of module Fields\n",
            ],
        ),
        (
            "INVARIANT InvAll1",
            &["Error: The invariant of InvAll1 is equal to FALSE\n"],
        ),
        (
            "INVARIANT InvNone1",
            &[
                missing,
                "line 12, col 32 to line 12, col 37 of module Fields\n",
            ],
        ),
        (
            "INVARIANT InvKept1",
            &[
                missing,
                "line 13, col 29 to line 13, col 34 of module Fields\n",
            ],
        ),
        ("NEXT Next2", &["Error: Deadlock reached.\n"]),
        (
            "INVARIANT InvAll2",
            &["Error: The invariant of InvAll2 is equal to FALSE\n"],
        ),
        (
            "INVARIANT InvNone2",
            &["Model checking completed. No error has been found.\n"],
        ),
        (
            "INVARIANT InvKept2",
            &["Model checking completed. No error has been found.\n"],
        ),
        ("NEXT Next3", &["Error: Deadlock reached.\n"]),
        (
            "INVARIANT InvAll3",
            &["Error: The invariant of InvAll3 is equal to FALSE\n"],
        ),
        (
            "INVARIANT InvNone3",
            &["Model checking completed. No error has been found.\n"],
        ),
        (
            "INVARIANT InvKept3",
            &["Error: The invariant of InvKept3 is equal to FALSE\n"],
        ),
        (
            "NEXT Next4",
            &[
                "Attempted to check equality of integer 3 with non-integer:\n\"z\"\n",
                "0. Line 10, column 30 to line 10, column 53 in Fields\n1. Line 10, column 30 to line 10, column 41 in Fields\n",
            ],
        ),
        (
            "INVARIANT InvAll4",
            &["Attempted to check equality of integer 3 with non-integer:\n\"b\"\n"],
        ),
        (
            "INVARIANT InvNone4",
            &["Attempted to check equality of integer 3 with non-integer:\n\"z\"\n"],
        ),
        (
            "INVARIANT InvKept4",
            &["Attempted to check equality of integer 3 with non-integer:\n\"a\"\n"],
        ),
    ];
    for (clause, expected) in cases {
        let config = if clause.starts_with("NEXT") {
            format!("CONSTANT M = M\nINIT Init\n{clause}\n")
        } else {
            format!("CONSTANT M = M\nINIT Init\nNEXT Stay\n{clause}\n")
        };
        std::fs::write(directory.join("Fields.cfg"), config).expect("a file");
        let output = run(
            &directory,
            &["-nowarning", "-fp", "0", "-noGenerateSpecTE", "Fields"],
        );
        let text = stdout(&output);
        for line in expected {
            assert!(text.contains(line), "{clause}: {line}\n{text}");
        }
    }
    std::fs::remove_dir_all(directory).expect("removed");
}

// Fairness whose ENABLED the search's steps answer, or don't, against what TLC built at d8fb231
// prints for each spec, on one thread and with every level shared between four.
#[test]
fn answers_enabled_from_the_steps_as_tlc_does() {
    let specs = [
        (
            // ENABLED <<A>>_x holds at x = 2, where no step takes A: A is a conjunct of the action
            // TLC splits, not the action, so ENABLED runs, and WF_x(A) rules out stuttering there.
            "Guarded",
            "---- MODULE Guarded ----\nEXTENDS Naturals\nVARIABLE x\nA == x' = x + 1\nNext == (x < 2 /\\ A) \\/ (x = 2 /\\ x' = 0)\nSpec == x = 0 /\\ [][Next]_x /\\ WF_x(A)\nLive == []<>(x = 0)\n====\n",
            "SPECIFICATION Spec\nPROPERTY Live\n",
            "Model checking completed. No error has been found.\n",
            "4 states generated, 3 distinct states found, 0 states left on queue.\n",
        ),
        (
            // TLC's ENABLED ignores the constraint that drops A's step from x = 2, so ENABLED runs.
            "Constrained",
            "---- MODULE Constrained ----\nEXTENDS Naturals\nVARIABLE x\nA == x' = x + 1\nB == x = 2 /\\ x' = 0\nNext == A \\/ B\nSpec == x = 0 /\\ [][Next]_x /\\ WF_x(A)\nLive == []<>(x = 0)\nSmall == x <= 2\n====\n",
            "SPECIFICATION Spec\nCONSTRAINT Small\nPROPERTY Live\n",
            "Model checking completed. No error has been found.\n",
            "5 states generated, 3 distinct states found, 0 states left on queue.\n",
        ),
        (
            // Inc(1) and Reset are TLC's actions, which label the steps that answer their ENABLED.
            "Counters",
            "---- MODULE Counters ----\nEXTENDS Naturals\nCONSTANT P\nVARIABLE x\nInc(p) == x[p] < 2 /\\ x' = [x EXCEPT ![p] = x[p] + 1]\nReset == (\\A p \\in P : x[p] = 2) /\\ x' = [p \\in P |-> 0]\nNext == (\\E p \\in P : Inc(p)) \\/ Reset\nSpec == x = [p \\in P |-> 0] /\\ [][Next]_x /\\ WF_x(Inc(1)) /\\ WF_x(Reset)\nDone == \\A p \\in P : <>(x[p] = 2)\n====\n",
            "CONSTANT P = {1, 2}\nSPECIFICATION Spec\nPROPERTY Done\n",
            concat!(
                "Error: Temporal property Done was violated.\n\n",
                "Error: The following behavior constitutes a counter-example:\n\n",
                "State 1: <Initial predicate>\nx = <<0, 0>>\n\n",
                "State 2: <Inc(2) line 5, col 11 to line 5, col 53 of module Counters>\nx = <<0, 1>>\n\n",
                "State 3: <Inc(1) line 5, col 11 to line 5, col 53 of module Counters>\nx = <<1, 1>>\n\n",
                "State 4: <Inc(1) line 5, col 11 to line 5, col 53 of module Counters>\nx = <<2, 1>>\n\n",
                "State 5: Stuttering\n",
            ),
            "14 states generated, 9 distinct states found, 0 states left on queue.\n",
        ),
        (
            // The labelled search counts and orders the states as the next-state relation's walk
            // does, which the POSTCONDITION reads.
            "Stats",
            "---- MODULE Stats ----\nEXTENDS Naturals, TLC\nCONSTANT P\nVARIABLE x\nInc(p) == x[p] < 2 /\\ x' = [x EXCEPT ![p] = x[p] + 1]\nReset == (\\A p \\in P : x[p] = 2) /\\ x' = [p \\in P |-> 0]\nNext == (\\E p \\in P : Inc(p)) \\/ Reset\nSpec == x = [p \\in P |-> 0] /\\ [][Next]_x /\\ \\A p \\in P : WF_x(Inc(p))\nDone == \\A p \\in P : []<>(x[p] = 2)\nPost == PrintT(<<TLCGet(\"stats\"), TLCGet(\"distinct\"), TLCGet(\"queue\"), TLCGet(\"level\")>>)\n====\n",
            "CONSTANT P = {1, 2}\nSPECIFICATION Spec\nPROPERTY Done\nPOSTCONDITION Post\n",
            "<< [ distinct |-> 9,\n     queue |-> 0,\n     worker |-> 0,\n     duration |-> 0,\n     generated |-> 14,\n     diameter |-> 5,\n     initial |-> 1 ],\n   9,\n   0,\n   0 >>\nModel checking completed. No error has been found.\n",
            "14 states generated, 9 distinct states found, 0 states left on queue.\n",
        ),
    ];
    for (name, spec, config, printed, count) in specs {
        let directory = std::env::temp_dir().join(format!(
            "prove-it-cli-enabled-{name}-{}",
            std::process::id()
        ));
        std::fs::create_dir_all(&directory).expect("a directory");
        std::fs::write(directory.join(format!("{name}.tla")), spec).expect("a spec");
        std::fs::write(directory.join(format!("{name}.cfg")), config).expect("a configuration");
        for threads in ["1", "4"] {
            let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
                .args(["-noTE", name])
                .current_dir(&directory)
                .env("PROVE_IT_WORKERS", threads)
                .env("PROVE_IT_SHARED_LEVEL", "1")
                .output()
                .expect("the binary runs");
            let text = stdout(&output);
            assert!(text.contains(printed), "{name} on {threads}: {text}");
            assert!(text.contains(count), "{name} on {threads}: {text}");
        }
        std::fs::remove_dir_all(directory).expect("removed");
    }
}

#[test]
fn unites_a_set_with_one_element_in_tlcs_order() {
    // S \cup {x} and {x} \cup S where no comparison can fail, which the store answers by a
    // binary search for x's place: an element before, between and after the set's, one already
    // in it, the empty set, tuples of other lengths, typed and untyped model values, and strings
    // in the order TLC ranks them. Each set is what TLC at d8fb231 prints.
    let directory = std::env::temp_dir().join(format!("prove-it-cli-union-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    let module = "---- MODULE Union ----\n\
         EXTENDS Integers, Sequences\n\
         CONSTANTS M1, M2, S1, S2, T1\n\
         VARIABLE y\n\
         Base(c) == CASE c = 1 -> {[t |-> \"a\", v |-> 1], [t |-> \"c\", v |-> 3]}\n\
         \x20            [] c = 2 -> {[t |-> \"a\", v |-> 1], [t |-> \"c\", v |-> 3]}\n\
         \x20            [] c = 3 -> {[t |-> \"a\", v |-> 1], [t |-> \"c\", v |-> 3]}\n\
         \x20            [] c = 4 -> {}\n\
         \x20            [] c = 5 -> {<<1>>, <<1, 2, 3>>}\n\
         \x20            [] c = 6 -> {S1}\n\
         \x20            [] c = 7 -> {S1}\n\
         \x20            [] c = 8 -> {M1, 2}\n\
         \x20            [] c = 9 -> {1, 2}\n\
         \x20            [] c = 10 -> {[t |-> \"a\"]}\n\
         \x20            [] c = 11 -> {<<\"a\", 1>>, <<\"b\", 2>>}\n\
         \x20            [] OTHER -> {\"a\", \"c\"}\n\
         Elem(c) == CASE c = 1 -> [t |-> \"b\", v |-> 2]\n\
         \x20            [] c = 2 -> [t |-> \"a\", v |-> 1]\n\
         \x20            [] c = 3 -> [t |-> \"z\", v |-> 9]\n\
         \x20            [] c = 4 -> 7\n\
         \x20            [] c = 5 -> <<1, 2>>\n\
         \x20            [] c = 6 -> S2\n\
         \x20            [] c = 7 -> T1\n\
         \x20            [] c = 8 -> M2\n\
         \x20            [] c = 9 -> \"a\"\n\
         \x20            [] c = 10 -> <<1>>\n\
         \x20            [] c = 11 -> <<\"a\", 0>>\n\
         \x20            [] OTHER -> \"b\"\n\
         Init == y = Base(C) \\cup {Elem(C)}\n\
         Next == UNCHANGED y\n\
         Inv == y = {}\n\
         Rev == {Elem(C)} \\cup Base(C) = {}\n\
         ====\n\
         ";
    let cases: [(u32, &str); 9] = [
        (
            1,
            "y = {[t |-> \"c\", v |-> 3], [t |-> \"a\", v |-> 1], [t |-> \"b\", v |-> 2]}\n",
        ),
        (2, "y = {[t |-> \"c\", v |-> 3], [t |-> \"a\", v |-> 1]}\n"),
        (
            3,
            "y = {[t |-> \"c\", v |-> 3], [t |-> \"a\", v |-> 1], [t |-> \"z\", v |-> 9]}\n",
        ),
        (4, "y = {7}\n"),
        (5, "y = {<<1>>, <<1, 2>>, <<1, 2, 3>>}\n"),
        (6, "y = {s_one, s_two}\n"),
        (8, "y = {M1, M2, 2}\n"),
        (11, "y = {<<\"a\", 0>>, <<\"a\", 1>>, <<\"b\", 2>>}\n"),
        (12, "y = {\"c\", \"a\", \"b\"}\n"),
    ];
    for (case, expected) in cases {
        std::fs::write(
            directory.join("Union.tla"),
            module.replace("Init ==", &format!("C == {case}\nInit ==")),
        )
        .expect("a file");
        for (invariant, line) in [
            ("Inv", expected),
            ("Rev", "Error: The invariant of Rev is equal to FALSE\n"),
        ] {
            std::fs::write(
                directory.join("Union.cfg"),
                format!("CONSTANTS M1 = M1 M2 = M2 S1 = s_one S2 = s_two T1 = t_one\nINIT Init\nNEXT Next\nINVARIANT {invariant}\n"),
            )
            .expect("a file");
            let output = run(
                &directory,
                &["-nowarning", "-fp", "0", "-noGenerateSpecTE", "Union"],
            );
            let text = stdout(&output);
            assert!(
                text.contains(line),
                "case {case}, {invariant}: {line}\n{text}"
            );
        }
    }
    std::fs::remove_dir_all(directory).expect("removed");
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

fn read_dump(directory: &Path, name: &str) -> String {
    std::fs::read_to_string(directory.join(name)).expect("a dump")
}

#[test]
fn dumps_every_state_found_as_tlc_writes_them() {
    let directory = commit_directory("dump");
    // TLC's own `-dump` of TCommit, at d8fb231 with `-workers 1`.
    let expected = include_str!("tcommit.dump");
    let output = run_ir(
        &directory,
        "TCommit",
        &["-workers", "1", "-noTE", "-dump", "states", "TCommit"],
    );
    assert_eq!(output.status.code(), Some(0), "{}", stdout(&output));
    assert_eq!(read_dump(&directory, "states.dump"), expected);
    // A name that ends in .dump keeps it, and with several workers the binary writes the states in
    // the order one finds them.
    let shared = run_ir_with(
        &directory,
        "TCommit",
        &["-workers", "4", "-noTE", "-dump", "shared.dump", "TCommit"],
        &[("PROVE_IT_SHARED_LEVEL", "1")],
    );
    assert_eq!(shared.status.code(), Some(0), "{}", stdout(&shared));
    assert_eq!(read_dump(&directory, "shared.dump"), expected);
    std::fs::remove_dir_all(directory).expect("removed");
}

// Specs and dumps as TLC ran and wrote them at d8fb231 with `-workers 1`.
#[test]
fn dumps_the_state_that_stops_the_search_as_tlc() {
    let counted = "State 1:\nx = 0\n\nState 2:\nx = 1\n\nState 3:\nx = 2\n\nState 4:\nx = 3\n\n";
    for (test, next, config, code) in [
        (
            "dump-invariant",
            "x' = x + 1",
            "INIT Init\nNEXT Next\nINVARIANT Inv\n",
            12,
        ),
        (
            "dump-deadlock",
            "x < 3 /\\ x' = x + 1",
            "INIT Init\nNEXT Next\n",
            11,
        ),
    ] {
        let spec = format!(
            "---- MODULE Stop ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == {next}\nInv == x < 3\n====\n"
        );
        let (output, directory) = run_spec_with(test, &spec, config, &["-dump", "states"]);
        assert_eq!(
            output.status.code(),
            Some(code),
            "{test}: {}",
            stdout(&output)
        );
        assert_eq!(read_dump(&directory, "states.dump"), counted, "{test}");
        std::fs::remove_dir_all(directory).expect("removed");
    }
}

#[test]
fn dumps_a_state_of_several_variables_as_tlc() {
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals\nVARIABLES x, r\nInit == x \\in {0, 1} /\\ r = [b |-> x, a |-> \"s\"]\nNext == x < 2 /\\ x' = x + 1 /\\ r' = [r EXCEPT !.b = x']\n====\n";
    let (output, directory) = run_spec_with(
        "dump-record",
        spec,
        "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n",
        &["-dump", "states"],
    );
    assert_eq!(output.status.code(), Some(0), "{}", stdout(&output));
    assert_eq!(
        read_dump(&directory, "states.dump"),
        "State 1:\n/\\ r = [b |-> 0, a |-> \"s\"]\n/\\ x = 0\n\nState 2:\n/\\ r = [b |-> 1, a |-> \"s\"]\n/\\ x = 1\n\nState 3:\n/\\ r = [b |-> 2, a |-> \"s\"]\n/\\ x = 2\n\n"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

// TLC opens the dump before it reads the configuration, so a configuration it rejects leaves the
// dump empty.
#[test]
fn opens_the_dump_before_it_reads_the_configuration() {
    let spec = "---- MODULE Stop ----\nVARIABLE x\nInit == x = 0\nNext == UNCHANGED x\n====\n";
    let (output, directory) = run_spec_with(
        "dump-configuration",
        spec,
        "INIT Init\n\"unterminated\n",
        &["-dump", "states"],
    );
    assert_eq!(output.status.code(), Some(151), "{}", stdout(&output));
    assert_eq!(read_dump(&directory, "states.dump"), "");
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn declines_a_dump_whose_contents_tlc_writes_otherwise() {
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x < 2 /\\ x' = x + 1\nLive == <>(x = 2)\nInv == x > 0\n====\n";
    for (test, config, args, reason) in [
        (
            "dump-dot",
            "INIT Init\nNEXT Next\n",
            &["-dump", "dot", "states"][..],
            "-dump dot",
        ),
        (
            "dump-metadir",
            "INIT Init\nNEXT Next\n",
            &["-dump", "${metadir}/states"],
            "-dump into the meta directory",
        ),
        // TLC writes each state again as it adds its stuttering step to the behavior graph.
        (
            "dump-temporal",
            "SPECIFICATION Spec\nPROPERTY Live\n",
            &["-dump", "states"],
            "-dump with temporal properties",
        ),
        // TLC returns without closing the dump, which holds what Java's buffers flushed.
        (
            "dump-initial",
            "INIT Init\nNEXT Next\nINVARIANT Inv\n",
            &["-dump", "states"],
            "-dump of a search stopped computing its initial states",
        ),
    ] {
        let spec = spec.replace("====", "Spec == Init /\\ [][Next]_x /\\ WF_x(Next)\n====");
        let (output, directory) = run_spec_with(test, &spec, config, args);
        assert_eq!(output.status.code(), Some(1), "{test}: {}", stdout(&output));
        assert_eq!(
            stderr(&output),
            format!("prove-it: not native yet: {reason}\n"),
            "{test}"
        );
        std::fs::remove_dir_all(directory).expect("removed");
    }
}

// TLC's FingerprintExceptionHang: TypeOK fails to evaluate on the second state, and TLC expands the
// first state again to print the call stack, writing the third state it finds then.
#[test]
fn declines_a_dump_where_tlc_replays_the_step_that_failed() {
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals\nCONSTANTS Nodes\nVARIABLES node_state\nvars == <<node_state>>\nLegalSets == {{}}\nTypeOK == node_state \\in [Nodes -> [set: LegalSets]]\nInit == \\E initial_members \\in LegalSets: node_state = [n \\in Nodes |-> [set |-> initial_members]]\nNext == \\E n \\in Nodes, new_members \\in {1}: node_state' = [node_state EXCEPT ![n].set = new_members]\nSpec == Init /\\ [][Next]_vars\n====\n";
    let (output, directory) = run_spec_with(
        "dump-replay",
        spec,
        "SPECIFICATION Spec\nCONSTANT Nodes = {A, B}\nCHECK_DEADLOCK FALSE\nINVARIANT TypeOK\n",
        &["-dump", "states"],
    );
    assert_eq!(output.status.code(), Some(1), "{}", stdout(&output));
    assert_eq!(
        stderr(&output),
        "prove-it: not native yet: -dump of states TLC finds as it replays a step\n"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn declines_a_temporal_property_tlc_rejects_after_it_warns_about_the_symmetry() {
    // tests/fixtures/cli-output/EventualAction: TLC starts the liveness checker, warns that a
    // symmetry is dangerous for liveness, then rejects the property:
    //   Warning: Declaring symmetry during liveness checking is dangerous. ...
    //   Error: Temporal formulas containing actions must be of forms <>[]A or []<>A.
    // The front end's failure doesn't print the warning, so the model isn't native yet.
    let fixtures =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../tests/fixtures/cli-output");
    let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .args(["-noGenerateSpecTE", "EventualAction.tla"])
        .current_dir(&fixtures)
        .output()
        .expect("the binary runs");
    assert_eq!(output.status.code(), Some(1), "{}", stdout(&output));
    assert_eq!(
        String::from_utf8_lossy(&output.stderr),
        "prove-it: not native yet: a temporal property TLC rejects after it warns about the symmetry\n"
    );
    // With -nowarning TLC prints no warning, and the binary prints TLC's error natively.
    let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .args(["-noGenerateSpecTE", "-nowarning", "EventualAction.tla"])
        .current_dir(&fixtures)
        .output()
        .expect("the binary runs");
    assert_eq!(output.status.code(), Some(255), "{}", stdout(&output));
    assert!(
        stdout(&output).contains(
            "Error: Temporal formulas containing actions must be of forms <>[]A or []<>A.\n"
        ),
        "{}",
        stdout(&output)
    );
}
