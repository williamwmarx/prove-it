//! Runs the binary on specs with a `_PERIODIC` expression, which TLC evaluates as it prints its
//! progress.

mod common;

use std::path::PathBuf;
use std::process::{Command, Output};

use common::{run_spec, run_spec_with, stdout};

// A counter with a `_PERIODIC` expression, as TLC's ran at d8fb231 with `-workers 1`: TLC
// evaluates the expression afresh just before it prints its progress, about 3 s in and each minute
// after, with no state, and not at all in a run that ends first. A constant-level expression it
// also evaluates as it starts.
fn periodic_spec(next: &str, periodic: &str) -> String {
    format!(
        "---- MODULE Stop ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == {next}\nPeriodic == {periodic}\n====\n"
    )
}

const PERIODIC_CONFIG: &str = "INIT Init\nNEXT Next\n_PERIODIC Periodic\nCHECK_DEADLOCK FALSE\n";

// A counter of 1001 states, which reports its progress after 300, 600 and 900 expanded states under
// PROVE_IT_TEST_PROGRESS_EVERY=300, in place of the clock's 3 s and each minute after.
const PERIODIC_COUNTER: &str = "x < 1000 /\\ x' = x + 1";

// Runs the binary on a spec of the test's own, with its progress every 300 expanded states.
fn run_spec_every_300(test: &str, spec: &str) -> (Output, PathBuf) {
    run_config_every_300(test, spec, PERIODIC_CONFIG)
}

fn run_config_every_300(test: &str, spec: &str, config: &str) -> (Output, PathBuf) {
    let directory =
        std::env::temp_dir().join(format!("prove-it-cli-{test}-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    std::fs::write(directory.join("Stop.tla"), spec).expect("a spec");
    std::fs::write(directory.join("Stop.cfg"), config).expect("a configuration");
    let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .args(["-noTE", "Stop"])
        .current_dir(&directory)
        .env("PROVE_IT_TEST_PROGRESS_EVERY", "300")
        .output()
        .expect("the binary runs");
    (output, directory)
}

// The lines after the initial states.
fn get_search_lines(text: &str) -> Vec<&str> {
    let lines: Vec<&str> = text.lines().collect();
    let start = lines
        .iter()
        .position(|line| line.starts_with("Finished computing initial states: "))
        .expect("the initial states");
    lines[start + 1..].to_vec()
}

// The depth, the states generated and found, and the states left on the queue a Progress line
// reports.
fn get_progress_counts(line: &str) -> [u64; 4] {
    let number = |text: &str| text.replace(',', "").parse::<u64>().expect("a count");
    let (depth, rest) = line
        .strip_prefix("Progress(")
        .and_then(|rest| rest.split_once(") at "))
        .expect("a Progress line");
    let (_, rest) = rest.split_once(": ").expect("the counts");
    let words: Vec<&str> = rest.split(' ').collect();
    let queued = words[words.len() - 5];
    [
        number(depth),
        number(words[0]),
        number(words[5]),
        number(queued),
    ]
}

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

// TLC printed `<<5605043, 5605043, 1, 5605043, 1>>` just before its Progress line: the counts as
// its workers stopped for it, which the Progress line's equal here, TLCGet("level") 1 of its empty
// state.
#[test]
fn prints_what_the_periodic_expression_prints_before_each_progress_as_tlc() {
    let spec = periodic_spec(
        PERIODIC_COUNTER,
        "PrintT(<<TLCGet(\"distinct\"), TLCGet(\"generated\"), TLCGet(\"queue\"), TLCGet(\"diameter\"), TLCGet(\"level\")>>)",
    );
    let (output, directory) = run_spec_every_300("periodic-counts", &spec);
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(0), "{text}");
    let lines = get_search_lines(&text);
    for (position, count) in [301, 601, 901].into_iter().enumerate() {
        assert_eq!(
            lines[position * 2],
            format!("<<{count}, {count}, 1, {count}, 1>>"),
            "{text}"
        );
        assert_eq!(
            get_progress_counts(lines[position * 2 + 1]),
            [count, count, count, 1],
            "{text}"
        );
    }
    assert_eq!(
        lines[6], "Model checking completed. No error has been found.",
        "{text}"
    );
    assert!(
        text.contains(
            "1001 states generated, 1001 distinct states found, 0 states left on queue.\n"
        ),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

// TLC printed "periodic" as it started, and again just before its Progress line.
#[test]
fn prints_a_constant_periodic_expression_again_before_each_progress_as_tlc() {
    let spec = periodic_spec(PERIODIC_COUNTER, "PrintT(\"periodic\")");
    let (output, directory) = run_spec_every_300("periodic-again", &spec);
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(0), "{text}");
    assert!(
        text.contains(")\n\"periodic\"\nComputing initial states...\n"),
        "{text}"
    );
    let lines = get_search_lines(&text);
    for (position, count) in [301, 601, 901].into_iter().enumerate() {
        assert_eq!(lines[position * 2], "\"periodic\"", "{text}");
        assert_eq!(
            get_progress_counts(lines[position * 2 + 1]),
            [count, count, count, 1],
            "{text}"
        );
    }
    assert_eq!(
        lines[6], "Model checking completed. No error has been found.",
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

// Where the expression holds at one progress and is FALSE at the next, TLC prints the first
// progress, and at the next what the expression printed and the statistics, with exit 10.
#[test]
fn stops_at_the_progress_where_the_periodic_expression_turns_false() {
    let spec = periodic_spec(
        "x' = x + 1",
        "PrintT(TLCGet(\"distinct\")) /\\ TLCGet(\"distinct\") < 500",
    );
    let (output, directory) = run_spec_every_300("periodic-turns", &spec);
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(10), "{text}");
    let lines = get_search_lines(&text);
    assert_eq!(lines[0], "301", "{text}");
    assert_eq!(get_progress_counts(lines[1]), [301, 301, 301, 1], "{text}");
    assert_eq!(
        lines[2..5],
        [
            "601",
            "601 states generated, 601 distinct states found, 1 states left on queue.",
            "The depth of the complete state graph search is 601.",
        ],
        "{text}"
    );
    assert!(lines[5].starts_with("Finished in "), "{text}");
    std::fs::remove_dir_all(directory).expect("removed");
}

// On the clock, which reaches its first progress at any speed on an endless counter: TLC stops at
// its first progress, where the expression is FALSE, with what it printed and the
// statistics in place of the Progress line: `6240082`, then "6240082 states generated, 6240082
// distinct states found, 1 states left on queue." and its depth, with exit 10. With -tool it
// prints the progress first, as it prints the statistics.
#[test]
fn stops_where_the_periodic_expression_is_false_as_tlc() {
    let spec = periodic_spec(
        "x' = x + 1",
        "PrintT(TLCGet(\"distinct\")) /\\ TLCGet(\"distinct\") < 100",
    );
    for is_tool in [false, true] {
        let args: &[&str] = if is_tool { &["-tool"] } else { &[] };
        let (output, directory) = run_spec_with("periodic-stop", &spec, PERIODIC_CONFIG, args);
        let text = stdout(&output);
        assert_eq!(output.status.code(), Some(10), "{text}");
        let lines: Vec<&str> = text.lines().collect();
        let start = lines
            .iter()
            .position(|line| line.starts_with("Finished computing initial states: "))
            .expect("the initial states")
            + 1;
        let count = lines[start + usize::from(is_tool)];
        let number = count.parse::<u64>().expect("a count");
        assert!(number >= 100, "{text}");
        let statistics = format!(
            "{count} states generated, {count} distinct states found, 1 states left on queue."
        );
        let depth = format!("The depth of the complete state graph search is {count}.");
        let expected = if is_tool {
            let progress = lines[start + 3];
            assert_eq!(
                get_progress_counts(progress),
                [number, number, number, 1],
                "{text}"
            );
            vec![
                "@!@!@ENDMSG 2190 @!@!@",
                count,
                "@!@!@STARTMSG 2200:0 @!@!@",
                progress,
                "@!@!@ENDMSG 2200 @!@!@",
                "@!@!@STARTMSG 2199:0 @!@!@",
                &statistics,
                "@!@!@ENDMSG 2199 @!@!@",
                "@!@!@STARTMSG 2194:0 @!@!@",
                &depth,
                "@!@!@ENDMSG 2194 @!@!@",
                "@!@!@STARTMSG 2186:0 @!@!@",
            ]
        } else {
            vec![count, &statistics, &depth]
        };
        let end = start + expected.len();
        assert_eq!(lines[start..end], expected[..], "{text}");
        assert!(lines[end].starts_with("Finished in "), "{text}");
        std::fs::remove_dir_all(directory).expect("removed");
    }
}

// TLC fails where the expression reads TLCGet("duration") and prints its progress, which the
// trace evaluator doesn't follow, and fails comparing a value that is no boolean with FALSE.
#[test]
fn declines_a_periodic_expression_it_doesnt_follow() {
    for (periodic, reason) in [
        (
            "TLCGet(\"duration\") >= 0",
            "a _PERIODIC that fails to evaluate: TLCGet",
        ),
        ("3", "a _PERIODIC that isn't a boolean"),
    ] {
        let spec = periodic_spec("x' = x + 1", periodic);
        let (output, directory) = run_spec_every_300("periodic-declined", &spec);
        let text = stdout(&output);
        assert_eq!(output.status.code(), Some(1), "{text}");
        assert_eq!(
            String::from_utf8_lossy(&output.stderr),
            format!("prove-it: not native yet: {reason}\n")
        );
        assert!(!text.contains("Progress("), "{text}");
        std::fs::remove_dir_all(directory).expect("removed");
    }
}

// TLC compares the function a function definition is with FALSE at its first progress, and fails
// (exit 255, "Attempted to compare equality of boolean FALSE with non-boolean").
#[test]
fn declines_a_periodic_function_definition() {
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x' = x + 1\nPeriodic[n \\in {1}] == FALSE\n====\n";
    let (output, directory) = run_spec_every_300("periodic-function", spec);
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(1), "{text}");
    assert_eq!(
        String::from_utf8_lossy(&output.stderr),
        "prove-it: not native yet: a _PERIODIC naming a function definition\n"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

// TLC fails as it starts where the configuration assigns a value to the _PERIODIC name: it finds
// the value among its definitions and casts it to one (a ClassCastException, exit 255).
#[test]
fn declines_a_periodic_the_configuration_assigns_a_value_to() {
    let (output, directory) = run_spec_with(
        "periodic-assigned",
        &periodic_spec(PERIODIC_COUNTER, "TRUE"),
        &format!("{PERIODIC_CONFIG}CONSTANT Periodic = FALSE\n"),
        &[],
    );
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(1), "{text}");
    assert_eq!(
        String::from_utf8_lossy(&output.stderr),
        "prove-it: not native yet: a _PERIODIC the configuration assigns a value to\n"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

// TLC reads a definition through an assignment qualified by a module, `Q = [Stop] FALSE`, which
// the engine and the trace evaluator don't follow, and checks the temporal properties of the
// current state space before it evaluates the expression: the search declines at its first
// progress, and a run that ends first prints what TLC prints.
#[test]
fn declines_a_periodic_it_doesnt_follow_at_its_first_progress() {
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x < 1000 /\\ x' = x + 1\nQ == TRUE\nPeriodic == Q\nSpec == Init /\\ [][Next]_x\nLive == <>(x >= 0)\n====\n";
    for (test, config, reason) in [
        (
            "periodic-module-assignment",
            format!("{PERIODIC_CONFIG}CONSTANT Q = [Stop] FALSE\n"),
            "a _PERIODIC with a module's assignment in the configuration",
        ),
        (
            "periodic-temporal",
            "SPECIFICATION Spec\nPROPERTY Live\n_PERIODIC Periodic\nCHECK_DEADLOCK FALSE\n"
                .to_string(),
            "a _PERIODIC with temporal properties",
        ),
    ] {
        let (output, directory) = run_config_every_300(test, spec, &config);
        let text = stdout(&output);
        assert_eq!(output.status.code(), Some(1), "{text}");
        assert_eq!(
            String::from_utf8_lossy(&output.stderr),
            format!("prove-it: not native yet: {reason}\n")
        );
        std::fs::remove_dir_all(directory).expect("removed");
        let (output, directory) = run_spec_with(&format!("{test}-short"), spec, &config, &[]);
        let text = stdout(&output);
        assert_eq!(output.status.code(), Some(0), "{text}");
        assert!(
            text.contains("Model checking completed. No error has been found.\n"),
            "{text}"
        );
        std::fs::remove_dir_all(directory).expect("removed");
    }
}
