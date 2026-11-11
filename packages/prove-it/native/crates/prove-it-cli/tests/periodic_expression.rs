//! Runs the binary on specs with a `_PERIODIC` expression, which TLC evaluates as it prints its
//! progress.

mod common;

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

// A counter long enough to reach the binary's first progress, 3 s in, in a debug build.
const PERIODIC_COUNTER: &str = "x < 4000000 /\\ x' = x + 1";

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
    let (output, directory) = run_spec("periodic-counts", &spec, PERIODIC_CONFIG);
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(0), "{text}");
    let lines: Vec<&str> = text.lines().collect();
    let progress: Vec<usize> = (0..lines.len())
        .filter(|&index| lines[index].starts_with("Progress("))
        .collect();
    assert!(!progress.is_empty(), "{text}");
    for index in progress {
        let [depth, generated, distinct, queued] = get_progress_counts(lines[index]);
        assert_eq!(
            lines[index - 1],
            format!("<<{distinct}, {generated}, {queued}, {depth}, 1>>"),
            "{text}"
        );
    }
    assert!(
        text.contains("Model checking completed. No error has been found."),
        "{text}"
    );
    assert!(
        text.contains(
            "4000001 states generated, 4000001 distinct states found, 0 states left on queue.\n"
        ),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

// TLC printed "periodic" as it started, and again just before its Progress line.
#[test]
fn prints_a_constant_periodic_expression_again_before_each_progress_as_tlc() {
    let spec = periodic_spec(PERIODIC_COUNTER, "PrintT(\"periodic\")");
    let (output, directory) = run_spec("periodic-again", &spec, PERIODIC_CONFIG);
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(0), "{text}");
    assert!(
        text.contains(")\n\"periodic\"\nComputing initial states...\n"),
        "{text}"
    );
    let lines: Vec<&str> = text.lines().collect();
    let progress: Vec<usize> = (0..lines.len())
        .filter(|&index| lines[index].starts_with("Progress("))
        .collect();
    assert!(!progress.is_empty(), "{text}");
    for &index in &progress {
        assert_eq!(lines[index - 1], "\"periodic\"", "{text}");
    }
    assert_eq!(
        lines.iter().filter(|line| **line == "\"periodic\"").count(),
        progress.len() + 1,
        "{text}"
    );
    assert!(
        text.contains("Model checking completed. No error has been found."),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

// TLC stops at its first progress, where the expression is FALSE, with what it printed and the
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
        let (output, directory) = run_spec("periodic-declined", &spec, PERIODIC_CONFIG);
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
