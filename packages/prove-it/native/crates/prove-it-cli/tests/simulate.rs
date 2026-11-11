//! `-simulate`: each expected output is what TLC at d8fb231 prints for the spec and command line
//! with `-workers 1`, from the line after `Starting...` to the one before `Finished in`, with each
//! date written as `_`.

mod common;

use common::{run_named, stdout};

const VIOL: &str = "---- MODULE Viol ----
EXTENDS Naturals
VARIABLE x, y
Init == x \\in {0, 1} /\\ y = 0
A == x' = x + 1 /\\ y' = y
B == y' = y + 2 /\\ x' = x
C == x' = x /\\ y' = y
Next == A \\/ B \\/ C
Inv == x + y < 12
====
";

const DEAD: &str = "---- MODULE Dead ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x < 3 /\\ x' \\in {x + 1, x + 2}
====
";

const PAR: &str = "---- MODULE Par ----
EXTENDS Naturals
VARIABLE x
Init == x = [p \\in {1, 2} |-> 0]
A(p) == x[p] < 2 /\\ x' = [x EXCEPT ![p] = @ + 1]
Next == \\E p \\in {1, 2} : A(p)
Inv == x[1] + x[2] < 3
====
";

const INITIAL: &str = "---- MODULE InitV ----
EXTENDS Naturals
VARIABLE x
Init == x \\in 0..5
Next == x' = x + 1
Inv == x < 3
====
";

const STUTTERING: &str = "---- MODULE Stut ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 0
A == x' = x + 1
B == UNCHANGED x
Next == A \\/ B
Inv == TLCGet(\"level\") < 9 \\/ x < 3
====
";

// TLC's Github743: a step from x = TRUE to x = "foo", which TLC fails to compare as it drops the
// trace's stuttering steps.
const INCOMPARABLE: &str = "---- MODULE Github743 ----
EXTENDS Integers
VARIABLES x, y
Init == x = \"foo\" /\\ y = 0
Next == \\/ x' = \"foo\" /\\ y' = y + 1
        \\/ x' = TRUE /\\ y' = y + 2
Inv == y < 5
====
";

const INVARIANT_CONFIG: &str = "INIT Init\nNEXT Next\nINVARIANT Inv\n";

// Each date, yyyy-mm-dd hh:mm:ss, as `_`.
fn replace_dates(line: &str) -> String {
    let shape = "0000-00-00 00:00:00";
    let bytes = line.as_bytes();
    let mut text = String::new();
    let mut index = 0;
    while index < bytes.len() {
        let is_date = bytes.len() - index >= shape.len()
            && shape.bytes().zip(&bytes[index..]).all(|(expected, &byte)| {
                if expected == b'0' {
                    byte.is_ascii_digit()
                } else {
                    byte == expected
                }
            });
        if is_date {
            text.push('_');
            index += shape.len();
        } else {
            text.push(bytes[index] as char);
            index += 1;
        }
    }
    text
}

// Simulates the spec, returning the exit code and what TLC prints between `Starting...` and
// `Finished in`.
fn simulate(test: &str, name: &str, files: (&str, &str), args: &[&str]) -> (Option<i32>, String) {
    let mut all = vec!["-workers", "1", "-nowarning", "-noTE"];
    all.extend_from_slice(args);
    all.push(name);
    let (output, directory) = run_named(test, name, files, &all);
    std::fs::remove_dir_all(directory).expect("removed");
    let text = stdout(&output);
    let lines: Vec<&str> = text.lines().collect();
    let start = lines
        .iter()
        .position(|line| line.starts_with("Starting... ("))
        .map_or(0, |index| index + 1);
    let end = lines.len().saturating_sub(1).max(start);
    let body: Vec<String> = lines[start..end]
        .iter()
        .map(|line| replace_dates(line))
        .collect();
    (output.status.code(), body.join("\n"))
}

#[test]
fn prints_a_violated_invariants_trace_as_tlc() {
    let (code, text) = simulate(
        "simulate-invariant",
        "Viol",
        (VIOL, INVARIANT_CONFIG),
        &["-seed", "4", "-simulate", "num=1", "-depth", "100"],
    );
    assert_eq!(code, Some(12), "{text}");
    assert_eq!(
        text,
        "Computed 2 initial states...
Finished computing initial states: 2 distinct state generated at _.
Error: Invariant Inv is violated.
Error: The behavior up to this point is:
State 1: <Init line 4, col 9 to line 4, col 29 of module Viol>
/\\ x = 1
/\\ y = 0

State 2: <A line 5, col 6 to line 5, col 25 of module Viol>
/\\ x = 2
/\\ y = 0

State 3: <A line 5, col 6 to line 5, col 25 of module Viol>
/\\ x = 3
/\\ y = 0

State 4: <B line 6, col 6 to line 6, col 25 of module Viol>
/\\ x = 3
/\\ y = 2

State 5: <B line 6, col 6 to line 6, col 25 of module Viol>
/\\ x = 3
/\\ y = 4

State 6: <A line 5, col 6 to line 5, col 25 of module Viol>
/\\ x = 4
/\\ y = 4

State 7: <B line 6, col 6 to line 6, col 25 of module Viol>
/\\ x = 4
/\\ y = 6

State 8: <B line 6, col 6 to line 6, col 25 of module Viol>
/\\ x = 4
/\\ y = 8

The number of states generated: 13
Simulation using seed 4 and aril 0
Progress: 13 states checked, 1 traces generated (trace length: mean=0, var(x)=0, sd=0)"
    );
}

#[test]
fn prints_a_deadlock_as_tlc() {
    let summary = "The number of states generated: 7
Simulation using seed 7 and aril 0
Progress: 7 states checked, 1 traces generated (trace length: mean=0, var(x)=0, sd=0)";
    let (code, text) = simulate(
        "simulate-deadlock",
        "Dead",
        (DEAD, "INIT Init\nNEXT Next\n"),
        &["-seed", "7", "-simulate", "num=1", "-depth", "10"],
    );
    assert_eq!(code, Some(11), "{text}");
    assert_eq!(
        text,
        format!(
            "Computed 1 initial states...
Finished computing initial states: 1 distinct state generated at _.
Error: Deadlock reached.
Error: The behavior up to this point is:
State 1: <Init line 4, col 9 to line 4, col 13 of module Dead>
x = 0

State 2: <Next line 5, col 9 to line 5, col 38 of module Dead>
x = 1

State 3: <Next line 5, col 9 to line 5, col 38 of module Dead>
x = 2

State 4: <Next line 5, col 9 to line 5, col 38 of module Dead>
x = 3

{summary}"
        )
    );
    // With no bound on the depth TLC prints the error state alone.
    let (code, text) = simulate(
        "simulate-unbounded",
        "Dead",
        (DEAD, "INIT Init\nNEXT Next\n"),
        &["-seed", "7", "-simulate", "num=1", "-depth", "-1"],
    );
    assert_eq!(code, Some(11), "{text}");
    assert_eq!(
        text,
        format!(
            "Computed 1 initial states...
Finished computing initial states: 1 distinct state generated at _.
Error: Deadlock reached.
The error state is:

State :
x = 3

{summary}"
        )
    );
}

#[test]
fn reports_the_lengths_of_the_traces_as_tlc() {
    let (code, text) = simulate(
        "simulate-lengths",
        "Dead",
        (DEAD, "INIT Init\nNEXT Next\n"),
        &[
            "-seed",
            "7",
            "-simulate",
            "num=5",
            "-depth",
            "10",
            "-deadlock",
        ],
    );
    assert_eq!(code, Some(0), "{text}");
    assert_eq!(
        text,
        "Computed 1 initial states...
Finished computing initial states: 1 distinct state generated at _.
Progress: 23 states checked, 5 traces generated (trace length: mean=4, var(x)=1, sd=1)
The number of states generated: 23
Simulation using seed 7 and aril 0"
    );
    let (code, text) = simulate(
        "simulate-tool",
        "Dead",
        (DEAD, "INIT Init\nNEXT Next\n"),
        &[
            "-tool",
            "-seed",
            "7",
            "-simulate",
            "num=5",
            "-depth",
            "10",
            "-deadlock",
        ],
    );
    assert_eq!(code, Some(0), "{text}");
    assert!(
        text.contains(
            "@!@!@STARTMSG 2209:0 @!@!@
Progress(5) at _: 23 states generated, -1 distinct states found, -1 states left on queue.
@!@!@ENDMSG 2209 @!@!@
@!@!@STARTMSG 2209:0 @!@!@
Progress(5) at _: 23 states generated, -1 distinct states found, -1 states left on queue.
@!@!@ENDMSG 2209 @!@!@
@!@!@STARTMSG 2210:0 @!@!@
The number of states generated: 23
Simulation using seed 7 and aril 0
@!@!@ENDMSG 2210 @!@!@
@!@!@STARTMSG 2186:0 @!@!@"
        ),
        "{text}"
    );
}

#[test]
fn labels_the_steps_with_tlcs_actions() {
    let (code, text) = simulate(
        "simulate-actions",
        "Par",
        (PAR, INVARIANT_CONFIG),
        &["-seed", "7", "-simulate", "num=1", "-depth", "10"],
    );
    assert_eq!(code, Some(12), "{text}");
    assert!(
        text.contains(
            "State 1: <Init line 4, col 9 to line 4, col 32 of module Par>
x = <<0, 0>>

State 2: <A(1) line 5, col 9 to line 5, col 48 of module Par>
x = <<1, 0>>

State 3: <A(2) line 5, col 9 to line 5, col 48 of module Par>
x = <<1, 1>>

State 4: <A(2) line 5, col 9 to line 5, col 48 of module Par>
x = <<1, 2>>
"
        ),
        "{text}"
    );
}

#[test]
fn checks_the_initial_states_first() {
    let (code, text) = simulate(
        "simulate-initial",
        "InitV",
        (INITIAL, INVARIANT_CONFIG),
        &["-seed", "3", "-simulate", "num=3", "-aril", "2"],
    );
    assert_eq!(code, Some(12), "{text}");
    assert_eq!(
        text,
        "Computed 6 initial states...
Error: Invariant Inv is violated by the initial state:
x = 3
"
    );
}

// TLC's worker goes on as its main thread prints a violation, so the counts it reports after one
// race the worker, but for a violation in the last trace.
#[test]
fn declines_what_races_tlcs_worker() {
    for args in [
        &["-seed", "4", "-simulate", "num=10"][..],
        &["-seed", "4", "-simulate"],
    ] {
        let (output, directory) = run_named(
            "simulate-races",
            "Viol",
            (VIOL, INVARIANT_CONFIG),
            &[&["-noTE"][..], args, &["Viol"]].concat(),
        );
        std::fs::remove_dir_all(directory).expect("removed");
        assert_eq!(output.status.code(), Some(1));
        let error = String::from_utf8_lossy(&output.stderr);
        assert!(
            error.contains("a simulation's violation before its last trace"),
            "{error}"
        );
    }
}

// TLC's simulator reports a violation under -continue and goes on generating traces, then exits
// with 0, which the binary doesn't model.
#[test]
fn declines_a_violation_under_continue() {
    let (output, directory) = run_named(
        "simulate-continue",
        "Viol",
        (VIOL, INVARIANT_CONFIG),
        &[
            "-noTE",
            "-seed",
            "4",
            "-simulate",
            "num=1",
            "-continue",
            "Viol",
        ],
    );
    std::fs::remove_dir_all(directory).expect("removed");
    assert_eq!(output.status.code(), Some(1));
    let error = String::from_utf8_lossy(&output.stderr);
    assert!(
        error.contains("a simulation's violation under -continue"),
        "{error}"
    );
}

// TLCGet("level") counts the stuttering steps, which the trace TLC prints drops.
#[test]
fn drops_the_stuttering_steps_as_tlc() {
    let (code, text) = simulate(
        "simulate-stuttering",
        "Stut",
        (STUTTERING, INVARIANT_CONFIG),
        &["-seed", "4", "-simulate", "num=1", "-depth", "50"],
    );
    assert_eq!(code, Some(12), "{text}");
    assert_eq!(
        text,
        "Computed 1 initial states...
Finished computing initial states: 1 distinct state generated at _.
Error: Invariant Inv is violated.
Error: The behavior up to this point is:
State 1: <Init line 4, col 9 to line 4, col 13 of module Stut>
x = 0

State 2: <A line 5, col 6 to line 5, col 15 of module Stut>
x = 1

State 3: <A line 5, col 6 to line 5, col 15 of module Stut>
x = 2

State 4: <A line 5, col 6 to line 5, col 15 of module Stut>
x = 3

State 5: <A line 5, col 6 to line 5, col 15 of module Stut>
x = 4

The number of states generated: 9
Simulation using seed 4 and aril 0
Progress: 9 states checked, 1 traces generated (trace length: mean=0, var(x)=0, sd=0)"
    );
}

// TLC reports the exception it throws comparing the states, which the binary doesn't print yet.
#[test]
fn declines_a_trace_tlc_fails_to_compare() {
    let (output, directory) = run_named(
        "simulate-incomparable",
        "Github743",
        (INCOMPARABLE, INVARIANT_CONFIG),
        &["-noTE", "-seed", "4", "-simulate", "num=1", "Github743"],
    );
    std::fs::remove_dir_all(directory).expect("removed");
    assert_eq!(output.status.code(), Some(1));
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("a failure evaluating the model in a simulation")
    );
}

// As TLC ran them at d8fb231: TLC caches TLCGet("config") as it builds its simulator, before it
// reads the aril, which the summary then reports.
#[test]
fn reads_tlcs_cached_config_aril() {
    let spec = "---- MODULE Aril ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == x' = (x + 1) % 3\nInv == TLCGet(\"config\").aril = \"0\"\n====\n";
    let (code, text) = simulate(
        "simulate-aril",
        "Aril",
        (spec, INVARIANT_CONFIG),
        &[
            "-seed",
            "4",
            "-aril",
            "2",
            "-simulate",
            "num=1",
            "-depth",
            "5",
        ],
    );
    assert_eq!(code, Some(0), "{text}");
    assert_eq!(
        text,
        "Computed 1 initial states...
Finished computing initial states: 1 distinct state generated at _.
Progress: 6 states checked, 1 traces generated (trace length: mean=5, var(x)=0, sd=0)
The number of states generated: 6
Simulation using seed 4 and aril 2"
    );
}

// TLC's simulation prints a deadlocked initial state through the ALIAS, as it does every state
// of its trace (`SimulationWorker`), where the model checker prints it as it is.
#[test]
fn prints_a_deadlocked_initial_state_through_the_alias() {
    let spec = "---- MODULE Dead ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x > 5 /\\ x' = x\nView == [shown |-> x + 10]\n====\n";
    let (code, text) = simulate(
        "simulate-alias",
        "Dead",
        (spec, "INIT Init\nNEXT Next\nALIAS View\n"),
        &["-seed", "4", "-simulate", "num=1"],
    );
    assert_eq!(code, Some(11), "{text}");
    assert_eq!(
        text,
        "Computed 1 initial states...
Finished computing initial states: 1 distinct state generated at _.
Error: Deadlock reached.
Error: The behavior up to this point is:
State 1: <Init line 4, col 9 to line 4, col 13 of module Dead>
shown = 10

The number of states generated: 1
Simulation using seed 4 and aril 0
Progress: 1 states checked, 1 traces generated (trace length: mean=0, var(x)=0, sd=0)"
    );
}

// TLC's simulation binds Trace to records that carry each state's action, `_action`
// (`TLCExt.getTrace`), which the trace evaluator doesn't make.
#[test]
fn declines_a_simulations_alias_that_reads_trace() {
    let spec = "---- MODULE Dead ----\nEXTENDS Naturals, TLCExt\nVARIABLE x\nInit == x = 0\nNext == x > 5 /\\ x' = x\nAl == [x |-> x, t |-> Trace]\n====\n";
    let (output, directory) = run_named(
        "simulate-alias-trace",
        "Dead",
        (spec, "INIT Init\nNEXT Next\nALIAS Al\n"),
        &["-noTE", "-seed", "1", "-simulate", "num=1", "Dead"],
    );
    std::fs::remove_dir_all(directory).expect("removed");
    assert_eq!(output.status.code(), Some(1));
    let error = String::from_utf8_lossy(&output.stderr);
    assert!(
        error.contains("a simulation's ALIAS that reads Trace"),
        "{error}"
    );
}
