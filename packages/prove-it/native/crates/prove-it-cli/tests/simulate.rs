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

const PARTIAL: &str = "---- MODULE Part ----
EXTENDS Naturals
VARIABLES x, y
Init == \\/ x = 0 /\\ y = 1
        \\/ x = 1
Next == x' = x /\\ y' = y
====
";

// TLC's simulator counts the initial states, then stops at the first one that leaves a variable
// without a value, as it goes through them.
#[test]
fn reports_an_incomplete_initial_state_once_it_has_counted_them() {
    let (code, text) = simulate(
        "simulate-partial",
        "Part",
        (PARTIAL, "INIT Init\nNEXT Next\n"),
        &["-seed", "3", "-simulate", "num=1"],
    );
    assert_eq!(code, Some(255), "{text}");
    assert_eq!(
        text,
        "Computed 2 initial states...
Error: State is not completely specified by the initial predicate:
/\\ x = 1
/\\ y = null
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

#[test]
fn executes_only_the_chosen_successors_last_deferred_call() {
    let spec = "---- MODULE Deferred ----\nEXTENDS Naturals, TLC, TLCExt\nVARIABLE x\nInit == x = 0\nNext == \\E i \\in 1..2 : TLCDefer(PrintT(\"overwritten\")) /\\ TLCDefer(PrintT(<<i, x, x'>>)) /\\ x' = i\n====\n";
    let (code, text) = simulate(
        "simulate-deferred",
        "Deferred",
        (spec, "INIT Init\nNEXT Next\n"),
        &["-seed", "4", "-simulate", "num=1", "-depth", "2"],
    );
    assert_eq!(code, Some(0), "{text}");
    assert_eq!(
        text,
        "Computed 1 initial states...
Finished computing initial states: 1 distinct state generated at _.
<<1, 0, 1>>
<<1, 1, 1>>
Progress: 3 states checked, 1 traces generated (trace length: mean=2, var(x)=0, sd=0)
The number of states generated: 3
Simulation using seed 4 and aril 0"
    );
}

#[test]
fn exit_stops_simulation_without_completing_the_trace_statistics() {
    let spec = "---- MODULE Exit ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == x' = (x + 1) % 2 /\\ TLCSet(\"exit\", TRUE)\n====\n";
    let (code, text) = simulate(
        "simulate-exit",
        "Exit",
        (spec, "INIT Init\nNEXT Next\n"),
        &["-seed", "4", "-simulate", "num=2", "-depth", "3"],
    );
    assert_eq!(code, Some(0), "{text}");
    assert_eq!(
        text,
        "Computed 1 initial states...
Finished computing initial states: 1 distinct state generated at _.
Progress: 2 states checked, 1 traces generated (trace length: mean=0, var(x)=0, sd=0)
The number of states generated: 2
Simulation using seed 4 and aril 0"
    );
}

#[test]
fn deferred_calls_in_enabled_and_unchosen_actions_do_not_execute() {
    for next in [
        "(TLCDefer(PrintT(\"failed\")) /\\ FALSE /\\ x' = 1) \\/ x' = 1",
        "x' = 1 /\\ ENABLED (x' = 1 /\\ TLCDefer(PrintT(\"enabled\")))",
    ] {
        let spec = format!(
            "---- MODULE Silent ----\nEXTENDS Naturals, TLC, TLCExt\nVARIABLE x\nInit == x = 0\nNext == {next}\n====\n"
        );
        let (code, text) = simulate(
            "simulate-deferred-silent",
            "Silent",
            (&spec, "INIT Init\nNEXT Next\n"),
            &["-seed", "4", "-simulate", "num=1", "-depth", "2"],
        );
        assert_eq!(code, Some(0), "{text}");
        assert_eq!(
            text,
            "Computed 1 initial states...
Finished computing initial states: 1 distinct state generated at _.
Progress: 3 states checked, 1 traces generated (trace length: mean=2, var(x)=0, sd=0)
The number of states generated: 3
Simulation using seed 4 and aril 0"
        );
    }
}

#[test]
fn preserves_discarded_clock_queries_in_deferred_calls() {
    for expression in ["JavaTime", "<<JavaTime, 1>>", "LET t == JavaTime IN t"] {
        let spec = format!(
            "---- MODULE Clock ----\nEXTENDS Naturals, TLC, TLCExt\nVARIABLE x\nInit == x = 0\nNext == x' = 1 /\\ TLCDefer({expression})\n====\n"
        );
        let (code, text) = simulate(
            "simulate-deferred-clock",
            "Clock",
            (&spec, "INIT Init\nNEXT Next\n"),
            &["-seed", "4", "-simulate", "num=1", "-depth", "2"],
        );
        assert_eq!(code, Some(0), "{text}");
        assert_eq!(
            text,
            "Computed 1 initial states...
Finished computing initial states: 1 distinct state generated at _.
Progress: 3 states checked, 1 traces generated (trace length: mean=2, var(x)=0, sd=0)
The number of states generated: 3
Simulation using seed 4 and aril 0"
        );
    }
}

#[test]
fn reports_a_failure_in_the_next_states_with_the_summary() {
    let (code, text) = simulate(
        "simulate-nextfail",
        "NextFail",
        (
            "---- MODULE NextFail ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = 1 \\div (1 - x)
====
",
            "INIT Init
NEXT Next
",
        ),
        &["-seed", "4", "-simulate", "num=1", "-depth", "5"],
    );
    assert_eq!(code, Some(255), "{text}");
    assert_eq!(
        text,
        "Computed 1 initial states...
Finished computing initial states: 1 distinct state generated at _.
Error: TLC threw an unexpected exception.
This was probably caused by an error in the spec or model.
See the User Output or TLC Console for clues to what happened.
The exception was a tlc2.tool.EvalException
: The second argument of \\div is 0.
Error: The behavior up to this point is:
State 1: <Init line 4, col 9 to line 4, col 13 of module NextFail>
x = 0

State 2: <Next line 5, col 9 to line 5, col 27 of module NextFail>
x = 1

The number of states generated: 2
Simulation using seed 4 and aril 0
Progress: 2 states checked, 1 traces generated (trace length: mean=0, var(x)=0, sd=0)"
    );
}

#[test]
fn reports_a_tlc_runtime_exception_without_the_summary() {
    let (code, text) = simulate(
        "simulate-recfail",
        "RecFail",
        (
            "---- MODULE RecFail ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = x + [a |-> 1].b
====
",
            "INIT Init
NEXT Next
",
        ),
        &["-seed", "4", "-simulate", "num=1", "-depth", "5"],
    );
    assert_eq!(code, Some(255), "{text}");
    assert_eq!(
        text,
        "Computed 1 initial states...
Finished computing initial states: 1 distinct state generated at _.
Error: TLC threw an unexpected exception.
This was probably caused by an error in the spec or model.
See the User Output or TLC Console for clues to what happened.
The exception was a java.lang.RuntimeException
: Attempted to select nonexistent field \"b\" from the record
[a |-> 1]
line 5, col 18 to line 5, col 28 of module RecFail
Error: The behavior up to this point is:
State 1: <Init line 4, col 9 to line 4, col 13 of module RecFail>
x = 0

Progress: 1 states checked, 1 traces generated (trace length: mean=0, var(x)=0, sd=0)"
    );
}

#[test]
fn reports_an_invariant_that_fails_to_evaluate() {
    let (code, text) = simulate(
        "simulate-invfail",
        "InvFail",
        (
            "---- MODULE InvFail ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = x + 1
Inv == 1 \\div (1 - x) >= 0
====
",
            "INIT Init
NEXT Next
INVARIANT Inv
",
        ),
        &["-seed", "4", "-simulate", "num=1", "-depth", "5"],
    );
    assert_eq!(code, Some(76), "{text}");
    assert_eq!(
        text,
        "Computed 1 initial states...
Finished computing initial states: 1 distinct state generated at _.
Error: Evaluating invariant Inv failed.
The second argument of \\div is 0.
Error: The behavior up to this point is:
State 1: <Init line 4, col 9 to line 4, col 13 of module InvFail>
x = 0

State 2: <Next line 5, col 9 to line 5, col 18 of module InvFail>
x = 1

The number of states generated: 2
Simulation using seed 4 and aril 0
Progress: 2 states checked, 1 traces generated (trace length: mean=0, var(x)=0, sd=0)"
    );
}

#[test]
fn checks_the_postconditions_once_it_has_simulated() {
    let (code, text) = simulate(
        "simulate-postfalse",
        "PostFalse",
        (
            "---- MODULE PostFalse ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 0
Next == x' = x + 1
Post == PrintT(x) /\\ x = 9
====
",
            "INIT Init
NEXT Next
POSTCONDITION Post
",
        ),
        &["-seed", "4", "-simulate", "num=1", "-depth", "5"],
    );
    assert_eq!(code, Some(10), "{text}");
    assert_eq!(
        text,
        "Computed 1 initial states...
Finished computing initial states: 1 distinct state generated at _.
Error: Evaluating postcondition Post at line 6, col 9 to line 6, col 26 of module PostFalse failed.
In evaluation, the identifier x is either undefined or not an operator.
line 6, col 16 to line 6, col 16 of module PostFalse
Progress: 6 states checked, 1 traces generated (trace length: mean=5, var(x)=0, sd=0)"
    );
}

#[test]
fn reports_a_violated_action_property() {
    let (code, text) = simulate(
        "simulate-actprop",
        "ActProp",
        (
            "---- MODULE ActProp ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == x' = x + 1
P == [][x' < 2]_x
====
",
            "INIT Init
NEXT Next
PROPERTY P
",
        ),
        &["-seed", "4", "-simulate", "num=1", "-depth", "5"],
    );
    assert_eq!(code, Some(13), "{text}");
    assert_eq!(
        text,
        "Computed 1 initial states...
Finished computing initial states: 1 distinct state generated at _.
Error: Action property P is violated.
Error: The behavior up to this point is:
State 1: <Init line 4, col 9 to line 4, col 13 of module ActProp>
x = 0

State 2: <Next line 5, col 9 to line 5, col 18 of module ActProp>
x = 1

State 3: <Next line 5, col 9 to line 5, col 18 of module ActProp>
x = 2

The number of states generated: 3
Simulation using seed 4 and aril 0
Progress: 3 states checked, 1 traces generated (trace length: mean=0, var(x)=0, sd=0)"
    );
}

#[test]
fn reads_the_simulations_run_with_tlcget() {
    let (code, text) = simulate(
        "simulate-run",
        "Run",
        ("---- MODULE Run ----
EXTENDS Naturals, TLC
VARIABLE x
Init == x = 0
A == x' = x + 1 /\\ PrintT(<<TLCGet(\"action\").name, TLCGet(\"diameter\"), TLCGet(\"stats\").generated, TLCGet(\"stats\").behavior.id>>)
B == x' = x + 2 /\\ PrintT(TLCGet(\"action\").location)
Next == A \\/ B
====
", "INIT Init
NEXT Next
"),
        &["-seed", "4", "-simulate", "num=2", "-depth", "2"],
    );
    assert_eq!(code, Some(0), "{text}");
    assert_eq!(
        text,
        "Computed 1 initial states...
Finished computing initial states: 1 distinct state generated at _.
<<\"Init\", 1, 1, 1>>
<<\"A\", 1, 2, 1>>
[ beginLine |-> 4,
  beginColumn |-> 9,
  endLine |-> 4,
  endColumn |-> 13,
  module |-> \"Run\" ]
<<\"B\", 2, 4, 2>>
Progress: 5 states checked, 2 traces generated (trace length: mean=2, var(x)=0, sd=0)
The number of states generated: 5
Simulation using seed 4 and aril 0"
    );
}

const TEMPORAL_CONFIG: &str = "SPECIFICATION Spec\nPROPERTY Prop\nCHECK_DEADLOCK FALSE\n";

// TLC's LiveCheck1 prints the behavior's states, from its first, as many as the prefix to the
// bad cycle and the cycle change state, then steps back by the behavior's next step.
#[test]
fn prints_a_behaviors_counterexample_to_a_temporal_property_as_tlc() {
    let (code, text) = simulate(
        "simulate-lasso",
        "Lasso",
        (
            "---- MODULE Lasso ----
EXTENDS Naturals
VARIABLE x
Next == x' = (x + 1) % 3
Spec == x = 0 /\\ [][Next]_x /\\ WF_x(Next)
Prop == x = 1 ~> x = 99
====
",
            TEMPORAL_CONFIG,
        ),
        &["-seed", "4", "-simulate", "num=8", "-depth", "6"],
    );
    assert_eq!(code, Some(13), "{text}");
    assert_eq!(
        text,
        "Implied-temporal checking--satisfiability problem has 1 branches.
Computed 1 initial states...
Finished computing initial states: 1 distinct state generated at _.
Error: Temporal property Prop was violated.

Error: The following behavior constitutes a counter-example:

State 1: <Initial predicate line 5, col 9 to line 5, col 13 of module Lasso>
x = 0

State 2: <Next line 4, col 9 to line 4, col 24 of module Lasso>
x = 1

State 3: <Next line 4, col 9 to line 4, col 24 of module Lasso>
x = 2

State 4: <Next line 4, col 9 to line 4, col 24 of module Lasso>
x = 0

Back to state 2: <Next line 4, col 9 to line 4, col 24 of module Lasso>

The number of states generated: 7
Simulation using seed 4 and aril 0
Progress: 7 states checked, 1 traces generated (trace length: mean=0, var(x)=0, sd=0)"
    );
}

// Where the bad cycle's node is the last state printed, TLC ends with a stuttering step.
#[test]
fn ends_a_behaviors_counterexample_by_stuttering_as_tlc() {
    let (code, text) = simulate(
        "simulate-stuttering-lasso",
        "Stut",
        (
            "---- MODULE Stut ----
EXTENDS Naturals
VARIABLE x
Next == x < 2 /\\ x' = x + 1
Spec == x = 0 /\\ [][Next]_x
Prop == []<>(x = 2)
====
",
            TEMPORAL_CONFIG,
        ),
        &["-seed", "4", "-simulate", "num=8", "-depth", "6"],
    );
    assert_eq!(code, Some(13), "{text}");
    assert_eq!(
        text,
        "Implied-temporal checking--satisfiability problem has 1 branches.
Computed 1 initial states...
Finished computing initial states: 1 distinct state generated at _.
Error: Temporal property Prop was violated.

Error: The following behavior constitutes a counter-example:

State 1: <Initial predicate line 5, col 9 to line 5, col 13 of module Stut>
x = 0

State 2: <Next line 4, col 9 to line 4, col 27 of module Stut>
x = 1

State 3: Stuttering
The number of states generated: 3
Simulation using seed 4 and aril 0
Progress: 3 states checked, 1 traces generated (trace length: mean=0, var(x)=0, sd=0)"
    );
}

// With temporal properties, TLC counts a trace's length at the level `SimulationWorker.getTrace`
// leaves its last state at: the number of states without the stuttering steps, unless the last
// step stutters, whose state keeps the level it was generated at. Recorded from TLC at d8fb231.
#[test]
fn counts_the_lengths_of_the_traces_it_checks_the_properties_of_as_tlc() {
    let cases = [
        (
            "---- MODULE Live ----
EXTENDS Naturals
VARIABLE x
Init == x \\in 0..2
Next == \\/ x' = (x + 1) % 4
        \\/ UNCHANGED x
Spec == Init /\\ [][Next]_x /\\ WF_x(x' = (x + 1) % 4)
Live == []<>(x = 3)
====
",
            "Computed 3 initial states...
Finished computing initial states: 3 distinct state generated at _.
Progress: 78 states checked, 5 traces generated (trace length: mean=12, var(x)=8, sd=3)
The number of states generated: 78
Simulation using seed 4 and aril 0",
        ),
        (
            "---- MODULE Live ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == \\/ x < 5 /\\ x' = x + 1
        \\/ UNCHANGED x
Spec == Init /\\ [][Next]_x /\\ WF_x(x < 5 /\\ x' = x + 1)
Live == <>(x = 5)
====
",
            "Computed 1 initial states...
Finished computing initial states: 1 distinct state generated at _.
Progress: 76 states checked, 5 traces generated (trace length: mean=15, var(x)=0, sd=0)
The number of states generated: 76
Simulation using seed 4 and aril 0",
        ),
    ];
    for (index, (spec, expected)) in cases.into_iter().enumerate() {
        let (code, text) = simulate(
            &format!("simulate-live-lengths-{index}"),
            "Live",
            (spec, "SPECIFICATION Spec\nPROPERTY Live\n"),
            &["-seed", "4", "-simulate", "num=5", "-depth", "15"],
        );
        assert_eq!(code, Some(0), "{text}");
        assert_eq!(
            text,
            format!(
                "Implied-temporal checking--satisfiability problem has 1 branches.\n{expected}"
            )
        );
    }
}

// A simulation without `num=` runs until it is stopped, as TLC's does, and holds no more memory
// the more traces it generates: the trace's number TLCGet("diameter") reads is never made a
// value, and a read of it or of TLCGet("stats") as the worker runs declines.
#[cfg(target_os = "linux")]
#[test]
fn simulates_without_end_in_constant_memory() {
    let spec = |invariant: &str| {
        format!(
            "---- MODULE Soak ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\n\
             Next == x' = (x + 1) % 3\nInv == {invariant}\n====\n"
        )
    };
    let run = |name: &str, invariant: &str, depth: &str| {
        let directory = std::env::temp_dir().join(format!(
            "prove-it-cli-simulate-soak-{name}-{}",
            std::process::id()
        ));
        std::fs::create_dir_all(&directory).expect("a directory");
        std::fs::write(directory.join("Soak.tla"), spec(invariant)).expect("a spec");
        std::fs::write(directory.join("Soak.cfg"), INVARIANT_CONFIG).expect("a configuration");
        let child = std::process::Command::new(env!("CARGO_BIN_EXE_prove-it"))
            .args([
                "-workers",
                "1",
                "-noTE",
                "-simulate",
                "-depth",
                depth,
                "Soak.tla",
            ])
            .current_dir(&directory)
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::piped())
            .spawn()
            .expect("the binary runs");
        (directory, child)
    };
    // The diameter in a disjunct the model never evaluates.
    for depth in ["0", "1", "5"] {
        let (directory, mut child) = run("flat", "x < 5 \\/ TLCGet(\"diameter\") > 0", depth);
        let resident = |pid: u32| -> Option<u64> {
            let status = std::fs::read_to_string(format!("/proc/{pid}/status")).ok()?;
            let line = status.lines().find(|line| line.starts_with("VmRSS:"))?;
            line.split_whitespace().nth(1)?.parse().ok()
        };
        std::thread::sleep(std::time::Duration::from_secs(1));
        let early = resident(child.id());
        std::thread::sleep(std::time::Duration::from_secs(3));
        let late = resident(child.id());
        let still_running = child.try_wait().expect("the child's status").is_none();
        child.kill().ok();
        child.wait().ok();
        std::fs::remove_dir_all(&directory).expect("removed");
        assert!(still_running, "the simulation stopped by itself");
        let (Some(early), Some(late)) = (early, late) else {
            panic!("no resident set size in /proc");
        };
        assert!(
            late < early + 16 * 1024,
            "the resident set grew from {early} kB to {late} kB at depth {depth}"
        );
    }
    for invariant in ["TLCGet(\"diameter\") >= 0", "TLCGet(\"stats\").traces >= 0"] {
        for depth in ["0", "5"] {
            let (directory, child) = run("declined", invariant, depth);
            let output = child.wait_with_output().expect("the binary ends");
            std::fs::remove_dir_all(&directory).expect("removed");
            assert_eq!(output.status.code(), Some(1));
            assert_eq!(
                String::from_utf8_lossy(&output.stderr),
                "prove-it: not native yet: the engine declined: unsupported: TLCGet of a trace's \
                 count in a simulation without end\n"
            );
        }
    }
}
