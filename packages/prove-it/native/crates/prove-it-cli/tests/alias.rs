//! Runs the binary on specs whose ALIAS TLC doesn't turn into a state, as TLC ran them at d8fb231
//! with `-workers 1`: TLC prints the state itself for an alias that is neither a record nor a
//! function of strings (`Value.toState`), and for a literal, which it keeps as an operator rather
//! than a value it computed as it started.

mod common;

use common::{run_spec_with, stdout};

fn alias_spec(initial: u32, alias: &str) -> String {
    format!(
        "---- MODULE Stop ----\nEXTENDS Naturals, TLC, Sequences\nVARIABLES x, y\nInit == x = {initial} /\\ y = \"s\"\nNext == x < 3 /\\ x' = x + 1 /\\ y' = y\nAl == {alias}\n====\n"
    )
}

const ALIAS_CONFIG: &str = "INIT Init\nNEXT Next\nALIAS Al\n";

#[test]
fn prints_the_states_where_the_alias_is_no_record_as_tlc() {
    for (test, alias) in [
        ("alias-tuple", "<<x, y>>"),
        ("alias-function", "[i \\in 1..2 |-> x]"),
        ("alias-number", "5"),
        ("alias-string", "\"str\""),
    ] {
        let (output, directory) = run_spec_with(test, &alias_spec(1, alias), ALIAS_CONFIG, &[]);
        let text = stdout(&output);
        assert_eq!(output.status.code(), Some(11), "{text}");
        assert!(
            text.contains("Error: Deadlock reached.\nError: The behavior up to this point is:\nState 1: <Initial predicate>\n/\\ x = 1\n/\\ y = \"s\"\n\nState 2: <Next line 5, col 9 to line 5, col 37 of module Stop>\n/\\ x = 2\n/\\ y = \"s\"\n\nState 3: <Next line 5, col 9 to line 5, col 37 of module Stop>\n/\\ x = 3\n/\\ y = \"s\"\n\n3 states generated"),
            "{alias}: {text}"
        );
        std::fs::remove_dir_all(directory).expect("removed");
    }
}

// TLC's simulation prints a deadlocked initial state through the ALIAS too.
#[test]
fn prints_a_simulated_initial_deadlock_where_the_alias_is_no_record_as_tlc() {
    for (test, alias) in [
        ("alias-simulated-tuple", "<<x, y>>"),
        ("alias-simulated-number", "5"),
    ] {
        let (output, directory) = run_spec_with(
            test,
            &alias_spec(5, alias),
            ALIAS_CONFIG,
            &["-simulate", "num=1", "-seed", "1"],
        );
        let text = stdout(&output);
        assert_eq!(output.status.code(), Some(11), "{text}");
        assert!(
            text.contains("Error: Deadlock reached.\nError: The behavior up to this point is:\nState 1: <Init line 4, col 9 to line 4, col 24 of module Stop>\n/\\ x = 5\n/\\ y = \"s\"\n\nThe number of states generated: 1\nSimulation using seed 1 and aril 0\n"),
            "{alias}: {text}"
        );
        std::fs::remove_dir_all(directory).expect("removed");
    }
}
