//! A state several threads reach in a shared level is checked by the first to reach it, and what
//! its check finds comes out where TLC's one worker finds it.

mod common;

use common::{run_spec, stdout};

// Every state of the second level steps to the same state, the first of them after 20,000 others,
// so that another thread reaches that state first and checks it.
const NEXT: &str = "VARIABLES x, y\nInit == x = 0 /\\ y = 0\nNext == \\/ x = 0 /\\ y = 0 /\\ x' \\in 1..64 /\\ y' = 0\n        \\/ x = 1 /\\ y = 0 /\\ x' = 1 /\\ y' \\in 1..20000\n        \\/ x >= 1 /\\ y = 0 /\\ x' = 100 /\\ y' = 0\n";
const CONFIG: &str = "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n";

fn assert_on_threads(test: &str, invariant: &str, status: i32, expected: &str) {
    let spec = format!("---- MODULE Stop ----\nEXTENDS Naturals\n{NEXT}{invariant}\n====\n");
    let (output, directory) = run_spec(test, &spec, CONFIG);
    assert_eq!(output.status.code(), Some(status), "{}", stdout(&output));
    assert!(stdout(&output).contains(expected), "{}", stdout(&output));
    for threads in ["2", "4"] {
        for _ in 0..8 {
            let shared = std::process::Command::new(env!("CARGO_BIN_EXE_prove-it"))
                .args(["-workers", "1", "-noTE", "Stop"])
                .current_dir(&directory)
                .env("PROVE_IT_SHARED_LEVEL", "1")
                .env("PROVE_IT_WORKERS", threads)
                .output()
                .expect("the binary runs");
            assert_eq!(
                shared.status.code(),
                Some(status),
                "{threads} threads: {}",
                stdout(&shared)
            );
            assert!(
                stdout(&shared).contains(expected),
                "{threads} threads: {}",
                stdout(&shared)
            );
        }
    }
    std::fs::remove_dir_all(directory).expect("removed");
}

// As TLC ran it at d8fb231 with `-workers 1`: the violation is the first state's step, with the
// counts of the states found before it.
#[test]
fn stops_at_the_first_state_that_steps_to_a_violation_another_thread_found() {
    let expected = "Error: Invariant Inv is violated.\nError: The behavior up to this point is:\nState 1: <Initial predicate>\n/\\ x = 0\n/\\ y = 0\n\nState 2: <Next line 5, col 12 to line 5, col 51 of module Stop>\n/\\ x = 1\n/\\ y = 0\n\nState 3: <Next line 7, col 12 to line 7, col 48 of module Stop>\n/\\ x = 100\n/\\ y = 0\n\n20066 states generated, 20066 distinct states found, 20063 states left on queue.\nThe depth of the complete state graph search is 3.\n";
    assert_on_threads("claims-violation", "Inv == x # 100", 12, expected);
}

// As TLC ran it at d8fb231 with `-workers 1`: the invariant's EXCEPT warns of the one state
// whose x is no key, which a thread that left the state to another's check would never print.
#[test]
fn prints_the_warning_of_a_check_another_thread_made() {
    let expected = "Warning: The EXCEPT was applied to non-existing fields of the value at\nline 8, col 9 to line 8, col 27 of module Stop\n(Use the -nowarning option to disable this warning.)\nModel checking completed. No error has been found.\n  Estimates of the probability that TLC did not check all reachable states\n  because two distinct states had the same fingerprint:\n  calculated (optimistic):  val = 7.0E-14\n20130 states generated, 20066 distinct states found, 0 states left on queue.\nThe depth of the complete state graph search is 3.\nThe average outdegree of the complete state graph is 0 (minimum is 0, the maximum 31 and the 95th percentile is 0).\n";
    assert_on_threads(
        "claims-warning",
        "Inv == [[i \\in 0..99 |-> 0] EXCEPT ![x] = 0][0] = 0",
        0,
        expected,
    );
}
