//! A warning raised while threads share a level comes out where TLC prints it.

mod common;

use common::{run_spec, stdout};

// As TLC ran it at d8fb231 with `-workers 1`: the EXCEPT of g warns at the first initial state,
// with the hint to -nowarning, and that of f at the last state of the second level, where g's
// warns once more without the hint; the third and later ones print nothing. With every level
// shared, a thread that raises a warning TLC may print stops the level at that state, so the
// warning comes out in its place, and one TLC never prints again stops nothing.
#[test]
fn prints_warnings_raised_in_shared_levels_where_tlc_does() {
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals\nVARIABLES f, g, n\nInit == f = [i \\in 1..2 |-> 0] /\\ g = [i \\in 1..2 |-> 0] /\\ n \\in 1..4\nNext == /\\ n < 8\n        /\\ n' = n + 1\n        /\\ g' = [g EXCEPT ![n + 2] = 1]\n        /\\ f' = [f EXCEPT ![n - 2] = 1]\n====\n";
    let config = "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n";
    let expected = "Warning: The EXCEPT was applied to non-existing fields of the value at\nline 7, col 18 to line 7, col 18 of module Stop\n(Use the -nowarning option to disable this warning.)\nWarning: The EXCEPT was applied to non-existing fields of the value at\nline 8, col 18 to line 8, col 18 of module Stop\nWarning: The EXCEPT was applied to non-existing fields of the value at\nline 7, col 18 to line 7, col 18 of module Stop\nModel checking completed. No error has been found.\n  Estimates of the probability that TLC did not check all reachable states\n  because two distinct states had the same fingerprint:\n  calculated (optimistic):  val = 1.4E-18\n15 states generated, 13 distinct states found, 0 states left on queue.\nThe depth of the complete state graph search is 6.\nThe average outdegree of the complete state graph is 1 (minimum is 0, the maximum 1 and the 95th percentile is 1).\n";
    let (output, directory) = run_spec("warnings-shared", spec, config);
    assert_eq!(output.status.code(), Some(0), "{}", stdout(&output));
    assert!(stdout(&output).contains(expected), "{}", stdout(&output));
    for threads in ["2", "4"] {
        let shared = std::process::Command::new(env!("CARGO_BIN_EXE_prove-it"))
            .args(["-workers", "1", "-noTE", "Stop"])
            .current_dir(&directory)
            .env("PROVE_IT_SHARED_LEVEL", "1")
            .env("PROVE_IT_WORKERS", threads)
            .output()
            .expect("the binary runs");
        assert_eq!(
            shared.status.code(),
            Some(0),
            "{threads} threads: {}",
            stdout(&shared)
        );
        assert!(
            stdout(&shared).contains(expected),
            "{threads} threads: {}",
            stdout(&shared)
        );
    }
    std::fs::remove_dir_all(directory).expect("removed");
}
