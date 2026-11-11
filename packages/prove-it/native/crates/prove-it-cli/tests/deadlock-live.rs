//! The binary's reports of a deadlock in a model with temporal properties where a check TLC runs
//! as it adds the deadlocked state to the behavior graphs fails, against TLC built at d8fb231.

use std::process::Command;

const STACK: &str = "Error: The error occurred when TLC was evaluating the nested\nexpressions at the following positions:\n";
const FAIR: &str = "Fair == x' = 1 \\div (x - 1)\n";
const NEXT: &str = "Next == x < 1 /\\ x' = x + 1\n";
const LIVE: &str = "SPECIFICATION Spec\nPROPERTY Live\n";

#[test]
fn reports_an_atom_that_fails_on_a_deadlocked_state() {
    // TLC reports the deadlock and its trace, then adds the state to the behavior graphs with the
    // stuttering step alone, and prints the call stack of the first check there that fails, or
    // nothing where none does or the rerun with its call stack throws a FingerprintException. It
    // exits as for the deadlock.
    let trace = "Error: Deadlock reached.\nError: The behavior up to this point is:\nState 1: <Initial predicate>\nx = 0\n\nState 2: <Next line 6, col 9 to line 6, col 27 of module M>\nx = 1\n\n";
    let statistics = "\n\n\n2 states generated, 2 distinct states found, 0 states left on queue.\nThe depth of the complete state graph search is 2.\n";
    let cases = [
        // ENABLED of the fairness fails.
        (
            format!(
                "Init == x = 0\n{FAIR}{NEXT}Spec == Init /\\ [][Next]_x /\\ WF_x(Fair)\nLive == []<>(x = 0)"
            ),
            LIVE.to_string(),
            format!(
                "{trace}{STACK}0. Line 7, column 36 to line 7, column 39 in M\n1. Line 5, column 9 to line 5, column 27 in M\n2. Line 5, column 14 to line 5, column 27 in M{statistics}"
            ),
        ),
        // The second of two fairness conditions, after an invariant that holds.
        (
            format!(
                "Init == x = 0\nA == x' = x + 1\n{FAIR}{NEXT}Inv == x < 2\nSpec == Init /\\ [][Next]_x /\\ WF_x(A) /\\ WF_x(Fair)\nLive == []<>(x = 0)"
            ),
            format!("{LIVE}INVARIANT Inv\n"),
            format!(
                "Error: Deadlock reached.\nError: The behavior up to this point is:\nState 1: <Initial predicate>\nx = 0\n\nState 2: <Next line 7, col 9 to line 7, col 27 of module M>\nx = 1\n\n{STACK}0. Line 9, column 47 to line 9, column 50 in M\n1. Line 6, column 9 to line 6, column 27 in M\n2. Line 6, column 14 to line 6, column 27 in M{statistics}"
            ),
        ),
        // A state predicate of the second property.
        (
            format!(
                "Init == x = 0\n{NEXT}Spec == Init /\\ [][Next]_x\nLive == []<>(x = 0)\nLive2 == []<>(1 \\div (1 - x) = 0)"
            ),
            format!("{LIVE}PROPERTY Live2\n"),
            format!(
                "Error: Deadlock reached.\nError: The behavior up to this point is:\nState 1: <Initial predicate>\nx = 0\n\nState 2: <Next line 5, col 9 to line 5, col 27 of module M>\nx = 1\n\n{STACK}0. Line 8, column 15 to line 8, column 32 in M\n1. Line 8, column 15 to line 8, column 28 in M{statistics}"
            ),
        ),
        // A postcondition that fails comes first.
        (
            format!(
                "Init == x = 0\n{FAIR}{NEXT}Post == TLCGet(\"distinct\") > 5\nSpec == Init /\\ [][Next]_x /\\ WF_x(Fair)\nLive == []<>(x = 0)"
            ),
            format!("{LIVE}POSTCONDITION Post\n"),
            format!(
                "{trace}Error: Postcondition Post at line 7, col 9 to line 7, col 30 of module M is false.\n{STACK}0. Line 8, column 36 to line 8, column 39 in M\n1. Line 5, column 9 to line 5, column 27 in M\n2. Line 5, column 14 to line 5, column 27 in M{statistics}"
            ),
        ),
        // The subscript of the stuttering step at a deadlocked initial state.
        (
            format!(
                "Init == x = 1\n{NEXT}Spec == Init /\\ [][Next]_x\nLive == []<><<x' = 0>>_(1 \\div (1 - x))"
            ),
            LIVE.to_string(),
            format!(
                "Error: Deadlock reached.\nError: The behavior up to this point is:\nState 1: <Initial predicate>\nx = 1\n\n{STACK}0. Line 7, column 25 to line 7, column 38 in M\n\n\n1 states generated, 1 distinct states found, 0 states left on queue.\nThe depth of the complete state graph search is 1.\n"
            ),
        ),
        // The rerun fails to fingerprint the tuple, which escapes: the plain deadlock.
        (
            format!(
                "Init == x = 0\nA == x' = <<1>>[x + 1]\n{NEXT}Spec == Init /\\ [][Next]_x /\\ WF_x(A)\nLive == []<>(x = 0)"
            ),
            LIVE.to_string(),
            format!("{trace}{}", &statistics[3..]),
        ),
        // Every check holds: the plain deadlock.
        (
            format!(
                "Init == x = 0\nFair == x' = x + 1\n{NEXT}Spec == Init /\\ [][Next]_x /\\ WF_x(Fair)\nLive == []<>(x = 0)"
            ),
            LIVE.to_string(),
            format!("{trace}{}", &statistics[3..]),
        ),
    ];
    for (index, (definitions, configuration, expected)) in cases.iter().enumerate() {
        let directory = std::env::temp_dir().join(format!(
            "prove-it-cli-deadlock-live-{index}-{}",
            std::process::id()
        ));
        std::fs::create_dir_all(&directory).expect("a directory");
        std::fs::write(
            directory.join("M.tla"),
            format!("---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLE x\n{definitions}\n====\n"),
        )
        .expect("a spec");
        std::fs::write(directory.join("M.cfg"), configuration).expect("a configuration");
        for arguments in [&["-noTE"][..], &["-noTE", "-lncheck", "final"]] {
            for threads in ["1", "4"] {
                let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
                    .args(arguments)
                    .arg("M")
                    .current_dir(&directory)
                    .env("PROVE_IT_WORKERS", threads)
                    .env("PROVE_IT_SHARED_LEVEL", "1")
                    .output()
                    .expect("the binary runs");
                let text = String::from_utf8_lossy(&output.stdout);
                assert_eq!(
                    output.status.code(),
                    Some(11),
                    "{index} {threads}: {text}{}",
                    String::from_utf8_lossy(&output.stderr)
                );
                assert!(
                    text.contains(expected.as_str()),
                    "{index} {threads}: {text}"
                );
            }
        }
        std::fs::remove_dir_all(directory).expect("removed");
    }
}

#[test]
fn reports_the_call_stack_with_tool() {
    let directory = std::env::temp_dir().join(format!(
        "prove-it-cli-deadlock-live-tool-{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&directory).expect("a directory");
    std::fs::write(
        directory.join("M.tla"),
        format!(
            "---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\n{FAIR}{NEXT}Spec == Init /\\ [][Next]_x /\\ WF_x(Fair)\nLive == []<>(x = 0)\n====\n"
        ),
    )
    .expect("a spec");
    std::fs::write(directory.join("M.cfg"), LIVE).expect("a configuration");
    for threads in ["1", "4"] {
        let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
            .args(["-noTE", "-tool", "M"])
            .current_dir(&directory)
            .env("PROVE_IT_WORKERS", threads)
            .env("PROVE_IT_SHARED_LEVEL", "1")
            .output()
            .expect("the binary runs");
        let text = String::from_utf8_lossy(&output.stdout);
        assert_eq!(output.status.code(), Some(11), "{threads}: {text}");
        assert!(
            text.contains("@!@!@STARTMSG 2114:1 @!@!@\nDeadlock reached.\n@!@!@ENDMSG 2114 @!@!@\n@!@!@STARTMSG 2121:1 @!@!@\nThe behavior up to this point is:\n@!@!@ENDMSG 2121 @!@!@\n@!@!@STARTMSG 2217:4 @!@!@\n1: <Initial predicate>\nx = 0\n\n@!@!@ENDMSG 2217 @!@!@\n@!@!@STARTMSG 2217:4 @!@!@\n2: <Next line 6, col 9 to line 6, col 27 of module M>\nx = 1\n\n@!@!@ENDMSG 2217 @!@!@\n@!@!@STARTMSG 2103:1 @!@!@\nThe error occurred when TLC was evaluating the nested\nexpressions at the following positions:\n0. Line 7, column 36 to line 7, column 39 in M\n1. Line 5, column 9 to line 5, column 27 in M\n2. Line 5, column 14 to line 5, column 27 in M\n\n\n@!@!@ENDMSG 2103 @!@!@\n"),
            "{threads}: {text}"
        );
    }
    std::fs::remove_dir_all(directory).expect("removed");
}
