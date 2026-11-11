//! The binary's reports of a failure of the next-state relation in a model with temporal
//! properties, against TLC built at d8fb231.

use std::process::{Command, Output};

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

#[test]
fn reports_a_failure_of_the_next_state_relation_in_a_model_with_temporal_properties() {
    // TLC's worker goes on after Next fails: it adds the state to the behavior graphs with the
    // successors Next gave before it failed, and prints the call stack of the first check there
    // that fails, in their fingerprints' order, in place of Next's, or Next's where none does.
    let cases = [
        (
            "Init == x = 0\nA == x' = 1 \\div x\nB == x' = x\nNext == A \\/ B\nFair == Next\nSpec == Init /\\ [][Next]_x /\\ WF_x(Fair)\nLive == []<>(x = 0)",
            "Error: The second argument of \\div is 0.\nError: The behavior up to this point is:\nState 1: <Initial predicate>\nx = 0\n\nError: The error occurred when TLC was evaluating the nested\nexpressions at the following positions:\n0. Line 9, column 36 to line 9, column 39 in M\n1. Line 8, column 9 to line 8, column 12 in M\n2. Line 7, column 9 to line 7, column 14 in M\n3. Line 7, column 9 to line 7, column 9 in M\n4. Line 5, column 6 to line 5, column 18 in M\n5. Line 5, column 11 to line 5, column 18 in M\n\n\n1 states generated, 1 distinct states found, 0 states left on queue.\nThe depth of the complete state graph search is 1.\n",
        ),
        (
            "Init == x = 0\nA == x' = IF x = 2 THEN 1 \\div 0 ELSE x + 1\nB == x' = x\nNext == A \\/ B\nSpec == Init /\\ [][Next]_x /\\ WF_x(B)\nLive == []<>(x = 0)",
            "Error: The second argument of \\div is 0.\nError: The behavior up to this point is:\nState 1: <Initial predicate>\nx = 0\n\nState 2: <A line 5, col 6 to line 5, col 43 of module M>\nx = 1\n\nState 3: <A line 5, col 6 to line 5, col 43 of module M>\nx = 2\n\nError: The error occurred when TLC was evaluating the nested\nexpressions at the following positions:\n0. Line 5, column 6 to line 5, column 43 in M\n1. Line 5, column 11 to line 5, column 43 in M\n2. Line 5, column 25 to line 5, column 32 in M\n\n\n5 states generated, 3 distinct states found, 0 states left on queue.\nThe depth of the complete state graph search is 3.\n",
        ),
        (
            "VARIABLE y\nInit == x = 0 /\\ y = 0\nNext == IF x = 0 THEN x' = 1 /\\ y' = 0 ELSE \\E i \\in 1..5 : y' = i /\\ x' = IF i = 4 THEN CHOOSE z \\in {} : TRUE ELSE 2\nSpec == Init /\\ [][Next]_<<x, y>>\nLive == []<><<IF y' = 2 THEN 1 \\div (y' - 2) = 0 ELSE IF y' = 3 THEN (CHOOSE z \\in {y} : z > 9) = 0 ELSE TRUE>>_<<x, y>>",
            "Error: TLC threw an unexpected exception.\nThis was probably caused by an error in the spec or model.\nSee the User Output or TLC Console for clues to what happened.\nThe exception was a java.lang.RuntimeException\n: Attempted to compute the value of an expression of form\nCHOOSE x \\in S: P, but no element of S satisfied P.\nline 6, col 90 to line 6, col 111 of module M\nError: The behavior up to this point is:\nState 1: <Initial predicate>\n/\\ x = 0\n/\\ y = 0\n\nState 2: <Next line 6, col 9 to line 6, col 118 of module M>\n/\\ x = 1\n/\\ y = 0\n\nError: The error occurred when TLC was evaluating the nested\nexpressions at the following positions:\n0. Line 8, column 15 to line 8, column 109 in M\n1. Line 8, column 55 to line 8, column 109 in M\n2. Line 8, column 70 to line 8, column 99 in M\n3. Line 8, column 71 to line 8, column 94 in M\n\n\n5 states generated, 5 distinct states found, 3 states left on queue.\nThe depth of the complete state graph search is 3.\n",
        ),
    ];
    for (index, (definitions, expected)) in cases.iter().enumerate() {
        let directory = std::env::temp_dir().join(format!(
            "prove-it-cli-next-failure-live-{index}-{}",
            std::process::id()
        ));
        std::fs::create_dir_all(&directory).expect("a directory");
        std::fs::write(
            directory.join("M.tla"),
            format!("---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLE x\n{definitions}\n====\n"),
        )
        .expect("a spec");
        std::fs::write(
            directory.join("M.cfg"),
            "SPECIFICATION Spec\nPROPERTY Live\n",
        )
        .expect("a configuration");
        for threads in ["1", "4"] {
            let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
                .args(["-noTE", "M"])
                .current_dir(&directory)
                .env("PROVE_IT_WORKERS", threads)
                .env("PROVE_IT_SHARED_LEVEL", "1")
                .output()
                .expect("the binary runs");
            let text = stdout(&output);
            assert_eq!(output.status.code(), Some(255), "{threads}: {text}");
            assert!(text.contains(expected), "{threads}: {text}");
        }
        std::fs::remove_dir_all(directory).expect("removed");
    }
}

#[test]
fn reports_an_incomplete_successor_in_a_model_without_temporal_properties() {
    // Without temporal properties, TLC reports a successor Next leaves a variable unassigned in
    // with its trace, as TLC built at d8fb231 prints it (TLC's IncompleteNext).
    let directory = std::env::temp_dir().join(format!(
        "prove-it-cli-next-failure-incomplete-{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&directory).expect("a directory");
    std::fs::write(
        directory.join("M.tla"),
        "---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLE x\nVARIABLE y\nInit == x = 0 /\\ y = 0\nNext == x' = x + 1\nSpec == Init /\\ [][Next]_<<x, y>>\n====\n",
    )
    .expect("a spec");
    std::fs::write(directory.join("M.cfg"), "SPECIFICATION Spec\n").expect("a configuration");
    let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .args(["-noTE", "M"])
        .current_dir(&directory)
        .output()
        .expect("the binary runs");
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(75), "{text}");
    assert!(
        text.contains("Error: Successor state is not completely specified by the next-state action. The following variable is not defined: y.\n\nError: The behavior up to this point is:\nState 1: <Initial predicate>\n/\\ x = 0\n/\\ y = 0\n\nState 2: <Next line 6, col 9 to line 6, col 18 of module M>\n/\\ x = 1\n/\\ y = null\n\n2 states generated, 1 distinct states found, 0 states left on queue.\nThe depth of the complete state graph search is 1.\n"),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}
