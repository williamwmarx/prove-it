//! The binary's reports of a stop, a deadlock, a violated invariant or a failure of Next or of an
//! invariant, in a model with temporal properties whose spec prints, against TLC built at
//! d8fb231: TLC prints as it searches, between the states it adds to the behavior graphs, then
//! adds the state it stopped at once it has printed the trace (`Worker.run`).

use std::process::Command;

fn run(
    name: &str,
    definitions: &str,
    config: &str,
    threads: &str,
) -> (Option<i32>, String, String) {
    let directory = std::env::temp_dir().join(format!(
        "prove-it-cli-printing-stop-{name}-{threads}-{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&directory).expect("a directory");
    std::fs::write(
        directory.join("M.tla"),
        format!("---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLE x\n{definitions}\n====\n"),
    )
    .expect("a spec");
    std::fs::write(directory.join("M.cfg"), config).expect("a configuration");
    let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .args(["-noTE", "M"])
        .current_dir(&directory)
        .env("PROVE_IT_WORKERS", threads)
        .env("PROVE_IT_SHARED_LEVEL", "1")
        .output()
        .expect("the binary runs");
    std::fs::remove_dir_all(directory).expect("removed");
    (
        output.status.code(),
        String::from_utf8_lossy(&output.stdout).into_owned(),
        String::from_utf8_lossy(&output.stderr).into_owned(),
    )
}

#[test]
fn prints_as_tlc_does_at_a_stop_in_a_model_with_temporal_properties() {
    // Each spec, its configuration, TLC's exit status, and what TLC prints after it has computed
    // the initial states, up to the time it took.
    let cases = [
        // TLC adds the deadlocked state after the trace: ENABLED A prints 2; before it, the rebuild for the postconditions prints 0 and 1
        (
            "Init == x = 0\nA == PrintT(x) /\\ x < 2 /\\ x' = x + 1\nSpec == Init /\\ [][A]_x /\\ WF_x(A)\nP == [](x = 0 => <>(x = 1))\nInv == x < 1",
            "SPECIFICATION Spec\nPROPERTY P\n",
            11,
            "0\n0\n0\n0\n0\n0\n0\n0\n1\n1\n1\n1\n2\nError: Deadlock reached.\n0\nError: The behavior up to this point is:\nState 1: <Initial predicate>\nx = 0\n\nState 2: <A line 5, col 6 to line 5, col 37 of module M>\nx = 1\n\n1\nState 3: <A line 5, col 6 to line 5, col 37 of module M>\nx = 2\n\n0\n1\n2\n3 states generated, 3 distinct states found, 0 states left on queue.\nThe depth of the complete state graph search is 3.\n",
        ),
        // an invariant violated: TLC adds the state it expanded with the violating successor after the trace, its late node running Next in full
        (
            "Init == x = 0\nA == PrintT(x) /\\ x < 2 /\\ x' = x + 1\nSpec == Init /\\ [][A]_x /\\ WF_x(A)\nP == [](x = 0 => <>(x = 1))\nInv == x < 1",
            "SPECIFICATION Spec\nPROPERTY P\nINVARIANT Inv",
            12,
            "0\nError: Invariant Inv is violated.\nError: The behavior up to this point is:\nState 1: <Initial predicate>\nx = 0\n\n0\nState 2: <A line 5, col 6 to line 5, col 37 of module M>\nx = 1\n\n0\n0\n0\n0\n0\n0\n0\n0\n2 states generated, 2 distinct states found, 0 states left on queue.\nThe depth of the complete state graph search is 2.\n",
        ),
        // an invariant that fails: the state is added before TLC replays the expansion
        (
            "Init == x = 0\nA == PrintT(<<\"A\", x>>) /\\ x < 3 /\\ x' = x + 1\nSpec == Init /\\ [][A]_x /\\ WF_x(A)\nP == [](x = 0 => <>(x = 1))\nInv == 1 \\div (1 - x) < 5",
            "SPECIFICATION Spec\nPROPERTY P\nINVARIANT Inv\n",
            76,
            "<<\"A\", 0>>\nError: Evaluating invariant Inv failed.\nThe second argument of \\div is 0.\nError: The behavior up to this point is:\nState 1: <Initial predicate>\nx = 0\n\n<<\"A\", 0>>\nState 2: <A line 5, col 6 to line 5, col 46 of module M>\nx = 1\n\n<<\"A\", 0>>\n<<\"A\", 0>>\n<<\"A\", 0>>\n<<\"A\", 0>>\n<<\"A\", 0>>\n<<\"A\", 0>>\n<<\"A\", 0>>\n<<\"A\", 0>>\n2 states generated, 2 distinct states found, 0 states left on queue.\nThe depth of the complete state graph search is 2.\nThe average outdegree of the complete state graph is 1 (minimum is 1, the maximum 1 and the 95th percentile is 1).\n",
        ),
        // a failure of Next whose fairness holds: the state is added before the replay of Next
        (
            "Init == x = 0\nAct == PrintT(<<\"A\", x>>) /\\ x < 7 /\\ x' = (IF x = 3 THEN 1 \\div 0 ELSE x + 1)\nNext == Act\nFair == x < 3 /\\ x' = x + 1\nSpec == Init /\\ [][Next]_x /\\ WF_x(Fair)\nP == [](x = 0 => <>(x = 1))\nInv == TRUE",
            "SPECIFICATION Spec\nPROPERTY P\n",
            255,
            "<<\"A\", 0>>\n<<\"A\", 0>>\n<<\"A\", 1>>\n<<\"A\", 2>>\n<<\"A\", 3>>\nError: The second argument of \\div is 0.\n<<\"A\", 0>>\n<<\"A\", 1>>\nError: The behavior up to this point is:\nState 1: <Initial predicate>\nx = 0\n\nState 2: <Act line 5, col 8 to line 5, col 78 of module M>\nx = 1\n\nState 3: <Act line 5, col 8 to line 5, col 78 of module M>\nx = 2\n\n<<\"A\", 2>>\nState 4: <Act line 5, col 8 to line 5, col 78 of module M>\nx = 3\n\n<<\"A\", 0>>\n<<\"A\", 1>>\n<<\"A\", 2>>\n<<\"A\", 3>>\nError: The error occurred when TLC was evaluating the nested\nexpressions at the following positions:\n0. Line 5, column 8 to line 5, column 78 in M\n1. Line 5, column 8 to line 5, column 34 in M\n2. Line 5, column 8 to line 5, column 25 in M\n3. Line 5, column 30 to line 5, column 34 in M\n4. Line 5, column 39 to line 5, column 78 in M\n5. Line 5, column 45 to line 5, column 77 in M\n6. Line 5, column 59 to line 5, column 66 in M\n\n\n4 states generated, 4 distinct states found, 0 states left on queue.\nThe depth of the complete state graph search is 4.\n",
        ),
        // only the fairness action prints
        (
            "Init == x = 0\nAct == x < 3 /\\ x' = x + 1\nNext == Act\nFair == PrintT(<<\"F\", x>>) /\\ Act\nSpec == Init /\\ [][Next]_x /\\ WF_x(Fair)\nP == [](x = 0 => <>(x = 1))\nInv == TRUE",
            "SPECIFICATION Spec\nPROPERTY P\n",
            11,
            "<<\"F\", 0>>\n<<\"F\", 0>>\n<<\"F\", 0>>\n<<\"F\", 0>>\n<<\"F\", 0>>\n<<\"F\", 0>>\n<<\"F\", 1>>\n<<\"F\", 1>>\n<<\"F\", 1>>\n<<\"F\", 2>>\n<<\"F\", 2>>\n<<\"F\", 2>>\nError: Deadlock reached.\nError: The behavior up to this point is:\nState 1: <Initial predicate>\nx = 0\n\nState 2: <Act line 5, col 8 to line 5, col 26 of module M>\nx = 1\n\nState 3: <Act line 5, col 8 to line 5, col 26 of module M>\nx = 2\n\nState 4: <Act line 5, col 8 to line 5, col 26 of module M>\nx = 3\n\n<<\"F\", 3>>\n4 states generated, 4 distinct states found, 0 states left on queue.\nThe depth of the complete state graph search is 4.\n",
        ),
        // strong fairness, a stop past the first level
        (
            "Init == x = 0\nAct == PrintT(<<\"A\", x>>) /\\ x < 7 /\\ x' = x + 1\nNext == Act\nFair == Act\nSpec == Init /\\ [][Next]_x /\\ SF_x(Fair)\nP == <>(x = 1)\nInv == 1 \\div (3 - x) # 7",
            "SPECIFICATION Spec\nPROPERTY P\nINVARIANT Inv\n",
            76,
            "<<\"A\", 0>>\n<<\"A\", 0>>\n<<\"A\", 0>>\n<<\"A\", 0>>\n<<\"A\", 1>>\n<<\"A\", 1>>\n<<\"A\", 1>>\n<<\"A\", 1>>\n<<\"A\", 2>>\nError: Evaluating invariant Inv failed.\nThe second argument of \\div is 0.\n<<\"A\", 0>>\nError: The behavior up to this point is:\nState 1: <Initial predicate>\nx = 0\n\nState 2: <Act line 5, col 8 to line 5, col 48 of module M>\nx = 1\n\n<<\"A\", 1>>\nState 3: <Act line 5, col 8 to line 5, col 48 of module M>\nx = 2\n\n<<\"A\", 2>>\nState 4: <Act line 5, col 8 to line 5, col 48 of module M>\nx = 3\n\n<<\"A\", 2>>\n<<\"A\", 2>>\n<<\"A\", 2>>\n<<\"A\", 2>>\n4 states generated, 4 distinct states found, 0 states left on queue.\nThe depth of the complete state graph search is 4.\nThe average outdegree of the complete state graph is 1 (minimum is 1, the maximum 1 and the 95th percentile is 1).\n",
        ),
        // a disjunct prints
        (
            "Init == x = 0\nAct == x < 1 /\\ (x' = x + 1 \\/ (PrintT(<<\"D\", x>>) /\\ x' = x + 1))\nNext == Act\nFair == Act\nSpec == Init /\\ [][Next]_x /\\ SF_x(Fair)\nP == []<>(x >= 0)\nInv == TRUE",
            "SPECIFICATION Spec\nPROPERTY P\n",
            11,
            "<<\"D\", 0>>\nError: Deadlock reached.\nError: The behavior up to this point is:\nState 1: <Initial predicate>\nx = 0\n\n<<\"D\", 0>>\nState 2: <Act line 5, col 8 to line 5, col 66 of module M>\nx = 1\n\n<<\"D\", 0>>\n3 states generated, 2 distinct states found, 0 states left on queue.\nThe depth of the complete state graph search is 2.\n",
        ),
        // a late node of a state before the deadlock prints its expansion again
        (
            "Init == x = 0\nNext == x < 2 /\\ x' = x + 1 /\\ PrintT(<<\"n\", x>>)\nSpec == Init /\\ [][Next]_x\nProp == [](x # 1 => [](x # 7))",
            "SPECIFICATION Spec\nPROPERTY Prop\n",
            11,
            "<<\"n\", 0>>\n<<\"n\", 0>>\n<<\"n\", 1>>\nError: Deadlock reached.\n<<\"n\", 0>>\nError: The behavior up to this point is:\nState 1: <Initial predicate>\nx = 0\n\nState 2: <Next line 5, col 9 to line 5, col 49 of module M>\nx = 1\n\n<<\"n\", 1>>\nState 3: <Next line 5, col 9 to line 5, col 49 of module M>\nx = 2\n\n<<\"n\", 0>>\n<<\"n\", 1>>\n3 states generated, 3 distinct states found, 0 states left on queue.\nThe depth of the complete state graph search is 3.\n",
        ),
    ];
    for (index, (definitions, config, code, expected)) in cases.iter().enumerate() {
        for threads in ["1", "4"] {
            let (status, text, errors) = run(&index.to_string(), definitions, config, threads);
            assert_eq!(status, Some(*code), "{index} on {threads}: {text}{errors}");
            let start = text
                .find("Finished computing initial states")
                .and_then(|start| text[start..].find('\n').map(|end| start + end + 1))
                .expect("the initial states");
            let end = text.find("Finished in").expect("the end");
            assert_eq!(&text[start..end], *expected, "{index} on {threads}");
        }
    }
}

#[test]
fn declines_a_late_node_of_a_state_whose_next_states_fail() {
    // TLC's late node of the state whose next states failed runs Next from it again, which fails
    // as TLC adds the state to the behavior graphs: TLC prints that failure's call stack after
    // evaluating the checks a second time, on a graph the first attempt changed.
    let (status, _, errors) = run(
        "late",
        "Init == x = 0\nA == PrintT(x) /\\ (x' = 1 \\/ x' = 1 \\div 0)\nSpec == Init /\\ [][A]_x /\\ WF_x(A)\nP == [](x = 0 => <>(x = 1))",
        "SPECIFICATION Spec\nPROPERTY P\n",
        "1",
    );
    assert_eq!(status, Some(1), "{errors}");
    assert!(
        errors.contains(
            "not native yet: the engine stopped: division by zero: a late node of a state whose next states fail, which TLC fails on again"
        ),
        "{errors}"
    );
}
