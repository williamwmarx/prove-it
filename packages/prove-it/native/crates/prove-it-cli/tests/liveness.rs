//! The binary's liveness reports against TLC built at d8fb231: lassos, the postconditions of a
//! lasso, and failures adding the initial states to the behavior graphs.

use std::path::PathBuf;
use std::process::{Command, Output};

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

// Writes the spec and its configuration to a directory of their own and checks them with TLC's
// command line.
fn run_lowered(test: &str, spec: &str, config: &str) -> (Output, PathBuf) {
    let directory =
        std::env::temp_dir().join(format!("prove-it-liveness-{test}-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    let name = spec
        .split_whitespace()
        .nth(2)
        .expect("the module's name")
        .to_string();
    std::fs::write(directory.join(format!("{name}.tla")), spec).expect("the spec");
    std::fs::write(directory.join(format!("{name}.cfg")), config).expect("the configuration");
    let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .args(["-noTE", &name])
        .current_dir(&directory)
        .output()
        .expect("the binary runs");
    (output, directory)
}

// A lasso of a spec whose actions print: TLC runs the actions again to rebuild the trace, so what
// they print comes before the counterexample, as TLC built at d8fb231 prints it.
#[test]
fn prints_a_lasso_whose_actions_print_as_tlc_rebuilds_it() {
    let specs = [
        (
            "---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == x < 2 /\\ Print(x, TRUE) /\\ x' = x + 1\nLive == <>(x = 2)\n====\n",
            "INIT Init\nNEXT Next\nPROPERTY Live\nCHECK_DEADLOCK FALSE\n",
            concat!(
                ")\n0  TRUE\nError: Temporal property Live was violated.\n\n",
                "Error: The following behavior constitutes a counter-example:\n\n",
                "State 1: <Initial predicate>\nx = 0\n\n",
                "State 2: <Next line 5, col 9 to line 5, col 45 of module M>\nx = 1\n\n",
                "State 3: Stuttering\n",
            ),
        ),
        (
            "---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLE x\nNext == \\/ x < 3 /\\ PrintT(x) /\\ x' = x + 1\n        \\/ x = 3 /\\ UNCHANGED x\nSpec == x = 0 /\\ [][Next]_x /\\ WF_x(Next)\nStays == <>[](x = 0)\n====\n",
            "SPECIFICATION Spec\nPROPERTY Stays\n",
            concat!(
                "0\n1\n2\nError: Temporal property Stays was violated.\n\n",
                "Error: The following behavior constitutes a counter-example:\n\n",
                "State 1: <Initial predicate>\nx = 0\n\n",
                "State 2: <Next line 4, col 12 to line 4, col 43 of module M>\nx = 1\n\n",
                "State 3: <Next line 4, col 12 to line 4, col 43 of module M>\nx = 2\n\n",
                "State 4: <Next line 4, col 12 to line 4, col 43 of module M>\nx = 3\n\n",
                "State 5: Stuttering\n",
            ),
        ),
    ];
    for (position, (spec, config, printed)) in specs.into_iter().enumerate() {
        let directory = std::env::temp_dir().join(format!(
            "prove-it-cli-printing-lasso-{position}-{}",
            std::process::id()
        ));
        std::fs::create_dir_all(&directory).expect("a directory");
        std::fs::write(directory.join("M.tla"), spec).expect("a spec");
        std::fs::write(directory.join("M.cfg"), config).expect("a configuration");
        for threads in ["1", "4"] {
            let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
                .args(["-noTE", "M"])
                .current_dir(&directory)
                .env("PROVE_IT_WORKERS", threads)
                .env("PROVE_IT_SHARED_LEVEL", "1")
                .output()
                .expect("the binary runs");
            let text = stdout(&output);
            assert_eq!(output.status.code(), Some(13), "{threads}: {text}");
            assert!(text.contains(printed), "{threads}: {text}");
        }
        std::fs::remove_dir_all(directory).expect("removed");
    }
}

// Small specs of two to four actions over two variables, with fairness and one or two temporal
// properties, whose lassos take many shapes: the binary prints what TLC built at d8fb231 prints
// for each (`lasso-grid/*.out`, with -fp 0 -seed 0 -nowarning), on one thread and with every level
// shared between four, checking the properties periodically and at the end.
#[test]
fn prints_the_lassos_tlc_prints() {
    let grid = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/lasso-grid");
    let mut names: Vec<String> = std::fs::read_dir(&grid)
        .expect("the grid")
        .filter_map(|entry| {
            let path = entry.expect("an entry").path();
            (path.extension()? == "tla").then(|| path.file_stem()?.to_str().map(String::from))?
        })
        .collect();
    names.sort();
    assert!(!names.is_empty());
    let untimed_lines = |text: &str| {
        text.lines()
            .filter(|line| {
                ![
                    "Running breadth-first search",
                    "Starting...",
                    "Finished in",
                    "Progress(",
                    "TLC2 Version",
                    "Parsing file",
                    "Finished computing initial states",
                    "Checking ",
                    "Finished checking temporal properties",
                    "Estimates of the probability",
                    "because two distinct states had the same fingerprint",
                    "calculated (optimistic)",
                ]
                .iter()
                .any(|timed| line.contains(timed))
            })
            .collect::<Vec<_>>()
            .join("\n")
    };
    let directory =
        std::env::temp_dir().join(format!("prove-it-cli-lasso-grid-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    let mut differences = Vec::new();
    for name in &names {
        for extension in ["tla", "cfg"] {
            std::fs::copy(
                grid.join(format!("{name}.{extension}")),
                directory.join(format!("{name}.{extension}")),
            )
            .expect("a copy");
        }
        let expected =
            std::fs::read_to_string(grid.join(format!("{name}.out"))).expect("TLC's output");
        for check in [&[][..], &["-lncheck", "final"][..]] {
            for threads in ["1", "4"] {
                let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
                    .args([
                        "-workers",
                        "1",
                        "-fp",
                        "0",
                        "-seed",
                        "0",
                        "-nowarning",
                        "-noTE",
                    ])
                    .args(check)
                    .arg(name)
                    .current_dir(&directory)
                    .env("PROVE_IT_WORKERS", threads)
                    .env("PROVE_IT_SHARED_LEVEL", "1")
                    .output()
                    .expect("the binary runs");
                let actual = format!(
                    "exit {}\n{}\n",
                    output.status.code().unwrap_or(-1),
                    untimed_lines(&stdout(&output))
                );
                if actual != expected {
                    differences.push(format!(
                        "{name} {check:?} on {threads}: {}\n{actual}",
                        String::from_utf8_lossy(&output.stderr)
                    ));
                }
            }
        }
    }
    std::fs::remove_dir_all(directory).expect("removed");
    assert!(differences.is_empty(), "{}", differences.join("\n"));
}

// A lasso whose cycle ends in its first state: TLC prints every state of the path, the last
// included, then stutters at the cycle's first, as `LiveWorker.printTrace` finds the last state's
// fingerprint the cycle state's. TLC built at d8fb231, with -fp 0, prints this.
#[test]
fn prints_a_lasso_that_ends_in_the_first_state_of_its_cycle() {
    let spec = "---- MODULE Stop ----\nVARIABLES x, y\nvars == <<x, y>>\nInit == x \\in {0, 1} /\\ y = 0\nA0 == x = 1 /\\ y = 0 /\\ x' = 1 /\\ y' \\in {0, 1}\nA1 == x = 1 /\\ x' = 0 /\\ y' = 1\nA2 == x = 1 /\\ y = 0 /\\ x' = 0 /\\ y' = y\nA3 == x = 0 /\\ x' = 1 /\\ y' \\in {0, 0}\nNext == A0 \\/ A1 \\/ A2 \\/ A3\nSpec == Init /\\ [][Next]_vars /\\ WF_vars(Next)\nP0 == []<>(x # 0)\nP1 == []((x = 0) => <>[](y = 1))\n====\n";
    let directory =
        std::env::temp_dir().join(format!("prove-it-cli-lasso-end-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    std::fs::write(directory.join("Stop.tla"), spec).expect("a spec");
    std::fs::write(
        directory.join("Stop.cfg"),
        "SPECIFICATION Spec\nPROPERTY P0\nPROPERTY P1\n",
    )
    .expect("a configuration");
    let mut trace = String::from(
        "Error: Temporal property P1 was violated.\n\nError: The following behavior constitutes a counter-example:\n\nState 1: <Initial predicate>\n/\\ x = 0\n/\\ y = 0\n\n",
    );
    let steps = [
        ("A3 line 8, col 7 to line 8, col 38", 1, 0),
        ("A1 line 6, col 7 to line 6, col 31", 0, 1),
        ("A3 line 8, col 7 to line 8, col 38", 1, 0),
        ("A0 line 5, col 7 to line 5, col 47", 1, 1),
        ("A1 line 6, col 7 to line 6, col 31", 0, 1),
        ("A3 line 8, col 7 to line 8, col 38", 1, 0),
    ];
    for (position, (action, x, y)) in steps.iter().enumerate() {
        trace.push_str(&format!(
            "State {}: <{action} of module Stop>\n/\\ x = {x}\n/\\ y = {y}\n\n",
            position + 2
        ));
    }
    trace.push_str("State 3: Stuttering\n");
    for threads in ["1", "4"] {
        let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
            .args([
                "tlc2.TLC", "-noTE", "-workers", "1", "-lncheck", "final", "Stop",
            ])
            .current_dir(&directory)
            .env("PROVE_IT_WORKERS", threads)
            .env("PROVE_IT_SHARED_LEVEL", "1")
            .output()
            .expect("the binary runs");
        let text = stdout(&output);
        assert_eq!(output.status.code(), Some(13), "{threads}: {text}");
        assert!(text.contains(&trace), "{threads}: {text}");
    }
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn checks_the_postconditions_once_a_stuttering_lasso_is_printed() {
    // TLC checks the postconditions once it has printed where a lasso closes, with the action of
    // the last step closing a lasso that stutters at the first state of its cycle, here A3.
    let spec = "---- MODULE Stop ----\nEXTENDS TLC, TLCExt\nVARIABLES x, y\nvars == <<x, y>>\nInit == x \\in {0, 1} /\\ y = 0\nA0 == x = 1 /\\ y = 0 /\\ x' = 1 /\\ y' \\in {0, 1}\nA1 == x = 1 /\\ x' = 0 /\\ y' = 1\nA2 == x = 1 /\\ y = 0 /\\ x' = 0 /\\ y' = y\nA3 == x = 0 /\\ x' = 1 /\\ y' \\in {0, 0}\nNext == A0 \\/ A1 \\/ A2 \\/ A3\nSpec == Init /\\ [][Next]_vars /\\ WF_vars(Next)\nP0 == []<>(x # 0)\nP1 == []((x = 0) => <>[](y = 1))\nPost == PrintT(<<\"closing\", {e[2].name : e \\in {f \\in CounterExample.action : f[1][1] = 7}}>>)\n====\n";
    let directory =
        std::env::temp_dir().join(format!("prove-it-cli-lasso-post-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    std::fs::write(directory.join("Stop.tla"), spec).expect("a spec");
    std::fs::write(
        directory.join("Stop.cfg"),
        "SPECIFICATION Spec\nPROPERTY P0\nPROPERTY P1\nPOSTCONDITION Post\n",
    )
    .expect("a configuration");
    for check in [&[][..], &["-lncheck", "final"][..]] {
        for threads in ["1", "4"] {
            let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
                .args([
                    "tlc2.TLC", "-noTE", "-workers", "1", "-fp", "0", "-seed", "0",
                ])
                .args(check)
                .arg("Stop")
                .current_dir(&directory)
                .env("PROVE_IT_WORKERS", threads)
                .env("PROVE_IT_SHARED_LEVEL", "1")
                .output()
                .expect("the binary runs");
            let text = stdout(&output);
            assert_eq!(output.status.code(), Some(13), "{threads}: {text}");
            assert!(
                text.contains(
                    "/\\ x = 1\n/\\ y = 0\n\nState 3: Stuttering\n<<\"closing\", {\"A3\"}>>\n"
                ),
                "{check:?} {threads}: {text}"
            );
        }
    }
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn reports_a_property_checked_as_an_invariant_that_fails_on_an_initial_state() {
    // TLC checks []P of a state predicate P as an invariant, after the model's own, and reports
    // one that fails to evaluate on an initial state with the state, then its replay's call stack.
    let spec = "---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nInit == x \\in {0, 1, 2}\nA == x' = x\nSpec == Init /\\ [][A]_x\nInv == x \\in 0..9\nP == [](IF x # 1 THEN x[1] = 0 ELSE TRUE)\n====\n";
    let (output, directory) = run_lowered(
        "property-invariant-initial",
        spec,
        "SPECIFICATION Spec\nINVARIANT Inv\nPROPERTY P\n",
    );
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(75), "{text}");
    assert!(
        text.contains("Computing initial states...\nError: A non-function (an integer) was applied as a function.\nline 8, col 23 to line 8, col 26 of module M\nWhile working on the initial state:\nx = 0\n\nError: The error occurred when TLC was evaluating the nested\nexpressions at the following positions:\n0. Line 4, column 9 to line 4, column 23 in M\n1. Line 8, column 9 to line 8, column 40 in M\n2. Line 8, column 23 to line 8, column 30 in M\n3. Line 8, column 23 to line 8, column 26 in M\n\n\n1 states generated, 1 distinct states found, 1 states left on queue.\nThe depth of the complete state graph search is 1.\n"),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn reports_an_atom_that_fails_on_one_of_the_initial_states() {
    // TLC adds each initial state to the behavior graphs as it finds it and stops where an atom
    // fails, then replays the initial states with its call stack, adding those it hadn't found:
    // where an atom fails again there, it prints that call stack and the counts of the replay.
    let cases = [
        (
            "TRUE",
            75,
            "Computing initial states...\nError: A non-function (an integer) was applied as a function.\nline 7, col 23 to line 7, col 26 of module M\nWhile working on the initial state:\nx = 0\n\nError: The error occurred when TLC was evaluating the nested\nexpressions at the following positions:\n0. Line 4, column 9 to line 4, column 20 in M\n1. Line 7, column 23 to line 7, column 30 in M\n2. Line 7, column 23 to line 7, column 26 in M\n\n\n2 states generated, 2 distinct states found, 2 states left on queue.\nThe depth of the complete state graph search is 1.\n",
        ),
        (
            "x = 1",
            255,
            "Computing initial states...\nError: A non-function (an integer) was applied as a function.\nline 7, col 24 to line 7, col 27 of module M\nWhile working on the initial state:\nx = 1\n\n2 states generated, 2 distinct states found, 2 states left on queue.\nThe depth of the complete state graph search is 1.\n",
        ),
    ];
    for (index, (condition, status, expected)) in cases.iter().enumerate() {
        let spec = format!(
            "---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nInit == x \\in {{0, 1}}\nA == x' = x\nSpec == Init /\\ [][A]_x\nP == []((IF {condition} THEN x[1] = 0 ELSE TRUE) => <>(x = 0))\n====\n"
        );
        let directory = std::env::temp_dir().join(format!(
            "prove-it-cli-initial-atoms-{index}-{}",
            std::process::id()
        ));
        std::fs::create_dir_all(&directory).expect("a directory");
        std::fs::write(directory.join("M.tla"), spec).expect("a spec");
        std::fs::write(directory.join("M.cfg"), "SPECIFICATION Spec\nPROPERTY P\n")
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
            assert_eq!(output.status.code(), Some(*status), "{threads}: {text}");
            assert!(text.contains(expected), "{threads}: {text}");
        }
        std::fs::remove_dir_all(directory).expect("removed");
    }
}
