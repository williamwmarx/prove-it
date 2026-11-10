//! -continue and action properties, as TLC reports them: each violation with its trace under
//! -continue, and the first step that violates an action property otherwise.

mod common;

use common::{run, run_spec, run_spec_with, stderr, stdout};

// TLC's output without its startup lines, with the times and dates of the run as _, as
// `getSteadyLines` (normalize-output.ts) writes them.
fn steady_lines(output: &str) -> Vec<String> {
    const STARTUP: [&str; 5] = [
        "TLC2 Version ",
        "Running breadth-first search ",
        "Parsing file ",
        "Semantic processing of module ",
        "Linting of module ",
    ];
    const TIMED: [&str; 4] = ["Starting... ", "Finished ", "Progress(", "Checking "];
    let is_date = |text: &[u8]| {
        text.len() >= 19
            && text[..19]
                .iter()
                .enumerate()
                .all(|(index, &byte)| match index {
                    4 | 7 => byte == b'-',
                    10 => byte == b' ',
                    13 | 16 => byte == b':',
                    _ => byte.is_ascii_digit(),
                })
    };
    output
        .split('\n')
        .filter(|line| !STARTUP.iter().any(|prefix| line.starts_with(prefix)))
        .map(|line| {
            if !TIMED.iter().any(|prefix| line.starts_with(prefix)) {
                return line.to_string();
            }
            let bytes = line.as_bytes();
            let mut text = String::new();
            let mut index = 0;
            while index < bytes.len() {
                if is_date(&bytes[index..]) {
                    text.push('_');
                    index += 19;
                } else {
                    text.push(bytes[index] as char);
                    index += 1;
                }
            }
            match (text.strip_prefix("Finished in "), text.find(" at (")) {
                (Some(_), Some(at)) => format!("Finished in _{}", &text[at..]),
                _ => text,
            }
        })
        .collect()
}

// TLC's own -continue tests (ContinueTest, DoInitFunctorInvariantContinueTest) and
// ContinueSuccessors, as TLC printed them at d8fb231 with `-workers 1`.
#[test]
fn reports_each_violation_under_continue_as_tlc() {
    for (name, spec, config, expected) in [
        (
            "Continue",
            include_str!("../../../../tests/fixtures/tlc-continue/Continue.tla"),
            include_str!("../../../../tests/fixtures/tlc-continue/Continue.cfg"),
            include_str!("../../../../tests/fixtures/tlc-continue/Continue.out"),
        ),
        (
            "ContinueSuccessors",
            include_str!("../../../../tests/fixtures/tlc-continue/ContinueSuccessors.tla"),
            include_str!("../../../../tests/fixtures/tlc-continue/ContinueSuccessors.cfg"),
            include_str!("../../../../tests/fixtures/tlc-continue/ContinueSuccessors.out"),
        ),
        (
            "DoInitFunctorInvariantContinue",
            include_str!(
                "../../../../tests/fixtures/tlc-continue/DoInitFunctorInvariantContinue.tla"
            ),
            include_str!(
                "../../../../tests/fixtures/tlc-continue/DoInitFunctorInvariantContinue.cfg"
            ),
            include_str!(
                "../../../../tests/fixtures/tlc-continue/DoInitFunctorInvariantContinue.out"
            ),
        ),
    ] {
        let directory = std::env::temp_dir().join(format!(
            "prove-it-cli-continue-{name}-{}",
            std::process::id()
        ));
        std::fs::create_dir_all(&directory).expect("a directory");
        std::fs::write(directory.join(format!("{name}.tla")), spec).expect("a spec");
        std::fs::write(directory.join(format!("{name}.cfg")), config).expect("a configuration");
        let output = run(&directory, &["-continue", name]);
        let text = stdout(&output);
        assert_eq!(output.status.code(), Some(0), "{name}: {text}");
        assert_eq!(
            steady_lines(&text),
            expected.split('\n').collect::<Vec<_>>(),
            "{name}"
        );
        std::fs::remove_dir_all(directory).expect("removed");
    }
}

// Specs as TLC ran them at d8fb231 with `-workers 1`: TLC names an action property by the
// configuration's name where the property is the `[][A]_v` alone, and otherwise by where the
// conjunct is written, and stops at the first step that violates one, whether or not the step's
// state is new.
#[test]
fn reports_an_action_property_violated_as_tlc() {
    let steps = "---- MODULE Stop ----\nEXTENDS Naturals\nVARIABLES x, y\n\nInit == x = 0 /\\ y = 0\nNext == \\/ x < 2 /\\ x' = x + 1 /\\ UNCHANGED y\n        \\/ x = 2 /\\ y < 2 /\\ y' = y + 1 /\\ UNCHANGED x\nSpec == Init /\\ [][Next]_<<x, y>>\n\nSteps == [][x' >= x]_x /\\ [][y' # 1]_y\nNoY == [][y' # 1]_y\n====\n";
    let trace = "Error: The behavior up to this point is:\nState 1: <Initial predicate>\n/\\ x = 0\n/\\ y = 0\n\nState 2: <Next line 6, col 12 to line 6, col 45 of module Stop>\n/\\ x = 1\n/\\ y = 0\n\nState 3: <Next line 6, col 12 to line 6, col 45 of module Stop>\n/\\ x = 2\n/\\ y = 0\n\nState 4: <Next line 7, col 12 to line 7, col 54 of module Stop>\n/\\ x = 2\n/\\ y = 1\n\n4 states generated, 4 distinct states found, 0 states left on queue.\nThe depth of the complete state graph search is 4.\n";
    let cycle = "---- MODULE Stop ----\nEXTENDS Naturals\nVARIABLES x, y\nInit == x = 0 /\\ y \\in {0, 1}\nNext == x' = (x + 1) % 3 /\\ y' = 1 - y\nUp == [][x' > x]_x\n====\n";
    let cycle_trace = "Error: Action property Up is violated.\nError: The behavior up to this point is:\nState 1: <Initial predicate>\n/\\ x = 0\n/\\ y = 0\n\nState 2: <Next line 5, col 9 to line 5, col 38 of module Stop>\n/\\ x = 1\n/\\ y = 1\n\nState 3: <Next line 5, col 9 to line 5, col 38 of module Stop>\n/\\ x = 2\n/\\ y = 0\n\nState 4: <Next line 5, col 9 to line 5, col 38 of module Stop>\n/\\ x = 0\n/\\ y = 1\n\n7 states generated, 6 distinct states found, 1 states left on queue.\nThe depth of the complete state graph search is 3.\n";
    for (test, spec, config, expected) in [
        (
            "action-conjunct",
            steps,
            "SPECIFICATION Spec\nPROPERTY Steps\n",
            format!(
                "Error: Action property line 10, col 27 to line 10, col 38 of module Stop is violated.\n{trace}"
            ),
        ),
        (
            "action-alone",
            steps,
            "SPECIFICATION Spec\nPROPERTY NoY\n",
            format!("Error: Action property NoY is violated.\n{trace}"),
        ),
        (
            "action-seen",
            cycle,
            "INIT Init\nNEXT Next\nPROPERTY Up\n",
            cycle_trace.to_string(),
        ),
    ] {
        let (output, directory) = run_spec(test, spec, config);
        let text = stdout(&output);
        assert_eq!(output.status.code(), Some(13), "{test}: {text}");
        assert!(
            steady_lines(&text)
                .join("\n")
                .contains(&format!(" generated at _.\n{expected}Finished in _ at (_)")),
            "{test}: {text}"
        );
        std::fs::remove_dir_all(directory).expect("removed");
    }
}

#[test]
fn declines_continue_where_the_binary_doesnt_follow_tlc() {
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == x < 2 /\\ x' = x + 1\nSpec == Init /\\ [][Next]_x /\\ WF_x(Next)\nLive == <>(x = 2)\nPost == TLCGet(\"distinct\") > 0\nView == x\n====\n";
    for (test, config, reason) in [
        (
            "continue-temporal",
            "SPECIFICATION Spec\nPROPERTY Live\n",
            "-continue with temporal properties",
        ),
        (
            "continue-view",
            "INIT Init\nNEXT Next\nVIEW View\n",
            "-continue under SYMMETRY or a VIEW",
        ),
        (
            "continue-postcondition",
            "INIT Init\nNEXT Next\nPOSTCONDITION Post\n",
            "-continue with a POSTCONDITION",
        ),
        (
            "continue-deadlock",
            "INIT Init\nNEXT Next\n",
            "-continue to a search that stops",
        ),
    ] {
        let (output, directory) = run_spec_with(test, spec, config, &["-continue"]);
        assert_eq!(output.status.code(), Some(1), "{test}: {}", stdout(&output));
        assert_eq!(
            stderr(&output),
            format!("prove-it: not native yet: {reason}\n"),
            "{test}"
        );
        std::fs::remove_dir_all(directory).expect("removed");
    }
    // TLC fails to recover the traces of a spec that draws at random as it goes on.
    let random = "---- MODULE Stop ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == x < 2 /\\ x' = x + RandomElement({1})\n====\n";
    let (output, directory) = run_spec_with(
        "continue-random",
        random,
        "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n",
        &["-continue"],
    );
    assert_eq!(output.status.code(), Some(1), "{}", stdout(&output));
    assert_eq!(
        stderr(&output),
        "prove-it: not native yet: -continue with random draws\n"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

// As TLC ran it at d8fb231 with `-workers 1`: all three initial states step to the VIEW's one key,
// and only the step from x = 3 violates the action property. TLC checks the property on each
// step, whichever found the key first, so the binary stops there on any number of threads.
#[test]
fn reports_an_action_property_violated_under_a_view_as_tlc() {
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals\nVARIABLES x, y\nInit == x \\in 1..3 /\\ y = 0\nNext == x' = 0 /\\ y' = x\nView == x\nNotThree == [][y' # 3]_y\n====\n";
    let config = "INIT Init\nNEXT Next\nVIEW View\nPROPERTY NotThree\nCHECK_DEADLOCK FALSE\n";
    let expected = "Error: Action property NotThree is violated.\nError: The behavior up to this point is:\nState 1: <Initial predicate>\n/\\ x = 3\n/\\ y = 0\n\nState 2: <Next line 5, col 9 to line 5, col 24 of module Stop>\n/\\ x = 0\n/\\ y = 3\n\n6 states generated, 4 distinct states found, 1 states left on queue.\nThe depth of the complete state graph search is 2.\n";
    let (output, directory) = run_spec("action-view", spec, config);
    assert_eq!(output.status.code(), Some(13), "{}", stdout(&output));
    assert!(stdout(&output).contains(expected), "{}", stdout(&output));
    let shared = std::process::Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .args(["-workers", "4", "-noTE", "Stop"])
        .current_dir(&directory)
        .env("PROVE_IT_SHARED_LEVEL", "1")
        .output()
        .expect("the binary runs");
    assert_eq!(shared.status.code(), Some(13), "{}", stdout(&shared));
    assert!(stdout(&shared).contains(expected), "{}", stdout(&shared));
    std::fs::remove_dir_all(directory).expect("removed");
}

// TLC prints what the spec prints as it evaluates, before each violation it reports, and sets its
// registers again as it rebuilds each trace, which the binary doesn't follow.
#[test]
fn declines_continue_on_a_spec_that_prints_or_sets_registers() {
    for (test, next) in [
        ("continue-print", "x < 2 /\\ PrintT(x) /\\ x' = x + 1"),
        ("continue-register", "x < 2 /\\ TLCSet(1, x) /\\ x' = x + 1"),
    ] {
        let spec = format!(
            "---- MODULE Stop ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == {next}\nInv == x < 1\n====\n"
        );
        let (output, directory) = run_spec_with(
            test,
            &spec,
            "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n",
            &["-continue"],
        );
        assert_eq!(output.status.code(), Some(1), "{test}: {}", stdout(&output));
        assert_eq!(
            stderr(&output),
            "prove-it: not native yet: -continue with a spec that prints or sets TLC's registers\n",
            "{test}"
        );
        std::fs::remove_dir_all(directory).expect("removed");
    }
}

// As TLC ran it at d8fb231 with `-workers 1`: TLC reports an invariant an initial state violates
// once, however many of its conjuncts fail, and then goes on to the next invariant.
#[test]
fn reports_an_initial_invariant_once_under_continue_as_tlc() {
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x < 1 /\\ x' = x + 1\nInv == x > 0 /\\ x > 1\nSmall == x > 5\n====\n";
    let (output, directory) = run_spec_with(
        "continue-conjuncts",
        spec,
        "INIT Init\nNEXT Next\nINVARIANT Inv\nINVARIANT Small\nCHECK_DEADLOCK FALSE\n",
        &["-continue"],
    );
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(0), "{text}");
    assert!(
        text.contains("Computing initial states...\nError: Invariant Inv is violated by the initial state:\nx = 0\n\nError: Invariant Small is violated by the initial state:\nx = 0\n\nFinished computing initial states: 1 distinct state generated at "),
        "{text}"
    );
    assert!(
        text.contains("Error: Invariant Inv is violated.\nError: The behavior up to this point is:\nState 1: <Initial predicate>\nx = 0\n\nState 2: <Next line 5, col 9 to line 5, col 27 of module Stop>\nx = 1\n\nModel checking completed. No error has been found.\n"),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

// As TLC ran it at d8fb231 with `-workers 1`: TLC checks each invariant whole, so one that shares a
// conjunct with an invariant before it is violated with it, and its own conjuncts past the shared
// one go unevaluated.
#[test]
fn reports_invariants_sharing_a_conjunct_under_continue_as_tlc() {
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x' = x\nCommon == x # 0\nInv1 == Common\nInv2 == Common /\\ (1 \\div x > 0)\nInv3 == Common\n====\n";
    let (output, directory) = run_spec_with(
        "continue-shared",
        spec,
        "INIT Init\nNEXT Next\nINVARIANT Inv1 Inv2 Inv3\n",
        &["-continue"],
    );
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(0), "{text}");
    assert!(
        text.contains("Computing initial states...\nError: Invariant Inv1 is violated by the initial state:\nx = 0\n\nError: Invariant Inv2 is violated by the initial state:\nx = 0\n\nError: Invariant Inv3 is violated by the initial state:\nx = 0\n\nFinished computing initial states: 1 distinct state generated at "),
        "{text}"
    );
    assert!(
        text.contains("Model checking completed. No error has been found.\n"),
        "{text}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}
