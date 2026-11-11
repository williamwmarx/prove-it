//! Runs the binary on specs with a `_PERIODIC` expression, which TLC evaluates 3 s after its
//! workers start and as it prints its progress after: the binary follows only an expression that
//! can't change what TLC prints whenever it evaluates it, and declines any other.

mod common;

use common::{run_spec, run_spec_with, stdout};

// A counter with a `_PERIODIC` expression, as TLC's ran at d8fb231 with `-workers 1`.
fn periodic_spec(next: &str, periodic: &str) -> String {
    format!(
        "---- MODULE Stop ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == {next}\nPeriodic == {periodic}\n====\n"
    )
}

const PERIODIC_CONFIG: &str = "INIT Init\nNEXT Next\n_PERIODIC Periodic\nCHECK_DEADLOCK FALSE\n";

const PERIODIC_COUNTER: &str = "x < 3 /\\ x' = x + 1";

// Declines the spec with this reason.
fn assert_declines(test: &str, spec: &str, config: &str, reason: &str) {
    let (output, directory) = run_spec_with(test, spec, config, &[]);
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(1), "{test}: {text}");
    assert_eq!(
        String::from_utf8_lossy(&output.stderr),
        format!("prove-it: not native yet: {reason}\n"),
        "{test}"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

// An expression TRUE whatever the counts, that prints nothing, changes nothing TLC prints, as TLC
// printed with and without it.
#[test]
fn checks_a_spec_with_an_inert_periodic_expression_as_tlc() {
    for periodic in ["TRUE", "TLCGet(\"level\") = 1"] {
        let spec = periodic_spec(PERIODIC_COUNTER, periodic);
        let (output, directory) = run_spec("periodic-inert", &spec, PERIODIC_CONFIG);
        let text = stdout(&output);
        assert_eq!(output.status.code(), Some(0), "{periodic}: {text}");
        assert!(
            text.contains("Model checking completed. No error has been found."),
            "{periodic}: {text}"
        );
        assert!(
            text.contains("4 states generated, 4 distinct states found, 0 states left on queue.\n"),
            "{periodic}: {text}"
        );
        std::fs::remove_dir_all(directory).expect("removed");
    }
}

// An expression that prints, or that is FALSE with some counts, changes what TLC prints where
// TLC's run lasts past 3 s, which no time of the binary's bounds: TLC printed `"p"` after its
// startup and nothing more for this 4-state counter, and stops at 3 s on a longer one.
#[test]
fn declines_a_periodic_expression_whose_evaluation_shows() {
    for periodic in ["PrintT(\"p\")", "FALSE"] {
        assert_declines(
            "periodic-shown",
            &periodic_spec(PERIODIC_COUNTER, periodic),
            PERIODIC_CONFIG,
            "a _PERIODIC that prints or is FALSE, which TLC evaluates at a time of its own",
        );
    }
    // An expression that reads the run's counts or the state may be TRUE at the start and far
    // along and FALSE between, as `TLCGet("distinct") # 2` is for this counter: whatever it is,
    // it declines.
    for periodic in [
        "PrintT(TLCGet(\"distinct\"))",
        "TLCGet(\"distinct\") < 10",
        "TLCGet(\"distinct\") # 2",
        "TLCGet(\"stats\").queue >= 0",
        "x = 0 => FALSE",
    ] {
        let (output, directory) = run_spec_with(
            "periodic-counts",
            &periodic_spec(PERIODIC_COUNTER, periodic),
            PERIODIC_CONFIG,
            &[],
        );
        assert_eq!(output.status.code(), Some(1), "{periodic}");
        assert!(
            String::from_utf8_lossy(&output.stderr)
                .starts_with("prove-it: not native yet: a _PERIODIC that reads the run"),
            "{periodic}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        std::fs::remove_dir_all(directory).expect("removed");
    }
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == x < 3 /\\ x' = x + 1\nPeriodic == TRUE\nT == JavaTime\n====\n";
    assert_declines(
        "periodic-time",
        spec,
        PERIODIC_CONFIG,
        "a _PERIODIC in a spec that reads the time or draws at random",
    );
}

// TLC fails where the expression reads TLCGet("duration") and prints its progress, which the
// trace evaluator doesn't follow, and fails comparing a value that is no boolean with FALSE.
#[test]
fn declines_a_periodic_expression_it_doesnt_follow() {
    for (periodic, reason) in [
        (
            "TLCGet(\"duration\") >= 0",
            "a _PERIODIC that reads the run or fails to evaluate: TLCGet",
        ),
        ("3", "a _PERIODIC that isn't a boolean"),
    ] {
        let (output, directory) = run_spec_with(
            "periodic-declined",
            &periodic_spec(PERIODIC_COUNTER, periodic),
            PERIODIC_CONFIG,
            &[],
        );
        assert_eq!(output.status.code(), Some(1), "{}", stdout(&output));
        assert!(
            String::from_utf8_lossy(&output.stderr)
                .starts_with(&format!("prove-it: not native yet: {reason}")),
            "{periodic}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        std::fs::remove_dir_all(directory).expect("removed");
    }
}

// TLC compares the function a function definition is with FALSE at its first progress, and fails
// (exit 255, "Attempted to compare equality of boolean FALSE with non-boolean").
#[test]
fn declines_a_periodic_function_definition() {
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x' = x + 1\nPeriodic[n \\in {1}] == FALSE\n====\n";
    let (output, directory) = run_spec("periodic-function", spec, PERIODIC_CONFIG);
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(1), "{text}");
    assert_eq!(
        String::from_utf8_lossy(&output.stderr),
        "prove-it: not native yet: a _PERIODIC naming a function definition\n"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

// TLC fails as it starts where the configuration assigns a value to the _PERIODIC name: it finds
// the value among its definitions and casts it to one (a ClassCastException, exit 255).
#[test]
fn declines_a_periodic_the_configuration_assigns_a_value_to() {
    let (output, directory) = run_spec_with(
        "periodic-assigned",
        &periodic_spec(PERIODIC_COUNTER, "TRUE"),
        &format!("{PERIODIC_CONFIG}CONSTANT Periodic = FALSE\n"),
        &[],
    );
    let text = stdout(&output);
    assert_eq!(output.status.code(), Some(1), "{text}");
    assert_eq!(
        String::from_utf8_lossy(&output.stderr),
        "prove-it: not native yet: a _PERIODIC the configuration assigns a value to\n"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

// TLC finds a builtin among its definitions as the value of its Java method, which it fails casting
// to a definition as it starts (a ClassCastException, exit 255).
#[test]
fn declines_a_periodic_naming_a_builtin() {
    for name in ["Nat", "TRUE"] {
        let (output, directory) = run_spec_with(
            "periodic-builtin",
            &periodic_spec(PERIODIC_COUNTER, "TRUE"),
            &PERIODIC_CONFIG.replace("_PERIODIC Periodic", &format!("_PERIODIC {name}")),
            &[],
        );
        let text = stdout(&output);
        assert_eq!(output.status.code(), Some(1), "{name}: {text}");
        assert_eq!(
            String::from_utf8_lossy(&output.stderr),
            "prove-it: not native yet: a _PERIODIC that names a builtin operator\n"
        );
        std::fs::remove_dir_all(directory).expect("removed");
    }
}

// TLC holds no operator of the core language among its definitions, so a _PERIODIC naming one
// isn't defined, as the binary reports.
#[test]
fn reports_a_periodic_naming_a_core_operator_as_undefined() {
    // TLC holds an operator by its first name only, so `<=`, `\\leq`'s synonym, isn't defined.
    for name in ["SUBSET", "<="] {
        let (output, directory) = run_spec_with(
            "periodic-core",
            &periodic_spec(PERIODIC_COUNTER, "TRUE"),
            &PERIODIC_CONFIG.replace("_PERIODIC Periodic", &format!("_PERIODIC {name}")),
            &[],
        );
        let text = stdout(&output);
        assert_eq!(output.status.code(), Some(151), "{name}: {text}");
        assert!(
            text.contains(&format!("Error: The periodic {name} specified in the configuration file\nis not defined in the specification.\n")),
            "{name}: {text}"
        );
        std::fs::remove_dir_all(directory).expect("removed");
    }
}

// TLC reads a definition through an assignment qualified by a module, `Q = [Stop] FALSE`, which
// the engine and the trace evaluator don't follow, and checks the temporal properties of the
// current state space as it evaluates the expression: both decline.
#[test]
fn declines_a_periodic_it_doesnt_follow() {
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x < 3 /\\ x' = x + 1\nQ == TRUE\nPeriodic == Q\nSpec == Init /\\ [][Next]_x\nLive == <>(x >= 0)\n====\n";
    assert_declines(
        "periodic-module-assignment",
        spec,
        &format!("{PERIODIC_CONFIG}CONSTANT Q = [Stop] FALSE\n"),
        "a _PERIODIC with a module's assignment in the configuration",
    );
    assert_declines(
        "periodic-temporal",
        spec,
        "SPECIFICATION Spec\nPROPERTY Live\n_PERIODIC Periodic\nCHECK_DEADLOCK FALSE\n",
        "a _PERIODIC with temporal properties",
    );
}

// TLC finds the value the configuration assigns a declared constant among its definitions too,
// and fails casting it to one as it starts (exit 255).
#[test]
fn declines_a_periodic_constant_the_configuration_assigns_a_value_to() {
    let spec = "---- MODULE Stop ----\nEXTENDS Naturals\nCONSTANT Periodic\nVARIABLE x\nInit == x = 0\nNext == x < 3 /\\ x' = x + 1\n====\n";
    let (output, directory) = run_spec_with(
        "periodic-constant-assigned",
        spec,
        &format!("{PERIODIC_CONFIG}CONSTANT Periodic = TRUE\n"),
        &[],
    );
    assert_eq!(output.status.code(), Some(1), "{}", stdout(&output));
    assert_eq!(
        String::from_utf8_lossy(&output.stderr),
        "prove-it: not native yet: a _PERIODIC the configuration assigns a value to\n"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}
