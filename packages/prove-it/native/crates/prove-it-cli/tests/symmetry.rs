//! TLC's warnings before a temporal property it rejects as it starts the liveness checker, against
//! TLC built at d8fb231.

use std::path::PathBuf;
use std::process::{Command, Output};

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn run(directory: &PathBuf, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .args(args)
        .current_dir(directory)
        .output()
        .expect("the binary runs")
}

// What the binary prints from `Starting...` to `Finished in`, both left out, and its exit code.
fn get_failure_lines(output: &Output) -> (Option<i32>, Vec<String>) {
    let text = stdout(output);
    let lines = text
        .lines()
        .skip_while(|line| !line.starts_with("Starting... ("))
        .skip(1)
        .take_while(|line| !line.starts_with("Finished in "))
        .map(str::to_owned)
        .collect();
    (output.status.code(), lines)
}

const LIVENESS_SYMMETRY_WARNING: &str = "Declaring symmetry during liveness checking is dangerous. It might cause TLC to miss violations of the stated liveness properties. Please check liveness without symmetry defined.";

#[test]
fn warns_about_the_symmetry_before_a_temporal_property_tlc_rejects() {
    // tests/fixtures/cli-output/EventualAction: TLC computes the symmetry, starts the liveness
    // checker, which warns that a symmetry is dangerous for liveness, then rejects the property.
    let fixtures =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../../tests/fixtures/cli-output");
    let error = "Temporal formulas containing actions must be of forms <>[]A or []<>A.";
    for (args, expected) in [
        (
            &["-noGenerateSpecTE", "EventualAction.tla"][..],
            vec![
                format!("Warning: {LIVENESS_SYMMETRY_WARNING}"),
                "(Use the -nowarning option to disable this warning.)".to_owned(),
                format!("Error: {error}"),
            ],
        ),
        (
            &["-noGenerateSpecTE", "-tool", "EventualAction.tla"],
            vec![
                "@!@!@ENDMSG 2185 @!@!@".to_owned(),
                "@!@!@STARTMSG 2279:3 @!@!@".to_owned(),
                LIVENESS_SYMMETRY_WARNING.to_owned(),
                "@!@!@ENDMSG 2279 @!@!@".to_owned(),
                "@!@!@STARTMSG 2214:1 @!@!@".to_owned(),
                error.to_owned(),
                "@!@!@ENDMSG 2214 @!@!@".to_owned(),
                "@!@!@STARTMSG 2186:0 @!@!@".to_owned(),
            ],
        ),
        (
            &["-noGenerateSpecTE", "-nowarning", "EventualAction.tla"],
            vec![format!("Error: {error}")],
        ),
    ] {
        let output = run(&fixtures, args);
        assert_eq!(
            get_failure_lines(&output),
            (Some(255), expected),
            "{args:?}\n{}",
            stdout(&output)
        );
    }
}

#[test]
fn warns_about_the_spec_then_the_symmetry_before_a_temporal_property_tlc_rejects() {
    // TLC warns about the invariant and the property as it processes the spec, then about the
    // symmetry as it starts the liveness checker, which can't handle Prop.
    let directory =
        std::env::temp_dir().join(format!("prove-it-cli-warned-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    std::fs::write(
        directory.join("Warned.tla"),
        "---- MODULE Warned ----\nEXTENDS TLC\nCONSTANTS a, b\nVARIABLE x\nInit == x = a\nNext == x' = b\nSpec == Init /\\ [][Next]_x\nTrue == TRUE\nStart == x = a\nProp == \\E v \\in {x} : [](x = v)\nSym == Permutations({a, b})\n====\n",
    )
    .expect("a file");
    std::fs::write(
        directory.join("Warned.cfg"),
        "CONSTANTS a = a b = b\nSPECIFICATION Spec\nINVARIANT True\nPROPERTIES Start Prop\nSYMMETRY Sym\n",
    )
    .expect("a file");
    let error =
        "TLC cannot handle the temporal formula line 10, col 9 to line 10, col 32 of module Warned";
    let output = run(&directory, &["-noGenerateSpecTE", "Warned"]);
    assert_eq!(
        get_failure_lines(&output),
        (
            Some(255),
            vec![
                "Warning: The invariant True is a constant-level formula (i.e., it contains no variables, primes, or temporal operators) and evaluates to TRUE. To assert constant-level formulas in your spec, use ASSUME ConstInv. If you optionally want to give the assumption a name, write ASSUME YourAssumption == ConstInv instead. See https://explain.tlapl.us/assumptions-and-invariants for additional details.".to_owned(),
                "(Use the -nowarning option to disable this warning.)".to_owned(),
                "Warning: The formula Start is a state-level formula, but it was used as a PROPERTY (or PROPERTIES), where a temporal formula is typically expected. State-level formulas used as PROPERTY or PROPERTIES are only checked in the initial state. To verify that the formula Start holds in all states of every behavior, use INVARIANT Start instead. Alternatively, applying the \"always\" temporal operator ([]) to the state-level formula Start changes it into a temporal formula, asserting that Start holds in all states of every behavior. See https://explain.tlapl.us/invariants-and-properties for additional details.".to_owned(),
                format!("Warning: {LIVENESS_SYMMETRY_WARNING}"),
                format!("Error: {error}"),
            ]
        ),
        "{}",
        stdout(&output)
    );
    let output = run(&directory, &["-noGenerateSpecTE", "-nowarning", "Warned"]);
    assert_eq!(
        get_failure_lines(&output),
        (Some(255), vec![format!("Error: {error}")]),
        "{}",
        stdout(&output)
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn declines_a_temporal_property_tlc_rejects_after_a_definition_prints_with_a_symmetry() {
    // TLC prints "shown" as it computes the constant definitions, before it warns about the
    // symmetry and rejects the property, which the front end doesn't follow.
    let directory =
        std::env::temp_dir().join(format!("prove-it-cli-printed-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    std::fs::write(
        directory.join("Printed.tla"),
        "---- MODULE Printed ----\nEXTENDS TLC\nCONSTANTS a, b\nVARIABLE x\nInit == x = a\nNext == x' = b\nSpec == Init /\\ [][Next]_x\nProp == <><<Next>>_x\nShown == Print(\"shown\", 1)\nSym == Permutations({a, b})\n====\n",
    )
    .expect("a file");
    std::fs::write(
        directory.join("Printed.cfg"),
        "CONSTANTS a = a b = b\nSPECIFICATION Spec\nPROPERTY Prop\nSYMMETRY Sym\n",
    )
    .expect("a file");
    let output = run(&directory, &["-noGenerateSpecTE", "Printed"]);
    assert_eq!(output.status.code(), Some(1), "{}", stdout(&output));
    assert_eq!(
        String::from_utf8_lossy(&output.stderr),
        "prove-it: not native yet: a temporal property TLC rejects after it warns about the symmetry, with a definition TLC may print as it starts\n"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

#[test]
fn declines_a_temporal_property_tlc_rejects_after_it_warns_the_symmetry_set_is_too_small() {
    // TLC warns that {a} is too small as it computes the symmetry, before the liveness checker
    // warns about the symmetry and rejects the property. Under -nowarning it prints the error
    // alone.
    let directory = std::env::temp_dir().join(format!(
        "prove-it-cli-small-symmetry-{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&directory).expect("a directory");
    std::fs::write(
        directory.join("Small.tla"),
        "---- MODULE Small ----\nEXTENDS TLC\nCONSTANTS a\nVARIABLE x\nInit == x = a\nNext == UNCHANGED x\nSpec == Init /\\ [][Next]_x\nProp == <><<Next>>_x\nSym == Permutations({a})\n====\n",
    )
    .expect("a file");
    std::fs::write(
        directory.join("Small.cfg"),
        "CONSTANTS a = a\nSPECIFICATION Spec\nPROPERTY Prop\nSYMMETRY Sym\n",
    )
    .expect("a file");
    let output = run(&directory, &["-noGenerateSpecTE", "Small"]);
    assert_eq!(output.status.code(), Some(1), "{}", stdout(&output));
    assert_eq!(
        String::from_utf8_lossy(&output.stderr),
        "prove-it: not native yet: a temporal property TLC rejects after it computes a symmetry it may report on\n"
    );
    let output = run(&directory, &["-noGenerateSpecTE", "-nowarning", "Small"]);
    assert_eq!(
        get_failure_lines(&output),
        (
            Some(255),
            vec![
                "Error: Temporal formulas containing actions must be of forms <>[]A or []<>A."
                    .to_owned()
            ]
        ),
        "{}",
        stdout(&output)
    );
    std::fs::remove_dir_all(directory).expect("removed");
}
