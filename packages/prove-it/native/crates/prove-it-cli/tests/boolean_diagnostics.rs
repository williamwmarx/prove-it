//! Boolean demands against TLC built at d8fb231.

use std::process::Command;

#[test]
fn reports_boolean_demands_of_known_value_classes() {
    for (name, expression, message) in [
        (
            "set_if",
            "IF {1} THEN TRUE ELSE FALSE",
            "A non-boolean expression (a set of the form {e1, ... ,eN}) was used as the condition of an IF.",
        ),
        (
            "eager_function",
            "IF [v \\in {1,2} |-> v] THEN TRUE ELSE TRUE",
            "A non-boolean expression (a function  of the form (d1 :> e1 @@ ... @@ dN :> eN)) was used as the condition of an IF.",
        ),
        (
            "tuple_case",
            "CASE <<1>> -> TRUE [] OTHER -> FALSE",
            "A non-boolean expression (a tuple) was used as a condition of a CASE.",
        ),
        (
            "quantifier",
            "\\A x \\in {1}: {x}",
            "TLC expected a boolean value, but did not find one. line 2, col 8 to line 2, col 24 of module M",
        ),
    ] {
        for workers in ["1", "4"] {
            let directory = std::env::temp_dir().join(format!(
                "prove-it-boolean-{name}-{workers}-{}",
                std::process::id()
            ));
            std::fs::create_dir_all(&directory).expect("a directory");
            std::fs::write(
                directory.join("M.tla"),
                format!("---- MODULE M ----\nASSUME {expression}\n====\n"),
            )
            .expect("the spec");
            std::fs::write(directory.join("M.cfg"), "").expect("the config");
            let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
                .args(["-workers", workers, "-noGenerateSpecTE", "M"])
                .current_dir(&directory)
                .output()
                .expect("the checker");
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert_eq!(output.status.code(), Some(10), "{name}: {stdout}\n{stderr}");
            assert!(stdout.contains(message), "{name}: {stdout}\n{stderr}");
            std::fs::remove_dir_all(directory).expect("removed");
        }
    }
}

#[test]
fn declines_a_materialized_function_without_class_proof() {
    let directory = std::env::temp_dir().join(format!(
        "prove-it-boolean-unknown-function-{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&directory).expect("a directory");
    std::fs::write(
        directory.join("M.tla"),
        "---- MODULE M ----\nASSUME LET S == {x \\in SUBSET {1}: TRUE} IN IF [v \\in S |-> v] THEN TRUE ELSE TRUE\n====\n",
    )
    .expect("the spec");
    std::fs::write(directory.join("M.cfg"), "").expect("the config");
    let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .args(["-workers", "1", "-noGenerateSpecTE", "M"])
        .current_dir(&directory)
        .output()
        .expect("the checker");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(1), "{stderr}");
    assert!(stderr.contains("prove-it: not native yet:"), "{stderr}");
    std::fs::remove_dir_all(directory).expect("removed");
}
