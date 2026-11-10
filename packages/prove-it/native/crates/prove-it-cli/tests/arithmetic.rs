//! The binary's arithmetic against TLC built at d8fb231, where TLC's methods for an operator
//! depend on the modules it loads.

use std::path::PathBuf;
use std::process::{Command, Output};

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

// Writes the spec and its configuration to a directory of their own and checks them with TLC's
// command line, without the trace exploration spec TLC would parse.
fn run_spec(test: &str, spec: &str, config: &str) -> (Output, PathBuf) {
    let directory =
        std::env::temp_dir().join(format!("prove-it-arithmetic-{test}-{}", std::process::id()));
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

#[test]
fn divides_with_naturals_or_integers_as_tlc_loads_them() {
    // `tlc2.module.Naturals#Divide` floors only a quotient Java truncates below 0 and lets
    // -2147483648 \\div -1 wrap, where `Integers#Divide` floors and reports the overflow. TLC
    // loads Integers' methods over Naturals' wherever the spec uses Integers.
    let divisions = "ASSUME PrintT((0 - 1) \\div 2)\nASSUME PrintT((0 - 7) \\div 2)\nASSUME PrintT((0 - 2147483647 - 1) \\div (0 - 1))\n";
    for (test, uses, printed) in [
        ("naturals", "EXTENDS Naturals, TLC", "0\n-4\n-2147483648\n"),
        (
            "instance",
            "EXTENDS Naturals, TLC\nLOCAL INSTANCE Integers",
            "-1\n-4\n",
        ),
        ("integers", "EXTENDS Integers, TLC", "-1\n-4\n"),
    ] {
        let spec = format!(
            "---- MODULE Divide ----\n{uses}\nVARIABLE x\nInit == x = 0\nNext == x' = x\n{divisions}====\n"
        );
        let (output, directory) = run_spec(test, &spec, "INIT Init\nNEXT Next\n");
        let text = stdout(&output);
        assert!(text.contains(&format!(")\n{printed}")), "{text}");
        if test == "naturals" {
            assert_eq!(output.status.code(), Some(0), "{text}");
        } else {
            assert_eq!(output.status.code(), Some(10), "{text}");
            assert!(
                text.contains("failed.\nOverflow when computing -2147483648 \\div -1\n"),
                "{text}"
            );
        }
        std::fs::remove_dir_all(directory).expect("removed");
    }
}
