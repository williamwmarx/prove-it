//! The binary's order of strings against TLC built at d8fb231.

use std::path::PathBuf;
use std::process::{Command, Output};

// Writes the spec and its configuration to a directory of their own as Stop and checks them with
// TLC's command line on one worker, without the trace exploration spec TLC would parse.
fn run_spec(test: &str, spec: &str, config: &str) -> (Output, PathBuf) {
    let directory =
        std::env::temp_dir().join(format!("prove-it-strings-{test}-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    std::fs::write(directory.join("Stop.tla"), spec).expect("the spec");
    std::fs::write(directory.join("Stop.cfg"), config).expect("the configuration");
    let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .args(["-workers", "1", "-noTE", "Stop"])
        .current_dir(&directory)
        .output()
        .expect("the binary runs");
    (output, directory)
}

// tests/string-order: sets of strings each spec makes with `\o`, one of each class of name TLC
// interns before it checks the model, which TLC prints in the order it interned them, as TLC
// printed them at d8fb231: SANY's, Location's once SANY has parsed the root module, the string
// literals, those the constant definitions make, with RecordValue's names where one builds a
// record, Action's name where the configuration has an action, TLCGetSet's, those createConfig
// makes, then those the assumptions make, as they make them. TLC orders the strings it makes as it
// searches by when it makes them, which the engine doesn't follow, so it declines them. The same
// text TLC interns once, so the counterexample's field names TLC makes each time compare equal. A
// constant definition's text with a lone surrogate ranks as it starts too, before what the search
// makes.
#[test]
fn orders_the_strings_it_makes_as_tlc() {
    let directory = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/string-order");
    let read = |name: &str| std::fs::read_to_string(directory.join(name)).expect("a fixture");
    for (name, exit) in [
        ("made", 0),
        ("reversed", 0),
        ("record", 0),
        ("constant", 0),
        ("counterexample", 12),
        ("lone", 0),
        ("searched", 1),
    ] {
        let (output, run) = run_spec(
            name,
            &read(&format!("{name}.tla")),
            &read(&format!("{name}.cfg")),
        );
        let text = format!(
            "{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(output.status.code(), Some(exit), "{name}: {text}");
        if name == "searched" {
            assert!(
                text.contains(
                    "not native yet: the engine stopped: an order of strings the search made"
                ),
                "{text}"
            );
        } else {
            assert!(
                text.contains(&read(&format!("{name}.txt"))),
                "{name}: {text}"
            );
        }
        std::fs::remove_dir_all(run).expect("removed");
    }
}
