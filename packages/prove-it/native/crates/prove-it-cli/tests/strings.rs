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
// makes, and is no literal spelled as the name it ranks by.
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
        ("alias", 0),
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

// What a run printed from `Starting...` to `Finished in`, but the lines that tell the time.
fn get_untimed(text: &str) -> String {
    let start = text.find("Starting... (").expect("the start");
    let end = text.find("Finished in ").expect("the end");
    text[start..end]
        .lines()
        .skip(1)
        .filter(|line| {
            ![
                "Finished computing initial states",
                "Progress(",
                "Checking ",
                "Finished checking temporal properties",
            ]
            .iter()
            .any(|prefix| line.starts_with(prefix))
        })
        .map(|line| format!("{line}\n"))
        .collect()
}

// Checks a fixture of tests/string-order as Stop with the arguments and returns its output, its
// untimed text, and the dump `-dump dumped` wrote, if any.
fn check_fixture(
    test: &str,
    (spec, config): (&str, &str),
    args: &[&str],
) -> (Output, String, Option<String>) {
    let directory = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/string-order");
    let read = |name: &str| std::fs::read_to_string(directory.join(name)).expect("a fixture");
    let run = std::env::temp_dir().join(format!("prove-it-strings-{test}-{}", std::process::id()));
    std::fs::create_dir_all(&run).expect("a directory");
    std::fs::write(run.join("Stop.tla"), read(spec)).expect("the spec");
    std::fs::write(run.join("Stop.cfg"), read(config)).expect("the configuration");
    let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .args(args)
        .arg("Stop")
        .current_dir(&run)
        .output()
        .expect("the binary runs");
    let text = String::from_utf8_lossy(&output.stdout).into_owned();
    let dump = std::fs::read_to_string(run.join("dumped.dump")).ok();
    std::fs::remove_dir_all(run).expect("removed");
    (output, get_untimed(&text), dump)
}

// tests/string-order/trace-modules: strings the root module writes only as literals, in functions,
// records, sets, sequences and nested values, with strings only the configuration names and field
// names of records, as TLC printed them at d8fb231 on 1 and 4 workers. SANY interns each token's
// image as it parses a module (SyntaxTreeNode.java 227), a string literal's with its quotes, and
// the literal's text only in semantic analysis (StringNode.java 39), after every module is parsed
// (SANY.java 192-196); TLC compares strings by when it interned them (UniqueString.java 227-231).
// Recording the trace, TLC adds `_TLCTrace` to the root module's EXTENDS (TraceExplorationSpec.java
// 70, ParameterizedSpecObj.java 76-85), whose modules name `e`, `b` and `Len` as identifiers, so
// with -noTE `"z"` comes before `"e"`, as the spec writes them, and without it after.
// tests/string-order/model-values: an untyped model value comes before any other value
// (ModelValue.java 166), and model values in the order the configuration names them, which TLC
// reads before SANY parses (Spec.java 100, ModelValue.java 91).
#[test]
fn orders_strings_by_the_tokens_of_the_modules_tlc_parses() {
    let directory = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/string-order");
    let read = |name: &str| std::fs::read_to_string(directory.join(name)).expect("a fixture");
    for workers in ["1", "4"] {
        for name in ["trace-modules", "model-values"] {
            let (output, untimed, _) = check_fixture(
                &format!("{name}-{workers}"),
                (&format!("{name}.tla"), &format!("{name}.cfg")),
                &["-workers", workers, "-noTE"],
            );
            assert_eq!(
                output.status.code(),
                Some(12),
                "{name} {workers}: {untimed}"
            );
            assert_eq!(untimed, read(&format!("{name}.txt")), "{name} {workers}");
        }
        let (output, untimed, dump) = check_fixture(
            &format!("recorded-{workers}"),
            ("trace-modules.tla", "trace-modules-recorded.cfg"),
            &["-workers", workers, "-dump", "dumped"],
        );
        assert_eq!(output.status.code(), Some(0), "{workers}: {untimed}");
        assert_eq!(untimed, read("trace-modules-recorded.txt"), "{workers}");
        assert_eq!(
            dump.as_deref(),
            Some(read("trace-modules-recorded.dump").as_str()),
            "{workers}"
        );
    }
}
