//! `S \in SUBSET T` and `S \subseteq T`, where T reads nothing: the engine tests only the
//! elements of S that the set which last passed there lacks (`Machine::holds_all`). Each spec of
//! `tests/passed` prints what TLC built at d8fb231 prints (`<name>.txt`, its output without the
//! lines that hold times), or declines where TLC's stack overflows, on one thread and with every
//! level shared between two and four.

mod common;

use std::path::Path;
use std::process::{Command, Output};

use common::{stderr, stdout};

const ARGUMENTS: [&str; 10] = [
    "-workers",
    "1",
    "-nowarning",
    "-seed",
    "4",
    "-fp",
    "0",
    "-lncheck",
    "final",
    "-noTE",
];

fn run(directory: &Path, name: &str, threads: Option<&str>) -> Output {
    let mut command = Command::new(env!("CARGO_BIN_EXE_prove-it"));
    command.args(ARGUMENTS).arg(name).current_dir(directory);
    if let Some(threads) = threads {
        command
            .env("PROVE_IT_SHARED_LEVEL", "1")
            .env("PROVE_IT_WORKERS", threads);
    }
    command.output().expect("the binary runs")
}

fn get_untimed(text: &str) -> String {
    let start = text.find("Starting... (").expect("the start");
    let end = text.find("Finished in ").expect("the end");
    text[start..end]
        .lines()
        .skip(1)
        .filter(|line| {
            !line.starts_with("Finished computing initial states") && !line.starts_with("Progress(")
        })
        .map(|line| format!("{line}\n"))
        .collect()
}

// PassedChange adds and removes messages, with a set of subsets among their fields. PassedFalse
// adds a message outside the set once five passed. PassedFalseFirst and PassedRaiseFirst add two
// at once, one outside the set and one whose test fails, in either order of TLC's: the first
// decides. PassedRaise adds only the one that fails. PassedInside and PassedInsideRaise are
// PassedFalse and PassedRaiseFirst with `S \subseteq T`. PassedState tests in a set that reads a
// variable, which shrinks under a set that passed. PassedShallow and PassedDepth test the same
// set, whose test calls a recursive operator, at each depth of another: 100 calls deep in each,
// and 1,700, where TLC's stack overflows.
#[test]
fn tests_the_elements_a_set_that_passed_lacks_as_tlc() {
    let tests = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/passed");
    let mut names: Vec<String> = std::fs::read_dir(&tests)
        .expect("the specs")
        .filter_map(|entry| {
            let path = entry.expect("an entry").path();
            (path.extension()? == "tla").then(|| path.file_stem()?.to_str().map(String::from))?
        })
        .collect();
    names.sort();
    assert_eq!(names.len(), 10);
    let directory =
        std::env::temp_dir().join(format!("prove-it-cli-passed-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    for name in names {
        for extension in ["tla", "cfg"] {
            let file = format!("{name}.{extension}");
            std::fs::copy(tests.join(&file), directory.join(&file)).expect("a copy");
        }
        let expected = std::fs::read_to_string(tests.join(format!("{name}.txt")));
        for threads in [None, Some("2"), Some("4")] {
            let output = run(&directory, &name, threads);
            let Ok(expected) = &expected else {
                assert_eq!(name, "PassedDepth");
                assert!(
                    stderr(&output).contains(
                        "prove-it: not native yet: the engine stopped: recursion too deep"
                    ),
                    "{name} on {threads:?} threads: {}{}",
                    stdout(&output),
                    stderr(&output)
                );
                // The recursion is in the one state, which no thread shares.
                break;
            };
            assert_eq!(
                &get_untimed(&stdout(&output)),
                expected,
                "{name} on {threads:?} threads: {}",
                stderr(&output)
            );
        }
    }
    std::fs::remove_dir_all(directory).expect("removed");
}
