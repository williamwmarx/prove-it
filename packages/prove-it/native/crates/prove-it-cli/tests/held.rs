//! `e \in S` of a set the state holds: a miss of the membership's table is answered by the
//! element's id where the set is short and no comparison of TLC's search can fail
//! (`Store::find_in_set`), and the table then takes no more entries than stay in a core's cache.
//! Each spec of `tests/held` prints what TLC built at d8fb231 prints (`<name>.txt`, its output
//! without the lines that hold times), on one thread and with every level shared between two and
//! four.

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

// Each tests in more sets than the table of a membership then takes.
// HeldRecords tests records of two shapes in sets of them, in a guard, a quantifier and an
// invariant. HeldMixed tests a record of the state in each, and then a number, which TLC fails to
// compare with a record. HeldLong tests in a set that grows past the length the engine scans and
// in a run of integers. HeldKinds tests sets, tuples and strings in sets of their kind, and
// HeldModel a model value in sets of numbers.
#[test]
fn tests_membership_in_a_set_the_state_holds_as_tlc() {
    let tests = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/held");
    let mut names: Vec<String> = std::fs::read_dir(&tests)
        .expect("the specs")
        .filter_map(|entry| {
            let path = entry.expect("an entry").path();
            (path.extension()? == "tla").then(|| path.file_stem()?.to_str().map(String::from))?
        })
        .collect();
    names.sort();
    assert_eq!(names.len(), 5);
    let directory = std::env::temp_dir().join(format!("prove-it-cli-held-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    for name in names {
        for extension in ["tla", "cfg"] {
            let file = format!("{name}.{extension}");
            std::fs::copy(tests.join(&file), directory.join(&file)).expect("a copy");
        }
        let expected = std::fs::read_to_string(tests.join(format!("{name}.txt"))).expect("txt");
        for threads in [None, Some("2"), Some("4")] {
            let output = run(&directory, &name, threads);
            assert_eq!(
                get_untimed(&stdout(&output)),
                expected,
                "{name} on {threads:?} threads: {}",
                stderr(&output)
            );
        }
    }
    std::fs::remove_dir_all(directory).expect("removed");
}
