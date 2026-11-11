//! TLC computes a 0-ary definition as it starts where `getLevelBound` finds it of constant level
//! (`processConstantDefns`), which differs from the level SANY gives it: an operator passed as an
//! argument is of level 0 whatever it reads, and any name spelled as a variable is of level 1.
//! Each spec here is one main printed another message for than TLC, with TLC's output (`tlc.out`,
//! recorded from TLC at d8fb231), on one thread and on four.

mod common;

use std::path::Path;

use common::{run, stderr, stdout};

fn get_untimed(text: &str) -> String {
    const DROPPED: [&str; 8] = [
        "Picked up JAVA_TOOL_OPTIONS",
        "TLC2 Version",
        "Running breadth-first",
        "Parsing file",
        "Starting...",
        "Finished in",
        "Warning: Please run the Java VM",
        "(Use the -nowarning",
    ];
    text.lines()
        .filter(|line| !DROPPED.iter().any(|dropped| line.starts_with(dropped)))
        .map(|line| {
            let line = if line.starts_with("Finished computing initial states:") {
                line.rsplit_once(" at ").map_or(line, |(kept, _)| kept)
            } else {
                line
            };
            format!("{line}\n")
        })
        .collect()
}

// Runs each case of a directory of cases on one thread and on four, and gives what `differs`
// finds of each run, by case and threads.
fn check_cases(cases: &str, differs: impl Fn(&str, &std::process::Output) -> bool) -> Vec<String> {
    let cases = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join(cases);
    let mut names: Vec<_> = std::fs::read_dir(&cases)
        .expect("the cases")
        .map(|entry| entry.expect("a case").file_name())
        .collect();
    names.sort();
    let mut differences = Vec::new();
    for name in names {
        let case = cases.join(&name);
        let directory = std::env::temp_dir().join(format!(
            "prove-it-cli-startup-level-{}-{}",
            name.to_string_lossy(),
            std::process::id()
        ));
        std::fs::create_dir_all(&directory).expect("a directory");
        for entry in std::fs::read_dir(&case).expect("the case") {
            let path = entry.expect("a file").path();
            if path.extension().is_some_and(|extension| extension != "out") {
                std::fs::copy(&path, directory.join(path.file_name().expect("a name")))
                    .expect("the spec");
            }
        }
        let expected = std::fs::read_to_string(case.join("tlc.out")).expect("TLC's output");
        for workers in ["1", "4"] {
            let output = run(&directory, &["-noGenerateSpecTE", "-workers", workers, "M"]);
            if differs(&expected, &output) {
                differences.push(format!(
                    "{} on {workers}:\n{}{}",
                    name.to_string_lossy(),
                    stdout(&output),
                    stderr(&output)
                ));
            }
        }
        std::fs::remove_dir_all(directory).expect("removed");
    }
    differences
}

// An ALIAS or a postcondition that reaches an instance's parameter or bound name spelled as a
// variable, which TLC neither computed as it started nor rejects as a constant.
#[test]
fn prints_what_tlc_prints_where_it_computes_a_definition_as_it_runs() {
    let differences = check_cases("startup-level", |expected, output| {
        get_untimed(&stdout(output)) != expected
    });
    assert!(differences.is_empty(), "{}", differences.join("\n"));
}
