//! Runs the binary with `-coverage` on the specs in tests/coverage, beside each TLC's output at
//! d8fb231 with `-workers 1 -coverage 1 -noGenerateSpecTE -fp 0`, plain and with `-tool`, less
//! its banner, the files it parsed, its progress and its times.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const FIXTURES: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/coverage");

fn run(test: &str, name: &str, args: &[&str]) -> Output {
    run_with(test, name, args, &[])
}

fn run_with(test: &str, name: &str, args: &[&str], environment: &[(&str, &str)]) -> Output {
    let directory = copy_fixtures(test);
    let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .envs(environment.iter().copied())
        .args([
            "-workers",
            "1",
            "-coverage",
            "1",
            "-noGenerateSpecTE",
            "-fp",
            "0",
        ])
        .args(args)
        .arg(name)
        .current_dir(&directory)
        .output()
        .expect("the binary runs");
    std::fs::remove_dir_all(directory).expect("removed");
    output
}

fn copy_fixtures(test: &str) -> PathBuf {
    let directory =
        std::env::temp_dir().join(format!("prove-it-coverage-{test}-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    for entry in std::fs::read_dir(FIXTURES).expect("the fixtures") {
        let path = entry.expect("an entry").path();
        if path
            .extension()
            .is_some_and(|extension| extension == "tla" || extension == "cfg")
        {
            std::fs::copy(&path, directory.join(path.file_name().expect("a name")))
                .expect("copied");
        }
    }
    directory
}

fn get_expected(file: &str) -> String {
    std::fs::read_to_string(Path::new(FIXTURES).join(file)).expect("TLC's output")
}

// The output less what differs from run to run or from TLC's in what TLC is: its banner, the
// files it parsed, its progress and its times.
fn get_normalized(text: &str) -> String {
    const SKIPPED: [&str; 7] = [
        "TLC2 Version ",
        "Running breadth-first search ",
        "Parsing file ",
        "Semantic processing of module ",
        "Linting of module ",
        "Progress(",
        "@!@!@STARTMSG 2200:",
    ];
    text.lines()
        .filter(|line| {
            !SKIPPED.iter().any(|prefix| line.starts_with(prefix))
                && *line != "@!@!@ENDMSG 2200 @!@!@"
        })
        .map(|line| match line.starts_with("Finished in ") {
            true => "Finished in _ at (_)\n".to_string(),
            false => format!("{}\n", get_undated(line)),
        })
        .collect()
}

// The line with each date and time, `2026-11-10 23:36:02`, as `_`.
fn get_undated(line: &str) -> String {
    const PATTERN: &[u8] = b"0000-00-00 00:00:00";
    let bytes = line.as_bytes();
    let mut undated = String::new();
    let mut index = 0;
    while index < bytes.len() {
        let is_date = bytes.len() - index >= PATTERN.len()
            && PATTERN
                .iter()
                .zip(&bytes[index..])
                .all(|(pattern, byte)| match pattern {
                    b'0' => byte.is_ascii_digit(),
                    _ => pattern == byte,
                });
        if is_date {
            undated.push('_');
            index += PATTERN.len();
        } else {
            let character = line[index..].chars().next().expect("a character");
            undated.push(character);
            index += character.len_utf8();
        }
    }
    undated
}

fn assert_as_tlc(name: &str) {
    for (args, suffix) in [(&[][..], ""), (&["-tool"][..], ".tool")] {
        let output = run(&format!("{name}{suffix}"), name, args);
        let text = String::from_utf8_lossy(&output.stdout);
        assert_eq!(
            get_normalized(&text),
            get_expected(&format!("{name}{suffix}.txt")),
            "{name}{suffix}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

#[test]
fn reports_coverage_of_a_run_that_ends_as_tlc() {
    // An action of two disjuncts reported apart (1:N), a LET, an operator two actions apply, a
    // state and an action constraint, and a variable of 2000 values, which TLC's HyperLogLog
    // estimates as 4276.
    assert_as_tlc("Counter");
}

#[test]
fn reports_coverage_the_engine_counts_as_tlc() {
    // Sets an expression builds and enumerates: a quantifier's, CHOOSE's, x' \in S's, a
    // function's domain and S \cup T's T, which count what they enumerate as secondary counts.
    assert_as_tlc("Built");
}

#[test]
fn counts_coverage_in_the_engine_as_the_replay_does() {
    // The engine's search counts these, and the replay counts them again to compare.
    for name in ["Counter", "Built", "LetOp"] {
        let output = run_with(
            &format!("compare-{name}"),
            name,
            &[],
            &[("PROVE_IT_TEST_COVERAGE_COMPARE", "1")],
        );
        let errors = String::from_utf8_lossy(&output.stderr);
        assert_eq!(
            errors, "coverage compare: engine counted\ncoverage compare: same\n",
            "{name}"
        );
        assert_eq!(
            get_normalized(&String::from_utf8_lossy(&output.stdout)),
            get_expected(&format!("{name}.txt")),
            "{name}"
        );
    }
}

#[test]
fn reports_coverage_of_a_violation_and_its_lazy_sets_as_tlc() {
    // SUBSET, [S -> T] and a filter, which count what they enumerate as secondary counts.
    assert_as_tlc("Sets");
}

#[test]
fn reports_coverage_of_a_deadlock_as_tlc() {
    assert_as_tlc("Stuck");
}

#[test]
fn declines_coverage_of_an_instance() {
    // TLC reports the definitions an INSTANCE copies under their substitutions, which the port
    // doesn't follow, so the binary declines rather than print a report TLC wouldn't.
    let output = run("Twin", "Twin", &[]);
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("prove-it: not native yet: coverage: a definition an INSTANCE copies"),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
}

#[test]
fn declines_coverage_on_more_than_one_worker() {
    let output = run("workers", "Stuck", &["-workers", "2"]);
    assert!(
        String::from_utf8_lossy(&output.stderr).contains(
            "prove-it: not native yet: coverage on more than one worker is timing-dependent in TLC"
        ),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
}

#[test]
fn declines_coverage_tlc_reports_part_way_through_the_search() {
    // With -coverage 0, TLC reports coverage after its first progress report, about 3 s in.
    let output = run("endless", "Endless", &["-coverage", "0"]);
    assert_eq!(
        String::from_utf8_lossy(&output.stderr),
        "prove-it: not native yet: coverage TLC reports part way through the search is timing-dependent\n",
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
}

#[test]
fn declines_coverage_of_a_run_past_the_cut() {
    // TLC ends the report of a run past 5 minutes with 2777, which a native run past the cut,
    // here 0 s, can't rule out.
    let output = run_with("cut", "Stuck", &[], &[("PROVE_IT_TEST_COVERAGE_CUT", "0")]);
    assert!(
        String::from_utf8_lossy(&output.stderr).contains(
            "prove-it: not native yet: coverage of a run TLC may take more than 5 minutes over"
        ),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
}

#[test]
fn declines_coverage_of_a_lazy_function_applied_in_a_walk() {
    // TLC applies a function it keeps lazy without building it, counting its body only for the
    // argument and no construction (TLC at d8fb231 reports the body twice, the engine counted it
    // four times), so neither the engine nor the replay counts it, and the binary declines.
    let output = run("LazyApply", "LazyApply", &[]);
    let errors = String::from_utf8_lossy(&output.stderr);
    assert!(
        errors.contains("prove-it: not native yet: coverage"),
        "{errors}"
    );
    assert!(
        !String::from_utf8_lossy(&output.stdout).contains("The coverage statistics"),
        "{errors}"
    );
}

#[test]
fn reports_coverage_of_a_let_operator_where_it_is_applied() {
    // TLC counts a LET operator's body under the application's wrapper, so P's body nests under
    // `P(x)` and prints nothing apart; the engine once counted it under the LET.
    assert_as_tlc("LetOp");
}
