//! Runs the binary on functions TLC builds at once or keeps lazy (`FcnLambdaValue`): a constant
//! definition's constructor over set enumerations and intervals that prints as TLC starts, a
//! constructor over a set TLC doesn't reduce, or written as the function of an application,
//! whose body TLC evaluates only at the keys it applies, and the text of one TLC can't build.
//! `lazy-functions/<spec>.out` is TLC's output, recorded from the pinned jar, with the lines
//! that hold times, paths and versions left out.

use std::path::Path;
use std::process::Command;

// The output with the lines that hold times, paths and versions left out.
fn get_untimed(text: &str) -> String {
    const DROPPED: [&str; 6] = [
        "Picked up JAVA_TOOL_OPTIONS",
        "TLC2 Version",
        "Running breadth-first",
        "Parsing file",
        "Starting...",
        "Finished in",
    ];
    text.lines()
        .filter(|line| !DROPPED.iter().any(|dropped| line.starts_with(dropped)))
        .map(|line| {
            if line.starts_with("Finished computing initial states:") {
                line.rsplit_once(" at ").map_or(line, |(kept, _)| kept)
            } else {
                line
            }
        })
        .map(|line| format!("{line}\n"))
        .collect()
}

// Checks the spec on one worker and on four: what differs from TLC's output.
fn get_differences(spec: &str) -> Vec<String> {
    let recorded = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/lazy-functions");
    let directory = std::env::temp_dir().join(format!(
        "prove-it-cli-lazy-functions-{spec}-{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&directory).expect("a directory");
    for extension in ["tla", "cfg"] {
        std::fs::copy(
            recorded.join(format!("{spec}.{extension}")),
            directory.join(format!("{spec}.{extension}")),
        )
        .expect("the spec");
    }
    let expected =
        std::fs::read_to_string(recorded.join(format!("{spec}.out"))).expect("TLC's output");
    let mut differences = Vec::new();
    for workers in ["1", "4"] {
        let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
            .args(["-noGenerateSpecTE", "-workers", workers, spec])
            .current_dir(&directory)
            .output()
            .expect("the binary runs");
        let stdout = String::from_utf8_lossy(&output.stdout);
        if get_untimed(&stdout) != expected {
            let stderr = String::from_utf8_lossy(&output.stderr);
            differences.push(format!("{spec} on {workers}:\n{stdout}{stderr}"));
        }
    }
    std::fs::remove_dir_all(directory).expect("removed");
    differences
}

#[test]
fn prints_a_constant_function_tlc_builds_as_it_starts() {
    let differences = get_differences("StartupBuilt");
    assert!(differences.is_empty(), "{}", differences.join("\n"));
}

#[test]
fn applies_a_function_tlc_keeps_lazy_only_where_it_is_applied() {
    let differences = get_differences("KeptLazy");
    assert!(differences.is_empty(), "{}", differences.join("\n"));
}

#[test]
fn reports_a_failure_at_the_applied_key_of_a_function_tlc_keeps_lazy() {
    let differences = get_differences("KeptLazyFailure");
    assert!(differences.is_empty(), "{}", differences.join("\n"));
}

#[test]
fn prints_a_function_tlc_cannot_build_unbuilt_in_a_message() {
    let differences = get_differences("LazyMerge");
    assert!(differences.is_empty(), "{}", differences.join("\n"));
}

// Checks a spec written here, which the binary declines: its message.
// A function TLC keeps lazy over a set that isn't Reducible, whose body fails at a key, prints
// unbuilt (`toString` swallows `toFcnRcd`'s failure) and applies at a key where it doesn't fail;
// one over a value that isn't a set fails to build as `FcnParams.size` does.
#[test]
fn prints_unbuilt_and_builds_a_lazy_function_as_tlc_does() {
    let differences = get_differences("LazyUnbuilt");
    assert!(differences.is_empty(), "{}", differences.join("\n"));
}

// A constructor TLC keeps lazy, applied in place, asks its domain for the argument first
// (`FcnLambdaValue.apply`), which fails as `SubsetValue.member` does.
#[test]
fn tests_the_argument_in_a_lazy_domain_as_tlc_does() {
    let differences = get_differences("LazyDomainMember");
    assert!(differences.is_empty(), "{}", differences.join("\n"));
}

// An EXCEPT of a constructor TLC built over an interval selects its key as the `FcnRcdValue`
// over that interval does.
#[test]
fn excepts_a_function_built_over_an_interval_as_tlc_does() {
    let differences = get_differences("IntervalExcept");
    assert!(differences.is_empty(), "{}", differences.join("\n"));
}

fn get_decline(spec: &str, text: &str) -> String {
    let directory = std::env::temp_dir().join(format!(
        "prove-it-cli-lazy-functions-{spec}-{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&directory).expect("a directory");
    std::fs::write(directory.join(format!("{spec}.tla")), text).expect("the spec");
    std::fs::write(directory.join(format!("{spec}.cfg")), "").expect("the config");
    let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .args(["-noGenerateSpecTE", spec])
        .current_dir(&directory)
        .output()
        .expect("the binary runs");
    std::fs::remove_dir_all(directory).expect("removed");
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    String::from_utf8_lossy(&output.stderr).into_owned()
}

// TLC evaluates the function of an application with `EvalControl.KeepLazy`, which reaches a
// constructor in a record, an EXCEPT, a CHOOSE's set or a LET definition, and keeps it lazy:
// `[a |-> [x \in 1..2 |-> PrintT(x)]].a[2]` prints only 2.
#[test]
fn declines_a_print_in_a_constructor_tlc_keeps_lazy_inside_the_applied_function() {
    for (spec, test) in [
        ("InRecord", "[a |-> [x \\in 1..2 |-> PrintT(x)]].a[2]"),
        (
            "InChoose",
            "(CHOOSE f \\in {[x \\in 1..2 |-> PrintT(x)]} : TRUE)[2]",
        ),
        (
            "InLet",
            "LET r == [a |-> [x \\in 1..2 |-> PrintT(x)]] IN r.a[2] /\\ r.a[1]",
        ),
    ] {
        let stderr = get_decline(
            spec,
            &format!("---- MODULE {spec} ----\nEXTENDS Integers, TLC\nASSUME {test}\n====\n"),
        );
        assert!(
            stderr.starts_with("prove-it: not native yet:"),
            "{spec}: {stderr}"
        );
    }
}

// A LET definition's constructor whose first use applies it keeps the FcnLambdaValue TLC made
// there, whose domain TLC reads unbuilt: the replay, which builds it, declines.
#[test]
fn declines_a_failing_constructor_a_let_names_after_its_first_application() {
    let stderr = get_decline(
        "LetDomain",
        "---- MODULE LetDomain ----\nEXTENDS Integers\nASSUME LET f == [x \\in 1..2 |-> \
         IF x = 1 THEN 1 \\div 0 ELSE x] IN f[2] = 2 /\\ DOMAIN f = 1..2\n====\n",
    );
    assert!(stderr.starts_with("prove-it: not native yet:"), "{stderr}");
}
