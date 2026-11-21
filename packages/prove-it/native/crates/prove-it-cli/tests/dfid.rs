//! Depth-first iterative-deepening against TLC d8fb231. Each `<name>.out` beside a spec is TLC's
//! whole -tool output at `-fp 0 -seed 4 -noGenerateSpecTE` with `-dfid` (`<name>.<limit>.out`
//! at another limit), run as `java -XX:+UseParallelGC -cp tla2tools.jar tlc2.TLC`, and
//! `<name>.exit` its exit code. Both outputs drop what depends on the build, the machine or the
//! time, as `transcript` has it.

use std::process::Command;

// TLC's output but its version and the line that describes the machine (messages 2262 and 2271),
// the files SANY parses, which name where the jar unpacks its standard modules, the dates and
// times, and the identity hash of TLC's tool.
fn transcript(text: &str) -> String {
    let mut result = String::new();
    let mut skipped = None;
    for line in text.lines() {
        if let Some(code) = skipped {
            if line.starts_with(&format!("@!@!@ENDMSG {code} ")) {
                skipped = None;
            }
            continue;
        }
        if let Some(code) = ["2262", "2271"]
            .into_iter()
            .find(|code| line.starts_with(&format!("@!@!@STARTMSG {code}:")))
        {
            skipped = Some(code);
            continue;
        }
        if line.starts_with("Parsing file ") {
            continue;
        }
        let line = if line.starts_with("Starting... (") {
            "Starting... (<date>)".to_owned()
        } else if line.starts_with("tlc2.tool.impl.FastTool@") {
            // `Object.toString` of TLC's tool, its identity hash.
            "tlc2.tool.impl.FastTool@<id>".to_owned()
        } else if line.starts_with("Finished in ") {
            "Finished in <time>".to_owned()
        } else if let Some((progress, rest)) = line
            .starts_with("Progress(")
            .then(|| line.split_once(" at "))
            .flatten()
        {
            // The date holds two colons of its own.
            let suffix = rest.splitn(4, ':').nth(3).unwrap_or_default();
            format!("{progress} at <date>:{suffix}")
        } else {
            line.to_owned()
        };
        result.push_str(&line);
        result.push('\n');
    }
    result
}

// Runs the binary on the fixture `name` with `-dfid limit` and the mode given, if any, and
// compares its exit code and transcript with TLC's, recorded as `recorded`.
fn check_against_tlc(name: &str, recorded: &str, workers: &str, mode: Option<&str>, limit: &str) {
    let fixtures = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/dfid");
    let directory =
        std::env::temp_dir().join(format!("prove-it-dfid-{recorded}-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    for extension in ["tla", "cfg"] {
        std::fs::copy(
            fixtures.join(format!("{name}.{extension}")),
            directory.join(format!("M.{extension}")),
        )
        .unwrap();
    }
    let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .args(["-tool", "-workers", workers])
        .args(["-fp", "0", "-seed", "4", "-noGenerateSpecTE"])
        .args(mode)
        .args(["-dfid", limit, "M"])
        .current_dir(&directory)
        .output()
        .unwrap();
    let expected: i32 = std::fs::read_to_string(fixtures.join(format!("{recorded}.exit")))
        .unwrap()
        .trim()
        .parse()
        .unwrap();
    assert_eq!(
        output.status.code(),
        Some(expected),
        "{recorded}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        transcript(&String::from_utf8_lossy(&output.stdout)),
        std::fs::read_to_string(fixtures.join(format!("{recorded}.out"))).unwrap(),
        "{recorded}"
    );
    std::fs::remove_dir_all(directory).unwrap();
}

#[test]
fn iterative_deepening_counts_and_limits() {
    for (name, limit) in [
        ("cycle", "10"),
        ("limit", "3"),
        ("print", "10"),
        ("live", "10"),
        ("workers", "10"),
        ("workers-assumption", "10"),
        ("invariant", "10"),
        ("deadlock", "10"),
        ("action", "10"),
        ("incomplete", "10"),
        ("partial-actions", "10"),
        ("continue-init", "10"),
        ("continue-invariant", "10"),
        ("continue-action", "10"),
        ("multi", "10"),
        ("post", "10"),
    ] {
        let workers = if name.starts_with("workers") {
            "4"
        } else {
            "1"
        };
        let mode = if name.starts_with("continue-") {
            "-continue"
        } else {
            "-modelcheck"
        };
        check_against_tlc(name, name, workers, Some(mode), limit);
    }
}

#[test]
fn iterative_deepening_evaluation_failures() {
    for name in [
        "error-next",
        "error-next-later",
        "error-overflow",
        "error-assert",
        "error-invariant",
        "error-action",
        "initial-incomplete",
        "error-initial-invariant",
        "error-initial-predicate",
    ] {
        check_against_tlc(name, name, "1", None, "10");
    }
}

// A failure that keeps TLC's call stack, of the next-state relation, an invariant or an action
// property, at the last level -dfid allows and at the level before it: TLC replays the expansion
// on the level after the failure, printing the nested expressions and counting what the replay
// generates, but at level `DFIDMax` its loop ends first (`DFIDModelChecker.modelCheckImpl`).
#[test]
fn iterative_deepening_failures_at_the_last_level() {
    for name in ["last-next", "last-invariant", "last-action"] {
        for limit in ["3", "4"] {
            check_against_tlc(name, &format!("{name}.{limit}"), "1", None, limit);
        }
    }
}

// TLC's DFIDWorker allocates its stacks for every level up to -dfid before it searches, which a
// deep enough -dfid runs out of memory for (TLC's output with 3 GB of heap at -dfid 30000000 is
// "Java ran out of memory"); a spec without variables, which the front end gives FALSE for Init
// and Next, may have no action in TLC, which then reports success after the initial states.
#[test]
fn declines_dfid_stacks_and_specs_without_variables() {
    let fixtures = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/dfid");
    for (name, limit, reason) in [
        (
            "limit",
            "100001",
            "-dfid with stacks TLC may not have the memory for",
        ),
        (
            "limit",
            "2147483647",
            "-dfid with stacks TLC may not have the memory for",
        ),
        // A search that never ends declines as its level 2 starts, as TLC runs out of memory.
        (
            "unbounded",
            "2147483647",
            "-dfid with stacks TLC may not have the memory for",
        ),
        ("no-variables", "3", "DFID of a spec without variables"),
    ] {
        let directory = std::env::temp_dir().join(format!(
            "prove-it-dfid-declines-{name}-{limit}-{}",
            std::process::id()
        ));
        std::fs::create_dir_all(&directory).unwrap();
        for extension in ["tla", "cfg"] {
            std::fs::copy(
                fixtures.join(format!("{name}.{extension}")),
                directory.join(format!("M.{extension}")),
            )
            .unwrap();
        }
        let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
            .args(["-dfid", limit, "M"])
            .current_dir(&directory)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(1), "{name} {limit}");
        assert!(output.stdout.is_empty(), "{name} {limit}");
        assert_eq!(
            String::from_utf8_lossy(&output.stderr),
            format!("prove-it: not native yet: {reason}\n"),
            "{name} {limit}"
        );
        std::fs::remove_dir_all(directory).unwrap();
    }
}

#[test]
fn declines_unmodelled_dfid_diameter() {
    let fixtures = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/dfid");
    let directory =
        std::env::temp_dir().join(format!("prove-it-dfid-diameter-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    for extension in ["tla", "cfg"] {
        std::fs::copy(
            fixtures.join(format!("diameter.{extension}")),
            directory.join(format!("M.{extension}")),
        )
        .unwrap();
    }
    let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .args([
            "-tool",
            "-workers",
            "1",
            "-fp",
            "0",
            "-seed",
            "4",
            "-noGenerateSpecTE",
            "-dfid",
            "10",
            "M",
        ])
        .current_dir(&directory)
        .output()
        .unwrap();
    assert_eq!(
        std::fs::read_to_string(fixtures.join("diameter.exit"))
            .unwrap()
            .trim(),
        "0"
    );
    assert!(
        std::fs::read_to_string(fixtures.join("diameter.full.txt"))
            .unwrap()
            .contains("Model checking completed. No error has been found.")
    );
    assert_eq!(output.status.code(), Some(1));
    assert!(
        output.stdout.is_empty(),
        "decline leaked stdout: {}",
        String::from_utf8_lossy(&output.stdout)
    );
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("DFID with TLCGet of diameter or distinct")
    );
    std::fs::remove_dir_all(directory).unwrap();
}

#[test]
fn declines_interacting_initial_states() {
    let fixtures = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/dfid");
    let directory =
        std::env::temp_dir().join(format!("prove-it-dfid-interacting-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    for extension in ["tla", "cfg"] {
        std::fs::copy(
            fixtures.join(format!("multi-interaction.{extension}")),
            directory.join(format!("M.{extension}")),
        )
        .unwrap();
    }
    let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .args([
            "-tool",
            "-workers",
            "1",
            "-fp",
            "0",
            "-seed",
            "4",
            "-noGenerateSpecTE",
            "-dfid",
            "10",
            "M",
        ])
        .current_dir(&directory)
        .output()
        .unwrap();
    assert_eq!(
        std::fs::read_to_string(fixtures.join("multi-interaction.exit"))
            .unwrap()
            .trim(),
        "0"
    );
    assert!(
        std::fs::read_to_string(fixtures.join("multi-interaction.tlc.txt"))
            .unwrap()
            .contains("Model checking completed. No error has been found.")
    );
    assert_eq!(output.status.code(), Some(1));
    assert!(
        output.stdout.is_empty(),
        "decline leaked stdout: {}",
        String::from_utf8_lossy(&output.stdout)
    );
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("DFID initial-state order can affect the search")
    );
    std::fs::remove_dir_all(directory).unwrap();
}

#[test]
fn declines_uncertain_tautology_order() {
    let fixtures = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/dfid");
    for (name, exit, message) in [
        ("tautology-live", "255", "1000:1"),
        ("tautology-empty", "77", "2253:1"),
    ] {
        let directory =
            std::env::temp_dir().join(format!("prove-it-dfid-{name}-{}", std::process::id()));
        std::fs::create_dir_all(&directory).unwrap();
        for extension in ["tla", "cfg"] {
            std::fs::copy(
                fixtures.join(format!("{name}.{extension}")),
                directory.join(format!("M.{extension}")),
            )
            .unwrap();
        }
        let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
            .args([
                "-tool",
                "-workers",
                "1",
                "-fp",
                "0",
                "-seed",
                "4",
                "-noGenerateSpecTE",
                "-dfid",
                "4",
                "M",
            ])
            .current_dir(&directory)
            .output()
            .unwrap();
        assert_eq!(
            std::fs::read_to_string(fixtures.join(format!("{name}.exit")))
                .unwrap()
                .trim(),
            exit
        );
        assert!(
            std::fs::read_to_string(fixtures.join(format!("{name}.full.txt")))
                .unwrap()
                .contains(message)
        );
        assert_eq!(output.status.code(), Some(1));
        assert!(
            output.stdout.is_empty(),
            "decline leaked stdout: {}",
            String::from_utf8_lossy(&output.stdout)
        );
        assert!(
            String::from_utf8_lossy(&output.stderr)
                .contains("DFID liveness constructor error before a tautology")
        );
        std::fs::remove_dir_all(directory).unwrap();
    }
}

// A DFID search that declines after it opened the -dump file puts the file back as it found it:
// the user's own file, or none where there was none.
#[test]
fn a_declined_dfid_search_leaves_the_dump_file_as_it_found_it() {
    let directory = std::env::temp_dir().join(format!("prove-it-dfid-dump-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&directory);
    std::fs::create_dir_all(&directory).unwrap();
    std::fs::write(
        directory.join("N.tla"),
        "---- MODULE N ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == x' = CHOOSE y : y = x\n====\n",
    )
    .unwrap();
    std::fs::write(directory.join("N.cfg"), "INIT Init\nNEXT Next\n").unwrap();
    let dump = directory.join("states.dump");
    for before in [Some("ORIGINAL\n"), None] {
        let _ = std::fs::remove_file(&dump);
        if let Some(before) = before {
            std::fs::write(&dump, before).unwrap();
        }
        let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
            .args([
                "-tool",
                "-workers",
                "1",
                "-fp",
                "0",
                "-seed",
                "4",
                "-noGenerateSpecTE",
                "-dfid",
                "3",
                "-dump",
                "states.dump",
                "N",
            ])
            .current_dir(&directory)
            .output()
            .unwrap();
        assert_eq!(output.status.code(), Some(1));
        assert!(
            String::from_utf8_lossy(&output.stderr).starts_with("prove-it: not native yet: "),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(std::fs::read_to_string(&dump).ok().as_deref(), before);
    }
    std::fs::remove_dir_all(directory).unwrap();
}

// A DFID search whose -dump file the run can't read first, to put it back on a later decline,
// declines before it opens the file, as main, which declined -dfid, left it.
#[cfg(unix)]
#[test]
fn a_dfid_search_declines_before_opening_a_dump_file_it_cant_read() {
    use std::os::unix::fs::PermissionsExt;
    let directory =
        std::env::temp_dir().join(format!("prove-it-dfid-dump-unread-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&directory);
    std::fs::create_dir_all(&directory).unwrap();
    std::fs::write(
        directory.join("B.tla"),
        "---- MODULE B ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x < 3 /\\ x' = x + 1\n====\n",
    )
    .unwrap();
    std::fs::write(directory.join("B.cfg"), "INIT Init\nNEXT Next\n").unwrap();
    let dump = directory.join("states.dump");
    std::fs::write(&dump, "ORIGINAL\n").unwrap();
    std::fs::set_permissions(&dump, std::fs::Permissions::from_mode(0o200)).unwrap();
    // A process that may read any file reads this one too, and keeps it.
    let is_readable = std::fs::read(&dump).is_ok();
    let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .args(["-workers", "1", "-dfid", "3", "-dump", "states.dump", "B"])
        .current_dir(&directory)
        .output()
        .unwrap();
    std::fs::set_permissions(&dump, std::fs::Permissions::from_mode(0o600)).unwrap();
    assert_eq!(output.status.code(), Some(1));
    if !is_readable {
        assert!(
            String::from_utf8_lossy(&output.stderr)
                .contains("-dfid with -dump into a file it can't keep"),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
    assert_eq!(std::fs::read_to_string(&dump).unwrap(), "ORIGINAL\n");
    std::fs::remove_dir_all(directory).unwrap();
}
