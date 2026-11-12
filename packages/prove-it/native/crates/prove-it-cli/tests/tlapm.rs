//! `prove-it tlapm` on the fixtures whose output tlapm 9ed0376 recorded: `tests/fixtures/obligations`
//! (what `tlapm -N` writes), and `tests/fixtures/tlapm-cli` (what tlapm writes as it proves, and the
//! theory and fingerprints it writes into its cache). Each run works in a copy of the fixtures,
//! since tlapm keeps its cache in the directory it runs in.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};

use prove_obligations::marshal::{MarshalValue, block, read_marshaled};

/// 2026-11-10 12:00:00 UTC.
const NOW: &str = "1794312000000";

const NOT_NATIVE: &str = "prove-it: not native yet: ";

fn fixtures() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../tests/fixtures")
}

fn read_recording(directory: &str, name: &str) -> String {
    fs::read_to_string(fixtures().join(directory).join(name)).expect("a recording")
}

fn copy_directory(from: &Path, to: &Path) {
    fs::create_dir_all(to).expect("a directory");
    for entry in fs::read_dir(from).expect("the fixtures") {
        let entry = entry.expect("an entry");
        let target = to.join(entry.file_name());
        if entry.file_type().expect("a type").is_dir() {
            copy_directory(&entry.path(), &target);
        } else {
            fs::copy(entry.path(), target).expect("a copy");
        }
    }
}

// A copy of a directory of fixtures.
fn copy_fixtures(directory: &str) -> PathBuf {
    static COUNT: AtomicUsize = AtomicUsize::new(0);
    let copy = std::env::temp_dir().join(format!(
        "prove-it-tlapm-{}-{}",
        std::process::id(),
        COUNT.fetch_add(1, Ordering::Relaxed)
    ));
    let _ = fs::remove_dir_all(&copy);
    copy_directory(&fixtures().join(directory), &copy);
    copy
}

fn run_in(directory: &Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .arg("tlapm")
        .args(args)
        .current_dir(directory)
        .env("PROVE_IT_TEST_NOW", NOW)
        .env("TZ", "UTC")
        .env_remove("TLAPM_CACHE_DIR")
        .output()
        .expect("the binary runs")
}

fn run(directory: &str, args: &[&str]) -> Output {
    run_in(&copy_fixtures(directory), args)
}

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

// The time each backend took varies from run to run.
fn without_time_used(text: &str) -> String {
    text.lines()
        .map(|line| match line.find("; time-used: ") {
            Some(start) => format!("{}; time-used: <time>", &line[..start]),
            None => line.to_owned(),
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn header(command: &str) -> String {
    format!(
        "\n\\* TLAPM version 9ed0376\n\\* launched at 2026-11-10 12:00:00 with command line:\n\\* prove-it tlapm {command}\n\n"
    )
}

#[test]
fn prints_the_obligations_tlapm_prints() {
    let cases: [(&[&str], &str); 5] = [
        (
            &["-N", "--toolbox", "0", "0", "--printallobs", "Proofs.tla"],
            "Proofs.toolbox",
        ),
        (&["-N", "--toolbox", "0", "0", "Omit.tla"], "Omit.toolbox"),
        (
            &["-N", "--toolbox", "6", "7", "Omit.tla"],
            "Omit-6-7.toolbox",
        ),
        (
            &["-N", "--toolbox", "0", "0", "--printallobs", "Renamed.tla"],
            "Renamed.toolbox",
        ),
        (
            &["-N", "--toolbox", "0", "0", "--printallobs", "Warnings.tla"],
            "Warnings.toolbox",
        ),
    ];
    for (args, recording) in cases {
        let output = run("obligations", args);
        assert_eq!(output.status.code(), Some(0), "{recording}");
        assert_eq!(stdout(&output), header(&args.join(" ")), "{recording}");
        assert_eq!(
            stderr(&output),
            read_recording("obligations", recording),
            "{recording}"
        );
    }
}

#[test]
fn reports_incomplete_proofs_and_empty_targets_under_strict() {
    let cases: [(&[&str], &str, i32); 2] = [
        (
            &["-N", "--strict", "Incomplete.tla"],
            "Incomplete.strict",
            11,
        ),
        (
            &["-N", "--strict", "--line", "2", "Proofs.tla"],
            "Proofs-2.strict",
            12,
        ),
    ];
    for (args, recording, status) in cases {
        let output = run("obligations", args);
        assert_eq!(output.status.code(), Some(status), "{recording}");
        assert_eq!(
            stderr(&output),
            read_recording("obligations", recording),
            "{recording}"
        );
    }
}

#[test]
fn prints_the_notes_and_the_summary_tlapm_prints() {
    let output = run("obligations", &["-N", "Notes.tla"]);
    assert_eq!(output.status.code(), Some(0));
    assert_eq!(
        stdout(&output),
        read_recording("obligations", "Notes.stdout")
    );
    assert_eq!(
        stderr(&output),
        read_recording("obligations", "Notes.stderr")
    );
    let output = run("obligations", &["--summary", "Incomplete.tla"]);
    assert_eq!(output.status.code(), Some(0));
    assert_eq!(
        stdout(&output),
        read_recording("obligations", "Incomplete.summary")
    );
    assert_eq!(stderr(&output), "");
    let output = run("obligations", &["-N", "Proofs.tla"]);
    assert_eq!(
        (stdout(&output), stderr(&output)),
        (String::new(), String::new())
    );
}

// tlapm ends with the backtrace of where it raised the error, which the recordings leave out.
#[test]
fn declines_an_error_tlapm_ends_with() {
    for name in [
        "Declaration",
        "Hide",
        "Label",
        "NotFound",
        "Recursive",
        "Tab",
        "Unexpected",
        "UnknownModule",
    ] {
        let recording = read_recording("obligation-errors", &format!("{name}.stderr"));
        let exception = recording
            .lines()
            .find_map(|line| line.strip_prefix(" tlapm ending abnormally with "))
            .expect("the error tlapm ends with");
        let output = run("obligation-errors", &["-N", &format!("{name}.tla")]);
        assert_eq!(output.status.code(), Some(1), "{name}");
        assert_eq!(stdout(&output), "", "{name}");
        assert_eq!(
            stderr(&output),
            format!("{NOT_NATIVE}the backtrace tlapm prints as it ends with {exception}\n"),
            "{name}"
        );
    }
    let output = run("obligations", &["-N", "Missing.tla"]);
    assert_eq!(output.status.code(), Some(1));
    assert!(stderr(&output).starts_with(NOT_NATIVE));
}

#[test]
fn declines_what_it_cant_do_as_tlapm_does() {
    let cases: [(&[&str], &str); 5] = [
        (&["-C", "Proofs.tla"], "the tlapm option -C"),
        (
            &["--printallobs", "Proofs.tla"],
            "--printallobs where tlapm proves",
        ),
        (
            &["--threads", "0", "Proofs.tla"],
            "--threads 0, which tlapm refuses",
        ),
        (&["Proof*.tla"], "globs"),
        (&[], "tlapm's report of a command line without a module"),
    ];
    for (args, reason) in cases {
        let output = run("obligations", args);
        assert_eq!(output.status.code(), Some(1), "{reason}");
        assert_eq!(stderr(&output), format!("{NOT_NATIVE}{reason}\n"));
    }
    let output = run("obligations", &["--version"]);
    assert_eq!(
        (output.status.code(), stdout(&output)),
        (Some(0), "9ed0376\n".to_owned())
    );
}

// OCaml's Arg reads the options in turn: --version prints and exits where it comes, and
// Tlapm_args.set_max_threads raises Arg.Bad on a negative count, whether or not tlapm proves.
#[test]
fn reads_the_options_in_turn_as_ocamls_arg_does() {
    let refused = format!("{NOT_NATIVE}tlapm's report of --threads -1, which it refuses\n");
    for args in [
        ["-N", "--threads", "-1", "Proofs.tla"].as_slice(),
        ["--threads", "-1", "--version"].as_slice(),
    ] {
        let output = run("obligations", args);
        assert_eq!(
            (output.status.code(), stderr(&output)),
            (Some(1), refused.clone())
        );
    }
    let output = run("obligations", &["--version", "--threads", "-1", "-C"]);
    assert_eq!(
        (output.status.code(), stdout(&output)),
        (Some(0), "9ed0376\n".to_owned())
    );
    let output = run("obligations", &["--threads", "1_000", "Proofs.tla"]);
    assert_eq!(
        stderr(&output),
        format!("{NOT_NATIVE}--threads 1000, which tlapm refuses\n")
    );
    let output = run(
        "obligations",
        &["-N", "--threads", "0x7fffffffffffffff", "Proofs.tla"],
    );
    assert_eq!(
        stderr(&output),
        format!("{NOT_NATIVE}tlapm's report of --threads 0x7fffffffffffffff, which it refuses\n")
    );
    let output = run(
        "obligations",
        &["-N", "--line", "9999999999999999999", "Proofs.tla"],
    );
    assert_eq!(
        stderr(&output),
        format!("{NOT_NATIVE}tlapm's report of --line without an integer\n")
    );
    let output = run("obligations", &["-N", "-I", "", "Proofs.tla"]);
    assert!(stderr(&output).starts_with(NOT_NATIVE));
}

// int_of_string reads 0x, 0o and 0b numbers, and _ between digits.
#[test]
fn reads_an_integer_as_tlapm_does() {
    let expected = run("obligations", &["-N", "--toolbox", "6", "7", "Omit.tla"]);
    let output = run(
        "obligations",
        &["-N", "--toolbox", "0x6", "0b111", "Omit.tla"],
    );
    assert_eq!(stderr(&output), stderr(&expected));
    assert_eq!(
        stderr(&output),
        read_recording("obligations", "Omit-6-7.toolbox")
    );
    let output = run(
        "obligations",
        &[
            "-N",
            "--toolbox",
            "0",
            "4_611_686_018_427_387_903",
            "Omit.tla",
        ],
    );
    assert_eq!(
        stderr(&output),
        read_recording("obligations", "Omit.toolbox")
    );
}

#[test]
fn proves_and_prints_what_tlapm_prints() {
    let output = run("obligations", &["Proofs.tla"]);
    assert_eq!(output.status.code(), Some(0));
    assert_eq!(
        stdout(&output),
        read_recording("tlapm-cli", "Proofs.stdout")
    );
    assert_eq!(
        stderr(&output),
        read_recording("tlapm-cli", "Proofs.stderr")
    );
    let output = run("tlapm-cli", &["Failures.tla"]);
    assert_eq!(output.status.code(), Some(3));
    assert_eq!(
        stdout(&output),
        read_recording("tlapm-cli", "Failures.stdout")
    );
    assert_eq!(
        stderr(&output),
        read_recording("tlapm-cli", "Failures.stderr")
    );
    let output = run("tlapm-cli", &["--strict", "Failures.tla"]);
    assert_eq!(output.status.code(), Some(10));
    assert_eq!(
        stderr(&output),
        read_recording("tlapm-cli", "Failures.strict")
    );
}

// With one thread, tlapm launches one decision at a time; with four, it prints each result as it
// comes back, in an order that depends on timing, which declines.
#[test]
fn prints_each_provers_result_in_toolbox_mode() {
    for name in ["Failures", "Twice"] {
        let args = ["--toolbox", "0", "0", &format!("{name}.tla")];
        let output = run("tlapm-cli", &[&["--threads", "1"], &args[..]].concat());
        assert_eq!(output.status.code(), Some(0), "{name}");
        assert_eq!(
            without_time_used(&stderr(&output)),
            without_time_used(&read_recording("tlapm-cli", &format!("{name}.toolbox"))),
            "{name}"
        );
        let output = run("tlapm-cli", &[&["--threads", "4"], &args[..]].concat());
        assert_eq!(
            (output.status.code(), stderr(&output)),
            (
                Some(1),
                format!(
                    "{NOT_NATIVE}toolbox messages of two decisions in flight at once, whose order depends on timing\n"
                )
            ),
            "{name}"
        );
    }
}

// tlapm evaluates an obligation's methods as its scheduler starts them (Prep.already_processed in
// Schedule.run's thunks), and launches every decision it can before it takes a result: with two
// threads, the second of two obligations with one fingerprint starts while the first's Zenon runs,
// and runs Zenon itself, where with one it reuses the first's failure.
#[test]
fn reuses_a_result_when_tlapm_has_it() {
    let module = "---- MODULE D ----\nEXTENDS Naturals, TLAPS\nTHEOREM A1 == 1 + 1 = 2\n  BY Zenon\nTHEOREM A2 == 1 + 1 = 2\n  BY Zenon\n====\n";
    let note = "Zenon error: exhausted search space without finding a proof\n";
    for (threads, notes) in [("1", 1), ("2", 2)] {
        let directory = write_files(&[("D.tla", module)]);
        let output = run_in(&directory, &["--threads", threads, "D.tla"]);
        assert_eq!(output.status.code(), Some(3));
        assert_eq!(stdout(&output).matches(note).count(), notes, "{threads}");
    }
    let directory = write_files(&[("D.tla", module)]);
    let output = run_in(
        &directory,
        &["--threads", "1", "--toolbox", "0", "0", "D.tla"],
    );
    assert_eq!(stderr(&output).matches("@!!already:true").count(), 1);
}

// With the default methods, the second of two obligations with one fingerprint evaluates Zenon's
// thunk once SMT fails, before or after the first's Zenon comes back, as timing has it.
#[test]
fn declines_a_reuse_timing_decides() {
    let module = "---- MODULE D ----\nEXTENDS Naturals, TLAPS\nCONSTANT x\nTHEOREM A1 == x = x + 0\n  OBVIOUS\nTHEOREM A2 == x = x + 0\n  OBVIOUS\n====\n";
    let directory = write_files(&[("D.tla", module)]);
    let output = run_in(&directory, &["--threads", "2", "D.tla"]);
    assert_eq!(
        (output.status.code(), stdout(&output), stderr(&output)),
        (
            Some(1),
            String::new(),
            format!(
                "{NOT_NATIVE}two obligations with one fingerprint, where the order decisions come back in decides what one reuses\n"
            )
        )
    );
}

// A copy of the fixtures whose cache holds the fingerprints tlapm wrote.
fn copy_with_cache() -> PathBuf {
    let directory = copy_fixtures("tlapm-cli");
    fs::create_dir_all(directory.join(".tlacache/Failures.tlaps")).expect("the cache");
    fs::copy(
        directory.join("Failures.fingerprints"),
        directory.join(".tlacache/Failures.tlaps/fingerprints"),
    )
    .expect("the fingerprints");
    directory
}

// The fingerprints file without the date and the versions stored with each result.
fn read_fingerprints(path: &Path) -> MarshalValue {
    fn strip(value: &MarshalValue) -> MarshalValue {
        let stored = MarshalValue::Text("<stored>".to_owned());
        match value {
            MarshalValue::Text(text)
                if text == "9ed0376"
                    || text == "Zenon version [268]"
                    || text == "Isabelle2025"
                    || text.starts_with("tla-ts ") =>
            {
                stored
            }
            MarshalValue::Block(inner)
                if inner.fields.len() == 6
                    && inner
                        .fields
                        .iter()
                        .all(|field| matches!(field, MarshalValue::Int(_))) =>
            {
                stored
            }
            MarshalValue::Block(inner) => {
                block(inner.tag, inner.fields.iter().map(strip).collect())
            }
            other => other.clone(),
        }
    }
    let bytes = fs::read(path).expect("a fingerprints file");
    let (_, next) = read_marshaled(&bytes, 0).expect("the magic number");
    strip(&read_marshaled(&bytes, next).expect("the table").0)
}

#[test]
fn writes_the_theory_and_the_fingerprints_tlapm_writes() {
    let directory = copy_fixtures("tlapm-cli");
    run_in(&directory, &["Failures.tla"]);
    let cache = directory.join(".tlacache/Failures.tlaps");
    assert_eq!(
        fs::read_to_string(cache.join("Failures.thy")).expect("the theory"),
        read_recording("tlapm-cli", "Failures.thy")
    );
    assert_eq!(
        read_fingerprints(&cache.join("fingerprints")),
        read_fingerprints(&directory.join("Failures.fingerprints"))
    );
    let history = cache.join("fingerprints.history/2026-11-10_12_00_00");
    assert_eq!(
        fs::read(history.join("Failures.tla")).expect("the module's copy"),
        fs::read(directory.join("Failures.tla")).expect("the module")
    );
}

#[test]
fn reuses_what_tlapm_concluded() {
    let output = run_in(
        &copy_with_cache(),
        &["--threads", "1", "--toolbox", "0", "0", "Failures.tla"],
    );
    assert_eq!(output.status.code(), Some(0));
    assert!(
        stdout(&output)
            .contains("(* loading fingerprints in \".tlacache/Failures.tlaps/fingerprints\" *)\n")
    );
    assert_eq!(
        stderr(&output),
        read_recording("tlapm-cli", "Failures.reused")
    );
}

#[test]
fn proves_again_under_nofp_and_cleanfp() {
    for option in ["nofp", "cleanfp"] {
        let output = run_in(
            &copy_with_cache(),
            &[&format!("--{option}"), "Failures.tla"],
        );
        assert_eq!(output.status.code(), Some(3), "{option}");
        assert_eq!(
            stdout(&output),
            read_recording("tlapm-cli", &format!("Failures.{option}")),
            "{option}"
        );
        assert_eq!(
            stderr(&output),
            read_recording("tlapm-cli", "Failures.stderr"),
            "{option}"
        );
    }
}

// Without proving, the fingerprints tlapm wrote are written back as the TypeScript wrote them back.
#[test]
fn writes_back_the_fingerprints_it_only_reuses() {
    let directory = copy_with_cache();
    let output = run_in(&directory, &["--noproving", "Failures.tla"]);
    assert_eq!(output.status.code(), Some(0));
    assert_eq!(
        fs::read(directory.join(".tlacache/Failures.tlaps/fingerprints")).expect("written"),
        fs::read(
            Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../prover/prover/tests/fixtures/failures-tlapm.resaved")
        )
        .expect("the fixture")
    );
}

// tlapm's file holds Zenon's and Isabelle's results of their own versions, which --safefp distrusts.
#[test]
fn trusts_no_zenon_or_isabelle_result_of_other_versions_under_safefp() {
    for (option, expected) in [
        (None, ["smt", "zenon", "zenon", "isabelle"].as_slice()),
        (Some("--safefp"), ["smt"].as_slice()),
    ] {
        let args = ["--noproving", "--toolbox", "0", "0"];
        let output = run_in(
            &copy_with_cache(),
            &[&args[..], option.as_slice(), &["Failures.tla"]].concat(),
        );
        let reused: Vec<String> = stderr(&output)
            .split("@!!BEGIN\n")
            .filter(|message| message.contains("@!!already:true"))
            .filter_map(|message| {
                message
                    .lines()
                    .find_map(|line| line.strip_prefix("@!!prover:"))
                    .map(str::to_owned)
            })
            .collect();
        assert_eq!(reused, expected, "{option:?}");
    }
}

// Fpfile.fp_init keeps the latest ten runs of history.
#[test]
fn keeps_the_latest_ten_runs_of_history() {
    let directory = copy_fixtures("tlapm-cli");
    let history = directory.join(".tlacache/Failures.tlaps/fingerprints.history");
    for day in 1..=11 {
        let run = history.join(format!("2026-01-{day:02}_00_00_00"));
        fs::create_dir_all(&run).expect("a run");
        let modified = std::time::UNIX_EPOCH + std::time::Duration::from_secs(day * 86_400);
        fs::File::open(&run)
            .expect("the run")
            .set_modified(modified)
            .expect("its time");
    }
    run_in(&directory, &["--noproving", "Failures.tla"]);
    let mut kept: Vec<String> = fs::read_dir(&history)
        .expect("the history")
        .map(|entry| {
            entry
                .expect("an entry")
                .file_name()
                .to_string_lossy()
                .into_owned()
        })
        .collect();
    kept.sort();
    let mut expected: Vec<String> = (3..=11)
        .map(|day| format!("2026-01-{day:02}_00_00_00"))
        .collect();
    expected.push("2026-11-10_12_00_00".to_owned());
    assert_eq!(kept, expected);
}

// `ls -1td <history>/*` lists no dotfile, so `rm -rf` of what it lists past the tenth keeps them.
#[test]
fn keeps_the_dotfiles_of_the_history() {
    let directory = copy_fixtures("tlapm-cli");
    let history = directory.join(".tlacache/Failures.tlaps/fingerprints.history");
    for name in [".old", "2026-01-01_00_00_00"] {
        let run = history.join(name);
        fs::create_dir_all(&run).expect("a run");
        fs::File::open(&run)
            .expect("the run")
            .set_modified(std::time::UNIX_EPOCH)
            .expect("its time");
    }
    for day in 2..=10 {
        fs::create_dir_all(history.join(format!("2026-01-{day:02}_00_00_00"))).expect("a run");
    }
    run_in(&directory, &["--noproving", "Failures.tla"]);
    assert!(history.join(".old").exists());
    assert!(!history.join("2026-01-01_00_00_00").exists());
    assert!(history.join("2026-01-02_00_00_00").exists());
}

fn read_tree(directory: &Path) -> Vec<String> {
    let mut paths = Vec::new();
    for entry in fs::read_dir(directory).expect("a directory") {
        let path = entry.expect("an entry").path();
        paths.push(path.to_string_lossy().into_owned());
        if path.is_dir() {
            paths.extend(read_tree(&path));
        }
    }
    paths.sort();
    paths
}

// Tlapm_lib.mkdir_tlaps makes the cache directory with Unix.mkdir, which makes no directory above
// it, and ends abnormally when it can't make the module's.
#[test]
fn declines_a_cache_directory_tlapm_cant_make() {
    let directory = copy_fixtures("obligations");
    let before = read_tree(&directory);
    let output = run_in(&directory, &["--cache-dir", "missing/sub", "Proofs.tla"]);
    assert_eq!(output.status.code(), Some(1));
    assert_eq!(stdout(&output), "");
    assert_eq!(
        stderr(&output),
        format!(
            "{NOT_NATIVE}the backtrace tlapm prints as it ends where it can't write missing/sub/Proofs.tlaps\n"
        )
    );
    assert_eq!(read_tree(&directory), before);
    fs::write(directory.join("file"), "").expect("a file");
    let output = run_in(&directory, &["-N", "--cache-dir", "file", "Proofs.tla"]);
    assert_eq!(
        stderr(&output),
        format!(
            "{NOT_NATIVE}the backtrace tlapm prints as it ends where it can't write file/Proofs.tlaps\n"
        )
    );
}

// With an empty cache directory, tlapm makes each module's directory at the root.
#[test]
fn declines_an_empty_cache_directory() {
    let directory = copy_fixtures("obligations");
    let before = read_tree(&directory);
    let reason =
        format!("{NOT_NATIVE}an empty cache directory, which has tlapm write its cache at /\n");
    let output = run_in(&directory, &["-N", "--cache-dir", "", "Proofs.tla"]);
    assert_eq!(
        (output.status.code(), stderr(&output)),
        (Some(1), reason.clone())
    );
    let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .args(["tlapm", "-N", "Proofs.tla"])
        .current_dir(&directory)
        .env("TLAPM_CACHE_DIR", "")
        .output()
        .expect("the binary runs");
    assert_eq!((output.status.code(), stderr(&output)), (Some(1), reason));
    assert_eq!(read_tree(&directory), before);
}

// A run that declines part way prints nothing tlapm would and writes nothing.
#[test]
fn prints_and_writes_nothing_where_it_declines_part_way() {
    let directory = copy_fixtures("tlapm-cli");
    fs::create_dir_all(directory.join(".tlacache/Failures.tlaps")).expect("the cache");
    fs::write(
        directory.join(".tlacache/Failures.tlaps/fingerprints"),
        b"not marshaled",
    )
    .expect("the fingerprints");
    let before = read_tree(&directory);
    let output = run_in(&directory, &["Failures.tla"]);
    assert_eq!(output.status.code(), Some(1));
    assert_eq!(stdout(&output), "");
    assert_eq!(
        stderr(&output),
        format!(
            "{NOT_NATIVE}a fingerprints file tlapm moves aside: .tlacache/Failures.tlaps/fingerprints\n"
        )
    );
    assert_eq!(read_tree(&directory), before);
}

// Where the file system refuses an operation the run's reads let it expect, it declines then.
#[test]
fn declines_an_operation_the_file_system_refuses() {
    if !Path::new("/proc/self").exists() {
        return;
    }
    let output = run(
        "obligations",
        &["-N", "--cache-dir", "/proc/prove-it-tlapm", "Proofs.tla"],
    );
    assert_eq!(output.status.code(), Some(1));
    assert_eq!(stdout(&output), "");
    assert_eq!(
        stderr(&output),
        format!("{NOT_NATIVE}a directory tlapm can't make: /proc/prove-it-tlapm\n")
    );
}

// A directory of its own with the files given.
fn write_files(files: &[(&str, &str)]) -> PathBuf {
    static COUNT: AtomicUsize = AtomicUsize::new(0);
    let directory = std::env::temp_dir().join(format!(
        "prove-it-tlapm-files-{}-{}",
        std::process::id(),
        COUNT.fetch_add(1, Ordering::Relaxed)
    ));
    let _ = fs::remove_dir_all(&directory);
    for (path, text) in files {
        let path = directory.join(path);
        fs::create_dir_all(path.parent().expect("a directory")).expect("a directory");
        fs::write(path, text).expect("a file");
    }
    directory
}

const MAIN: &str = "---- MODULE Main ----\nEXTENDS Defs\nTHEOREM X = 2\n  BY DEF X\n====\n";

fn get_defs(value: u32) -> String {
    format!("---- MODULE Defs ----\nX == {value}\n====\n")
}

fn get_defined(output: &Output) -> Vec<String> {
    stderr(output)
        .lines()
        .filter_map(|line| {
            line.find("X == ")
                .map(|start| line[start..].trim().to_owned())
        })
        .collect()
}

// M_save.file_search' looks in the current directory, then each -I directory in the order given,
// then the standard library; only where none has the file does Loader look in the command line's
// directories.
#[test]
fn finds_a_module_where_tlapm_does() {
    let (one, two) = (get_defs(1), get_defs(2));
    let args = ["-N", "--toolbox", "0", "0", "--printallobs"];
    let directory = write_files(&[
        ("I1/Defs.tla", &one),
        ("I2/Defs.tla", &two),
        ("Main.tla", MAIN),
    ]);
    let output = run_in(
        &directory,
        &[&args[..], &["-I", "I1", "-I", "I2", "Main.tla"]].concat(),
    );
    assert_eq!(get_defined(&output), ["X == 1"]);
    let output = run_in(
        &directory,
        &[&args[..], &["-I", "I2", "-I", "I1", "Main.tla"]].concat(),
    );
    assert_eq!(get_defined(&output), ["X == 2"]);
    let directory = write_files(&[
        ("Defs.tla", &one),
        ("sub/Defs.tla", &two),
        ("sub/Main.tla", MAIN),
    ]);
    let output = run_in(&directory, &[&args[..], &["sub/Main.tla"]].concat());
    assert_eq!(get_defined(&output), ["X == 1"]);
}

// Loader names the module by the file it was asked for, without the directory it found it in.
#[test]
fn names_a_module_by_the_path_tlapm_finds_it_at() {
    let other = "---- MODULE Other ----\nX == 1\n====\n";
    let main = "---- MODULE Main ----\nEXTENDS Defs\n====\n";
    let warning = |file: &str| {
        format!(
            "File \"{file}\", line 1, character 1 to line 3, character 4 :\nWarning: module name \"Other\" does not match file name \"Defs.tla\".\n"
        )
    };
    let directory = write_files(&[("sub/Defs.tla", other), ("sub/Main.tla", main)]);
    let output = run_in(&directory, &["-N", "sub/Main.tla"]);
    assert_eq!(output.status.code(), Some(0));
    assert_eq!(stderr(&output), warning("Defs.tla"));
    let directory = write_files(&[("Defs.tla", other), ("sub/Main.tla", main)]);
    let output = run_in(&directory, &["-N", "sub/Main.tla"]);
    assert_eq!(stderr(&output), warning("./Defs.tla"));
    let output = run_in(&directory.join("sub"), &["-N", "-I", "..", "Main.tla"]);
    assert_eq!(stderr(&output), warning("../Defs.tla"));
}

// tlapm adds ./ only to a path that Filename.is_implicit holds of.
#[test]
fn names_the_command_lines_module_as_tlapm_does() {
    let directory = copy_fixtures("obligations");
    let expected = read_recording("obligations", "Notes.stderr");
    let output = run_in(&directory, &["-N", "./Notes.tla"]);
    assert_eq!(stderr(&output), expected);
    let absolute = directory.join("Notes.tla").to_string_lossy().into_owned();
    let output = run_in(&directory, &["-N", &absolute]);
    assert_eq!(stderr(&output), expected.replace("./Notes.tla", &absolute));
}

// Tlapm_args gathers the command line's modules last first, and Tlapm_lib.read_new_modules adds
// each to a map by its name, so the first of two with one name is the one tlapm proves.
#[test]
fn proves_the_first_of_two_modules_with_one_name() {
    let directory = write_files(&[
        (
            "d1/M.tla",
            "---- MODULE M ----\nTHEOREM 1 = 3\n  OBVIOUS\n====\n",
        ),
        (
            "d2/M.tla",
            "---- MODULE M ----\nTHEOREM 1 = 2\n  OBVIOUS\n====\n",
        ),
    ]);
    let args = ["-N", "--toolbox", "0", "0", "--printallobs"];
    let output = run_in(&directory, &[&args[..], &["d1/M.tla", "d2/M.tla"]].concat());
    assert!(
        stderr(&output).contains("@!!obl:1 = 3\n"),
        "{}",
        stderr(&output)
    );
    assert!(!stderr(&output).contains("1 = 2"));
    let output = run_in(&directory, &[&args[..], &["d2/M.tla", "d1/M.tla"]].concat());
    assert!(stderr(&output).contains("@!!obl:1 = 2\n"));
}

fn write_bytes(files: &[(&str, &[u8])]) -> PathBuf {
    let directory = write_files(&[]);
    for (path, bytes) in files {
        fs::create_dir_all(&directory).expect("a directory");
        fs::write(directory.join(path), bytes).expect("a file");
    }
    directory
}

fn not_utf8(path: &str) -> String {
    format!("{NOT_NATIVE}a byte that isn't UTF-8 outside a comment in {path}\n")
}

// tlapm reads bytes, so these two strings differ. Read with U+FFFD for each byte that isn't UTF-8,
// they would be one, and the theorem proved: ED A0 80 and ED B0 80 encode U+D800 and U+DC00.
#[test]
fn declines_a_string_that_isnt_utf8() {
    let cases: [(&[u8], &[u8], &str); 3] = [
        (b"\xff", b"\xfe", "="),
        (b"\xed\xa0\x80", b"\xed\xb0\x80", "="),
        (b"\xed\xa0\x80", b"\xed\xb0\x80", "#"),
    ];
    for (left, right, operator) in cases {
        let definitions = [b"L == \"", left, b"\"\nR == \"", right, b"\"\n"].concat();
        for (path, extended) in [("M.tla", ""), ("./Lib.tla", "Lib, ")] {
            let main = [
                format!("---- MODULE M ----\nEXTENDS {extended}TLAPS\n").as_bytes(),
                if extended.is_empty() {
                    &definitions
                } else {
                    b""
                },
                format!("THEOREM L {operator} R BY SMT DEF L, R\n====\n").as_bytes(),
            ]
            .concat();
            let library = [b"---- MODULE Lib ----\n", definitions.as_slice(), b"====\n"].concat();
            let directory = write_bytes(&[("M.tla", &main), ("Lib.tla", &library)]);
            let output = run_in(&directory, &["M.tla"]);
            assert_eq!(
                (output.status.code(), stdout(&output), stderr(&output)),
                (Some(1), String::new(), not_utf8(path)),
                "{path} {operator}"
            );
        }
    }
}

fn run_bytes(text: &[u8], args: &[&str]) -> Output {
    let directory = write_bytes(&[("M.tla", text)]);
    run_in(&directory, &[args, &["M.tla"]].concat())
}

// tlapm's lexer skips what comes before a module's header, what a comment holds and what follows
// the module's end, so a byte that isn't UTF-8 there changes nothing: the run prints what it prints
// with an `e` in its place.
#[test]
fn reads_a_byte_that_isnt_utf8_where_tlapm_skips_it() {
    let cases: [(&[u8], &[u8], &[u8]); 10] = [
        (b"\xe9\n", b"", b""),
        (b"(*{ \xe9\n", b"", b""),
        (b"", b"\\* caf\xe9\n", b""),
        (b"", b"(* (* caf\xe9 *) \xe9 *)\n", b""),
        (b"", b"\\* (*{ \xe9\n", b""),
        (b"", b"(* (*{ \xe9 }*) *)\n", b""),
        (b"", b"", b"\xe9\n"),
        (b"", b"", b"\"\xe9\"\n"),
        (b"", b"---- MODULE Inner ----\n(* \xe9 *)\n====\n", b""),
        // tlapm's lexer ends a `\*` comment at a carriage return too, and Prove It's at a line
        // feed alone (fallback.md), so here both read the rest of the line as a comment.
        (b"", b"\\* abc\r\xe9\n", b""),
    ];
    for (before, inside, after) in cases {
        let get_module = |byte: u8| {
            let replace = |bytes: &[u8]| -> Vec<u8> {
                bytes
                    .iter()
                    .map(|value| if *value == 0xe9 { byte } else { *value })
                    .collect()
            };
            [
                replace(before),
                b"---- MODULE M ----\nEXTENDS TLAPS\n".to_vec(),
                replace(inside),
                b"THEOREM 1 = 1 OBVIOUS\n====\n".to_vec(),
                replace(after),
            ]
            .concat()
        };
        let read = run_bytes(&get_module(0xe9), &["-N", "--toolbox", "0", "0"]);
        let expected = run_bytes(&get_module(b'e'), &["-N", "--toolbox", "0", "0"]);
        let case = String::from_utf8_lossy(&get_module(0xe9)).into_owned();
        assert_eq!(read.status.code(), Some(0), "{case}");
        assert_eq!(stderr(&read), stderr(&expected), "{case}");
    }
}

// tlapm's columns count bytes, so a comment holding two bytes of a three-byte sequence puts what
// follows it two columns on, as two ASCII characters do; and an `é` is two columns too.
#[test]
fn counts_columns_in_bytes() {
    let run = |comment: &[u8]| {
        let text = [
            b"---- MODULE M ----\nEXTENDS TLAPS\nTHEOREM ",
            comment,
            b" 1 = 1 OBVIOUS\n====\n",
        ]
        .concat();
        stderr(&run_bytes(&text, &["-N", "--toolbox", "0", "0"]))
    };
    let expected = run(b"(*ab*)");
    assert!(expected.contains("@!!loc:3:22:3:29\n"), "{expected}");
    assert_eq!(run(b"(*\xe2\x82*)"), expected);
    assert_eq!(run("(*é*)".as_bytes()), expected);
    assert_eq!(run("(*\u{20ac}*)".as_bytes()), run(b"(*abc*)"));
}

// What the obligations hold of a byte that isn't UTF-8 decides: a nested module's string the
// module uses, a string past a nested module's end, a theorem of a module it extends, and pragmas.
#[test]
fn judges_a_byte_that_isnt_utf8_by_what_the_obligations_hold() {
    let cases: [(&[u8], Option<&str>); 9] = [
        (b"---- MODULE Inner ----\nS == \"\xff\"\n====\nTHEOREM TRUE OBVIOUS\n====\n", None),
        (
            b"---- MODULE Inner ----\nS == \"\xff\"\n====\nI == INSTANCE Inner\nTHEOREM I!S = \"a\" OBVIOUS\n====\n",
            Some("M.tla"),
        ),
        (
            b"---- MODULE Inner ----\n====\nS == \"\xff\"\nTHEOREM TRUE OBVIOUS\n====\n",
            Some("M.tla"),
        ),
        (
            b"THEOREM TRUE OBVIOUS (*{ by (isabelle \"a}*)(*\xff*)(*\") }*)\n====\n",
            Some("M.tla"),
        ),
        (b"x == 1 (*{ note *)\n(* \xff *)\n====\n", None),
        (b"x == 1 = (*{ \xff }*) 1\n====\n", None),
        (
            b"F == TRUE (*{ by (prover:\"\xff\") }*)\nTHEOREM 1 = 1 BY F\n====\n",
            Some("M.tla"),
        ),
        (b"S == \"\xff\"\n====\n", None),
        (b"THEOREM 1 = 1 OBVIOUS \\* \xff\n====\n", None),
    ];
    for (body, declined) in cases {
        let text = [b"---- MODULE M ----\nEXTENDS TLAPS\n", body].concat();
        let output = run_bytes(&text, &["-N", "--toolbox", "0", "0", "--printallobs"]);
        let case = String::from_utf8_lossy(&text).into_owned();
        match declined {
            Some(path) => assert_eq!(
                (output.status.code(), stderr(&output)),
                (Some(1), not_utf8(path)),
                "{case}"
            ),
            None => assert!(
                !stderr(&output).contains(NOT_NATIVE),
                "{case}: {}",
                stderr(&output)
            ),
        }
    }
    // The lexer fails on the byte, which tlapm fails on too.
    let output = run_bytes(b"---- MODULE M ----\nS == \xff\n====\n", &["-N"]);
    assert_eq!(
        stderr(&output),
        format!(
            "{NOT_NATIVE}the backtrace tlapm prints as it ends with Failure(\"Module.Parser.parse_file\")\n"
        )
    );
    let directory = write_bytes(&[
        (
            "Lib.tla",
            b"---- MODULE Lib ----\nTHEOREM \"\xff\" = \"\xfe\" OBVIOUS\n====\n",
        ),
        (
            "M.tla",
            b"---- MODULE M ----\nEXTENDS Lib, TLAPS\nTHEOREM TRUE OBVIOUS\n====\n",
        ),
    ]);
    let output = run_in(&directory, &["-N", "M.tla"]);
    assert_eq!(stderr(&output), not_utf8("./Lib.tla"));
}

// A module that holds a character a byte that isn't UTF-8 reads as would read alike with it.
#[test]
fn declines_a_module_that_holds_a_marker() {
    let output = run_bytes(
        "---- MODULE M ----\nS == \"\u{10ffff}\"\n====\n".as_bytes(),
        &["-N"],
    );
    assert_eq!(
        stderr(&output),
        format!("{NOT_NATIVE}U+10FFFF in M.tla, which Prove It reads a byte that isn't UTF-8 as\n")
    );
}

// tlapm sends Isabelle's stdout to a file, and Isabelle writes nothing to stderr for a proof it
// doesn't find, so the failure prints as any other.
#[test]
fn prints_a_proof_isabelle_doesnt_find_as_any_failure() {
    let module = "---- MODULE I ----\nEXTENDS Naturals, TLAPS\nCONSTANT x\nTHEOREM x = x + 0\n  BY Isa\n====\n";
    let output = run_in(
        &write_files(&[("I.tla", module)]),
        &["--threads", "1", "I.tla"],
    );
    assert_eq!(output.status.code(), Some(3));
    assert_eq!(
        stdout(&output),
        "(* created new \".tlacache/I.tlaps/I.thy\" *)\n(* fingerprints written in \".tlacache/I.tlaps/fingerprints\" *)\n"
    );
    assert!(stderr(&output).contains("[ERROR]: 1/2 obligations failed.\n"));
    let output = run_in(
        &write_files(&[("I.tla", module)]),
        &["--threads", "1", "--toolbox", "0", "0", "I.tla"],
    );
    assert!(
        stderr(&output).contains("@!!prover:isabelle\n@!!meth:auto; time-limit: 30; time-used: ")
    );
    assert!(stderr(&output).contains("@!!reason:false\n"));
}
