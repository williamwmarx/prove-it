//! Each way a spec can be named or found, in TLC's default mode, for a check that passes and for
//! one that writes the trace exploration spec (an Assert that fails in an action), against what
//! TLC at d8fb231 did with the same command line: its exit code, the path it printed and where it
//! wrote the spec. TLC names the spec's directory by the path it was given, so a spec found on the
//! library path has its trace exploration spec written in the working directory.

use std::path::Path;
use std::process::Command;

const NOW_MILLISECONDS: &str = "1794371200000";
const NOW_SECONDS: &str = "1794371200";

const PASSING: &str = "---- MODULE M ----\nVARIABLE x\nInit == x = 0\nNext == UNCHANGED x\n====\n";
const FAILING: &str = "---- MODULE M ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == x' = x + 1 /\\ Assert(x < 1, \"x is one\")\n====\n";
const CONFIG: &str = "INIT Init\nNEXT Next\n";

enum Outcome {
    // TLC's exit code, and for the failing check the path it printed and where it wrote the spec,
    // relative to the root.
    Checked(i32, Option<(&'static str, &'static str)>),
    Declined,
}

struct Case {
    name: &'static str,
    directory: &'static str,
    args: &'static [&'static str],
    passing: Outcome,
    failing: Outcome,
}

const fn written(path: &'static str, file: &'static str) -> Outcome {
    Outcome::Checked(14, Some((path, file)))
}

const CASES: &[Case] = &[
    Case {
        name: "bare",
        directory: "specs",
        args: &["M"],
        passing: Outcome::Checked(0, None),
        failing: written("./M", "specs/M"),
    },
    Case {
        name: "extension",
        directory: "specs",
        args: &["M.tla"],
        passing: Outcome::Checked(0, None),
        failing: written("./M", "specs/M"),
    },
    Case {
        name: "relative",
        directory: ".",
        args: &["specs/M"],
        passing: Outcome::Checked(0, None),
        failing: written("specs/M", "specs/M"),
    },
    Case {
        name: "relative-extension",
        directory: ".",
        args: &["specs/M.tla"],
        passing: Outcome::Checked(0, None),
        failing: written("specs/M", "specs/M"),
    },
    Case {
        name: "dot",
        directory: ".",
        args: &["./specs/M"],
        passing: Outcome::Checked(0, None),
        failing: written("./specs/M", "specs/M"),
    },
    Case {
        name: "parent",
        directory: "other",
        args: &["../specs/M"],
        passing: Outcome::Checked(0, None),
        failing: written("../specs/M", "specs/M"),
    },
    Case {
        name: "absolute",
        directory: ".",
        args: &["{root}/specs/M"],
        passing: Outcome::Checked(0, None),
        failing: written("{root}/specs/M", "specs/M"),
    },
    Case {
        name: "absolute-extension",
        directory: ".",
        args: &["{root}/specs/M.tla"],
        passing: Outcome::Checked(0, None),
        failing: written("{root}/specs/M", "specs/M"),
    },
    Case {
        name: "symlink",
        directory: ".",
        args: &["link/M"],
        passing: Outcome::Checked(0, None),
        failing: written("link/M", "specs/M"),
    },
    Case {
        name: "library",
        directory: "other",
        args: &["-DTLA-Library={root}/specs", "M"],
        passing: Outcome::Checked(0, None),
        failing: written("./M", "other/M"),
    },
    Case {
        name: "library-config",
        directory: "other",
        args: &[
            "-DTLA-Library={root}/specs",
            "-config",
            "{root}/specs/M.cfg",
            "M",
        ],
        passing: Outcome::Checked(0, None),
        failing: written("./M", "other/M"),
    },
    Case {
        name: "config-elsewhere",
        directory: ".",
        args: &["-config", "conf/M.cfg", "specs/M"],
        passing: Outcome::Checked(0, None),
        failing: written("specs/M", "specs/M"),
    },
    Case {
        name: "directory",
        directory: ".",
        args: &["specs"],
        passing: Outcome::Checked(151, None),
        failing: Outcome::Checked(151, None),
    },
    Case {
        name: "trailing-slash",
        directory: ".",
        args: &["specs/M/"],
        passing: Outcome::Checked(151, None),
        failing: Outcome::Checked(151, None),
    },
    // The binary declines the option, which TLC writes the spec into.
    Case {
        name: "spec-directory",
        directory: ".",
        args: &["-teSpecOutDir", "out", "specs/M"],
        passing: Outcome::Declined,
        failing: Outcome::Declined,
    },
    // TLC writes specs/M_TTrace_<epoch>.tla, as Java's Path drops the empty name; the binary
    // declines to write beside a path it doesn't normalize.
    Case {
        name: "double-slash",
        directory: ".",
        args: &["specs//M"],
        passing: Outcome::Checked(0, None),
        failing: Outcome::Declined,
    },
];

fn set_up(root: &Path, body: &str) {
    for directory in ["specs", "other", "conf"] {
        std::fs::create_dir_all(root.join(directory)).expect("a directory");
    }
    std::fs::write(root.join("specs/M.tla"), body).expect("the spec");
    std::fs::write(root.join("specs/M.cfg"), CONFIG).expect("the configuration");
    std::fs::write(root.join("conf/M.cfg"), CONFIG).expect("the configuration");
    std::os::unix::fs::symlink(root.join("specs"), root.join("link")).expect("the link");
}

fn get_trace_files(root: &Path) -> Vec<String> {
    let mut found = Vec::new();
    for directory in ["specs", "other", "conf", "."] {
        for entry in std::fs::read_dir(root.join(directory)).expect("a directory") {
            let name = entry.expect("an entry").file_name();
            let name = name.to_string_lossy();
            if name.contains("_TTrace_") {
                found.push(format!("{directory}/{name}"));
            }
        }
    }
    found
}

// The case's arguments at the root, as TLC's command line: Java's properties come before the
// class, as `java -D… tlc2.TLC` takes them.
fn get_command_line(args: &[&str], root: &str) -> Vec<String> {
    let args: Vec<String> = args.iter().map(|arg| arg.replace("{root}", root)).collect();
    let (properties, rest): (Vec<String>, Vec<String>) =
        args.into_iter().partition(|arg| arg.starts_with("-D"));
    let class = (!properties.is_empty()).then(|| "tlc2.TLC".to_string());
    properties
        .into_iter()
        .chain(class)
        .chain(["-workers".to_string(), "1".to_string()])
        .chain(rest)
        .collect()
}

#[test]
fn names_the_trace_exploration_spec_as_tlc_however_the_spec_is_named() {
    for case in CASES {
        for (is_failing, body, outcome) in [
            (false, PASSING, &case.passing),
            (true, FAILING, &case.failing),
        ] {
            let label = format!(
                "{} {}",
                case.name,
                if is_failing { "failing" } else { "passing" }
            );
            let root = std::env::temp_dir().join(format!(
                "prove-it-spec-paths-{}-{is_failing}-{}",
                case.name,
                std::process::id()
            ));
            set_up(&root, body);
            let root_text = root.to_string_lossy().into_owned();
            let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
                .args(get_command_line(case.args, &root_text))
                .env("PROVE_IT_TEST_NOW", NOW_MILLISECONDS)
                .env_remove("TZ")
                .current_dir(root.join(case.directory))
                .output()
                .expect("the binary runs");
            let text = format!(
                "{}{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
            match outcome {
                Outcome::Declined => {
                    assert!(
                        text.contains("prove-it: not native yet:"),
                        "{label}: {text}"
                    );
                }
                Outcome::Checked(exit, spec) => {
                    assert_eq!(output.status.code(), Some(*exit), "{label}: {text}");
                    assert!(!text.contains("not native yet"), "{label}: {text}");
                    let files = get_trace_files(&root);
                    match spec {
                        Some((path, file)) => {
                            let path = path.replace("{root}", &root_text);
                            assert!(
                                text.ends_with(&format!(
                                    "Trace exploration spec path: {path}_TTrace_{NOW_SECONDS}.tla\n"
                                )),
                                "{label}: {text}"
                            );
                            assert_eq!(
                                files,
                                [format!("{file}_TTrace_{NOW_SECONDS}.tla")],
                                "{label}"
                            );
                        }
                        None => {
                            assert!(!text.contains("Trace exploration spec path"), "{label}");
                            assert!(files.is_empty(), "{label}: {files:?}");
                        }
                    }
                }
            }
            std::fs::remove_dir_all(&root).expect("removed");
        }
    }
}

#[test]
fn checks_each_spec_given_once_however_often_it_is_named() {
    // The binary checks several specs in turn; a spec named twice is checked once, and each keeps
    // the path it was given, so N, given after M twice, checks as it does alone.
    let root =
        std::env::temp_dir().join(format!("prove-it-spec-paths-twice-{}", std::process::id()));
    std::fs::create_dir_all(&root).expect("a directory");
    for module in ["M", "N"] {
        std::fs::write(
            root.join(format!("{module}.tla")),
            PASSING.replace("MODULE M", &format!("MODULE {module}")),
        )
        .expect("the spec");
        std::fs::write(root.join(format!("{module}.cfg")), CONFIG).expect("the configuration");
    }
    let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .args(["-workers", "1", "M", "M", "N"])
        .current_dir(&root)
        .output()
        .expect("the binary runs");
    let text = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(output.status.code(), Some(0), "{text}");
    assert!(!text.contains("not native yet"), "{text}");
    assert_eq!(
        text.matches("Checking M.tla with M.cfg").count(),
        1,
        "{text}"
    );
    assert!(text.contains("Checking N.tla with N.cfg"), "{text}");
    assert_eq!(
        text.matches("Model checking completed. No error has been found.")
            .count(),
        2,
        "{text}"
    );
    std::fs::remove_dir_all(&root).expect("removed");
}
