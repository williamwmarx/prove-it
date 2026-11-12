//! Each way a spec can be named or found, in TLC's default mode, for a check that passes and for
//! one that writes the trace exploration spec (an Assert that fails in an action), against what
//! TLC at d8fb231 did with the same command line: its exit code, the path it printed and where it
//! wrote the spec. TLC names the spec's directory by the path it was given, so a spec found on the
//! library path has its trace exploration spec written in the working directory.

mod common;

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
    common::link(&root.join("specs"), &root.join("link"));
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
            if cfg!(windows) && !matches!(outcome, Outcome::Declined) {
                // A spec named through `.`, `..` or a link is found by a path that isn't its real
                // one; any other spec TLC writes a trace exploration spec of prints its path.
                let reason = if ["dot", "parent", "symlink"].contains(&case.name) {
                    Some(common::DECLINED_FILE_URL)
                } else if let Outcome::Checked(_, Some(_)) = outcome {
                    Some(common::DECLINED_TRACE_SPEC)
                } else {
                    None
                };
                if let Some(reason) = reason {
                    common::assert_declined(&output, reason, &label);
                    std::fs::remove_dir_all(&root).expect("removed");
                    continue;
                }
            }
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

// A spec that extends a module beside it and, where it says, one on the library path.
fn set_up_extending(root: &Path, is_library_used: bool, is_shadowed: bool) {
    for directory in ["specs", "other", "conf", "lib"] {
        std::fs::create_dir_all(root.join(directory)).expect("a directory");
    }
    let extended = if is_library_used { "N, Lib" } else { "N" };
    std::fs::write(
        root.join("specs/M.tla"),
        format!("---- MODULE M ----\nEXTENDS Naturals, TLC, {extended}\nVARIABLE x\nInit == x = K\nNext == UNCHANGED x\n====\n"),
    )
    .expect("the spec");
    std::fs::write(root.join("specs/M.cfg"), CONFIG).expect("the configuration");
    std::fs::write(root.join("conf/M.cfg"), CONFIG).expect("the configuration");
    std::fs::write(
        root.join("specs/N.tla"),
        "---- MODULE N ----\nK == 0\n====\n",
    )
    .expect("N");
    std::fs::write(
        root.join("lib/Lib.tla"),
        "---- MODULE Lib ----\nJ == 1\n====\n",
    )
    .expect("Lib");
    if is_shadowed {
        std::fs::write(root.join("N.tla"), "---- MODULE N ----\nK == 5\n====\n").expect("N");
    }
    common::link(&root.join("specs"), &root.join("link"));
}

struct Resolution {
    name: &'static str,
    directory: &'static str,
    args: &'static [&'static str],
    is_library_used: bool,
    is_shadowed: bool,
    exit: i32,
    // The files of the spec's own modules, as TLC printed them.
    parsed: &'static [&'static str],
}

const RESOLUTIONS: &[Resolution] = &[
    Resolution {
        name: "relative",
        directory: ".",
        args: &["specs/M"],
        is_library_used: false,
        is_shadowed: false,
        exit: 0,
        parsed: &["{root}/specs/M.tla", "{root}/specs/N.tla"],
    },
    Resolution {
        name: "dot",
        directory: ".",
        args: &["./specs/M"],
        is_library_used: false,
        is_shadowed: false,
        exit: 0,
        parsed: &[
            "{root}/specs/M.tla (file:{root}/./specs/M.tla)",
            "{root}/specs/N.tla (file:{root}/./specs/N.tla)",
        ],
    },
    Resolution {
        name: "parent",
        directory: "other",
        args: &["../specs/M"],
        is_library_used: false,
        is_shadowed: false,
        exit: 0,
        parsed: &[
            "{root}/specs/M.tla (file:{root}/other/../specs/M.tla)",
            "{root}/specs/N.tla (file:{root}/other/../specs/N.tla)",
        ],
    },
    Resolution {
        name: "parent-inside",
        directory: ".",
        args: &["specs/../specs/M"],
        is_library_used: false,
        is_shadowed: false,
        exit: 0,
        parsed: &[
            "{root}/specs/M.tla (file:{root}/specs/../specs/M.tla)",
            "{root}/specs/N.tla (file:{root}/specs/../specs/N.tla)",
        ],
    },
    Resolution {
        name: "absolute-parent",
        directory: ".",
        args: &["{root}/other/../specs/M"],
        is_library_used: false,
        is_shadowed: false,
        exit: 0,
        parsed: &[
            "{root}/specs/M.tla (file:{root}/other/../specs/M.tla)",
            "{root}/specs/N.tla (file:{root}/other/../specs/N.tla)",
        ],
    },
    Resolution {
        name: "symlink",
        directory: ".",
        args: &["link/M"],
        is_library_used: false,
        is_shadowed: false,
        exit: 0,
        parsed: &[
            "{root}/specs/M.tla (file:{root}/link/M.tla)",
            "{root}/specs/N.tla (file:{root}/link/N.tla)",
        ],
    },
    Resolution {
        name: "symlink-absolute",
        directory: ".",
        args: &["{root}/link/M"],
        is_library_used: false,
        is_shadowed: false,
        exit: 0,
        parsed: &[
            "{root}/specs/M.tla (file:{root}/link/M.tla)",
            "{root}/specs/N.tla (file:{root}/link/N.tla)",
        ],
    },
    Resolution {
        name: "library",
        directory: "specs",
        args: &["-DTLA-Library={root}/lib", "M"],
        is_library_used: true,
        is_shadowed: false,
        exit: 0,
        parsed: &[
            "{root}/specs/M.tla",
            "{root}/specs/N.tla",
            "{root}/lib/Lib.tla",
        ],
    },
    Resolution {
        name: "library-relative",
        directory: "specs",
        args: &["-DTLA-Library=../lib", "M"],
        is_library_used: true,
        is_shadowed: false,
        exit: 0,
        parsed: &[
            "{root}/specs/M.tla",
            "{root}/specs/N.tla",
            "{root}/lib/Lib.tla (file:{root}/specs/../lib/Lib.tla)",
        ],
    },
    // TLC's resolver for a spec named with a directory searches only that directory, after the
    // working one, so it doesn't find Lib.
    Resolution {
        name: "library-spec-directory",
        directory: ".",
        args: &["-DTLA-Library={root}/lib", "specs/M"],
        is_library_used: true,
        is_shadowed: false,
        exit: 150,
        parsed: &["{root}/specs/M.tla", "{root}/specs/N.tla"],
    },
    Resolution {
        name: "library-absolute",
        directory: ".",
        args: &["-DTLA-Library={root}/lib", "{root}/specs/M"],
        is_library_used: true,
        is_shadowed: false,
        exit: 0,
        parsed: &[
            "{root}/specs/M.tla",
            "{root}/specs/N.tla",
            "{root}/lib/Lib.tla",
        ],
    },
    // The working directory comes before the spec's.
    Resolution {
        name: "shadowed",
        directory: ".",
        args: &["specs/M"],
        is_library_used: false,
        is_shadowed: true,
        exit: 0,
        parsed: &["{root}/specs/M.tla", "{root}/N.tla"],
    },
];

#[test]
fn finds_and_names_the_modules_as_tlc_however_the_spec_is_named() {
    for resolution in RESOLUTIONS {
        let created = std::env::temp_dir().join(format!(
            "prove-it-spec-resolution-{}-{}",
            resolution.name,
            std::process::id()
        ));
        std::fs::create_dir_all(&created).expect("a directory");
        let root = common::get_working_path(&created);
        set_up_extending(&root, resolution.is_library_used, resolution.is_shadowed);
        let root_text = root.to_string_lossy().into_owned();
        let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
            .args(get_command_line(resolution.args, &root_text))
            .arg("-noTE")
            .current_dir(root.join(resolution.directory))
            .output()
            .expect("the binary runs");
        let text = String::from_utf8_lossy(&output.stdout);
        let mut expected: Vec<String> = resolution
            .parsed
            .iter()
            .map(|file| file.replace("{root}", &root_text))
            .collect();
        if cfg!(windows) {
            let lines: Vec<String> = expected
                .iter()
                .map(|file| format!("Parsing file {file}"))
                .collect();
            match common::get_windows_expectation(&lines) {
                common::OnWindows::Declined(reason) => {
                    common::assert_declined(&output, reason, resolution.name);
                    std::fs::remove_dir_all(&root).expect("removed");
                    continue;
                }
                common::OnWindows::Printed(lines) => {
                    expected = lines
                        .iter()
                        .map(|line| line.trim_start_matches("Parsing file ").to_owned())
                        .collect();
                }
            }
        }
        assert_eq!(
            output.status.code(),
            Some(resolution.exit),
            "{}: {text}",
            resolution.name
        );
        let parsed: Vec<&str> = text
            .lines()
            .filter_map(|line| line.strip_prefix("Parsing file "))
            .filter(|file| !file.contains("/tlc-") && !file.contains("\\tlc-"))
            .collect();
        assert_eq!(parsed, expected, "{}", resolution.name);
        std::fs::remove_dir_all(&root).expect("removed");
    }
}
