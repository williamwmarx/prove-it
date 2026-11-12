//! Where TLC's resolver finds a spec, its modules and their Java overrides, against what TLC at
//! d8fb231 printed for the same files and command line: the files SANY parses, the overrides TLC
//! loads, its errors and its exit code, with the case's root written `{root}`. The binary prints
//! the same, or declines what it doesn't.

mod common;

use std::path::Path;
use std::process::Command;

const SPEC: &str = "---- MODULE Spec ----\nEXTENDS Naturals, M\nVARIABLE x\nInit == x = CM\nNext == UNCHANGED x\nInv == x = 1\n====\n";
const MODULE: &str = "---- MODULE M ----\nCM == 1\n====\n";
const CONFIG: &str = "INIT Init\nNEXT Next\nINVARIANT Inv\n";

// M.class overrides CM with 5 (M.java), which violates Inv.
const VIOLATED: &str = "Error: Invariant Inv is violated by the initial state:";

enum Outcome {
    Printed(&'static [&'static str]),
    Declined,
}

struct Case {
    name: &'static str,
    // Each file the case holds by its path from the root: a spec, a module, a configuration,
    // M.class, a link to a path, or a directory.
    files: &'static [(&'static str, &'static str)],
    args: &'static [&'static str],
    outcome: Outcome,
}

const CASES: &[Case] = &[
    Case {
        name: "class-in-working-directory",
        files: &[
            ("sub/Spec.tla", SPEC),
            ("sub/Spec.cfg", CONFIG),
            ("sub/M.tla", MODULE),
            ("M.class", "class"),
        ],
        args: &["tlc2.TLC", "sub/Spec"],
        outcome: Outcome::Printed(&[
            "Parsing file {root}/sub/Spec.tla",
            "Parsing file {root}/sub/M.tla",
            "Loading CM operator override from file:{root}/M.class with signature: <Java Method: public static tlc2.value.impl.Value M.CM()>.",
            VIOLATED,
            "exit 12",
        ]),
    },
    Case {
        name: "class-on-library-path",
        files: &[
            ("Spec.tla", SPEC),
            ("Spec.cfg", CONFIG),
            ("lib/M.tla", MODULE),
            ("lib/M.class", "class"),
        ],
        args: &["-DTLA-Library=lib", "tlc2.TLC", "Spec"],
        outcome: Outcome::Printed(&[
            "Parsing file {root}/Spec.tla",
            "Parsing file {root}/lib/M.tla",
            "Loading CM operator override from file:{root}/lib/M.class with signature: <Java Method: public static tlc2.value.impl.Value M.CM()>.",
            VIOLATED,
            "exit 12",
        ]),
    },
    Case {
        name: "class-through-dot",
        files: &[
            ("sp/Spec.tla", SPEC),
            ("sp/Spec.cfg", CONFIG),
            ("lib/M.tla", MODULE),
            ("lib/M.class", "class"),
        ],
        args: &["-DTLA-Library=./lib", "tlc2.TLC", "{root}/sp/Spec.tla"],
        outcome: Outcome::Printed(&[
            "Parsing file {root}/sp/Spec.tla",
            "Parsing file {root}/lib/M.tla (file:{root}/./lib/M.tla)",
            "Loading CM operator override from file:{root}/lib/M.class with signature: <Java Method: public static tlc2.value.impl.Value M.CM()>.",
            VIOLATED,
            "exit 12",
        ]),
    },
    Case {
        name: "spec-on-library-path",
        files: &[
            ("lib/Spec.tla", SPEC),
            ("lib/Spec.cfg", CONFIG),
            ("ll", "->lib"),
        ],
        args: &["-DTLA-Library=ll", "tlc2.TLC", "Spec"],
        outcome: Outcome::Printed(&[
            "Parsing file {root}/lib/Spec.tla (file:{root}/ll/Spec.tla)",
            "Fatal errors while parsing TLA+ spec in file Spec",
            "Cannot find source file for module M imported in module Spec.",
            "Cannot find source file for module M imported in module Spec.",
            "Error: Parsing or semantic analysis failed.",
            "exit 150",
        ]),
    },
    Case {
        name: "spec-through-dot",
        files: &[
            ("lib/Spec.tla", SPEC),
            ("lib/Spec.cfg", CONFIG),
            ("lib/M.tla", MODULE),
        ],
        args: &["-DTLA-Library=lib/.", "tlc2.TLC", "Spec"],
        outcome: Outcome::Printed(&[
            "Parsing file {root}/lib/Spec.tla (file:{root}/lib/./Spec.tla)",
            "Parsing file {root}/lib/M.tla (file:{root}/lib/./M.tla)",
            "exit 0",
        ]),
    },
    Case {
        name: "last-library-path",
        files: &[
            ("Spec.tla", SPEC),
            ("Spec.cfg", CONFIG),
            ("a/M.tla", MODULE),
            ("b/M.tla", MODULE),
        ],
        args: &["-DTLA-Library=a", "-DTLA-Library=b", "tlc2.TLC", "Spec"],
        outcome: Outcome::Printed(&[
            "Parsing file {root}/Spec.tla",
            "Parsing file {root}/b/M.tla",
            "exit 0",
        ]),
    },
    // Java's String.split drops the empty paths at the end, so TLC looks for M beside the spec
    // alone, not in the working directory.
    Case {
        name: "empty-library-paths",
        files: &[
            ("sp/Spec.tla", SPEC),
            ("sp/Spec.cfg", CONFIG),
            ("M.tla", MODULE),
        ],
        args: &["-DTLA-Library=:", "tlc2.TLC", "{root}/sp/Spec.tla"],
        outcome: Outcome::Printed(&[
            "Parsing file {root}/sp/Spec.tla",
            "Fatal errors while parsing TLA+ spec in file Spec",
            "Cannot find source file for module M imported in module Spec.",
            "Cannot find source file for module M imported in module Spec.",
            "Error: Parsing or semantic analysis failed.",
            "exit 150",
        ]),
    },
    // TLC stops at the first M.class it finds, and loads no override from a directory.
    Case {
        name: "class-directory",
        files: &[
            ("Spec.tla", SPEC),
            ("Spec.cfg", CONFIG),
            ("l1/M.tla", MODULE),
            ("cd1/M.class", "/"),
            ("l2/M.class", "class"),
        ],
        args: &["-DTLA-Library=l1:cd1:l2", "tlc2.TLC", "Spec"],
        outcome: Outcome::Printed(&[
            "Parsing file {root}/Spec.tla",
            "Parsing file {root}/l1/M.tla",
            "exit 0",
        ]),
    },
    // The system follows the link before .., as Java does.
    Case {
        name: "link-then-parent",
        files: &[
            ("Spec.tla", SPEC),
            ("Spec.cfg", CONFIG),
            ("other/X/M.tla", MODULE),
            ("other/deep", "/"),
            ("dl", "->other/deep"),
        ],
        args: &["-DTLA-Library=dl/../X", "tlc2.TLC", "Spec"],
        outcome: Outcome::Printed(&[
            "Parsing file {root}/Spec.tla",
            "Parsing file {root}/other/X/M.tla (file:{root}/dl/../X/M.tla)",
            "exit 0",
        ]),
    },
    // TLC reads anything there but a directory, such as /dev/null.
    Case {
        name: "module-device",
        files: &[
            ("Spec.tla", SPEC),
            ("Spec.cfg", CONFIG),
            ("M.tla", "->/dev/null"),
        ],
        args: &["tlc2.TLC", "Spec"],
        outcome: Outcome::Printed(&[
            "Parsing file {root}/Spec.tla",
            "Parsing file /dev/null (file:{root}/M.tla)",
            "Fatal errors while parsing TLA+ spec in file Spec",
            "Error: Parsing or semantic analysis failed.",
            "exit 150",
        ]),
    },
    // A path the system can't follow, as a link to itself, isn't there.
    Case {
        name: "configuration-loop",
        files: &[
            ("Spec.tla", SPEC),
            ("M.tla", MODULE),
            ("Spec.cfg", "->Spec.cfg"),
        ],
        args: &["tlc2.TLC", "Spec"],
        outcome: Outcome::Printed(&[
            "Error: TLC encountered the following error when trying to read the configuration file Spec.cfg:",
            "exit 151",
        ]),
    },
    // MonolithSpecExtractor.getConfig: TLC reads a -config x as x.cfg.
    Case {
        name: "configuration-without-extension",
        files: &[("Spec.tla", SPEC), ("M.tla", MODULE), ("x.cfg", CONFIG)],
        args: &["tlc2.TLC", "-config", "x", "Spec"],
        outcome: Outcome::Printed(&[
            "Parsing file {root}/Spec.tla",
            "Parsing file {root}/M.tla",
            "exit 0",
        ]),
    },
    // TLC reads the configuration before the spec.
    Case {
        name: "spec-directory-without-configuration",
        files: &[("D.tla", "/")],
        args: &["tlc2.TLC", "D"],
        outcome: Outcome::Printed(&[
            "Error: TLC encountered the following error when trying to read the configuration file D.cfg:",
            "exit 151",
        ]),
    },
    // TLC prints `***Internal error: Unable to create FileInputStream` as it fails to read the
    // directory.
    Case {
        name: "configuration-directory",
        files: &[("Spec.tla", SPEC), ("M.tla", MODULE), ("C.cfg", "/")],
        args: &["tlc2.TLC", "-config", "C.cfg", "Spec"],
        outcome: Outcome::Declined,
    },
    // A -DTLA-Library without a value sets the library path to the empty one, so TLC doesn't
    // find the spec.
    Case {
        name: "library-path-without-value",
        files: &[
            ("Spec.cfg", CONFIG),
            ("L/Spec.tla", SPEC),
            ("L/M.tla", MODULE),
        ],
        args: &["-DTLA-Library=L", "-DTLA-Library", "tlc2.TLC", "Spec"],
        outcome: Outcome::Declined,
    },
    // TLC prints `***Internal error: Unable to create NamedInputStream in toIStream method` as it
    // fails to read the directory, which tla-front doesn't write.
    Case {
        name: "module-directory",
        files: &[("Spec.tla", SPEC), ("Spec.cfg", CONFIG), ("M.tla", "/")],
        args: &["tlc2.TLC", "Spec"],
        outcome: Outcome::Declined,
    },
    Case {
        name: "missing-spec-in-directory",
        files: &[("sub/Nope.cfg", CONFIG), ("lib", "/")],
        args: &["-DTLA-Library=lib", "tlc2.TLC", "sub/Nope"],
        outcome: Outcome::Declined,
    },
];

fn set_up(root: &Path, files: &[(&str, &str)]) {
    let class = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/resolver-order/M.class");
    for (path, contents) in files {
        let path = root.join(path);
        std::fs::create_dir_all(path.parent().expect("a parent")).expect("a directory");
        match *contents {
            "/" => std::fs::create_dir_all(&path).expect("a directory"),
            "class" => {
                std::fs::copy(&class, &path).expect("the class");
            }
            link if link.starts_with("->") => common::link(Path::new(&link[2..]), &path),
            text => std::fs::write(&path, text).expect("a file"),
        }
    }
}

// What TLC prints of where it finds the files, and how the run ends: its exit code last.
fn get_printed(text: &str, code: Option<i32>) -> Vec<String> {
    const PREFIXES: &[&str] = &[
        "Parsing file ",
        "Loading ",
        "Fatal errors",
        "Cannot find",
        "Error:",
    ];
    text.lines()
        .filter(|line| PREFIXES.iter().any(|prefix| line.starts_with(prefix)))
        .filter(|line| !line.contains("/tlc-") && !line.contains("\\tlc-"))
        .map(str::to_owned)
        .chain([format!("exit {}", code.unwrap_or(-1))])
        .collect()
}

#[test]
fn finds_specs_modules_and_overrides_as_tlc_does() {
    for case in CASES {
        // A link to /dev/null, which exists only on Unix.
        if !cfg!(unix) && case.name == "module-device" {
            continue;
        }
        let created = std::env::temp_dir().join(format!(
            "prove-it-resolver-order-{}-{}",
            case.name,
            std::process::id()
        ));
        std::fs::create_dir_all(&created).expect("a directory");
        let root = common::get_working_path(&created);
        set_up(&root, case.files);
        let root_text = root.to_string_lossy().into_owned();
        // TLC writes no trace exploration spec with -noGenerateSpecTE.
        let args = case.args.iter().flat_map(|arg| {
            let arg = arg.replace("{root}", &root_text);
            let is_class = arg == "tlc2.TLC";
            std::iter::once(arg).chain(is_class.then(|| "-noGenerateSpecTE".to_owned()))
        });
        let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
            .args(args)
            .current_dir(&root)
            .output()
            .expect("the binary runs");
        let text = format!(
            "{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        match case.outcome {
            Outcome::Declined => {
                assert!(
                    text.contains("prove-it: not native yet:"),
                    "{}: {text}",
                    case.name
                );
            }
            Outcome::Printed(lines) => {
                let mut expected: Vec<String> = lines
                    .iter()
                    .map(|line| line.replace("{root}", &root_text))
                    .collect();
                if cfg!(windows) {
                    match common::get_windows_expectation(&expected) {
                        common::OnWindows::Declined(reason) => {
                            common::assert_declined(&output, reason, case.name);
                            std::fs::remove_dir_all(&root).expect("removed");
                            continue;
                        }
                        common::OnWindows::Printed(lines) => expected = lines,
                    }
                }
                assert_eq!(
                    get_printed(&text, output.status.code()),
                    expected,
                    "{}: {text}",
                    case.name
                );
            }
        }
        std::fs::remove_dir_all(&root).expect("removed");
    }
}
