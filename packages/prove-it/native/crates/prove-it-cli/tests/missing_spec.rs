//! A spec no file holds, as TLC at d8fb231 reports it: SANY's resolver says on standard error
//! where it looked, and SANY reports the root module it can't find as a fatal error.

use std::path::Path;
use std::process::Command;

const CONFIG: &str = "INIT Init\nNEXT Next\n";

struct Case {
    name: &'static str,
    args: &'static [&'static str],
    /// The module SANY names, then where its resolver looked, relative to the root.
    module: &'static str,
    looked: &'static str,
}

const CASES: &[Case] = &[
    Case {
        name: "directory",
        args: &["-DTLA-Library=lib", "tlc2.TLC", "sub/Nope"],
        module: "sub/Nope",
        looked: "{root}/./sub/Nope.tla while looking in these directories: {root}, sub",
    },
    Case {
        name: "extension",
        args: &["tlc2.TLC", "sub/Nope.tla"],
        module: "sub/Nope",
        looked: "{root}/./sub/Nope.tla while looking in these directories: {root}, sub",
    },
    Case {
        name: "doubled-directory",
        args: &["tlc2.TLC", ".//Nope"],
        module: ".//Nope",
        looked: "{root}/././Nope.tla while looking in these directories: {root}, .",
    },
    Case {
        name: "library-path-without-value",
        args: &["-DTLA-Library=lib", "-DTLA-Library", "tlc2.TLC", "Nope"],
        module: "Nope",
        looked: "{root}/./Nope.tla while looking in these directories: {root}, ",
    },
    Case {
        name: "library-path",
        args: &["-DTLA-Library=lib:sub", "tlc2.TLC", "Nope"],
        module: "Nope",
        looked: "{root}/./Nope.tla while looking in these directories: {root}, lib, sub",
    },
    Case {
        name: "absolute",
        args: &["tlc2.TLC", "{root}/sub/Nope"],
        module: "Nope",
        looked: "{root}/sub/Nope.tla while looking in these directories: {root}/sub, ",
    },
    // TLC names the directories as Java's Path does, without repeated or trailing separators.
    Case {
        name: "absolute-doubled",
        args: &["tlc2.TLC", "{root}//sub//Nope"],
        module: "Nope",
        looked: "{root}/sub/Nope.tla while looking in these directories: {root}/sub, ",
    },
    Case {
        name: "library-path-separators",
        args: &["-DTLA-Library=lib/:sub//", "tlc2.TLC", "Nope"],
        module: "Nope",
        looked: "{root}/./Nope.tla while looking in these directories: {root}, lib, sub",
    },
];

fn run(root: &Path, args: &[&str]) -> (String, String, Option<i32>) {
    let root_text = root.display().to_string();
    let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .args(args.iter().map(|arg| arg.replace("{root}", &root_text)))
        .current_dir(root)
        .output()
        .expect("the binary runs");
    let normalize = |bytes: &[u8]| {
        String::from_utf8_lossy(bytes)
            .replace(&root_text, "{root}")
            .lines()
            .filter(|line| !line.starts_with("TLC2 Version") && !line.starts_with("Running "))
            .map(|line| match line.find(" (") {
                Some(end) if line.starts_with("Starting...") => &line[..end],
                _ if line.starts_with("Finished in") => "Finished in",
                _ => line,
            })
            .collect::<Vec<_>>()
            .join("\n")
    };
    (
        normalize(&output.stdout),
        normalize(&output.stderr),
        output.status.code(),
    )
}

fn set_up(name: &str) -> std::path::PathBuf {
    let root = std::env::temp_dir().join(format!(
        "prove-it-missing-spec-{name}-{}",
        std::process::id()
    ));
    for directory in ["sub", "lib"] {
        std::fs::create_dir_all(root.join(directory)).expect("a directory");
    }
    std::fs::write(root.join("Nope.cfg"), CONFIG).expect("the configuration");
    std::fs::write(root.join("sub/Nope.cfg"), CONFIG).expect("the configuration");
    root
}

#[test]
fn reports_a_spec_no_file_holds_as_tlc() {
    for case in CASES {
        let root = set_up(case.name);
        let module = case.module;
        let fatal = format!("Unknown location\n\nCannot find source file for module {module}");
        assert_eq!(
            run(&root, case.args),
            (
                format!(
                    "\nFatal errors while parsing TLA+ spec in file {module}\n\n{fatal}\n*** Errors: 1\n\n{fatal}\n\n\n\nStarting...\nError: Parsing or semantic analysis failed.\nFinished in"
                ),
                format!(
                    "File does not exist: {}, classpath:/tla2sany/StandardModules, classpath:/",
                    case.looked
                ),
                Some(150)
            ),
            "{}",
            case.name
        );
        std::fs::remove_dir_all(&root).expect("the root is removed");
    }
}

#[test]
fn reports_a_spec_no_file_holds_as_tlc_with_tool() {
    let root = set_up("tool");
    let (stdout, stderr, code) = run(&root, &["tlc2.TLC", "-tool", "sub/Nope"]);
    let fatal = "Unknown location\n\nCannot find source file for module sub/Nope";
    assert!(
        stdout.contains(&format!(
            "@!@!@STARTMSG 2220:0 @!@!@\nStarting SANY...\n@!@!@ENDMSG 2220 @!@!@\n\nFatal errors while parsing TLA+ spec in file sub/Nope\n\n{fatal}\n*** Errors: 1\n\n{fatal}\n\n\n\n@!@!@STARTMSG 2219:0 @!@!@\nSANY finished.\n@!@!@ENDMSG 2219 @!@!@\n@!@!@STARTMSG 2185:0 @!@!@\nStarting...\n@!@!@ENDMSG 2185 @!@!@\n@!@!@STARTMSG 3002:1 @!@!@\nParsing or semantic analysis failed.\n@!@!@ENDMSG 3002 @!@!@"
        )),
        "{stdout}"
    );
    assert!(stderr.starts_with("File does not exist: {root}/./sub/Nope.tla"));
    assert_eq!(code, Some(150));
    std::fs::remove_dir_all(&root).expect("the root is removed");
}

// Where TLC may still find the spec, names the files it looked for in a way the binary doesn't, or
// stops before it parses the spec as it makes its meta directory, the binary declines.
#[test]
fn declines_a_spec_no_file_holds_where_tlc_may_not_report_it() {
    for (name, file, args) in [
        (
            "in-jar",
            "pcal/PlusCal.cfg",
            &["tlc2.TLC", "pcal/PlusCal"][..],
        ),
        (
            "in-jar-standard",
            "_CBORTrace.cfg",
            &["tlc2.TLC", "_CBORTrace"],
        ),
        (
            "in-library",
            "lib/Nope.tla",
            &["-DTLA-Library=lib", "tlc2.TLC", "{root}/Nope"],
        ),
        (
            "on-class-path",
            "lib/Nope.tla",
            &["-cp", "tla2tools.jar:lib", "tlc2.TLC", "Nope"],
        ),
        (
            "user-directory",
            "sub/Nope.cfg",
            &["-Duser.dir={root}/sub", "tlc2.TLC", "Nope"],
        ),
        ("extension-case", "Nope.TLA.cfg", &["tlc2.TLC", "Nope.TLA"]),
        (
            "library-encoding",
            "Nope.cfg",
            &["-DTLA-Library=\u{fc}", "tlc2.TLC", "Nope"],
        ),
        (
            "metadir",
            "Nope.cfg",
            &["tlc2.TLC", "-metadir", "m", "Nope"],
        ),
        ("metadir-file", "states", &["tlc2.TLC", "Nope"]),
        ("metadir-relative", "states", &["tlc2.TLC", "sub/Nope"]),
        (
            "in-own-directory",
            "sub/sub/Nope.tla",
            &["tlc2.TLC", "sub/Nope"],
        ),
        (
            "path-separator",
            "Nope.cfg",
            &[
                "-Dpath.separator=;",
                "-DTLA-Library=lib;sub",
                "tlc2.TLC",
                "Nope",
            ],
        ),
    ] {
        let root = set_up(name);
        let path = root.join(file);
        std::fs::create_dir_all(path.parent().expect("a parent")).expect("a directory");
        std::fs::write(&path, CONFIG).expect("the file");
        let (_, stderr, code) = run(&root, args);
        assert!(
            stderr.contains("prove-it: not native yet: ")
                && stderr.contains("a spec no file holds"),
            "{name}: {stderr}"
        );
        assert_eq!(code, Some(1), "{name}");
        std::fs::remove_dir_all(&root).expect("the root is removed");
    }
}

// TLC makes the meta directory of a relative spec in the working directory, so a file named states
// beside the spec doesn't stop it.
#[test]
fn reports_a_relative_spec_no_file_holds_beside_a_states_file() {
    let root = set_up("states-beside");
    std::fs::write(root.join("sub/states"), CONFIG).expect("the file");
    let (stdout, _, code) = run(&root, &["tlc2.TLC", "sub/Nope"]);
    assert!(
        stdout.contains("Cannot find source file for module sub/Nope"),
        "{stdout}"
    );
    assert_eq!(code, Some(150));
    std::fs::remove_dir_all(&root).expect("the root is removed");
}
