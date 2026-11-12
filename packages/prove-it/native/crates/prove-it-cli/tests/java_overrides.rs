//! The binary's Java overrides of an operator a module declares RECURSIVE and defines LOCAL, which
//! SANY doesn't hide (`Generator.processRecursive`), so TLC loads the method of a class beside the
//! spec in its place, as Hanoi's Bits.class overrides And in tlaplus/Examples.

mod common;

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

// Copies the fixture `tests/java-overrides/<fixture>` to a directory of its own and checks M there
// as TLC's command line does.
fn run_fixture(fixture: &str) -> (Output, PathBuf) {
    let source = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/java-overrides")
        .join(fixture);
    let directory = std::env::temp_dir().join(format!(
        "prove-it-java-overrides-{fixture}-{}",
        std::process::id()
    ));
    std::fs::create_dir_all(&directory).expect("a directory");
    for name in ["M.tla", "M.cfg", "Ext.tla", "Ext.class"] {
        std::fs::copy(source.join(name), directory.join(name)).expect("a fixture file");
    }
    let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .args([
            "-workers",
            "1",
            "-nowarning",
            "-noGenerateSpecTE",
            "-config",
            "M.cfg",
            "M.tla",
        ])
        .current_dir(&directory)
        .output()
        .expect("the binary runs");
    (output, directory)
}

// What TLC built at d8fb231 prints but its version, the machine, times and the standard modules'
// paths, with the fixture's directory in place of `{directory}`.
fn get_untimed_lines(text: &str, directory: &str) -> String {
    text.lines()
        .filter(|line| {
            ![
                "TLC2 Version",
                "Running breadth-first",
                "Starting...",
                "Finished in",
            ]
            .iter()
            .any(|timed| line.starts_with(timed))
                && !line
                    .strip_prefix("Parsing file ")
                    .is_some_and(|path| !path.starts_with(directory))
        })
        .map(|line| format!("{}\n", line.replace(directory, "{directory}")))
        .collect()
}

#[test]
fn loads_the_override_of_a_recursive_local_operator_as_tlc() {
    let (output, directory) = run_fixture("recursive");
    let working = common::get_working_path(&directory);
    let path = working.to_str().expect("a path");
    let text = String::from_utf8_lossy(&output.stdout);
    if cfg!(windows) {
        common::assert_declined(&output, common::DECLINED_CLASS_URL, "recursive");
        std::fs::remove_dir_all(directory).expect("removed");
        return;
    }
    assert_eq!(output.status.code(), Some(12), "{text}");
    assert_eq!(
        get_untimed_lines(&text, path),
        concat!(
            "Parsing file {directory}/M.tla\n",
            "Parsing file {directory}/Ext.tla\n",
            "Semantic processing of module Ext\n",
            "Semantic processing of module Naturals\n",
            "Semantic processing of module M\n",
            "Linting of module Ext\n",
            "Linting of module M\n",
            "Loading Op operator override from file:{directory}/Ext.class with signature: <Java Method: public static tlc2.value.impl.Value Ext.Op()>.\n",
            "Computing initial states...\n",
            "Error: Invariant Inv is violated by the initial state:\n",
            "v = 101\n",
            "\n",
        )
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

// TLC runs the method of a recursive local operator with parameters, as it runs Bits.And, which
// the binary can't.
#[test]
fn declines_the_override_of_a_recursive_local_operator_with_parameters() {
    let (output, directory) = run_fixture("parameters");
    assert_eq!(output.status.code(), Some(1));
    assert_eq!(
        String::from_utf8_lossy(&output.stderr),
        "prove-it: not native yet: a Java override with parameters, whose arguments TLC evaluates\n"
    );
    std::fs::remove_dir_all(directory).expect("removed");
}

// TLC names the class by the URL its loader read it from (`TLAClass.loadClass`): the path its
// resolver joined, made absolute against `user.dir`. That is `getcwd`, which resolves symbolic
// links, so a spec reached through a link from the working directory has its class named by the
// link, and one whose working directory is the link has it named by the real directory, as
// macOS's temporary directory, under the link `/var`, is named under `/private/var`.
#[test]
fn names_the_class_by_the_path_tlc_reaches_it_through_a_link() {
    let source = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/java-overrides/recursive");
    let created = std::env::temp_dir().join(format!(
        "prove-it-java-overrides-link-{}",
        std::process::id()
    ));
    std::fs::create_dir_all(created.join("real")).expect("a directory");
    let root = common::get_working_path(&created);
    for name in ["M.tla", "M.cfg", "Ext.tla", "Ext.class"] {
        std::fs::copy(source.join(name), root.join("real").join(name)).expect("a fixture file");
    }
    common::link(Path::new("real"), &root.join("link"));
    let root_text = root.to_str().expect("a path");
    let absolute = format!("{root_text}/link/M.tla");
    for (working, spec, class) in [
        ("link", "M.tla", "{root}/real/Ext.class"),
        (".", "link/M.tla", "{root}/link/Ext.class"),
        (".", absolute.as_str(), "{root}/link/Ext.class"),
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
            .args(["-workers", "1", "-nowarning", "-noGenerateSpecTE", spec])
            .current_dir(root.join(working))
            .output()
            .expect("the binary runs");
        // Windows names a working directory reached through a link by the link, so each spec is
        // found by a path that isn't its real one, whose URL no run of TLC on Windows recorded.
        if cfg!(windows) {
            common::assert_declined(&output, common::DECLINED_FILE_URL, spec);
            continue;
        }
        let text = String::from_utf8_lossy(&output.stdout);
        assert_eq!(
            output.status.code(),
            Some(12),
            "{spec} from {working}: {text}"
        );
        let loading: Vec<&str> = text
            .lines()
            .filter(|line| line.starts_with("Loading "))
            .collect();
        assert_eq!(
            loading,
            [format!(
                "Loading Op operator override from file:{} with signature: <Java Method: public static tlc2.value.impl.Value Ext.Op()>.",
                class.replace("{root}", root_text)
            )],
            "{spec} from {working}"
        );
    }
    std::fs::remove_dir_all(root).expect("removed");
}
