//! Runs the binary on TLC's Java launch with a tla2tools.jar on the class path, which picks the TLC
//! it reproduces and names the standard modules TLC copies from it.

mod common;

use std::path::PathBuf;
use std::process::{Command, Output};

fn run(directory: &PathBuf, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .args(args)
        .current_dir(directory)
        .output()
        .expect("the binary runs")
}

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

#[test]
fn checks_with_the_tla2tools_jar_on_the_class_path() {
    let directory = std::env::temp_dir().join(format!("prove-it-cli-jar-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    for (file, contents) in [
        (
            "Spec.tla",
            &b"---- MODULE Spec ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x < 2 /\\ x' = x + 1\n====\n"[..],
        ),
        ("Spec.cfg", b"INIT Init\nNEXT Next\n"),
        (
            "tla2tools.jar",
            include_bytes!("../../prove-it-check/fixtures/tla2tools.jar"),
        ),
        (
            "tla2tools-1.7.4.jar",
            include_bytes!("../../prove-it-check/fixtures/tla2tools-1.7.4.jar"),
        ),
        ("bogus.jar", b"not a jar"),
    ] {
        std::fs::write(directory.join(file), contents).expect("a file");
    }
    let real = std::fs::canonicalize(&directory).expect("a real path");
    let launch = |class_path: &str| {
        run(
            &directory,
            &[
                "-cp",
                class_path,
                "tlc2.TLC",
                "-noGenerateSpecTE",
                "-deadlock",
                "Spec",
            ],
        )
    };
    // TLC copies a standard module out of the jar, and names the copy and where it copied it from.
    let delimiter = if cfg!(windows) { ';' } else { ':' };
    let output = launch(&format!("classes{delimiter}tla2tools.jar"));
    // No run of TLC on Windows recorded the jar's URL, which Java writes with File.toURI.
    if cfg!(windows) {
        common::assert_declined(&output, common::DECLINED_JAR, "jar");
    } else {
        let text = stdout(&output);
        assert_eq!(output.status.code(), Some(0), "{text}");
        let naturals = text
            .lines()
            .find(|line| line.ends_with("/Naturals.tla)"))
            .expect("Naturals parsed");
        let jar_url = format!(
            "Naturals.tla (jar:file:{}/tla2tools.jar!/tla2sany/StandardModules/Naturals.tla)",
            real.display()
        );
        assert!(
            naturals.starts_with("Parsing file ")
                && naturals.contains("Naturals.tla (jar:file:/")
                && naturals.ends_with(&jar_url),
            "{text}"
        );
        assert!(
            text.contains("\nModel checking completed. No error has been found.\n"),
            "{text}"
        );
    }
    for (class_path, what) in [
        ("tla2tools-1.7.4.jar", "TLC 1.7.4"),
        (
            "bogus.jar",
            "the version of bogus.jar: no end of central directory record",
        ),
    ] {
        let output = launch(class_path);
        assert_eq!(output.status.code(), Some(1), "{class_path}");
        assert_eq!(stdout(&output), "", "{class_path}");
        assert_eq!(
            String::from_utf8_lossy(&output.stderr),
            format!("prove-it: not native yet: {what}\n")
        );
    }
    // -Dtla-ts.tlc names the TLC in place of the jar.
    let named = run(
        &directory,
        &[
            "-Dtla-ts.tlc=master",
            "-cp",
            "tla2tools-1.7.4.jar",
            "tlc2.TLC",
            "-noGenerateSpecTE",
            "-deadlock",
            "Spec",
        ],
    );
    if cfg!(windows) {
        common::assert_declined(&named, common::DECLINED_JAR, "named");
    } else {
        assert_eq!(named.status.code(), Some(0), "{}", stdout(&named));
    }
    std::fs::remove_dir_all(directory).expect("removed");
}
