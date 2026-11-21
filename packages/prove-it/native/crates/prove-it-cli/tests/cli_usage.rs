//! Command-line errors recorded from TLC at d8fb231, before it reads a module.

use std::path::Path;
use std::process::Command;

#[test]
fn reports_configured_and_missing_inputs_as_tlc() {
    let fixtures = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/cli-usage");
    let mut names: Vec<_> = std::fs::read_dir(fixtures)
        .expect("fixtures")
        .map(|entry| entry.expect("a fixture").path())
        .collect();
    names.sort();
    assert!(!names.is_empty());
    for fixture in names {
        let args = std::fs::read_to_string(fixture.join("args")).expect("arguments");
        let expected = std::fs::read_to_string(fixture.join("tlc.out")).expect("TLC's output");
        for java_launch in [false, true] {
            let mut command = Command::new(env!("CARGO_BIN_EXE_prove-it"));
            if java_launch {
                command.arg("tlc2.TLC");
            }
            let output = command
                .args(args.lines())
                .current_dir(&fixture)
                .output()
                .expect("the binary runs");
            let actual = format!(
                "exit {}\n{}",
                output.status.code().unwrap_or(-1),
                String::from_utf8_lossy(&output.stdout)
                    .lines()
                    .filter(|line| !line.starts_with("TLC2 Version"))
                    .map(|line| format!("{line}\n"))
                    .collect::<String>()
            );
            assert_eq!(actual, expected, "{fixture:?}, Java launch: {java_launch}");
            assert!(output.stderr.is_empty(), "{:?}", output.stderr);
        }
    }
}

#[test]
fn keeps_the_native_batch_launcher() {
    let directory = std::env::temp_dir().join(format!("prove-it-cli-batch-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    for name in ["One", "Two"] {
        std::fs::write(
            directory.join(format!("{name}.tla")),
            format!(
                "---- MODULE {name} ----\nVARIABLE x\nInit == x = 0\nNext == UNCHANGED x\n====\n"
            ),
        )
        .expect("a module");
        std::fs::write(
            directory.join(format!("{name}.cfg")),
            "INIT Init\nNEXT Next\n",
        )
        .expect("a configuration");
    }
    let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
        .args(["-workers", "1", "-fp", "0", "-noTE", "One.tla", "Two.cfg"])
        .current_dir(&directory)
        .output()
        .expect("the binary runs");
    let text = String::from_utf8_lossy(&output.stdout);
    assert_eq!(output.status.code(), Some(0), "{text}");
    assert!(text.contains("Checking One.tla with One.cfg\n"), "{text}");
    assert!(text.contains("Checking Two.tla with Two.cfg\n"), "{text}");
    assert!(output.stderr.is_empty(), "{:?}", output.stderr);
    std::fs::remove_dir_all(directory).expect("removed");
}

// `-recover` of a directory without a readable `vars.chkpt`: TLC's FileNotFoundException, then
// the Finished line `TLC.process`'s finally block prints, recorded from TLC at d8fb231 with the
// time of the run left out.
#[test]
fn reports_a_checkpoint_it_cant_recover_as_tlc() {
    let fixture = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/recover-missing");
    for (is_tool, recorded) in [(false, "tlc.out"), (true, "tlc-tool.out")] {
        let expected = std::fs::read_to_string(fixture.join(recorded)).expect("TLC's output");
        let mut command = Command::new(env!("CARGO_BIN_EXE_prove-it"));
        if is_tool {
            command.arg("-tool");
        }
        let output = command
            .args(["-recover", "nope", "-config", "M.cfg", "M.tla"])
            .current_dir(&fixture)
            .output()
            .expect("the binary runs");
        // Windows words the failure to open a file differently, so the binary declines there.
        if cfg!(windows) {
            assert_eq!(
                String::from_utf8_lossy(&output.stderr),
                "prove-it: not native yet: -recover from a checkpoint"
            );
            assert_eq!(output.status.code(), Some(1));
            continue;
        }
        let actual = format!(
            "exit {}\n{}",
            output.status.code().unwrap_or(-1),
            String::from_utf8_lossy(&output.stdout)
                .lines()
                .filter(|line| !line.starts_with("TLC2 Version"))
                .map(|line| {
                    if line.starts_with("Finished in ") {
                        "Finished in {time}\n".to_owned()
                    } else {
                        format!("{line}\n")
                    }
                })
                .collect::<String>()
        );
        assert_eq!(actual, expected, "-tool: {is_tool}");
    }
}
