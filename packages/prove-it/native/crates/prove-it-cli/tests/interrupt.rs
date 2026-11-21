//! A run the user stops while the binary still holds its output: TLC prints each line as it
//! goes, so a stop leaves what it printed so far, and so does the binary, which then ends as the
//! signal ends it.

#[cfg(unix)]
#[test]
fn prints_what_it_holds_when_interrupted() {
    use std::os::unix::process::ExitStatusExt;
    use std::process::{Command, Stdio};

    let directory =
        std::env::temp_dir().join(format!("prove-it-cli-interrupt-{}", std::process::id()));
    std::fs::create_dir_all(&directory).expect("a directory");
    std::fs::write(
        directory.join("M.tla"),
        "---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x' = (x + 1) % 100000000\n====\n",
    )
    .expect("a spec");
    std::fs::write(directory.join("M.cfg"), "INIT Init\nNEXT Next\n").expect("a configuration");
    for signal in ["INT", "TERM"] {
        let child = Command::new(env!("CARGO_BIN_EXE_prove-it"))
            .args(["-workers", "1", "M"])
            .current_dir(&directory)
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("the binary runs");
        // Within the hold, once the binary has parsed the spec and started its search.
        std::thread::sleep(std::time::Duration::from_millis(800));
        let killed = Command::new("kill")
            .args([format!("-{signal}"), child.id().to_string()])
            .status()
            .expect("kill runs");
        assert!(killed.success());
        let output = child.wait_with_output().expect("the binary ends");
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert_eq!(
            output.status.signal(),
            Some(if signal == "INT" { 2 } else { 15 }),
            "{stdout}"
        );
        assert!(stdout.starts_with("TLC2 Version"), "{stdout}");
        assert!(stdout.contains("\nStarting... ("), "{stdout}");
    }
    std::fs::remove_dir_all(directory).expect("removed");
}
