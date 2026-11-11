//! Command lines around the trace exploration spec, each against what TLC at d8fb231 did in the
//! case's directory (tests/te-cases): `command` holds the working directory, then the arguments;
//! `tlc` the exit code, what TLC printed, with the case's root written `{root}`, the files it wrote
//! and the specs among them. The binary prints and writes the same, or declines with the reason in
//! `declined`. TLC names the spec by the second its run started and dates it as it writes it; the
//! binary runs with its clock fixed by PROVE_IT_TEST_NOW, and the comparison drops both.

use std::path::{Path, PathBuf};
use std::process::Command;

const NOW_MILLISECONDS: &str = "1794371200000";

fn cases() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/te-cases")
}

fn read(path: &Path) -> String {
    std::fs::read_to_string(path).unwrap_or_else(|error| panic!("{}: {error}", path.display()))
}

fn copy(from: &Path, to: &Path) {
    std::fs::create_dir_all(to).expect("a directory");
    for entry in std::fs::read_dir(from).expect("the case") {
        let entry = entry.expect("an entry");
        let name = entry.file_name();
        if ["tlc", "command", "declined"].contains(&name.to_string_lossy().as_ref()) {
            continue;
        }
        if entry.file_type().expect("a type").is_dir() {
            copy(&entry.path(), &to.join(&name));
        } else {
            std::fs::copy(entry.path(), to.join(&name)).expect("a file");
        }
    }
}

// The files under the root but TLC's states directory, relative to it.
fn list(root: &Path, directory: &Path, found: &mut Vec<String>) {
    for entry in std::fs::read_dir(directory).expect("a directory") {
        let path = entry.expect("an entry").path();
        let relative = path
            .strip_prefix(root)
            .expect("under the root")
            .to_string_lossy()
            .into_owned();
        if path.is_dir() && relative != "states" {
            list(root, &path, found);
        } else if path.is_file() {
            found.push(relative);
        }
    }
}

fn get_files(root: &Path) -> Vec<String> {
    let mut found = Vec::new();
    list(root, root, &mut found);
    found.sort();
    found
}

// The trace exploration spec's name with its second written 0.
fn replace_second(text: &str) -> String {
    let mut replaced = String::new();
    let mut rest = text;
    while let Some(index) = rest.find("_TTrace_") {
        let (head, tail) = rest.split_at(index + "_TTrace_".len());
        replaced.push_str(head);
        let digits = tail.len() - tail.trim_start_matches(|c: char| c.is_ascii_digit()).len();
        replaced.push_str(if digits > 0 { "0" } else { "" });
        rest = &tail[digits..];
    }
    replaced.push_str(rest);
    replaced
}

// What a run prints but its times, its machine, where it copies the standard modules, its
// progress and the second it names the trace exploration spec by.
fn normalize(text: &str) -> String {
    let lines = text.lines().filter(|line| !line.starts_with("Progress("));
    let lines = lines.map(|line| {
        let timed = [
            "TLC2 Version ",
            "Running breadth-first search ",
            "Running Random Simulation ",
            "Starting... ",
            "Finished in ",
            "\\* Generated on ",
        ]
        .into_iter()
        .find(|prefix| line.starts_with(prefix));
        match (timed, line.strip_prefix("Parsing file ")) {
            (Some(prefix), _) => prefix.to_owned(),
            (None, Some(path)) if path.contains("/tlc-") => {
                let path = path.split(' ').next().unwrap_or(path);
                format!("Parsing file {}", path.rsplit('/').next().unwrap_or(path))
            }
            _ if line.starts_with("Finished computing initial states") => line
                .rsplit_once(" at ")
                .map_or(line, |(head, _)| head)
                .to_owned(),
            _ => line.to_owned(),
        }
    });
    replace_second(&lines.collect::<Vec<_>>().join("\n"))
}

#[test]
fn checks_around_the_trace_exploration_spec_as_tlc() {
    let mut names: Vec<_> = std::fs::read_dir(cases())
        .expect("the cases")
        .map(|entry| entry.expect("a case").file_name())
        .collect();
    names.sort();
    for name in names {
        let name = name.to_string_lossy();
        let case = cases().join(name.as_ref());
        let created =
            std::env::temp_dir().join(format!("prove-it-te-cases-{name}-{}", std::process::id()));
        copy(&case, &created);
        let root = std::fs::canonicalize(&created).expect("the root");
        let root_text = root.to_string_lossy().into_owned();
        let before = get_files(&root);
        let command = read(&case.join("command"));
        let mut lines = command.lines();
        let directory = lines.next().expect("the working directory");
        let (properties, rest): (Vec<&str>, Vec<&str>) =
            lines.partition(|arg| arg.starts_with("-D"));
        let class = (!properties.is_empty()).then_some("tlc2.TLC");
        let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
            .args(properties.into_iter().chain(class).chain(rest))
            .env("PROVE_IT_TEST_NOW", NOW_MILLISECONDS)
            .env_remove("TZ")
            .current_dir(root.join(directory))
            .output()
            .expect("the binary runs");
        let stdout = String::from_utf8_lossy(&output.stdout).replace(&root_text, "{root}");
        let stderr = String::from_utf8_lossy(&output.stderr);
        let written: Vec<String> = get_files(&root)
            .into_iter()
            .filter(|file| !before.contains(file))
            .collect();
        match std::fs::read_to_string(case.join("declined")) {
            Ok(reason) => {
                assert_eq!(
                    stderr,
                    format!("prove-it: not native yet: {}", reason),
                    "{name}"
                );
                assert_eq!(written, Vec::<String>::new(), "{name}");
            }
            Err(_) => {
                let tlc = case.join("tlc");
                assert_eq!(
                    output.status.code().map(|code| format!("{code}\n")),
                    Some(read(&tlc.join("exit"))),
                    "{name}: {stdout}{stderr}"
                );
                assert_eq!(
                    normalize(&stdout),
                    normalize(&read(&tlc.join("stdout"))),
                    "{name}"
                );
                let expected: Vec<String> = read(&tlc.join("written"))
                    .lines()
                    .map(str::to_owned)
                    .collect();
                assert_eq!(
                    written
                        .iter()
                        .map(|file| replace_second(file))
                        .collect::<Vec<_>>(),
                    expected,
                    "{name}"
                );
                for file in written.iter().filter(|file| file.ends_with(".tla")) {
                    assert_eq!(
                        normalize(&read(&root.join(file))),
                        normalize(&read(&tlc.join("files").join(replace_second(file)))),
                        "{name}: {file}"
                    );
                }
            }
        }
        std::fs::remove_dir_all(&root).expect("removed");
    }
}
