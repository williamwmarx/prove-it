//! The tlapm conformance cases of tla-ts under tests/upstream-tlapm, copied as they are from
//! `packages/conformance/test/tlapm` at 0341dbe5 (MIT, Aiden Bai), each a module whose header
//! names the mode and whose trailing block records what tlapm b91fb6c printed, normalized as
//! tla-ts's harness normalizes a transcript (`packages/conformance/scripts/tlapm.ts`). Each case
//! runs here as that harness runs it, `--strict --toolbox 0 0 --threads 1 --cache-dir` and the
//! mode's options, and its transcript, normalized the same way, and its exit must equal the
//! recording.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

struct Case {
    path: PathBuf,
    mode: String,
    exit: i32,
    transcript: String,
}

/// The header's scalar field, where the header is the first `(*--- ... ---*)` comment.
fn get_header_field(text: &str, name: &str) -> Option<String> {
    let header = text.strip_prefix("(*---\n")?;
    let end = header.find("\n---*)\n")?;
    header[..end]
        .lines()
        .find_map(|line| line.strip_prefix(&format!("{name}: ")))
        .map(|value| value.trim().to_owned())
}

fn unescape(quoted: &str) -> String {
    let mut text = String::new();
    let mut chars = quoted.chars();
    while let Some(char) = chars.next() {
        if char != '\\' {
            text.push(char);
            continue;
        }
        match chars.next() {
            Some('n') => text.push('\n'),
            Some('t') => text.push('\t'),
            Some('r') => text.push('\r'),
            Some(other) => text.push(other),
            None => {}
        }
    }
    text
}

/// The `all` context's exit and transcript of the trailing `(*--- recorded ... ---*)` block.
fn read_recording(text: &str) -> (i32, String) {
    let start = text.rfind("\n(*--- recorded\n").expect("a recording") + "\n(*--- recorded\n".len();
    let block = text[start..]
        .strip_suffix("---*)\n")
        .expect("the block's end");
    let lines: Vec<&str> = block.lines().collect();
    assert_eq!(lines.first(), Some(&"all:"), "one context, all");
    let mut exit = None;
    let mut transcript = String::new();
    let mut index = 1;
    while index < lines.len() {
        let line = lines[index];
        index += 1;
        if let Some(value) = line.strip_prefix("  exit: ") {
            exit = Some(value.trim().parse().expect("an exit code"));
        } else if let Some(value) = line.strip_prefix("  transcript: ") {
            let value = value.trim_end();
            if value == "|-" || value == "|" {
                let mut block_lines = Vec::new();
                while index < lines.len() {
                    let line = lines[index];
                    match line.strip_prefix("    ") {
                        Some(rest) => block_lines.push(rest),
                        None if line.trim().is_empty() => block_lines.push(""),
                        None => break,
                    }
                    index += 1;
                }
                transcript = block_lines.join("\n");
                if value == "|-" {
                    transcript = transcript.trim_end_matches('\n').to_owned();
                }
            } else if let Some(inner) = value
                .strip_prefix('"')
                .and_then(|rest| rest.strip_suffix('"'))
            {
                transcript = unescape(inner);
            } else if value == "''" || value == "\"\"" {
                transcript = String::new();
            } else {
                transcript = value.to_owned();
            }
        } else {
            panic!("an unexpected recording line: {line}");
        }
    }
    (exit.expect("an exit"), transcript)
}

fn read_case(path: &Path) -> (Case, String) {
    let text = std::fs::read_to_string(path).expect("the case");
    for key in ["args", "includes", "stack", "contexts"] {
        assert!(
            get_header_field(&text, key).is_none(),
            "{} needs {key}, which this harness doesn't take",
            path.display()
        );
    }
    let (exit, transcript) = read_recording(&text);
    let source = text[..text.rfind("\n(*--- recorded\n").expect("a recording")].trim_end();
    (
        Case {
            path: path.to_path_buf(),
            mode: get_header_field(&text, "mode").unwrap_or_else(|| "proof".to_owned()),
            exit,
            transcript,
        },
        format!("{source}\n"),
    )
}

fn is_hex(byte: u8) -> bool {
    byte.is_ascii_hexdigit()
}

fn is_word(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || byte == b'_'
}

/// `tlapm_[0-9a-f]{6}` as a word becomes `tlapm_<id>`.
fn hide_temporary_names(text: &str) -> String {
    let bytes = text.as_bytes();
    let mut out = String::new();
    let mut index = 0;
    while index < bytes.len() {
        let rest = &bytes[index..];
        let before_ok = index == 0 || !is_word(bytes[index - 1]);
        if before_ok
            && rest.starts_with(b"tlapm_")
            && rest.len() >= 12
            && rest[6..12].iter().all(|&byte| is_hex(byte))
            && rest.get(12).is_none_or(|&byte| !is_word(byte))
        {
            out.push_str("tlapm_<id>");
            index += 12;
            continue;
        }
        let char = text[index..].chars().next().expect("a char");
        out.push(char);
        index += char.len_utf8();
    }
    out
}

/// `; time-used: [\d.]+ \(\d+%\)` dropped.
fn drop_time_used(text: &str) -> String {
    let mut out = String::new();
    let mut rest = text;
    while let Some(start) = rest.find("; time-used: ") {
        let after = &rest[start + "; time-used: ".len()..];
        let number = after
            .bytes()
            .take_while(|byte| byte.is_ascii_digit() || *byte == b'.')
            .count();
        let matched = number > 0 && after[number..].starts_with(" (") && {
            let percent = &after[number + 2..];
            let digits = percent.bytes().take_while(u8::is_ascii_digit).count();
            digits > 0 && percent[digits..].starts_with("%)")
        };
        if !matched {
            out.push_str(&rest[..start + 1]);
            rest = &rest[start + 1..];
            continue;
        }
        let percent = &after[number + 2..];
        let digits = percent.bytes().take_while(u8::is_ascii_digit).count();
        out.push_str(&rest[..start]);
        rest = &percent[digits + 2..];
    }
    out.push_str(rest);
    out
}

fn is_backtrace_line(line: &str) -> bool {
    [
        "Raised at ",
        "Raised by primitive operation at ",
        "Called from ",
        "Re-raised at ",
    ]
    .iter()
    .any(|prefix| line.starts_with(prefix))
}

fn is_shell_not_found(line: &str) -> bool {
    line.starts_with("sh: ") && line.ends_with(": not found") && line.contains("type: ")
}

/// The line filters of `normalizeTlapmTranscript` that work line by line: shell `type` failures,
/// backtrace lines, tlapm's config dump (`version == "..."` and the non-blank lines after it that
/// aren't toolbox lines), and `not found in this PATH:` followed by the path.
fn filter_lines(text: &str) -> String {
    let mut out: Vec<String> = Vec::new();
    let mut lines = text.split('\n').peekable();
    let mut in_dump = false;
    let mut hide_path = false;
    while let Some(line) = lines.next() {
        if hide_path {
            hide_path = false;
            out.push("<PATH>".to_owned());
            continue;
        }
        if in_dump {
            if !line.trim().is_empty() && !line.starts_with("@!!") {
                continue;
            }
            in_dump = false;
        }
        if is_shell_not_found(line) || is_backtrace_line(line) {
            continue;
        }
        if line.starts_with("version == \"") && line.ends_with('"') {
            in_dump = true;
            continue;
        }
        if line.ends_with("not found in this PATH:") && lines.peek().is_some() {
            hide_path = true;
        }
        out.push(line.to_owned());
    }
    out.join("\n")
}

fn parse_toolbox_message(block: &str) -> Vec<(String, String)> {
    let mut fields: Vec<(String, String)> = Vec::new();
    for line in block.split('\n') {
        let field = line
            .strip_prefix("@!!")
            .and_then(|rest| rest.split_once(':'))
            .filter(|(key, _)| {
                !key.is_empty() && key.bytes().all(|byte| byte.is_ascii_lowercase())
            });
        match field {
            Some((key, value)) => fields.push((key.to_owned(), value.to_owned())),
            None => {
                if let Some(last) = fields.last_mut() {
                    last.1.push('\n');
                    last.1.push_str(line);
                }
            }
        }
    }
    for field in &mut fields {
        field.1 = field.1.trim_end().to_owned();
    }
    fields
}

fn format_toolbox_message(fields: &[(String, String)]) -> String {
    fields
        .iter()
        .map(|(key, value)| format!("@{key}: {value}"))
        .collect::<Vec<_>>()
        .join("\n")
}

/// tla-ts's `normalizeTlapmTranscript` of stdout, a line feed and stderr.
fn normalize(output: &str, directory: &str) -> String {
    let text = output
        .replace(&format!("/private{directory}"), "")
        .replace(directory, "");
    let text = filter_lines(&drop_time_used(&hide_temporary_names(&text)));
    let mut messages: Vec<Vec<(String, String)>> = Vec::new();
    let mut remainder = String::new();
    let mut rest = text.as_str();
    while let Some(start) = rest.find("@!!BEGIN\n") {
        let after = &rest[start + "@!!BEGIN\n".len()..];
        let Some(end) = after.find("@!!END") else {
            break;
        };
        messages.push(parse_toolbox_message(&after[..end]));
        remainder.push_str(&rest[..start]);
        let mut next = &after[end + "@!!END".len()..];
        if let Some(stripped) = next.strip_prefix('\n') {
            next = stripped;
        }
        rest = next;
    }
    remainder.push_str(rest);
    let lines: Vec<&str> = remainder
        .split('\n')
        .filter(|line| {
            !(line.starts_with("\\* ")
                || line.starts_with("(* created new")
                || line.starts_with("(* fingerprints written"))
        })
        .collect();
    let mut obligations: BTreeMap<i64, Vec<&Vec<(String, String)>>> = BTreeMap::new();
    let mut others = Vec::new();
    for message in &messages {
        let get = |name: &str| {
            message
                .iter()
                .find(|(key, _)| key == name)
                .map(|(_, value)| value.as_str())
        };
        match (
            get("type"),
            get("id").and_then(|id| id.trim().parse::<i64>().ok()),
        ) {
            (Some("obligation"), Some(id)) => obligations.entry(id).or_default().push(message),
            _ => others.push(message),
        }
    }
    let mut parts: Vec<String> = Vec::new();
    for messages in obligations.values() {
        let first = messages[0];
        let last = messages[messages.len() - 1];
        parts.push(format_toolbox_message(first));
        if !std::ptr::eq(first, last) {
            parts.push(format_toolbox_message(last));
        }
    }
    parts.extend(others.iter().map(|message| format_toolbox_message(message)));
    let log: Vec<&str> = lines
        .iter()
        .copied()
        .filter(|line| !line.trim().is_empty())
        .collect();
    if !log.is_empty() {
        parts.push(log.join("\n"));
    }
    parts.join("\n\n")
}

fn find_cases(directory: &Path, cases: &mut Vec<PathBuf>) {
    for entry in std::fs::read_dir(directory).expect("the cases") {
        let path = entry.expect("an entry").path();
        if path.is_dir() {
            find_cases(&path, cases);
        } else if path.extension().is_some_and(|extension| extension == "tla") {
            cases.push(path);
        }
    }
}

#[test]
fn prints_what_tlapm_printed_on_each_upstream_case() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/upstream-tlapm");
    let mut paths = Vec::new();
    find_cases(&root, &mut paths);
    paths.sort();
    assert!(!paths.is_empty());
    let mut failures = Vec::new();
    for path in paths {
        let (case, source) = read_case(&path);
        let name = path
            .file_name()
            .expect("a name")
            .to_string_lossy()
            .into_owned();
        let directory = std::env::temp_dir().join(format!(
            "prove-it-upstream-tlapm-{}-{}",
            path.file_stem().expect("a stem").to_string_lossy(),
            std::process::id()
        ));
        std::fs::create_dir_all(&directory).expect("a case directory");
        std::fs::write(directory.join(&name), source).expect("the module");
        let cache = directory.join(".tlacache");
        let mode_arguments: &[&str] = match case.mode.as_str() {
            "proof" => &[],
            "obligations" => &["-N", "--printallobs"],
            other => panic!("{}: the mode {other} isn't run here", path.display()),
        };
        let output = Command::new(env!("CARGO_BIN_EXE_prove-it"))
            .arg("tlapm")
            .args([
                "--strict",
                "--toolbox",
                "0",
                "0",
                "--threads",
                "1",
                "--cache-dir",
            ])
            .arg(&cache)
            .args(mode_arguments)
            .arg(&name)
            .current_dir(&directory)
            .output()
            .expect("the binary runs");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        let transcript = normalize(&format!("{stdout}\n{stderr}"), &directory.to_string_lossy());
        let exit = output.status.code().unwrap_or(-1);
        if exit != case.exit || transcript != case.transcript {
            failures.push(format!(
                "{}: exit {exit}, recorded {}\n--- printed\n{transcript}\n--- recorded\n{}\n",
                case.path.display(),
                case.exit,
                case.transcript
            ));
        }
        std::fs::remove_dir_all(directory).expect("removed the case directory");
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
