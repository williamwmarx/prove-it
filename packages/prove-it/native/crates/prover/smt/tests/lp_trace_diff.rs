//! Compares the `.lptrace` files of two directories, as the TypeScript theory (`lp-trace.ts`) and
//! the Rust one (`prove_smt::lp::trace`) record them: `PROVE_IT_LP_TRACE_DIFF=<tsdir>:<rustdir>`.
//! Each trace present under both, by its path relative to them, is compared line by line as
//! parsed JSON, so field order and the spelling of numbers do not count. Every file is reported
//! same, differs (at its first differing line, with both lines) or missing on one side; the test
//! fails when one differs. Without the variable the test only says so.

use std::fs;
use std::path::{Path, PathBuf};

use prove_smt::lp::json::parse;

/// The `.lptrace` files under the directory, by their paths relative to it.
fn collect_traces(root: &Path, directory: &Path, paths: &mut Vec<PathBuf>) {
    let Ok(entries) = fs::read_dir(directory) else {
        return;
    };
    for path in entries.filter_map(|entry| entry.ok().map(|entry| entry.path())) {
        if path.is_dir() {
            collect_traces(root, &path, paths);
        } else if path
            .extension()
            .is_some_and(|extension| extension == "lptrace")
            && let Ok(relative) = path.strip_prefix(root)
        {
            paths.push(relative.to_path_buf());
        }
    }
}

fn get_traces(root: &Path) -> Vec<PathBuf> {
    let mut paths = Vec::new();
    collect_traces(root, root, &mut paths);
    paths.sort();
    paths
}

/// The first line where the traces differ, with its text on each side ("end of file" past the
/// end), or None when they are the same.
fn get_difference(left: &str, right: &str) -> Option<(usize, String, String)> {
    let parse_line = |text: &str| parse(text).map_err(|error| format!("{error}: {text}"));
    let mut left_lines = left.lines().filter(|line| !line.is_empty());
    let mut right_lines = right.lines().filter(|line| !line.is_empty());
    let mut number = 0;
    loop {
        number += 1;
        match (left_lines.next(), right_lines.next()) {
            (None, None) => return None,
            (left_line, right_line) => {
                let left_value = left_line.map(parse_line);
                let right_value = right_line.map(parse_line);
                let is_same = matches!(
                    (&left_value, &right_value),
                    (Some(Ok(left_json)), Some(Ok(right_json))) if left_json == right_json
                );
                if !is_same {
                    let get_text = |line: Option<&str>| line.unwrap_or("end of file").to_string();
                    return Some((number, get_text(left_line), get_text(right_line)));
                }
            }
        }
    }
}

#[test]
fn lp_trace_diff() {
    let Some(setting) = std::env::var_os("PROVE_IT_LP_TRACE_DIFF") else {
        println!(
            "PROVE_IT_LP_TRACE_DIFF=<typescript traces>:<rust traces> compares two trace directories"
        );
        return;
    };
    let setting = setting.to_string_lossy().into_owned();
    let (left_root, right_root) = setting
        .split_once(':')
        .map(|roots| (PathBuf::from(roots.0), PathBuf::from(roots.1)))
        .expect("PROVE_IT_LP_TRACE_DIFF is <typescript traces>:<rust traces>");
    let left = get_traces(&left_root);
    let right = get_traces(&right_root);
    let mut paths: Vec<&PathBuf> = left.iter().chain(&right).collect();
    paths.sort();
    paths.dedup();
    let mut same = 0;
    let mut differs = 0;
    let mut missing = 0;
    for path in paths {
        let name = path.display();
        let read = |root: &Path| fs::read_to_string(root.join(path)).ok();
        match (read(&left_root), read(&right_root)) {
            (Some(left_text), Some(right_text)) => match get_difference(&left_text, &right_text) {
                None => {
                    same += 1;
                    println!("same      {name}");
                }
                Some((line, left_line, right_line)) => {
                    differs += 1;
                    println!(
                        "differs   {name}:{line}\n  typescript {left_line}\n  rust       {right_line}"
                    );
                }
            },
            (left_text, _) => {
                missing += 1;
                let side = if left_text.is_none() {
                    "typescript"
                } else {
                    "rust"
                };
                println!("missing   {name} in the {side} traces");
            }
        }
    }
    println!(
        "lp traces of {} and {}: {same} same, {differs} differ, {missing} missing on one side",
        left_root.display(),
        right_root.display()
    );
    assert!(differs == 0, "{differs} lp traces differ");
}

#[test]
fn compares_lines_as_json() {
    let left = "{\"c\":\"lar#0\",\"m\":\"addVar\",\"a\":[0,false],\"r\":0}\n";
    assert_eq!(
        get_difference(
            left,
            "{\"r\":0.0,\"a\":[0,false],\"m\":\"addVar\",\"c\":\"lar#0\"}"
        ),
        None
    );
    assert_eq!(
        get_difference(
            left,
            "{\"c\":\"lar#0\",\"m\":\"addVar\",\"a\":[0,false],\"r\":1}"
        ),
        Some((
            1,
            left.trim_end().to_string(),
            "{\"c\":\"lar#0\",\"m\":\"addVar\",\"a\":[0,false],\"r\":1}".to_string()
        ))
    );
    assert_eq!(
        get_difference(&format!("{left}{left}"), left),
        Some((2, left.trim_end().to_string(), "end of file".to_string()))
    );
}
