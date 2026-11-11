//! `sanyText`: SANY's report, asked again with what it names until it has what it reads.

use prove_it_host::sany::sany_text;
use prove_it_host::value::HostValue;

fn get(value: &HostValue, name: &str) -> HostValue {
    match value {
        HostValue::Object(properties) => properties
            .iter()
            .find(|(key, _)| *key == name)
            .map(|(_, value)| value.clone())
            .unwrap_or(HostValue::Undefined),
        _ => HostValue::Undefined,
    }
}

fn text(value: &HostValue) -> String {
    match value {
        HostValue::Text(units) => String::from_utf16_lossy(units),
        _ => panic!("not a string: {value:?}"),
    }
}

/// Calls `sanyText` with what it names until it returns something else, and returns that with the
/// keys it asked for, in order.
fn write(source: &str, read: impl Fn(&str) -> Option<String>) -> (HostValue, Vec<String>) {
    let mut known: Vec<(String, Option<String>)> = Vec::new();
    let mut asked = Vec::new();
    loop {
        let entries = known
            .iter()
            .map(|(key, value)| {
                HostValue::Array(vec![
                    HostValue::text(key),
                    value
                        .as_deref()
                        .map_or(HostValue::Undefined, HostValue::text),
                ])
            })
            .collect();
        let result = sany_text(&[
            HostValue::text("Main"),
            HostValue::text(source),
            HostValue::text("Main"),
            HostValue::text("master"),
            HostValue::Array(Vec::new()),
            HostValue::Array(entries),
        ])
        .expect("a result");
        if text(&get(&result, "kind")) != "needed" {
            return (result, asked);
        }
        let HostValue::Array(keys) = get(&result, "keys") else {
            panic!("keys");
        };
        for key in keys.iter().map(text) {
            asked.push(key.clone());
            known.push((key.clone(), read(&key)));
        }
    }
}

#[test]
fn writes_the_report_once_it_has_the_modules_and_files_it_names() {
    let (result, asked) = write(
        "---- MODULE Main ----\nEXTENDS Other\n====\n",
        |key| match key {
            "module:Other" => Some("---- MODULE Other ----\nX == 1\n====\n".to_owned()),
            "file:file:Main" => Some("Main.tla".to_owned()),
            "file:file:Other" => Some("Other.tla".to_owned()),
            _ => None,
        },
    );
    assert_eq!(text(&get(&result, "kind")), "text");
    assert_eq!(
        text(&get(&result, "text")),
        "Parsing file Main.tla\nParsing file Other.tla\nSemantic processing of module Other\nSemantic processing of module Main\nLinting of module Other\nLinting of module Main\n"
    );
    assert_eq!(get(&result, "isFailed"), HostValue::Bool(false));
    assert!(asked.contains(&"module:Other".to_owned()), "{asked:?}");
}

#[test]
fn declines_what_tla_front_does_not_write() {
    let (result, _) = write(
        "---- MODULE Main ----\nUSE MODULE Inner\n---- MODULE Inner ----\n====\n====\n",
        |_| Some("Main.tla".to_owned()),
    );
    assert_eq!(text(&get(&result, "kind")), "declined");
}

#[test]
fn writes_the_report_of_a_deep_formula_from_a_shallow_stack() {
    let source = format!(
        "---- MODULE Main ----\nX == {}TRUE{}\n====\n",
        "(".repeat(400),
        ")".repeat(400)
    );
    let result = std::thread::Builder::new()
        .stack_size(1024 * 1024)
        .spawn(move || {
            write(&source, |key| {
                (key == "file:root file:Main").then(|| "Main.tla".to_owned())
            })
            .0
        })
        .expect("a thread")
        .join()
        .expect("the report");
    assert_eq!(text(&get(&result, "kind")), "text");
    assert_eq!(get(&result, "isFailed"), HostValue::Bool(false));
}
