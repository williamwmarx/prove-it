//! `checkSources`: the binary's check, asked again with what it names until it has what it reads.

use prove_it_host::check::check_sources;
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

fn machine() -> HostValue {
    HostValue::Object(vec![
        ("system", HostValue::text("Linux")),
        ("release", HostValue::text("6.0")),
        ("arch", HostValue::text("x64")),
        ("cores", HostValue::Number(4.0)),
        ("memoryMegabytes", HostValue::Number(1024.0)),
        ("pid", HostValue::Number(7.0)),
        // 2026-11-10 12:00:00 UTC.
        ("now", HostValue::Number(1_794_312_000_000.0)),
        ("zone", HostValue::text("UTC0")),
        ("variables", HostValue::Array(Vec::new())),
    ])
}

/// Calls `checkSources` with what it names until it returns something else, and returns that with
/// the number of rounds it took.
fn check(args: &[&str], read: impl Fn(&str) -> Option<String>) -> (HostValue, usize) {
    let mut known: Vec<(String, Option<String>)> = Vec::new();
    for round in 1.. {
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
        let result = check_sources(&[
            HostValue::Array(args.iter().map(|arg| HostValue::text(arg)).collect()),
            HostValue::Array(entries),
            machine(),
        ])
        .expect("a result");
        if text(&get(&result, "kind")) != "needed" {
            return (result, round);
        }
        let HostValue::Array(keys) = get(&result, "keys") else {
            panic!("keys");
        };
        for key in keys.iter().map(text) {
            assert!(
                known.iter().all(|(known, _)| *known != key),
                "asked again for {key}"
            );
            let value = read(&key);
            known.push((key, value));
        }
    }
    unreachable!()
}

#[test]
fn checks_a_spec_once_it_has_the_files_it_names() {
    let spec = "---- MODULE Counter ----\nEXTENDS Naturals, Other\nVARIABLE x\nInit == x = 0\nNext == x < Limit /\\ x' = x + 1\n====\n";
    let (result, rounds) = check(
        &["-noGenerateSpecTE", "-deadlock", "/specs/Counter.tla"],
        |key| match key {
            "text:/specs/Counter.tla" => Some(spec.to_owned()),
            "text:/specs/Counter.cfg" => Some("INIT Init\nNEXT Next\n".to_owned()),
            "module:Other" => Some("---- MODULE Other ----\nLimit == 3\n====\n".to_owned()),
            key => key
                .strip_prefix("file:file:")
                .map(|name| format!("/specs/{name}.tla"))
                .or_else(|| {
                    key.strip_prefix("file:standard:")
                        .map(|name| format!("/tmp/{name}.tla"))
                }),
        },
    );
    assert_eq!(text(&get(&result, "kind")), "checked", "{result:?}");
    let out = text(&get(&result, "out"));
    assert_eq!(get(&result, "exitCode"), HostValue::Number(0.0), "{out}");
    assert!(out.contains("Parsing file /specs/Counter.tla\n"), "{out}");
    assert!(out.contains("Parsing file /specs/Other.tla\n"), "{out}");
    assert!(
        out.contains("[pid: 7] (Linux 6.0 x64, prove-it native 64bit"),
        "{out}"
    );
    assert!(out.contains("Starting... (2026-11-10 12:00:00)\n"), "{out}");
    assert!(
        out.contains("4 states generated, 4 distinct states found, 0 states left on queue.\n"),
        "{out}"
    );
    assert_eq!(text(&get(&result, "err")), "");
    assert!(rounds <= 4, "{rounds} rounds");
}

#[test]
fn reports_a_missing_configuration_as_tlc_does() {
    let (result, _) = check(&["-noGenerateSpecTE", "/specs/Spec.tla"], |key| {
        (key == "text:/specs/Spec.tla")
            .then(|| "---- MODULE Spec ----\nVARIABLE x\n====\n".to_owned())
    });
    let out = text(&get(&result, "out"));
    assert_eq!(get(&result, "exitCode"), HostValue::Number(151.0), "{out}");
    assert!(
        out.contains("the configuration file /specs/Spec.cfg:\nFile not found."),
        "{out}"
    );
}
