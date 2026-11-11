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

// The machine, with whether the library's check runs the check, which then reads its outcome.
fn machine(is_library: bool) -> HostValue {
    HostValue::Array(vec![
        HostValue::text("Linux"),
        HostValue::text("6.0"),
        HostValue::text("x64"),
        HostValue::Number(4.0),
        HostValue::Number(1024.0),
        HostValue::Number(7.0),
        // 2026-11-10 12:00:00 UTC.
        HostValue::Number(1_794_312_000_000.0),
        HostValue::text("UTC0"),
        HostValue::Array(Vec::new()),
        HostValue::Bool(is_library),
    ])
}

/// Calls `checkSources` with what it names until it returns something else, and returns that with
/// the number of rounds it took.
fn check(args: &[&str], read: impl Fn(&str) -> Option<String>) -> (HostValue, usize) {
    check_on(args, false, read)
}

fn check_on(
    args: &[&str],
    is_library: bool,
    read: impl Fn(&str) -> Option<String>,
) -> (HostValue, usize) {
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
            machine(is_library),
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
    let outcome = get(&result, "outcome");
    assert_eq!(text(&get(&outcome, "status")), "success");
    assert_eq!(get(&outcome, "generatedStates"), HostValue::Number(4.0));
    assert_eq!(get(&outcome, "violations"), HostValue::Array(Vec::new()));
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
    // TLC stops before it searches, which the library reports as the error it throws.
    assert_eq!(get(&result, "outcome"), HostValue::Undefined);
}

#[test]
fn declines_several_specs_whose_modules_it_would_name_alike() {
    let (result, _) = check(&["-noGenerateSpecTE", "/a/One.tla", "/b/Two.tla"], |key| {
        key.strip_prefix("text:").map(|_| String::new())
    });
    assert_eq!(text(&get(&result, "kind")), "declined");
    assert_eq!(
        text(&get(&result, "reason")),
        "several specifications in one check of a host's sources"
    );
}

// The CLI reads only what the check prints, so the check keeps none of the spec's prints for an
// outcome the library alone reads.
#[test]
fn keeps_the_prints_only_for_the_library() {
    let spec = "---- MODULE Printing ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == x < 3 /\\ PrintT(x) /\\ x' = x + 1\n====\n";
    let read = |key: &str| match key {
        "text:/specs/Printing.tla" => Some(spec.to_owned()),
        "text:/specs/Printing.cfg" => {
            Some("INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n".to_owned())
        }
        _ => key.strip_prefix("file:").map(|_| String::new()),
    };
    for (is_library, prints) in [(false, 0), (true, 3)] {
        let (result, _) = check_on(
            &["-noGenerateSpecTE", "/specs/Printing.tla"],
            is_library,
            read,
        );
        let out = text(&get(&result, "out"));
        assert!(out.contains("\n0\n1\n2\n"), "{out}");
        let HostValue::Array(kept) = get(&get(&result, "outcome"), "prints") else {
            panic!("no prints: {result:?}");
        };
        assert_eq!(kept.len(), prints, "{is_library}");
    }
}
