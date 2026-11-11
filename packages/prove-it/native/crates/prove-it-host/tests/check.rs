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

/// What a host answers for the files at these absolute paths, in the working directory `/work`: the
/// CLI's keys by path, and the library's, `text:<path>` and `module:<name>`.
fn read_files<'f>(files: &'f [(&str, &str)]) -> impl Fn(&str) -> HostValue + 'f {
    move |key| {
        let (kind, path) = key.split_once(':').unwrap_or((key, ""));
        let path = if path.starts_with('/') {
            path.to_owned()
        } else {
            format!("/work/{path}")
        };
        let file = files.iter().find(|(file, _)| *file == path);
        let is_directory = files
            .iter()
            .any(|(file, _)| file.starts_with(&format!("{}/", path.trim_end_matches('/'))));
        match (kind, file) {
            ("cwd", _) => HostValue::text("/work"),
            ("tmpdir", _) => HostValue::text("/tmp"),
            ("stat", Some(_)) => HostValue::text("file"),
            ("stat", None) if is_directory => HostValue::text("directory"),
            ("realpath", Some(_)) => HostValue::text(&path),
            ("bytes", Some((_, text))) => HostValue::Uint8s(text.as_bytes().to_vec()),
            ("text", Some((_, text))) => HostValue::text(text),
            ("module", _) => files
                .iter()
                .find(|(file, _)| file.ends_with(&format!("/{}.tla", &key["module:".len()..])))
                .map_or(HostValue::Undefined, |(_, text)| HostValue::text(text)),
            _ => HostValue::Undefined,
        }
    }
}

/// Calls `checkSources` with what it names until it returns something else, and returns that with
/// the number of rounds it took.
fn check(args: &[&str], files: &[(&str, &str)]) -> (HostValue, usize) {
    check_on(args, false, files)
}

fn check_on(args: &[&str], is_library: bool, files: &[(&str, &str)]) -> (HostValue, usize) {
    let read = read_files(files);
    let mut known: Vec<(String, HostValue)> = Vec::new();
    for round in 1.. {
        let entries = known
            .iter()
            .map(|(key, value)| HostValue::Array(vec![HostValue::text(key), value.clone()]))
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
        &[
            ("/specs/Counter.tla", spec),
            ("/specs/Counter.cfg", "INIT Init\nNEXT Next\n"),
            (
                "/specs/Other.tla",
                "---- MODULE Other ----\nLimit == 3\n====\n",
            ),
        ],
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
    let (result, _) = check(
        &["-noGenerateSpecTE", "/specs/Spec.tla"],
        &[(
            "/specs/Spec.tla",
            "---- MODULE Spec ----\nVARIABLE x\n====\n",
        )],
    );
    let out = text(&get(&result, "out"));
    assert_eq!(get(&result, "exitCode"), HostValue::Number(151.0), "{out}");
    assert!(
        out.contains("the configuration file Spec.cfg:\nFile not found."),
        "{out}"
    );
    // TLC stops before it searches, which the library reports as the error it throws.
    assert_eq!(get(&result, "outcome"), HostValue::Undefined);
}

// Each spec is checked on its own: the library names a module by its name alone, which each spec
// could find in another file, and the CLI would end in the exit code of a spec that fails before
// another declines.
#[test]
fn declines_several_specs() {
    for is_library in [true, false] {
        let (result, _) = check_on(
            &["-noGenerateSpecTE", "/a/One.tla", "/b/Two.tla"],
            is_library,
            &[("/a/One.tla", ""), ("/b/Two.tla", "")],
        );
        assert_eq!(text(&get(&result, "kind")), "declined");
        assert_eq!(
            text(&get(&result, "reason")),
            "several specifications in one check of a host's sources"
        );
    }
}

// The CLI reads only what the check prints, so the check keeps none of the spec's prints for an
// outcome the library alone reads.
#[test]
fn keeps_the_prints_only_for_the_library() {
    let spec = "---- MODULE Printing ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == x < 3 /\\ PrintT(x) /\\ x' = x + 1\n====\n";
    let files = [
        ("/specs/Printing.tla", spec),
        (
            "/specs/Printing.cfg",
            "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n",
        ),
    ];
    for (is_library, prints) in [(false, 0), (true, 3)] {
        let (result, _) = check_on(
            &["-noGenerateSpecTE", "/specs/Printing.tla"],
            is_library,
            &files,
        );
        let out = text(&get(&result, "out"));
        assert!(out.contains("\n0\n1\n2\n"), "{out}");
        let HostValue::Array(kept) = get(&get(&result, "outcome"), "prints") else {
            panic!("no prints: {result:?}");
        };
        assert_eq!(kept.len(), prints, "{is_library}");
    }
}

// With -continue, TLC reports each initial state that violates an invariant and goes on; the CLI
// reads only what is printed, so the check keeps the violations only for the library.
#[test]
fn keeps_the_continued_violations_only_for_the_library() {
    let spec = "---- MODULE Many ----\nEXTENDS Naturals\nVARIABLE x\nInit == x \\in 1..3\nNext == UNCHANGED x\nInv == x > 3\n====\n";
    let files = [
        ("/specs/Many.tla", spec),
        ("/specs/Many.cfg", "INIT Init\nNEXT Next\nINVARIANT Inv\n"),
    ];
    for (is_library, kept) in [(false, 0), (true, 3)] {
        let (result, _) = check_on(
            &["-noGenerateSpecTE", "-continue", "/specs/Many.tla"],
            is_library,
            &files,
        );
        let out = text(&get(&result, "out"));
        assert_eq!(out.matches("Invariant Inv is violated").count(), 3, "{out}");
        let HostValue::Array(violations) = get(&get(&result, "outcome"), "violations") else {
            panic!("no violations: {result:?}");
        };
        assert_eq!(violations.len(), kept, "{is_library}: {out}");
    }
}
