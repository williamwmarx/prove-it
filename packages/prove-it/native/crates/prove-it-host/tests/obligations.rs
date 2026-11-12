//! `obligations` and `fingerprint`: a module's obligations and what Prep makes of them, asked again
//! with the modules they read until they have them.

use prove_it_host::hooks::HookResult;
use prove_it_host::obligations::{fingerprint, obligations};
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

fn items(value: &HostValue) -> Vec<HostValue> {
    match value {
        HostValue::Array(items) => items.clone(),
        _ => panic!("not an array: {value:?}"),
    }
}

/// Calls `export` with what `read` gives for each key it asks for until it returns something
/// else, and returns that with the keys it asked for, in order.
fn read_all(
    export: impl Fn(HostValue) -> HookResult,
    read: impl Fn(&str) -> Option<String>,
) -> (HostValue, Vec<String>) {
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
        let result = export(HostValue::Array(entries)).expect("a result");
        if text(&get(&result, "kind")) != "needed" {
            return (result, asked);
        }
        for key in items(&get(&result, "keys")).iter().map(text) {
            asked.push(key.clone());
            known.push((key.clone(), read(&key)));
        }
    }
}

fn get_obligations(
    source: &str,
    encode: &[(f64, &str)],
    read: impl Fn(&str) -> Option<String>,
) -> (HostValue, Vec<String>) {
    let encode = HostValue::Array(
        encode
            .iter()
            .map(|(index, prover)| {
                HostValue::Array(vec![HostValue::Number(*index), HostValue::text(prover)])
            })
            .collect(),
    );
    read_all(
        |known| {
            obligations(&[
                HostValue::text("Main.tla"),
                HostValue::text(source),
                known,
                encode.clone(),
            ])
        },
        read,
    )
}

const MAIN: &str = "---- MODULE Main ----\nEXTENDS Naturals, Lib, TLAPS\nTHEOREM X = 1 BY SMT DEF X\nTHEOREM ASSUME NEW x \\in Nat PROVE x + 0 = x BY Zenon\n====\n";

fn read_library(key: &str) -> Option<String> {
    match key {
        "module:Lib#1" => Some("---- MODULE Lib ----\nX == 1\n====\n".to_owned()),
        "path:Lib#1" => Some("/library/Lib.tla".to_owned()),
        _ => None,
    }
}

#[test]
fn prints_the_obligations_once_it_has_the_modules_they_read() {
    let (result, asked) = get_obligations(MAIN, &[], read_library);
    assert_eq!(text(&get(&result, "kind")), "obligations");
    assert!(asked.contains(&"module:Lib#1".to_owned()), "{asked:?}");
    assert!(asked.contains(&"path:Lib#1".to_owned()), "{asked:?}");
    let printed = items(&get(&result, "obligations"));
    let first = &printed[0];
    assert_eq!(get(first, "id"), HostValue::Number(1.0));
    assert_eq!(text(&get(first, "kind")), "Main");
    assert_eq!(
        text(&get(first, "text")),
        "ASSUME X == 1,\n       SMT \nPROVE  X = 1\n"
    );
    let methods = items(&get(first, "methods"));
    assert_eq!(text(&get(&methods[0], "prover")), "smt");
    assert_eq!(get(&methods[0], "timeLimitMs"), HostValue::Number(5000.0));
    assert_eq!(items(&get(&result, "encodings")), Vec::new());
}

// TLAPS, which the reader doesn't have, is the one the obligations know, as prove's is.
#[test]
fn knows_tlaps() {
    let (result, asked) = get_obligations(MAIN, &[], read_library);
    assert!(asked.contains(&"module:TLAPS#1".to_owned()), "{asked:?}");
    assert_eq!(text(&get(&result, "kind")), "obligations");
}

// The SMT encoder numbers the CASE errors it standardizes across what it encodes in turn.
#[test]
fn counts_the_case_errors_across_the_encodings() {
    let source = "---- MODULE Main ----\nEXTENDS Naturals, TLAPS\nTHEOREM ASSUME NEW x PROVE (CASE x = 1 -> 2) = 2 BY SMT\n====\n";
    let encode = |requests: &[(f64, &str)]| {
        let (result, _) = get_obligations(source, requests, |_| None);
        items(&get(&result, "encodings"))
            .iter()
            .map(|encoding| text(&get(encoding, "text")))
            .collect::<Vec<_>>()
    };
    let twice = encode(&[(0.0, "smt"), (0.0, "smt")]);
    assert_eq!(twice[0], encode(&[(0.0, "smt")])[0]);
    assert_ne!(twice[0], twice[1]);
}

// Where MAIN's Zenon obligation is among its obligations.
const ZENON_INDEX: f64 = 2.0;

#[test]
fn encodes_each_obligation_asked_for_in_turn() {
    let (result, _) = get_obligations(
        MAIN,
        &[(ZENON_INDEX, "zenon"), (0.0, "smt"), (0.0, "cvc4")],
        read_library,
    );
    let encodings = items(&get(&result, "encodings"));
    assert_eq!(encodings.len(), 3);
    assert_eq!(text(&get(&encodings[0], "kind")), "text");
    assert!(text(&get(&encodings[0], "text")).contains("$goal"));
    assert!(text(&get(&encodings[1], "text")).contains("(check-sat)"));
    assert_eq!(text(&get(&encodings[2], "kind")), "error");
    assert_eq!(text(&get(&encodings[2], "name")), "TlaUnsupportedError");
    assert_eq!(text(&get(&encodings[2], "message")), "the cvc4 backend");
}

#[test]
fn refuses_an_obligation_it_does_not_have() {
    let result = obligations(&[
        HostValue::text("Main.tla"),
        HostValue::text("---- MODULE Main ----\n====\n"),
        HostValue::Array(Vec::new()),
        HostValue::Array(vec![HostValue::Array(vec![
            HostValue::Number(1.0),
            HostValue::text("smt"),
        ])]),
    ]);
    assert_eq!(
        result,
        Err("there is no obligation at 1 to encode".to_owned())
    );
}

// An error names the file the module came from.
#[test]
fn fails_as_the_obligations_do() {
    let (result, _) =
        get_obligations(
            "---- MODULE Main ----\nEXTENDS Lib\n====\n",
            &[],
            |key| match key {
                "module:Lib#1" => Some("---- MODULE Lib ----\nX == == 1\n====\n".to_owned()),
                "path:Lib#1" => Some("/library/Lib.tla".to_owned()),
                _ => None,
            },
        );
    assert_eq!(text(&get(&result, "kind")), "error");
    assert!(
        text(&get(&result, "message")).contains("/library/Lib.tla"),
        "{result:?}"
    );
}

#[test]
fn fingerprints_each_obligation() {
    let source = "---- MODULE Main ----\nEXTENDS Naturals\nTHEOREM \\A x \\in Nat : x + 0 = x\n  OBVIOUS\nTHEOREM \\A y \\in Nat : y + 0 = y\n  OBVIOUS\n====\n";
    let (result, _) = read_all(
        |known| fingerprint(&[HostValue::text("Main.tla"), HostValue::text(source), known]),
        |_| None,
    );
    assert_eq!(text(&get(&result, "kind")), "fingerprints");
    let fingerprints = items(&get(&result, "fingerprints"));
    assert_eq!(get(&fingerprints[0], "id"), HostValue::Number(1.0));
    assert_eq!(get(&fingerprints[1], "id"), HostValue::Number(2.0));
    let first = text(&get(&fingerprints[0], "fingerprint"));
    assert_eq!(first.len(), 32);
    assert_eq!(first, text(&get(&fingerprints[1], "fingerprint")));
}

// A submodule's own result comes first, its ids starting at 1, so id 1 is its theorem there and the
// module's first theorem in the module's result: an obligation is asked for by its place.
#[test]
fn encodes_the_obligation_at_its_place_where_ids_repeat() {
    let source = "---- MODULE Main ----\nEXTENDS Naturals, TLAPS\nTHEOREM 3 = 3 BY Zenon\n---- MODULE Inner ----\nEXTENDS Naturals, TLAPS\nTHEOREM 1 = 1 BY Zenon\n====\nTHEOREM 2 = 2 BY Zenon\n====\n";
    let (result, _) = get_obligations(source, &[], |_| None);
    let obligations = items(&get(&result, "obligations"));
    let ids = obligations
        .iter()
        .map(|obligation| get(obligation, "id"))
        .collect::<Vec<_>>();
    let places = (0..obligations.len())
        .map(|index| (index as f64, "zenon"))
        .collect::<Vec<_>>();
    let (encoded, _) = get_obligations(source, &places, |_| None);
    let texts = items(&get(&encoded, "encodings"))
        .iter()
        .map(|encoding| text(&get(encoding, "text")))
        .collect::<Vec<_>>();
    let first = ids
        .iter()
        .position(|id| *id == HostValue::Number(1.0))
        .expect("an obligation 1");
    let last = ids
        .iter()
        .rposition(|id| *id == HostValue::Number(1.0))
        .expect("an obligation 1");
    assert_ne!(first, last);
    assert_ne!(texts[first], texts[last]);
}
