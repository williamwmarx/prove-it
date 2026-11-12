//! `prove`: a file name, source or module that isn't well-formed UTF-16 declines before any
//! decision. Its lone surrogates read as U+FFFD would make different strings one, so that
//! `"\uD800" = "\uDC00"` would be proved.

use prove_it_host::prove::prove;
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

/// Proves in rounds, reading each module from `modules` and answering every decision `unsat`, and
/// returns the last round with every decision's prover and text.
fn prove_all(source: &[u16], modules: &[(&str, Vec<u16>)]) -> (HostValue, Vec<(String, String)>) {
    let mut known: Vec<(String, HostValue)> = Vec::new();
    let mut decided = Vec::new();
    loop {
        let entries = known
            .iter()
            .map(|(key, value)| HostValue::Array(vec![HostValue::text(key), value.clone()]))
            .collect();
        let result = prove(&[
            HostValue::text("M.tla"),
            HostValue::Text(source.to_vec()),
            HostValue::Array(entries),
        ])
        .expect("prove takes its arguments");
        if text(&get(&result, "kind")) != "needed" {
            return (result, decided);
        }
        for key in items(&get(&result, "keys")) {
            let key = text(&key);
            let name = &key["module:".len()..key.rfind('#').expect("a read count")];
            let module = modules
                .iter()
                .find(|(module, _)| *module == name)
                .map_or(HostValue::Undefined, |(_, units)| {
                    HostValue::Text(units.clone())
                });
            known.push((key, module));
        }
        for request in items(&get(&result, "requests")) {
            decided.push((text(&get(&request, "prover")), text(&get(&request, "text"))));
            known.push((
                format!("decide:{}", text(&get(&request, "key"))),
                HostValue::text("unsat 1"),
            ));
        }
    }
}

fn units(text: &str, surrogate: u16) -> Vec<u16> {
    text.encode_utf16()
        .map(|unit| if unit == 0xfffd { surrogate } else { unit })
        .collect()
}

fn get_declined(what: &str) -> HostValue {
    HostValue::Object(vec![
        ("kind", HostValue::text("error")),
        ("name", HostValue::text("TlaUnsupportedError")),
        (
            "message",
            HostValue::text(&format!("not native yet: {what} isn't well-formed UTF-16")),
        ),
    ])
}

const SOURCE: &str = "---- MODULE M ----\nEXTENDS Lib, TLAPS\nTHEOREM \"\u{fffd}\" = Y BY SMT DEF Y\nTHEOREM X BY Zenon DEF X\n====\n";
const LIBRARY: &str =
    "---- MODULE Lib ----\nX == \"\u{fffd}\" = \"\u{fffd}\"\nY == \"\u{fffd}\"\n====\n";

#[test]
fn proves_well_formed_text() {
    let (result, decided) = prove_all(&units(SOURCE, 0xfffd), &[("Lib", units(LIBRARY, 0xfffd))]);
    assert_eq!(text(&get(&result, "kind")), "proved");
    assert_eq!(decided.len(), 2);
}

#[test]
fn declines_a_lone_surrogate_in_the_source_before_reading_a_module() {
    for surrogate in [0xd800, 0xdbff, 0xdc00, 0xdfff] {
        assert_eq!(
            prove_all(
                &units(SOURCE, surrogate),
                &[("Lib", units(LIBRARY, 0xfffd))]
            ),
            (get_declined("the source"), Vec::new())
        );
    }
}

#[test]
fn declines_a_lone_surrogate_in_a_module() {
    for surrogate in [0xd800, 0xdfff] {
        assert_eq!(
            prove_all(
                &units(SOURCE, 0xfffd),
                &[("Lib", units(LIBRARY, surrogate))]
            ),
            (get_declined("the module Lib"), Vec::new())
        );
    }
}

#[test]
fn declines_different_lone_surrogates_rather_than_prove_them_equal() {
    let source: Vec<u16> =
        "---- MODULE M ----\nEXTENDS TLAPS\nTHEOREM \"\u{fffd}\" = \"\u{fffe}\" BY SMT\n====\n"
            .encode_utf16()
            .map(|unit| match unit {
                0xfffd => 0xd800,
                0xfffe => 0xdc00,
                unit => unit,
            })
            .collect();
    assert_eq!(
        prove_all(&source, &[]),
        (get_declined("the source"), Vec::new())
    );
}

#[test]
fn declines_a_lone_surrogate_in_the_file_name() {
    let result = prove(&[
        HostValue::Text(vec![0x4d, 0xd800]),
        HostValue::text("---- MODULE M ----\n====\n"),
        HostValue::Array(Vec::new()),
    ]);
    assert_eq!(result, Ok(get_declined("the file name")));
}
