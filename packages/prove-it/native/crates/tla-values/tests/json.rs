//! TLC's Json module over the store, from the fixtures `tests/unit/json.test.ts` checks against
//! TLC's Java Json class.

use tla_values::Store;
use tla_values::json::{read_json, read_nd_json, write_json};

const FIXTURES: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../../../tests/fixtures/json");

fn units(text: &str) -> Vec<u16> {
    text.encode_utf16().collect()
}

fn read_fixture(name: &str) -> Vec<u16> {
    units(&std::fs::read_to_string(format!("{FIXTURES}/{name}")).expect("the fixture"))
}

fn to_json(store: &Store, id: u32) -> String {
    let mut text = Vec::new();
    write_json(store, id, &mut text).expect("JSON");
    String::from_utf16(&text).expect("text")
}

#[test]
fn reads_numbers_as_gson_truncates_them() {
    let mut store = Store::new();
    let numbers = read_json(&mut store, &read_fixture("Numbers.json")).expect("a value");
    let expected: Vec<u32> = [1, -2, 1, -1, 1000, -1294967296, -350287150, 0, 0]
        .iter()
        .map(|&number| store.int(number).expect("an integer"))
        .collect();
    assert_eq!(store.tuple_elements(numbers), expected);
}

#[test]
fn reads_each_line_that_isnt_blank() {
    let mut store = Store::new();
    let lines = read_nd_json(&mut store, &read_fixture("Lines.ndjson")).expect("a value");
    assert_eq!(to_json(&store, lines), r#"[1,[2,"x"],{"a":true}]"#);
    assert!(read_json(&mut store, &read_fixture("Empty.json")).is_err());
}

#[test]
fn writes_records_sequences_and_strings_as_tlc_does() {
    let mut store = Store::new();
    let text = units(r#"{"a":3,"b":{"c":[4,5,6]}}"#);
    let value = read_json(&mut store, &text).expect("a value");
    assert_eq!(to_json(&store, value), r#"{"a":3,"b":{"c":[4,5,6]}}"#);
    // A lone surrogate is Gson's to keep, and TLC's file's UTF-8 encoder writes it as '?'.
    let escaped = units("\"q\\\" \\\\ \\n \\u0001 \\u2028 \\ud83d\"");
    let string = read_json(&mut store, &escaped).expect("a string");
    assert_eq!(
        to_json(&store, string),
        "\"q\\\" \\\\ \\n \\u0001 \\u2028 ?\""
    );
}

#[test]
fn orders_keys_that_are_array_indices_first_as_javascript_does() {
    let mut store = Store::new();
    let value =
        read_json(&mut store, &units(r#"{"b":1,"2":2,"a":3,"b":4,"1":5}"#)).expect("a value");
    // The record holds its keys in TLC's order of strings, which ranks them as they are read.
    assert_eq!(to_json(&store, value), r#"{"1":5,"2":2,"b":4,"a":3}"#);
}

#[test]
fn decline_an_empty_object_tlc_holds_apart_from_the_empty_sequence() {
    let mut store = Store::new();
    for text in ["{}", "[{}]", r#"{"a":{}}"#] {
        assert!(read_json(&mut store, &units(text)).is_err(), "{text}");
    }
    let value = read_json(&mut store, &units("[[]]")).expect("a value");
    assert_eq!(to_json(&store, value), "[[]]");
}

#[test]
fn trim_each_line_as_java_does() {
    // String.trim trims the units up to a space, and Gson reads past one leading byte order mark.
    let mut store = Store::new();
    let value =
        read_nd_json(&mut store, &units("\u{feff}{\"a\":1}\u{b}\r\n \t\n")).expect("a value");
    assert_eq!(to_json(&store, value), r#"[{"a":1}]"#);
    for text in [
        "{\"a\":1}\n\u{a0}\n",
        "\u{3000}{\"a\":1}\n",
        "{\"a\":1}\u{feff}\n",
    ] {
        assert!(read_nd_json(&mut store, &units(text)).is_err(), "{text:?}");
    }
}
