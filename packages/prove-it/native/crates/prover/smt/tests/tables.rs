//! prove-smt's foundation against the TypeScript it ports: the tables
//! `scripts/smt-foundation-tables.ts` recorded from `hash.ts`, `hashtable.ts` and `random-gen.ts`.

use prove_smt::util::hash::{
    ast_array_hash, combine_hash, get_composite_hash, hash_u, mk_mix, string_hash,
};
use prove_smt::util::hashtable::{ObjMap, get_identity_hash};
use prove_smt::util::random_gen::RandomGen;

fn number(text: &str) -> u32 {
    text.parse().unwrap()
}

fn numbers(text: &str) -> Vec<u32> {
    text.split(',')
        .filter(|item| !item.is_empty())
        .map(number)
        .collect()
}

/// A JSON string of the table: printable ASCII escaped by `JSON.stringify`, or other characters.
fn unquote(text: &str) -> String {
    let inner = &text[1..text.len() - 1];
    let mut result = String::new();
    let mut characters = inner.chars();
    while let Some(character) = characters.next() {
        if character != '\\' {
            result.push(character);
            continue;
        }
        match characters.next() {
            Some('"') => result.push('"'),
            Some('\\') => result.push('\\'),
            other => panic!("unexpected escape {other:?} in {text}"),
        }
    }
    result
}

#[test]
fn hashes_are_z3s() {
    let table = include_str!("tables/hash.txt");
    let keys: Vec<u32> = table
        .lines()
        .filter_map(|line| line.strip_prefix("u "))
        .map(|rest| number(rest.split(' ').next().unwrap()))
        .collect();
    for line in table.lines() {
        let fields: Vec<&str> = line.splitn(4, ' ').collect();
        match fields[0] {
            "u" => assert_eq!(hash_u(number(fields[1])), number(fields[2]), "{line}"),
            "combine" => assert_eq!(
                combine_hash(number(fields[1]), number(fields[2])),
                number(fields[3]),
                "{line}"
            ),
            "mix" => {
                let fields: Vec<&str> = line.split(' ').collect();
                assert_eq!(
                    mk_mix(number(fields[1]), number(fields[2]), number(fields[3])),
                    number(fields[4]),
                    "{line}"
                );
            }
            "string" => assert_eq!(
                string_hash(&unquote(fields[3]), number(fields[1])),
                number(fields[2]),
                "{line}"
            ),
            "composite" => assert_eq!(
                get_composite_hash(
                    &numbers(fields.get(3).copied().unwrap_or("")),
                    number(fields[1])
                ),
                number(fields[2]),
                "{line}"
            ),
            "array" => assert_eq!(
                ast_array_hash(
                    &numbers(fields.get(3).copied().unwrap_or("")),
                    |item| keys[item as usize],
                    number(fields[1])
                ),
                number(fields[2]),
                "{line}"
            ),
            kind => panic!("unknown kind {kind}"),
        }
    }
}

#[test]
fn hash_tables_iterate_in_z3s_slot_order() {
    let table = include_str!("tables/hashtable.txt");
    for label in ["identity", "hashed"] {
        let get_hash: fn(u32) -> u32 = if label == "identity" {
            get_identity_hash
        } else {
            hash_u
        };
        let mut map = ObjMap::new();
        let mut records = table
            .lines()
            .filter(|line| line.starts_with(&format!("{label} ")))
            .peekable();
        let operations = include_str!("tables/hashtable-operations.txt");
        for line in operations
            .lines()
            .filter(|line| line.starts_with(&format!("{label} ")))
        {
            let fields: Vec<&str> = line.split(' ').collect();
            let key = number(fields[2]);
            let step = number(fields[3]);
            match fields[1] {
                "set" => map.insert(key, get_hash(key), step),
                "delete" => map.remove(key, get_hash(key)),
                "replace" => map.replace(key, get_hash(key), step),
                "clear" => map.clear(),
                operation => panic!("unknown operation {operation}"),
            }
            let Some(record) = records.next_if(|record| {
                let fields: Vec<&str> = record.split(' ').collect();
                fields[1] == step.to_string()
            }) else {
                continue;
            };
            let expected = record.split(' ').nth(2).unwrap_or("");
            let actual = map
                .iter()
                .map(|(key, value)| format!("{key}:{value}"))
                .collect::<Vec<_>>()
                .join(",");
            assert_eq!(actual, expected, "{record}");
            assert_eq!(
                map.len(),
                expected
                    .split(',')
                    .filter(|entry| !entry.is_empty())
                    .count()
            );
        }
        assert!(records.next().is_none(), "{label}: records left over");
    }
}

#[test]
fn the_random_generator_is_z3s() {
    let mut unseeded = RandomGen::new(0);
    let mut seeded = RandomGen::new(123_456_789);
    for line in include_str!("tables/random-gen.txt").lines() {
        let fields: Vec<&str> = line.split(' ').collect();
        assert_eq!(unseeded.next(), number(fields[0]), "{line}");
        assert_eq!(seeded.next(), number(fields[1]), "{line}");
    }
}
