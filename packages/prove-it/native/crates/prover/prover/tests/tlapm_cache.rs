//! The OCaml Marshal format and tlapm's fingerprints file against what the TypeScript writes, as
//! `scripts/tlapm-cache-fixtures.ts` records it in `tests/fixtures`, and `tlapm-cache.test.ts`.

use std::fs;
use std::path::{Path, PathBuf};

use prove_it_prover::tlapm_cache::{FingerprintTable, KnownResults, LocalTime, load_fingerprints};
use prove_obligations::marshal::{MarshalValue, read_marshaled, write_marshaled};

const VERSION: &str = "tla-ts 0.3.0";

const NOW: LocalTime = LocalTime {
    year: 2026,
    month: 10,
    day: 10,
    hours: 12,
    minutes: 0,
    seconds: 0,
};

fn fixture(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures")
        .join(name)
}

fn from_hex(text: &str) -> Vec<u8> {
    (0..text.len())
        .step_by(2)
        .map(|index| u8::from_str_radix(&text[index..index + 2], 16).expect("hex"))
        .collect()
}

fn temporary(name: &str) -> PathBuf {
    let directory =
        std::env::temp_dir().join(format!("prove-it-tlapm-cache-{}", std::process::id()));
    fs::create_dir_all(&directory).expect("a temporary directory");
    directory.join(name)
}

fn read_values(path: &Path) -> (MarshalValue, MarshalValue) {
    let bytes = fs::read(path).expect("the file");
    let (magic, next) = read_marshaled(&bytes, 0).expect("the magic number");
    (magic, read_marshaled(&bytes, next).expect("the table").0)
}

fn resave(input: &Path, output: &Path) {
    let mut table = FingerprintTable::new();
    load_fingerprints(&mut table, input, false, VERSION).expect("a fingerprints file");
    KnownResults::new(&table)
        .save(&mut table, output, VERSION, NOW)
        .expect("saved");
}

#[test]
fn marshal_writes_and_reads_what_the_typescript_does() {
    let lines = fs::read_to_string(fixture("marshal.txt")).expect("marshal.txt");
    let mut count = 0;
    for line in lines.lines() {
        let (input, rewritten) = line.split_once(' ').expect("two fields");
        let (value, next) = read_marshaled(&from_hex(input), 0).expect("readable");
        assert_eq!(next, input.len() / 2, "{line}");
        assert_eq!(write_marshaled(&value), from_hex(rewritten), "{line}");
        let (again, _) = read_marshaled(&from_hex(rewritten), 0).expect("readable");
        assert_eq!(write_marshaled(&again), from_hex(rewritten), "{line}");
        count += 1;
    }
    assert_eq!(count, 54);
}

#[test]
fn marshal_refuses_what_is_cut_short_or_not_marshaled() {
    let line = fs::read_to_string(fixture("marshal.txt")).expect("marshal.txt");
    let input = from_hex(
        line.lines()
            .last()
            .expect("a line")
            .split(' ')
            .next()
            .expect("hex"),
    );
    for cut in [0, 4, 19, 20, input.len() - 1] {
        assert!(read_marshaled(&input[..cut], 0).is_err(), "cut at {cut}");
    }
    assert!(read_marshaled(&[0; 24], 0).is_err());
    // A shared reference to no value before it: distance 0, or past the first value.
    for data in [[0x04, 0x00], [0x04, 0x01], [0x05, 0x00]] {
        let mut input = from_hex("8495a6be000000020000000000000000000000000000");
        input[7] = data.len() as u8;
        input.truncate(20);
        input.extend(data);
        assert!(read_marshaled(&input, 0).is_err(), "{data:?}");
    }
}

#[test]
fn fingerprints_files_save_as_the_typescript_saves_them() {
    for name in [
        "failures-tlapm",
        "failures",
        "failures-nofp",
        "twice",
        "twice-nofp",
    ] {
        let output = temporary(&format!("{name}.saved"));
        resave(&fixture(&format!("{name}.fingerprints")), &output);
        let expected = fs::read(fixture(&format!("{name}.resaved"))).expect("resaved");
        assert_eq!(fs::read(&output).expect("saved"), expected, "{name}");
        resave(&output, &output);
        assert_eq!(
            fs::read(&output).expect("saved"),
            expected,
            "{name} saved twice"
        );
    }
}

// tlapm-cache.test.ts, on the fingerprints tlapm 9ed0376 wrote for tlapm-cli/Failures.tla.

fn get_provers(is_safe: bool) -> Vec<String> {
    let mut table = FingerprintTable::new();
    load_fingerprints(
        &mut table,
        &fixture("failures-tlapm.fingerprints"),
        is_safe,
        VERSION,
    )
    .expect("a fingerprints file");
    let mut provers: Vec<String> = KnownResults::new(&table)
        .results
        .values()
        .flat_map(|known| known.attempts.keys().cloned().collect::<Vec<_>>())
        .collect();
    provers.sort();
    provers
}

#[test]
fn writes_back_what_it_reads_in_the_buckets_tlapm_hashes_each_fingerprint_into() {
    let output = temporary("fingerprints");
    resave(&fixture("failures-tlapm.fingerprints"), &output);
    assert_eq!(
        read_values(&output),
        read_values(&fixture("failures-tlapm.fingerprints"))
    );
}

#[test]
fn reads_what_each_prover_concluded() {
    assert_eq!(get_provers(false), ["isabelle", "smt", "zenon", "zenon"]);
}

#[test]
fn trusts_no_zenon_or_isabelle_result_of_other_versions_under_safefp() {
    assert_eq!(get_provers(true), ["smt"]);
}

// Thirty blocks, each holding its child twice, the second time by a shared reference: a DAG of
// thirty nodes that reads back as one, not as a tree of 2^30.
#[test]
fn marshal_keeps_shared_blocks_shared() {
    let mut data = vec![0xa0, 0x40, 0x40];
    for level in 2..=30u8 {
        data.insert(0, 0xa0);
        data.extend([0x04, level - 1]);
    }
    let mut input = from_hex("8495a6be0000000000000000000000000000000000000000");
    input.truncate(20);
    input[4..8].copy_from_slice(&(data.len() as u32).to_be_bytes());
    input.extend(&data);
    let (mut value, _) = read_marshaled(&input, 0).expect("readable");
    let mut depth = 0;
    while let MarshalValue::Block(inner) = value {
        let first = inner.fields[0].clone();
        match (&first, &inner.fields[1]) {
            (MarshalValue::Block(left), MarshalValue::Block(right)) => {
                assert!(std::rc::Rc::ptr_eq(left, right), "shared at depth {depth}");
            }
            _ => assert_eq!(depth, 29),
        }
        value = first;
        depth += 1;
    }
    assert_eq!(depth, 30);
}

fn nested(depth: usize) -> Vec<u8> {
    let mut input = from_hex("8495a6be0000000000000000000000000000000000000000");
    input.truncate(20);
    input[4..8].copy_from_slice(&(depth as u32 + 1).to_be_bytes());
    input.extend(std::iter::repeat_n(0x90, depth));
    input.push(0x40);
    input
}

// Blocks nested 256 deep read, compare and drop within a test thread's stack; deeper ones
// are corrupt, not a stack overflow.
#[test]
fn marshal_bounds_how_deep_blocks_nest() {
    let input = nested(256);
    let (value, _) = read_marshaled(&input, 0).expect("readable");
    let (again, _) = read_marshaled(&input, 0).expect("readable");
    assert!(value == again);
    drop(value);
    for depth in [257, 50_000] {
        assert!(read_marshaled(&nested(depth), 0).is_err(), "{depth}");
    }
}

// Headers that claim more than the input holds: a block of four million fields and a string of
// 4 GB, each in a few bytes. Both are corrupt, found before anything is reserved for them.
#[test]
fn marshal_refuses_sizes_the_input_cannot_hold() {
    for data in [
        vec![0x08, 0xff, 0xff, 0xfc, 0x00, 0x40],
        vec![0x0a, 0xff, 0xff, 0xff, 0xff, 0x61],
    ] {
        let mut input = from_hex("8495a6be0000000000000000000000000000000000000000");
        input.truncate(20);
        input[4..8].copy_from_slice(&(data.len() as u32).to_be_bytes());
        input.extend(&data);
        assert!(read_marshaled(&input, 0).is_err(), "{data:?}");
    }
}

// Sibling blocks, each holding the one before it by a shared reference: the encoding nests two
// levels, but the value is a chain as long as the list. Up to 256 it reads, compares and drops;
// longer is corrupt.
fn chained(length: usize) -> Vec<u8> {
    let mut data = vec![0x08];
    data.extend(((length as u32) << 10).to_be_bytes());
    data.extend([0x90, 0x40]);
    for _ in 1..length {
        data.extend([0x90, 0x04, 0x02]);
    }
    let mut input = from_hex("8495a6be0000000000000000000000000000000000000000");
    input.truncate(20);
    input[4..8].copy_from_slice(&(data.len() as u32).to_be_bytes());
    input.extend(data);
    input
}

#[test]
fn marshal_bounds_how_deep_shared_references_chain() {
    let input = chained(255);
    let (value, _) = read_marshaled(&input, 0).expect("readable");
    let (again, _) = read_marshaled(&input, 0).expect("readable");
    assert!(value == again);
    drop(value);
    for length in [256, 50_000] {
        assert!(read_marshaled(&chained(length), 0).is_err(), "{length}");
    }
}
