//! Random sequences of the store's operations, with arguments right and wrong, through
//! `trace::perform`, which must never panic. A second store given the same operations must give
//! the same answers, compare must be antisymmetric, a state's fingerprint must be the same from
//! its parent, the state before and from scratch, and a value read back from transfer.ts's
//! encoding must write the same words again.

#![no_main]

use libfuzzer_sys::fuzz_target;
use tla_values::fingerprint::Fingerprints;
use tla_values::store::Store;
use tla_values::trace::{Answer, Argument, Failure, perform};
use tla_values::transfer::{StateEncoder, decode_states};

// Each operation with its arguments: i an id, I ids, n a number, N numbers, t a text, T texts.
const SIGNATURES: [(&str, &str); 33] = [
    ("resetStore", "T"),
    ("rankStrings", "T"),
    ("int", "n"),
    ("str", "t"),
    ("model", "t"),
    ("compare", "ii"),
    ("equals", "ii"),
    ("setOf", "I"),
    ("setOfRange", "I"),
    ("setOfSorted", "I"),
    ("setOfSortedRange", "I"),
    ("isMember", "ii"),
    ("union", "ii"),
    ("intersection", "ii"),
    ("difference", "ii"),
    ("isSubset", "ii"),
    ("withElement", "ii"),
    ("tupleOf", "I"),
    ("tupleOfRange", "I"),
    ("recordOf", "II"),
    ("functionOfSorted", "II"),
    ("functionOverSet", "iI"),
    ("functionOf", "II"),
    ("findKey", "ii"),
    ("apply", "ii"),
    ("except", "iii"),
    ("exceptAt", "iNI"),
    ("applyField", "ii"),
    ("domainOf", "i"),
    ("sliceTuple", "inn"),
    ("concatTuples", "ii"),
    ("appendTuple", "ii"),
    ("getValueCount", ""),
];

const NUMBERS: [f64; 12] = [
    0.0,
    1.0,
    2.0,
    3.0,
    -1.0,
    4096.0,
    4097.0,
    -257.0,
    2147483647.0,
    -2147483648.0,
    2147483648.0,
    1.5,
];

fn texts() -> Vec<Vec<u16>> {
    let mut texts: Vec<Vec<u16>> = ["a", "b", "zz", "A_x", "B_y", "m", "é", "\u{101}", ""]
        .iter()
        .map(|text| text.encode_utf16().collect())
        .collect();
    texts.push(vec![0xd800]);
    texts
}

struct Bytes<'a>(&'a [u8]);

impl Bytes<'_> {
    fn next(&mut self) -> Option<u8> {
        let (&first, rest) = self.0.split_first()?;
        self.0 = rest;
        Some(first)
    }
}

// An id among those made so far, mostly, or any number.
fn get_id(bytes: &mut Bytes, made: &[f64]) -> Option<f64> {
    let byte = bytes.next()?;
    Some(if byte < 240 && !made.is_empty() {
        made[byte as usize % made.len()]
    } else {
        f64::from(byte) * 37.0
    })
}

fn get_arguments(
    bytes: &mut Bytes,
    signature: &str,
    made: &[f64],
    texts: &[Vec<u16>],
) -> Option<Vec<Argument>> {
    signature
        .chars()
        .map(|kind| {
            Some(match kind {
                'i' => Argument::Number(get_id(bytes, made)?),
                'n' => Argument::Number(NUMBERS[bytes.next()? as usize % NUMBERS.len()]),
                't' => Argument::Text(texts[bytes.next()? as usize % texts.len()].clone()),
                'T' => {
                    let length = bytes.next()? % 6;
                    let chosen = (0..length)
                        .map(|_| Some(texts[bytes.next()? as usize % texts.len()].clone()));
                    Argument::Texts(chosen.collect::<Option<_>>()?)
                }
                'N' => {
                    let length = bytes.next()? % 5;
                    let chosen = (0..length).map(|_| Some(f64::from(bytes.next()? % 5)));
                    Argument::Numbers(chosen.collect::<Option<_>>()?)
                }
                _ => {
                    let length = bytes.next()? % 9;
                    let chosen = (0..length).map(|_| get_id(bytes, made));
                    Argument::Numbers(chosen.collect::<Option<_>>()?)
                }
            })
        })
        .collect()
}

fuzz_target!(|data: &[u8]| {
    let texts = texts();
    let mut bytes = Bytes(data);
    let (mut store, mut other) = (Store::new(), Store::new());
    let mut made: Vec<f64> = Vec::new();
    while let Some(choice) = bytes.next() {
        let (name, signature) = SIGNATURES[choice as usize % SIGNATURES.len()];
        let Some(arguments) = get_arguments(&mut bytes, signature, &made, &texts) else {
            break;
        };
        let answer = perform(&mut store, name, &arguments);
        assert_eq!(
            perform(&mut other, name, &arguments),
            answer,
            "{name} {arguments:?}"
        );
        if name == "resetStore" {
            made.clear();
        }
        if name == "compare"
            && let Ok(Answer::Number(forward)) = answer
            && let Ok(Answer::Number(backward)) = perform(
                &mut store,
                name,
                &[arguments[1].clone(), arguments[0].clone()],
            )
        {
            assert_eq!(forward.signum(), -backward.signum(), "{arguments:?}");
            let _ = perform(
                &mut other,
                name,
                &[arguments[1].clone(), arguments[0].clone()],
            );
        }
        let returns_id = !matches!(
            name,
            "resetStore"
                | "rankStrings"
                | "compare"
                | "equals"
                | "isMember"
                | "isSubset"
                | "findKey"
                | "getValueCount"
        );
        match answer {
            Ok(Answer::Number(id)) if returns_id => made.push(id as f64),
            Err(Failure::Argument(_)) | Err(Failure::Bail(_)) | Ok(_) => {}
        }
    }
    let ids: Vec<u32> = made.iter().map(|&id| id as u32).collect();
    if ids.is_empty() {
        return;
    }
    // States of two values, each from the one before it, as the engine's initial states are.
    let states: Vec<u32> = ids
        .iter()
        .zip(ids.iter().rev())
        .flat_map(|(&left, &right)| [left, right])
        .collect();
    let mut fingerprints = Fingerprints::new();
    let order = [1, 0];
    let scratch: Vec<u64> = states
        .chunks_exact(2)
        .map(|state| fingerprints.get_state(&store, state, &order))
        .collect();
    assert_eq!(
        fingerprints.get_states(&store, &states, 2, &order, None),
        scratch
    );
    assert_eq!(
        Fingerprints::new().get_states_reference(&store, &states, 2, &order),
        scratch
    );
    // A value read back is normalized, so reading it back again changes nothing. The encoding
    // writes a value as a tree, which a value that shares its parts, such as <<x, x>> nested 30
    // deep, makes exponential, so only values whose trees TLC would fingerprint in under a
    // megabyte are written.
    let bytes: u64 = ids
        .iter()
        .map(|&id| fingerprints.get_value(&store, id).1)
        .sum();
    if bytes > 1 << 20 {
        return;
    }
    let mut encoder = StateEncoder::new();
    encoder.encode(&store, &ids);
    let encoded = encoder.finish();
    let mut first = Store::new();
    let Ok(read) = decode_states(&mut first, &encoded, ids.len()) else {
        return;
    };
    let mut again = StateEncoder::new();
    again.encode(&first, &read);
    let rewritten = again.finish();
    let mut second = Store::new();
    let reread =
        decode_states(&mut second, &rewritten, ids.len()).expect("a value read back reads again");
    let mut last = StateEncoder::new();
    last.encode(&second, &reread);
    assert_eq!(last.finish(), rewritten);
});
