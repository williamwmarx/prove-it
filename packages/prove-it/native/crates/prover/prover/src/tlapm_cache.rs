//! tlapm's fingerprints file, ported from src/backend/fpfile.ml through `src/prover/tlapm/cache.ts`.
//!
//! It reads and writes the file's bytes, which the caller reads and writes where its host keeps
//! them. The caller also passes the clock and the version: `version` is what Prove It stores as
//! `tla-ts <package version>`, and `now` the local time.

use prove_obligations::errors::{ObligationError, Result};
use prove_obligations::marshal::{MarshalValue, block, read_marshaled, write_marshaled};
use prove_obligations::prep::methods::Method;
use prove_obligations::ship::ProofAttempt;
use prove_smt::util::ordered_map::OrderedMap;

use crate::driver::Attempt;

/// One optional result per prover, in V13.str's order, by fingerprint, in the order they were set.
pub type FingerprintTable = OrderedMap<String, Vec<MarshalValue>>;

/// A local date and time, with the month counted from 0, as JavaScript's `Date` gives it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LocalTime {
    pub year: i64,
    pub month: i64,
    pub day: i64,
    pub hours: i64,
    pub minutes: i64,
    pub seconds: i64,
}

const MAGIC_NUMBER: i64 = 20210223;

const RECORD_SIZE: usize = 23;

// Each prover's field in V13.str and constructor in V13.meth, in the order the TypeScript's
// `PROVERS` lists them.
const PROVERS: [(&str, usize, u8); 5] = [
    ("zenon", 1, 1),
    ("isabelle", 2, 0),
    ("smt", 10, 8),
    ("z3", 11, 9),
    ("ls4", 17, 16),
];

const FAIL_METHOD: i64 = 5;

const REASONS: [&str; 2] = ["false", "timeout"];

// The fields of V13.str whose version --safefp compares: Zenon's and Isabelle's.
const CHECKED_VERSIONS: [(usize, usize); 2] = [(1, 3), (2, 4)];

fn corrupted() -> ObligationError {
    ObligationError::proof("corrupted fingerprint file")
}

fn get_prover(prover: &str) -> Option<(usize, u8)> {
    PROVERS
        .iter()
        .find(|known| known.0 == prover)
        .map(|known| (known.1, known.2))
}

fn get_field(value: Option<&MarshalValue>, index: usize) -> Option<&MarshalValue> {
    match value {
        Some(MarshalValue::Block(inner)) => inner.fields.get(index),
        _ => None,
    }
}

fn get_float(value: Option<&MarshalValue>) -> f64 {
    match value {
        Some(MarshalValue::Float(float)) => *float,
        _ => f64::INFINITY,
    }
}

// String(value) on what the TypeScript reads: a string, a number, or an object otherwise.
fn get_text(value: Option<&MarshalValue>) -> String {
    match value {
        Some(MarshalValue::Text(text)) => text.clone(),
        Some(MarshalValue::Int(integer)) => integer.to_string(),
        Some(_) => "[object Object]".into(),
        None => "undefined".into(),
    }
}

// Hashtbl.hash on a string.
fn hash_key(key: &str) -> u32 {
    let bytes = key.as_bytes();
    let byte = |index: usize| u32::from(bytes.get(index).copied().unwrap_or(0));
    let mixed = (0..bytes.len().div_ceil(4))
        .map(|index| {
            byte(index * 4)
                | (byte(index * 4 + 1) << 8)
                | (byte(index * 4 + 2) << 16)
                | (byte(index * 4 + 3) << 24)
        })
        .fold(0u32, |hash, word| {
            let data = word
                .wrapping_mul(0xcc9e2d51)
                .rotate_left(15)
                .wrapping_mul(0x1b873593);
            (hash ^ data)
                .rotate_left(13)
                .wrapping_mul(5)
                .wrapping_add(0xe6546b64)
        });
    let length = bytes.len() as u32;
    let first = (mixed ^ length ^ ((mixed ^ length) >> 16)).wrapping_mul(0x85ebca6b);
    let second = (first ^ (first >> 13)).wrapping_mul(0xc2b2ae35);
    (second ^ (second >> 16)) & 0x3fffffff
}

fn read_bucket(entry: Option<&MarshalValue>, pairs: &mut Vec<(MarshalValue, MarshalValue)>) {
    let mut entry = entry;
    while let Some(MarshalValue::Block(inner)) = entry {
        let field = |index: usize| {
            inner
                .fields
                .get(index)
                .cloned()
                .unwrap_or(MarshalValue::Int(0))
        };
        pairs.push((field(0), field(1)));
        entry = inner.fields.get(2);
    }
}

/// Fpfile.load_fingerprints, from the file's bytes. Each bucket lists the latest fingerprint first.
pub fn load_fingerprints(
    table: &mut FingerprintTable,
    bytes: &[u8],
    is_safe: bool,
    version: &str,
) -> Result<()> {
    let (magic, next) = read_marshaled(bytes, 0)?;
    let (contents, _) = read_marshaled(bytes, next)?;
    if magic != MarshalValue::Int(MAGIC_NUMBER)
        || !matches!(&contents, MarshalValue::Block(inner) if inner.tag == 0)
    {
        return Err(corrupted());
    }
    let buckets = get_field(get_field(Some(&contents), 0), 1);
    let is_trusted = |result: &MarshalValue, field: usize| {
        let Some(index) = CHECKED_VERSIONS.iter().find(|checked| checked.0 == field) else {
            return true;
        };
        !is_safe
            || get_field(get_field(Some(result), 0), index.1)
                == Some(&MarshalValue::Text(version.into()))
    };
    table.clear();
    let Some(MarshalValue::Block(buckets)) = buckets else {
        return Ok(());
    };
    for bucket in &buckets.fields {
        let mut pairs = Vec::new();
        read_bucket(Some(bucket), &mut pairs);
        for (key, record) in pairs.into_iter().rev() {
            let (MarshalValue::Text(key), MarshalValue::Block(record)) = (key, record) else {
                return Err(corrupted());
            };
            let fields = record
                .fields
                .iter()
                .enumerate()
                .map(|(field, result)| {
                    if is_trusted(result, field) {
                        result.clone()
                    } else {
                        MarshalValue::Int(0)
                    }
                })
                .collect();
            table.insert(key, fields);
        }
    }
    Ok(())
}

fn decode_result(prover: &str, result: Option<&MarshalValue>) -> Option<Attempt> {
    let status = get_field(result, 0);
    let outcome = get_field(status, 0)?;
    if *outcome == MarshalValue::Int(1) {
        return None;
    }
    let argument = get_field(get_field(status, 1), 0);
    let is_isabelle = prover == "isabelle";
    let seconds = get_float(get_field(
        if is_isabelle {
            get_field(argument, 0)
        } else {
            argument
        },
        0,
    ));
    let tactic = match get_field(argument, 1) {
        Some(MarshalValue::Text(tactic)) if is_isabelle => Some(tactic.clone()),
        _ => None,
    };
    let reason = get_field(get_field(Some(outcome), 0), 0).map(|reason| match reason {
        MarshalValue::Int(index) => usize::try_from(*index)
            .ok()
            .and_then(|index| REASONS.get(index))
            .map(|reason| reason.to_string()),
        other => Some(get_text(get_field(Some(other), 0))),
    });
    Some(Attempt {
        attempt: ProofAttempt {
            method: Method {
                prover: prover.into(),
                time_limit_ms: seconds * 1000.0,
                rlimit: None,
                tactic,
            },
            is_proved: *outcome == MarshalValue::Int(0),
            is_reused: false,
        },
        reason: reason.flatten(),
        verdict: None,
        time_used_ms: None,
    })
}

/// Fpfile.fp_writes, whose date counts months from 0. None for a prover the file has no field for.
fn encode_result(attempt: &Attempt, version: &str, now: LocalTime) -> Option<MarshalValue> {
    let method = &attempt.attempt.method;
    let (_, tag) = get_prover(&method.prover)?;
    let timeout = MarshalValue::Float(
        method
            .rlimit
            .map_or(method.time_limit_ms / 1000.0, |rlimit| rlimit as f64),
    );
    let argument = match method.prover.as_str() {
        "zenon" => block(0, vec![timeout, MarshalValue::Int(FAIL_METHOD)]),
        "isabelle" => block(
            0,
            vec![
                block(0, vec![timeout]),
                MarshalValue::Text(method.tactic.clone().unwrap_or_else(|| "auto".into())),
            ],
        ),
        _ => block(0, vec![timeout]),
    };
    let reason = match &attempt.reason {
        None => MarshalValue::Int(0),
        Some(reason) => block(
            0,
            vec![match REASONS.iter().position(|known| known == reason) {
                Some(index) => MarshalValue::Int(index as i64),
                None => block(0, vec![MarshalValue::Text(reason.clone())]),
            }],
        ),
    };
    let outcome = if attempt.attempt.is_proved {
        MarshalValue::Int(0)
    } else {
        block(0, vec![reason])
    };
    let date = [
        now.year,
        now.month,
        now.day,
        now.hours,
        now.minutes,
        now.seconds,
    ]
    .map(MarshalValue::Int);
    Some(block(
        0,
        vec![block(
            0,
            vec![
                block(0, vec![outcome, block(tag, vec![argument])]),
                block(0, date.to_vec()),
                MarshalValue::Text(version.into()),
                MarshalValue::Text(version.into()),
                MarshalValue::Text(version.into()),
            ],
        )],
    ))
}

fn encode_table(table: &FingerprintTable) -> MarshalValue {
    let exponent = (table.len() as f64 / 2.0).log2().ceil().max(9.0) as u32;
    let length = 1usize << exponent;
    let mut buckets = vec![MarshalValue::Int(0); length];
    for (fingerprint, record) in table.iter() {
        let index = hash_key(fingerprint) as usize & (length - 1);
        let rest = std::mem::replace(&mut buckets[index], MarshalValue::Int(0));
        buckets[index] = block(
            0,
            vec![
                MarshalValue::Text(fingerprint.clone()),
                block(0, record.clone()),
                rest,
            ],
        );
    }
    block(
        0,
        vec![block(
            0,
            vec![
                MarshalValue::Int(table.len() as i64),
                block(0, buckets),
                MarshalValue::Int(0),
                MarshalValue::Int(512),
            ],
        )],
    )
}

/// A prover's result for a fingerprint, with the field it was loaded from, which saving keeps
/// unchanged; a result recorded since has none and is encoded anew.
#[derive(Clone, Debug)]
pub struct KnownAttempt {
    pub attempt: Attempt,
    stored: Option<MarshalValue>,
}

impl KnownAttempt {
    pub fn new(attempt: Attempt) -> Self {
        Self {
            attempt,
            stored: None,
        }
    }
}

/// What each prover concluded for a fingerprint, with the record it was loaded from, which saving
/// keeps with its date, versions and other provers' results; a fingerprint set anew has none.
#[derive(Clone, Debug, Default)]
pub struct KnownAttempts {
    pub attempts: OrderedMap<String, KnownAttempt>,
    stored: Option<Vec<MarshalValue>>,
}

/// Fpfile.query: what each prover concluded for each fingerprint. The TypeScript keeps the loaded
/// fields in maps keyed by the result objects; here each result carries its own.
#[derive(Clone, Debug, Default)]
pub struct KnownResults {
    pub results: OrderedMap<String, KnownAttempts>,
}

impl KnownResults {
    pub fn new(table: &FingerprintTable) -> Self {
        let mut results = OrderedMap::new();
        for (fingerprint, record) in table.iter() {
            let mut attempts = OrderedMap::new();
            for (prover, field, _) in PROVERS {
                let stored = record.get(field);
                if let Some(attempt) = decode_result(prover, get_field(stored, 0)) {
                    attempts.insert(
                        prover.to_string(),
                        KnownAttempt {
                            attempt,
                            stored: stored.cloned(),
                        },
                    );
                }
            }
            results.insert(
                fingerprint.clone(),
                KnownAttempts {
                    attempts,
                    stored: Some(record.clone()),
                },
            );
        }
        Self { results }
    }

    /// Saving them, as fp_writes, add_to_table and fp_close_and_consolidate do, sets the table to
    /// the results and gives the file's bytes. Fails on a result of a prover the file has no field
    /// for, where the TypeScript throws.
    pub fn save(
        &self,
        table: &mut FingerprintTable,
        version: &str,
        now: LocalTime,
    ) -> Result<Vec<u8>> {
        table.clear();
        for (fingerprint, known) in self.results.iter() {
            let mut record = known
                .stored
                .clone()
                .unwrap_or_else(|| vec![MarshalValue::Int(0); RECORD_SIZE]);
            for (prover, known_attempt) in known.attempts.iter() {
                let (field, _) = get_prover(prover).ok_or_else(|| {
                    ObligationError::proof(format!("no fingerprint field for the prover {prover}"))
                })?;
                let result = match &known_attempt.stored {
                    Some(stored) => stored.clone(),
                    None => encode_result(&known_attempt.attempt, version, now)
                        .expect("the prover has a field"),
                };
                if record.len() <= field {
                    record.resize(field + 1, MarshalValue::Int(0));
                }
                record[field] = result;
            }
            table.insert(fingerprint.clone(), record);
        }
        let mut bytes = write_marshaled(&MarshalValue::Int(MAGIC_NUMBER));
        bytes.extend(write_marshaled(&encode_table(table)));
        Ok(bytes)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn get_int(value: Option<&MarshalValue>) -> i64 {
        match value {
            Some(MarshalValue::Int(integer)) => *integer,
            other => panic!("not an int: {other:?}"),
        }
    }

    // Every result the TypeScript encoded into the fixtures' files, decoded and encoded again at its
    // own date and version, is the value it wrote.
    #[test]
    fn encodes_a_result_as_the_typescript_does() {
        let mut count = 0;
        for name in ["failures", "failures-nofp", "twice", "twice-nofp"] {
            let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("tests/fixtures")
                .join(format!("{name}.fingerprints"));
            let bytes = std::fs::read(path).expect("a fingerprints file");
            let mut table = FingerprintTable::new();
            load_fingerprints(&mut table, &bytes, false, "").expect("a fingerprints file");
            for (_, record) in table.iter() {
                for (prover, field, _) in PROVERS {
                    let stored = record.get(field);
                    let Some(attempt) = decode_result(prover, get_field(stored, 0)) else {
                        continue;
                    };
                    let result = get_field(stored, 0);
                    let date = get_field(result, 1);
                    let now = LocalTime {
                        year: get_int(get_field(date, 0)),
                        month: get_int(get_field(date, 1)),
                        day: get_int(get_field(date, 2)),
                        hours: get_int(get_field(date, 3)),
                        minutes: get_int(get_field(date, 4)),
                        seconds: get_int(get_field(date, 5)),
                    };
                    let Some(MarshalValue::Text(version)) = get_field(result, 2) else {
                        panic!("no version");
                    };
                    assert_eq!(
                        encode_result(&attempt, version, now).as_ref(),
                        stored,
                        "{name} {prover}"
                    );
                    count += 1;
                }
            }
        }
        assert!(count >= 4, "{count} results");
    }
}
