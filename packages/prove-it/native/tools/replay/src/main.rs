//! Replays what the TypeScript engine recorded on the Rust store, and reports the first line whose
//! result differs:
//!
//! - `replay store <trace>...` runs each operation of a trace `PROVE_IT_STORE_TRACE` wrote, as
//!   `scripts/store-replay.ts` does on the TypeScript store, and checks every id, comparison and
//!   reason to stop;
//! - `replay fingerprints <log>...` interns each state of a log `PROVE_IT_STATE_LOG` wrote, or the
//!   key it was fingerprinted by, and checks TLC's fingerprint of it, from the state's parent as the
//!   engine computes it and from scratch.
//!
//! Both read a file a line at a time, so a trace larger than memory replays.

mod json;

use std::fs::File;
use std::io::{BufRead, BufReader};
use std::process::ExitCode;

use json::{Json, parse};
use tla_values::fingerprint::Fingerprints;
use tla_values::trace::{Answer, Argument, Failure, perform};
use tla_values::transfer::{EncodedStates, decode_states};
use tla_values::{Id, Store};

fn read_lines(
    path: &str,
    mut visit: impl FnMut(usize, &str) -> Result<(), String>,
) -> Result<usize, String> {
    let file = File::open(path).map_err(|error| format!("{path}: {error}"))?;
    let mut reader = BufReader::with_capacity(1 << 20, file);
    let mut line = String::new();
    let mut number = 0;
    loop {
        line.clear();
        if reader
            .read_line(&mut line)
            .map_err(|error| format!("{path}: {error}"))?
            == 0
        {
            return Ok(number);
        }
        number += 1;
        let text = line.trim_end_matches(['\n', '\r']);
        if !text.is_empty() {
            visit(number, text).map_err(|error| format!("{path}:{number}: {error}"))?;
        }
    }
}

fn to_argument(value: &Json) -> Result<Argument, String> {
    Ok(match value {
        Json::Number(number) => Argument::Number(*number),
        Json::String(text) => Argument::Text(text.clone()),
        Json::Array(items)
            if items.iter().all(|item| matches!(item, Json::String(_))) && !items.is_empty() =>
        {
            Argument::Texts(
                items
                    .iter()
                    .filter_map(|item| item.as_text().map(<[u16]>::to_vec))
                    .collect(),
            )
        }
        Json::Array(items) => Argument::Numbers(
            items
                .iter()
                .map(|item| item.as_number().ok_or("an array of mixed values"))
                .collect::<Result<_, _>>()?,
        ),
        _ => return Err(format!("an argument {value:?}")),
    })
}

fn format_result(result: &Result<Answer, Failure>) -> String {
    match result {
        Ok(Answer::Null) => "null".into(),
        Ok(Answer::Bool(value)) => value.to_string(),
        Ok(Answer::Number(value)) => value.to_string(),
        Err(Failure::Bail(bail)) => format!("{{\"bail\":{:?}}}", bail.0),
        Err(Failure::Argument(error)) => format!("an error: {error}"),
    }
}

fn is_expected(result: &Result<Answer, Failure>, expected: &Json) -> bool {
    match (result, expected) {
        (Ok(Answer::Null), Json::Null) => true,
        (Ok(Answer::Bool(value)), Json::Bool(other)) => value == other,
        (Ok(Answer::Number(value)), Json::Number(other)) => *value as f64 == *other,
        (Err(Failure::Bail(bail)), Json::Object(_)) => {
            expected.get("bail").and_then(Json::as_text)
                == Some(&bail.0.encode_utf16().collect::<Vec<u16>>()[..])
        }
        _ => false,
    }
}

fn replay_trace(path: &str) -> Result<String, String> {
    let mut store = Store::new();
    let mut operations = 0u64;
    read_lines(path, |_, line| {
        let record = parse(line)?;
        let fields = record
            .as_array()
            .filter(|fields| fields.len() == 3)
            .ok_or("not [name, arguments, result]")?;
        let name = String::from_utf16_lossy(fields[0].as_text().ok_or("no operation name")?);
        let arguments = fields[1]
            .as_array()
            .ok_or("no arguments")?
            .iter()
            .map(to_argument)
            .collect::<Result<Vec<_>, _>>()?;
        let result = perform(&mut store, &name, &arguments);
        operations += 1;
        if is_expected(&result, &fields[2]) {
            return Ok(());
        }
        let expected = line
            .rsplit_once(',')
            .map_or("", |(_, rest)| rest.trim_end_matches(']'));
        Err(format!(
            "{name} gave {}, the trace {expected}",
            format_result(&result)
        ))
    })?;
    Ok(format!(
        "{path}: replayed {operations} operations exactly, {} values",
        store.value_count()
    ))
}

fn get_numbers(value: Option<&Json>, what: &str) -> Result<Vec<i64>, String> {
    value
        .and_then(Json::as_array)
        .ok_or(format!("no {what}"))?
        .iter()
        .map(|item| {
            item.as_number()
                .map(|number| number as i64)
                .ok_or(format!("{what} that aren't numbers"))
        })
        .collect()
}

fn get_encoded(words: Option<&Json>, strings: Option<&Json>) -> Result<EncodedStates, String> {
    Ok(EncodedStates {
        words: get_numbers(words, "words")?
            .into_iter()
            .map(|word| word as i32)
            .collect(),
        strings: strings
            .and_then(Json::as_array)
            .ok_or("no strings")?
            .iter()
            .map(|text| {
                text.as_text()
                    .map(<[u16]>::to_vec)
                    .ok_or("a string that isn't one")
            })
            .collect::<Result<_, _>>()?,
        count: 1,
    })
}

fn replay_log(path: &str) -> Result<String, String> {
    let mut store = Store::new();
    let mut keys: Vec<Id> = Vec::new();
    let mut parents: Vec<i32> = Vec::new();
    let mut logged: Vec<u64> = Vec::new();
    let mut shape: Option<(usize, Vec<usize>, bool)> = None;
    read_lines(path, |_, line| {
        let record = parse(line)?;
        let Some((width, _, is_keyed)) = &shape else {
            let order = get_numbers(record.get("order"), "order (a log from before M2)")?;
            let strings = record
                .get("strings")
                .and_then(Json::as_array)
                .ok_or("no strings")?;
            store.reset(strings.iter().filter_map(Json::as_text));
            let key_width = record.get("keyWidth").and_then(Json::as_number);
            let width = match key_width {
                Some(width) => width as usize,
                None => record
                    .get("variables")
                    .and_then(Json::as_array)
                    .ok_or("no variables")?
                    .len(),
            };
            shape = Some((
                width,
                order.into_iter().map(|index| index as usize).collect(),
                key_width.is_some(),
            ));
            return Ok(());
        };
        let fields = record.as_array().ok_or("not a state")?;
        let (words, strings) = if *is_keyed {
            (fields.get(6), fields.get(7))
        } else {
            (fields.get(4), fields.get(5))
        };
        let encoded = get_encoded(words, strings)?;
        keys.extend(
            decode_states(&mut store, &encoded, *width).map_err(|error| format!("{error:?}"))?,
        );
        parents.push(fields.get(1).and_then(Json::as_number).ok_or("no parent")? as i32);
        let fingerprint = fields
            .get(3)
            .and_then(Json::as_text)
            .ok_or("no fingerprint")?;
        logged.push(
            u64::from_str_radix(&String::from_utf16_lossy(fingerprint), 16)
                .map_err(|error| error.to_string())?,
        );
        Ok(())
    })?;
    let (width, order, _) = shape.ok_or("an empty log")?;
    let mut fingerprints = Fingerprints::new();
    let from_parents = fingerprints.get_states(&store, &keys, width, &order, Some(&parents));
    let reference = fingerprints.get_states_reference(&store, &keys, width, &order);
    for (index, &expected) in logged.iter().enumerate() {
        for (how, fingerprints) in [
            ("from its parent", &from_parents),
            ("from scratch", &reference),
        ] {
            if fingerprints[index] != expected {
                return Err(format!(
                    "{path}: state {index}'s fingerprint {how} is {:016x}, the log's {expected:016x}",
                    fingerprints[index]
                ));
            }
        }
    }
    Ok(format!(
        "{path}: fingerprinted {} states as the log does",
        logged.len()
    ))
}

fn main() -> ExitCode {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let replay = match arguments.first().map(String::as_str) {
        Some("store") => replay_trace,
        Some("fingerprints") => replay_log,
        _ => {
            eprintln!("usage: replay store <trace>... | replay fingerprints <state log>...");
            return ExitCode::from(2);
        }
    };
    let mut is_exact = true;
    for path in &arguments[1..] {
        match replay(path) {
            Ok(summary) => println!("{summary}"),
            Err(error) => {
                println!("{error}");
                is_exact = false;
            }
        }
    }
    if is_exact {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}
