//! Where TLC fails to fingerprint a value (`fingerprint` and `size` of its values): a power set of
//! a set of 31 elements or more, whose size overflows an int (`SubsetValue.size`), and a union it
//! can't enumerate (`SetCupValue.fingerPrint`).

use tla_values::fingerprint::Fingerprints;

use crate::print::format_pretty;
use crate::value::{Lazy, TlcMessage, Value, elements};

/// `EC.TLC_MODULE_OVERFLOW`.
const OVERFLOW: u32 = 2178;

/// Whether a fingerprint of a value fails, and if so the values it fails in, outermost first,
/// with TLC's message. `Err` where the evaluator doesn't know whether TLC fails: a lazy set it
/// doesn't size.
pub fn fingerprint_failure(value: &Value) -> Result<Option<(Vec<Value>, TlcMessage)>, ()> {
    let held: Vec<&Value> = match value {
        Value::Set(elements) => elements.iter().collect(),
        Value::Function(function) => function.domain.iter().chain(&function.range).collect(),
        Value::Lazy(lazy) => match &**lazy {
            Lazy::Subset(base) => {
                // TLC sizes the power set by its base, which it sizes first.
                if let Some((mut chain, message)) = fingerprint_failure(base)? {
                    chain.insert(0, value.clone());
                    return Ok(Some((chain, message)));
                }
                if size(base)? >= 31 {
                    let message = TlcMessage {
                        text: format!(
                            "Overflow when computing the number of elements in:\n{}",
                            format_pretty(value)
                        ),
                        code: Some(OVERFLOW),
                        is_eval_exception: false,
                    };
                    return Ok(Some((vec![value.clone()], message)));
                }
                // Each subset holds elements of the base, which fingerprint.
                return Ok(None);
            }
            // TLC enumerates it to fingerprint it. The evaluator follows only a union that fails
            // to enumerate.
            Lazy::Cup(..) => {
                let Err(error) = crate::sets::enumerate(lazy) else {
                    return Err(());
                };
                return error
                    .message
                    .map(|message| Some((vec![value.clone()], message)))
                    .ok_or(());
            }
            _ => return Err(()),
        },
        Value::Unsorted(_) => return Err(()),
        _ => Vec::new(),
    };
    for inner in held {
        if let Some((mut chain, message)) = fingerprint_failure(inner)? {
            chain.insert(0, value.clone());
            return Ok(Some((chain, message)));
        }
    }
    Ok(None)
}

// The number of elements of a set the evaluator sizes, as TLC's `size` gives it.
fn size(set: &Value) -> Result<u64, ()> {
    match set {
        Value::Set(elements) => Ok(elements.len() as u64),
        Value::Interval(low, high) => Ok((i64::from(*high) - i64::from(*low) + 1).max(0) as u64),
        Value::Lazy(lazy) => match &**lazy {
            Lazy::Subset(base) => match size(base)? {
                count if count < 31 => Ok(1 << count),
                _ => Err(()),
            },
            _ => Err(()),
        },
        _ => Err(()),
    }
}

/// TLC's fingerprint of a state the evaluator holds, its values in TLC's order of the variables,
/// as the search's of the same state in its store. `None` where the evaluator doesn't hold a
/// value as the store would: a set it doesn't enumerate, or a text the IR doesn't rank.
pub fn state_fingerprint(fingerprints: &mut Fingerprints, values: &[&Value]) -> Option<u64> {
    let values: Option<Vec<_>> = values
        .iter()
        .map(|value| value_fingerprint(fingerprints, value))
        .collect();
    Some(fingerprints.of_state(&values?))
}

// F and length of a value (`Fingerprints::get_value` of the store's).
fn value_fingerprint(fingerprints: &mut Fingerprints, value: &Value) -> Option<(u64, u64)> {
    let polynomial = fingerprints.polynomial();
    match value {
        Value::Bool(boolean) => Some(polynomial.of_bool(*boolean)),
        Value::Int(int) => Some(polynomial.of_int(*int)),
        Value::Str(text) => Some(polynomial.of_string(&text.units)),
        Value::Model(text) => (text.rank >= 0).then(|| polynomial.of_model(text.rank)),
        Value::Unsorted(_) | Value::Lambda(_) => None,
        Value::Function(function) => {
            let mut parts = Vec::with_capacity(function.domain.len() * 2);
            for (key, held) in function.domain.iter().zip(&function.range) {
                parts.push(value_fingerprint(fingerprints, key)?);
                parts.push(value_fingerprint(fingerprints, held)?);
            }
            Some(fingerprints.of_parts(false, &parts))
        }
        Value::Set(_) | Value::Interval(..) | Value::Lazy(_) => {
            let parts: Option<Vec<_>> = elements(value)
                .ok()?
                .iter()
                .map(|element| value_fingerprint(fingerprints, element))
                .collect();
            Some(fingerprints.of_parts(true, &parts?))
        }
    }
}
