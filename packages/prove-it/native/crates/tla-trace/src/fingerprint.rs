//! Where TLC fails to fingerprint a value (`fingerprint` and `size` of its values): a power set of
//! a set of 31 elements or more, whose size overflows an int (`SubsetValue.size`).

use crate::print::format_value;
use crate::value::{Lazy, TlcMessage, Value};

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
                            format_value(value)
                        ),
                        code: Some(OVERFLOW),
                        is_eval_exception: false,
                    };
                    return Ok(Some((vec![value.clone()], message)));
                }
                // Each subset holds elements of the base, which fingerprint.
                return Ok(None);
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
