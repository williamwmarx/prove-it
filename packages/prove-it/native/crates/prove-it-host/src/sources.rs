//! How an export reads what JavaScript holds, such as a spec's modules, without a file system and
//! without calling back into JavaScript: it takes what is known so far as `[key, value]` pairs, and
//! where it reads a key that isn't among them, it returns `{ kind: "needed", keys }` instead of its
//! result, and JavaScript calls it again with those keys answered, undefined where there is
//! nothing. The export starts again from the beginning each round, so it asks only for what it
//! reads. The keys are:
//!
//! - `module:<name>`, a module's text from a file of its own, beside the spec or in a library;
//! - `file:<origin>:<name>`, the file TLC prints that it parses a module from, for the origins
//!   `file`, `root file` and `standard`.
//!
//! An export that reads something else names it by a key of a new kind, which this list gains.

use std::cell::RefCell;
use std::collections::HashMap;

use crate::value::HostValue;

/// What JavaScript has answered, and the keys asked for that it hasn't.
pub struct Sources {
    known: HashMap<String, Option<String>>,
    needed: RefCell<Vec<String>>,
}

/// A string argument, or the message of the TypeError for another.
pub fn get_text(value: &HostValue, what: &str) -> Result<String, String> {
    match value {
        HostValue::Text(units) => Ok(String::from_utf16_lossy(units)),
        _ => Err(format!("{what} must be a string")),
    }
}

impl Sources {
    /// What is known, from its `[key, value]` pairs.
    pub fn new(known: &HostValue) -> Result<Sources, String> {
        let wrong = || "what is known must be an array of [key, value] pairs".to_owned();
        let HostValue::Array(entries) = known else {
            return Err(wrong());
        };
        let known = entries
            .iter()
            .map(|entry| match entry {
                HostValue::Array(pair) if pair.len() == 2 => {
                    let value = match &pair[1] {
                        HostValue::Undefined | HostValue::Null => None,
                        value => Some(get_text(value, "a known value")?),
                    };
                    Ok((get_text(&pair[0], "a known key")?, value))
                }
                _ => Err(wrong()),
            })
            .collect::<Result<_, String>>()?;
        Ok(Sources {
            known,
            needed: RefCell::default(),
        })
    }

    /// The value of the key, or None, where it is known to have none or isn't known yet, which
    /// `get_needed` then asks for.
    pub fn get(&self, key: String) -> Option<String> {
        let value = self.known.get(&key).cloned();
        if value.is_none() {
            self.needed.borrow_mut().push(key);
        }
        value.flatten()
    }

    /// `{ kind: "needed", keys }` where the export read a key that isn't known, in place of its
    /// result.
    pub fn get_needed(self) -> Option<HostValue> {
        let needed = self.needed.into_inner();
        (!needed.is_empty()).then(|| {
            HostValue::Object(vec![
                ("kind", HostValue::text("needed")),
                (
                    "keys",
                    HostValue::Array(needed.iter().map(|key| HostValue::text(key)).collect()),
                ),
            ])
        })
    }
}
