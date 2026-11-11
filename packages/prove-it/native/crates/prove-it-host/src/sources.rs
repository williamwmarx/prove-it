//! How an export reads what JavaScript holds, such as a spec's modules, without a file system and
//! without calling back into JavaScript: it takes what is known so far as `[key, value]` pairs, and
//! where it reads a key that isn't among them, it returns `{ kind: "needed", keys }` instead of its
//! result, and JavaScript calls it again with those keys answered, undefined where there is
//! nothing. The export starts again from the beginning each round, so it asks only for what it
//! reads. The keys are:
//!
//! - `stat:<path>`, `"file"` or `"directory"` where the system finds something at the path,
//!   `bytes:<path>`, the bytes of a file there, as a Uint8Array, `realpath:<path>`, the path with
//!   its links followed, `cwd`, the working directory, and `tmpdir`, the system's temporary
//!   directory: the CLI's files, which the binary's resolver finds (`checkSources`,
//!   `resolveFiles`);
//! - `text:<path>`, the text of the library's spec or configuration, `module:<name>`, a module's
//!   text, and `class:<name>`, the Java override for a module as a Uint8Array: the library's
//!   (`checkSources`); and `module:<name>` and `file:<origin>:<name>`, the file TLC prints that it
//!   parses a module from, for the origins `file`, `root file` and `standard`, which the CLI's
//!   TypeScript check answers through `resolveFiles` (`sanyText`);
//! - `decide:<key>`, a backend's answer to a decision `prove` asks for, with its text, by the key it
//!   gives it (`prove`).
//!
//! An export that reads something else names it by a key of a new kind, which this list gains.

use std::cell::RefCell;
use std::collections::HashMap;

use crate::value::HostValue;

/// What JavaScript has answered, and the keys asked for that it hasn't.
pub struct Sources {
    known: HashMap<String, Option<Known>>,
    needed: RefCell<Vec<String>>,
}

/// A value JavaScript answered: a string, or a Uint8Array.
#[derive(Clone)]
enum Known {
    Text(String),
    Bytes(Vec<u8>),
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
                        HostValue::Uint8s(bytes) => Some(Known::Bytes(bytes.clone())),
                        value => Some(Known::Text(get_text(value, "a known value")?)),
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
        match self.get_known(key)? {
            Known::Text(text) => Some(text),
            Known::Bytes(_) => None,
        }
    }

    /// `get` of a key JavaScript answers with a Uint8Array.
    pub fn get_bytes(&self, key: String) -> Option<Vec<u8>> {
        match self.get_known(key)? {
            Known::Bytes(bytes) => Some(bytes),
            Known::Text(_) => None,
        }
    }

    /// The keys JavaScript answered that start with `prefix`, with their texts, in key order.
    pub fn get_answered_with(&self, prefix: &str) -> Vec<(String, Option<String>)> {
        let mut answered: Vec<_> = self
            .known
            .iter()
            .filter(|(key, _)| key.starts_with(prefix))
            .map(|(key, value)| {
                let text = match value {
                    Some(Known::Text(text)) => Some(text.clone()),
                    _ => None,
                };
                (key.clone(), text)
            })
            .collect();
        answered.sort();
        answered
    }

    fn get_known(&self, key: String) -> Option<Known> {
        let value = self.known.get(&key).cloned();
        let mut needed = self.needed.borrow_mut();
        if value.is_none() && !needed.contains(&key) {
            needed.push(key);
        }
        value.flatten()
    }

    /// Whether a key was read that isn't known.
    pub fn has_needed(&self) -> bool {
        !self.needed.borrow().is_empty()
    }

    /// `{ kind: "needed", keys }` where the export read a key that isn't known, in place of its
    /// result.
    pub fn get_needed(&self) -> Option<HostValue> {
        let needed = self.needed.borrow();
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
