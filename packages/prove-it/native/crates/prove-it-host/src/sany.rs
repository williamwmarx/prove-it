//! What SANY prints for a spec, as tla-front writes it, for the CLI of `dist/`: the report the
//! native binary prints. `sanyText(root, source, fileName, known)` takes the root module's name and
//! text, the file name TLC gives SANY, and what the CLI has read so far as `[key, value]` pairs,
//! and returns one of:
//!
//! - `{ kind: "text", text, isFailed, exception }`, SANY's report;
//! - `{ kind: "needed", keys }`, what the report reads that `known` doesn't hold, which the CLI
//!   reads and calls again with: `module:<name>`, a module's text from a file of its own, or
//!   undefined where there is none, and `file:<origin>:<name>`, the file TLC prints that it parses
//!   the module from, for the origins `file`, `root file` and `standard`;
//! - `{ kind: "declined", reason }`, where tla-front doesn't write SANY's report.
//!
//! The CLI reads files, which WebAssembly can't, so it answers what the report asks for, and the
//! report is written again from the start with each answer.

use std::cell::RefCell;
use std::collections::HashMap;

use tla_front::TlcVersion;
use tla_front::errors::FrontError;
use tla_front::report::{ModuleOrigin, ReportOptions, get_sany_text_of};

use crate::hooks::HookResult;
use crate::value::HostValue;

fn get_text(value: &HostValue, what: &str) -> Result<String, String> {
    match value {
        HostValue::Text(units) => Ok(String::from_utf16_lossy(units)),
        _ => Err(format!("{what} must be a string")),
    }
}

fn get_origin(origin: ModuleOrigin) -> &'static str {
    match origin {
        ModuleOrigin::File => "file",
        ModuleOrigin::RootFile => "root file",
        ModuleOrigin::Standard => "standard",
    }
}

/// `sanyText(root, source, fileName, known)`.
pub fn sany_text(arguments: &[HostValue]) -> HookResult {
    let [root, source, file_name, known] = arguments else {
        return Err(
            "sanyText takes a module's name, its text, a file name and what is known".into(),
        );
    };
    let root = get_text(root, "the root module's name")?;
    let source = get_text(source, "the root module's text")?;
    let file_name = match file_name {
        HostValue::Undefined | HostValue::Null => None,
        file_name => Some(get_text(file_name, "the file name")?),
    };
    let HostValue::Array(entries) = known else {
        return Err("what is known must be an array of [key, value] pairs".into());
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
            _ => Err("what is known must be an array of [key, value] pairs".to_owned()),
        })
        .collect::<Result<HashMap<_, _>, String>>()?;
    let needed = RefCell::new(Vec::new());
    let find = |key: String| {
        let value = known.get(&key).cloned();
        if value.is_none() {
            needed.borrow_mut().push(key);
        }
        value.flatten()
    };
    let options = ReportOptions {
        version: TlcVersion::Master,
        file_name: file_name.as_deref(),
        load_module: &|name| find(format!("module:{name}")),
        describe_file: &|name, origin| {
            find(format!("file:{}:{name}", get_origin(origin))).unwrap_or_default()
        },
    };
    let result = get_sany_text_of(&root, &source, &options);
    let needed = needed.into_inner();
    if !needed.is_empty() {
        return Ok(HostValue::Object(vec![
            ("kind", HostValue::text("needed")),
            (
                "keys",
                HostValue::Array(needed.iter().map(|key| HostValue::text(key)).collect()),
            ),
        ]));
    }
    Ok(HostValue::Object(match result {
        Ok(sany) => vec![
            ("kind", HostValue::text("text")),
            ("text", HostValue::text(&sany.text)),
            ("isFailed", HostValue::Bool(sany.is_failed)),
            (
                "exception",
                sany.exception
                    .as_deref()
                    .map_or(HostValue::Null, HostValue::text),
            ),
        ],
        Err(FrontError::NotYet(reason)) => vec![
            ("kind", HostValue::text("declined")),
            (
                "reason",
                HostValue::text(&format!("SANY's report of {reason}")),
            ),
        ],
        Err(_) => vec![
            ("kind", HostValue::text("declined")),
            (
                "reason",
                HostValue::text("SANY's report, which tla-front doesn't write"),
            ),
        ],
    }))
}
