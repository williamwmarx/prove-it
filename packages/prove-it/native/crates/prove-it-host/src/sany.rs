//! What SANY prints for a spec, as tla-front writes it, for the CLI of `dist/`: the report the
//! native binary prints. `sanyText(root, source, fileName, version, rootExtendees, known)` takes the
//! root module's name and text, or null where no file holds it, the file name TLC gives SANY, TLC's version ("master" or "1.7.4"),
//! the modules TLC adds to the root module's EXTENDS for its post conditions, and what is known of
//! the spec's other modules and files (`sources`), and returns one of:
//!
//! - `{ kind: "text", text, isFailed, exception }`, SANY's report;
//! - `{ kind: "needed", keys }`, what the report reads that isn't known yet (`sources`);
//! - `{ kind: "declined", reason }`, where tla-front doesn't write SANY's report.
//!
//! The CLI's TypeScript check answers its keys through `resolveFiles` (`check`).

use tla_front::TlcVersion;
use tla_front::errors::FrontError;
use tla_front::report::{
    ModuleOrigin, ReportOptions, get_missing_root_text, get_sany_text_of, get_standard_root_text,
};

use crate::hooks::HookResult;
use crate::sources::{Sources, get_strings, get_text};
use crate::value::HostValue;

fn get_origin(origin: ModuleOrigin) -> &'static str {
    match origin {
        ModuleOrigin::File => "file",
        ModuleOrigin::RootFile => "root file",
        ModuleOrigin::Standard => "standard",
    }
}

fn declined(reason: &str) -> HostValue {
    HostValue::Object(vec![
        ("kind", HostValue::text("declined")),
        ("reason", HostValue::text(reason)),
    ])
}

/// Runs `write` on this thread: wasm's stack is the one it links.
#[cfg(target_arch = "wasm32")]
fn on_deep_stack(write: impl FnOnce() -> HookResult + Send) -> HookResult {
    write()
}

/// Runs `write` on a thread with a deep stack.
#[cfg(not(target_arch = "wasm32"))]
fn on_deep_stack(write: impl FnOnce() -> HookResult + Send) -> HookResult {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(tla_front::report::REPORT_STACK_BYTES)
            .spawn_scoped(scope, write)
            .expect("a thread for SANY's report")
            .join()
            .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
    })
}

/// `sanyText(root, source, fileName, version, rootExtendees, known)`.
pub fn sany_text(arguments: &[HostValue]) -> HookResult {
    on_deep_stack(|| write_sany_text(arguments))
}

fn write_sany_text(arguments: &[HostValue]) -> HookResult {
    let [root, source, file_name, version, root_extendees, known] = arguments else {
        return Err(
            "sanyText takes a module's name, its text, a file name, TLC's version, the root \
             module's added extendees and what is known"
                .into(),
        );
    };
    let version = match get_text(version, "TLC's version")?.as_str() {
        "master" => TlcVersion::Master,
        "1.7.4" => TlcVersion::V1_7_4,
        other => return Err(format!("TLC's version is master or 1.7.4, not {other}")),
    };
    let root_extendees = get_strings(root_extendees, "the root module's added extendees")?;
    let root_extendees: Vec<&str> = root_extendees.iter().map(String::as_str).collect();
    let root = get_text(root, "the root module's name")?;
    let source = match source {
        HostValue::Undefined | HostValue::Null => None,
        source => Some(get_text(source, "the root module's text")?),
    };
    let file_name = match file_name {
        HostValue::Undefined | HostValue::Null => None,
        file_name => Some(get_text(file_name, "the file name")?),
    };
    let sources = Sources::new(known)?;
    let options = ReportOptions {
        version,
        file_name: file_name.as_deref(),
        load_module: &|name| sources.get(format!("module:{name}")),
        describe_file: &|name, origin| {
            sources
                .get(format!("file:{}:{name}", get_origin(origin)))
                .unwrap_or_default()
        },
        root_extendees: &root_extendees,
        is_xml_export: false,
    };
    let name = file_name.as_deref().unwrap_or(&root);
    let standard = source
        .is_none()
        .then(|| get_standard_root_text(&root, &options))
        .flatten();
    let result = match &source {
        Some(source) => get_sany_text_of(&root, source, &options),
        // SANY reads a root module no file holds from its standard modules.
        None if standard.is_some() => standard.expect("a standard root"),
        // SANY names a root module no file holds by the spec's name as TLC was given it.
        None if version == TlcVersion::Master => Ok(get_missing_root_text(name, name)),
        None => Err(FrontError::NotYet("a spec without its file".to_owned())),
    };
    if let Some(needed) = sources.get_needed() {
        return Ok(needed);
    }
    Ok(match result {
        Ok(sany) => HostValue::Object(vec![
            ("kind", HostValue::text("text")),
            ("text", HostValue::text(&sany.text)),
            ("isFailed", HostValue::Bool(sany.is_failed)),
            (
                "exception",
                sany.exception
                    .as_deref()
                    .map_or(HostValue::Null, HostValue::text),
            ),
        ]),
        Err(FrontError::NotYet(reason)) => declined(&format!("SANY's report of {reason}")),
        Err(_) => declined("SANY's report, which tla-front doesn't write"),
    })
}
