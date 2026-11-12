//! What SANY prints for a spec, as tla-front writes it, for the CLI of `dist/`: the report the
//! native binary prints. `sanyText(root, source, fileName, known)` takes the root module's name and
//! text, the file name TLC gives SANY, and what is known of the spec's other modules and files
//! (`sources`), and returns one of:
//!
//! - `{ kind: "text", text, isFailed, exception }`, SANY's report;
//! - `{ kind: "needed", keys }`, what the report reads that isn't known yet (`sources`);
//! - `{ kind: "declined", reason }`, where tla-front doesn't write SANY's report.
//!
//! The CLI's TypeScript check answers its keys through `resolveFiles` (`check`).

use tla_front::TlcVersion;
use tla_front::errors::FrontError;
use tla_front::report::{ModuleOrigin, ReportOptions, get_sany_text_of};

use crate::hooks::HookResult;
use crate::sources::{Sources, get_text};
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

/// The stack of the thread the report is written on: the front end recurses as deep as TLC's
/// translation of a formula does, which the stack of the thread JavaScript calls on doesn't hold,
/// as `prove-it-cli`'s run thread doesn't.
#[cfg(not(target_arch = "wasm32"))]
const REPORT_STACK_BYTES: usize = 64 * 1024 * 1024;

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
            .stack_size(REPORT_STACK_BYTES)
            .spawn_scoped(scope, write)
            .expect("a thread for SANY's report")
            .join()
            .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
    })
}

/// `sanyText(root, source, fileName, known)`.
pub fn sany_text(arguments: &[HostValue]) -> HookResult {
    on_deep_stack(|| write_sany_text(arguments))
}

fn write_sany_text(arguments: &[HostValue]) -> HookResult {
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
    let sources = Sources::new(known)?;
    let options = ReportOptions {
        version: TlcVersion::Master,
        file_name: file_name.as_deref(),
        load_module: &|name| sources.get(format!("module:{name}")),
        describe_file: &|name, origin| {
            sources
                .get(format!("file:{}:{name}", get_origin(origin)))
                .unwrap_or_default()
        },
        root_extendees: &[],
        is_xml_export: false,
    };
    let result = get_sany_text_of(&root, &source, &options);
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
