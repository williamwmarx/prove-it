//! A module's obligations as tlapm prints them, for the scripts and tests that compare them, and
//! what Prep makes of them, with the Rust obligations crate:
//!
//! - `obligations(file, source, known, encode)` returns
//!   `{ kind: "obligations", obligations, encodings, missingProofCount, omittedProofCount }`, with
//!   the counts of missing and omitted proofs as `prove` gives them. Each obligation is
//!   `{ id, location, kind, text, methods }`, every result's in order, a submodule's before the
//!   module that contains it. `kind` is `Main`, `Support`, `Error` or `Omitted`, and `methods` the
//!   methods Prep tries, each `{ prover, timeLimitMs }`, or the error that stops it. `encode` holds
//!   `[index, prover]` pairs, each an obligation's place in `obligations`, as a submodule's ids
//!   start again at 1, and `encodings` the text each backend receives for each, as `prove`
//!   would send it, or the error that stops it: `{ kind: "text", text }` or an error. They are
//!   encoded in turn in one run, so that the SMT encoder counts its CASE errors across them;
//! - `fingerprint(file, source, known)` returns `{ kind: "fingerprints", fingerprints }`, each
//!   obligation's `{ id, fingerprint }`, its fingerprint as tlapm's `fp_sequent` makes it, or the
//!   error that stops it.
//!
//! Each reads a module it doesn't know as `prove` does (`module:<name>#<n>`), and the file it read
//! it from under `path:<name>#<n>`, which errors name. Where it can't read the module it returns
//! `{ kind: "needed", keys }`, and where the obligations fail,
//! `{ kind: "error", name, message, failure, exception }`, as `prove` does.

use std::collections::HashMap;

use prove_obligations::index::{
    ModuleObligations, ObligationSource, PrintedObligation, get_obligations,
};
use prove_obligations::prep::fingerprint::get_fingerprint;
use prove_obligations::prep::methods::find_methods;
use prove_obligations::proof::ObligationKind;
use prove_obligations::reset_caches;
use prove_obligations::ship::encode_for_backend;
use prove_obligations::smt::rewrite::EncodingSession;
use prove_obligations::tlaps_module::TLAPS_MODULE;

use crate::hooks::HookResult;
use crate::prove::get_error;
use crate::sources::{Sources, get_text};
use crate::value::HostValue;

#[cfg(not(target_arch = "wasm32"))]
const OBLIGATIONS_STACK_BYTES: usize = 256 * 1024 * 1024;

/// `obligations(file, source, known, encode)`.
pub fn obligations(arguments: &[HostValue]) -> HookResult {
    let [file, source, known, encode, ..] = arguments else {
        return Err(
            "obligations takes a file name, a source, what is known and what to encode".into(),
        );
    };
    let file = get_text(file, "the file name")?;
    let source = get_text(source, "the source")?;
    let sources = Sources::new(known)?;
    let requests = get_requests(encode)?;
    on_deep_stack(move || {
        let modules = match load(file, source, &sources) {
            Ok(modules) => modules,
            Err(result) => return Ok(result),
        };
        let count = |get: fn(&ModuleObligations) -> usize| modules.iter().map(get).sum::<usize>();
        let missing = count(|module| module.summary.absent.len());
        let omitted = count(|module| module.summary.omitted.len());
        let obligations = get_printed(modules);
        let mut session = EncodingSession::default();
        let encodings = requests
            .iter()
            .map(|(index, prover)| {
                let obligation = obligations
                    .get(*index)
                    .ok_or_else(|| format!("there is no obligation at {index} to encode"))?;
                Ok(match encode_for_backend(obligation, prover, &mut session) {
                    Ok(text) => HostValue::Object(vec![
                        ("kind", HostValue::text("text")),
                        ("text", HostValue::text(&text)),
                    ]),
                    Err(error) => get_error(&error),
                })
            })
            .collect::<Result<_, String>>()?;
        Ok(HostValue::Object(vec![
            ("kind", HostValue::text("obligations")),
            (
                "obligations",
                HostValue::Array(obligations.iter().map(get_obligation).collect()),
            ),
            ("encodings", HostValue::Array(encodings)),
            ("missingProofCount", HostValue::Number(missing as f64)),
            ("omittedProofCount", HostValue::Number(omitted as f64)),
        ]))
    })
}

/// `fingerprint(file, source, known)`.
pub fn fingerprint(arguments: &[HostValue]) -> HookResult {
    let [file, source, known, ..] = arguments else {
        return Err("fingerprint takes a file name, a source and what is known".into());
    };
    let file = get_text(file, "the file name")?;
    let source = get_text(source, "the source")?;
    let sources = Sources::new(known)?;
    on_deep_stack(move || {
        let obligations = match load(file, source, &sources) {
            Ok(modules) => get_printed(modules),
            Err(result) => return Ok(result),
        };
        let fingerprints = obligations
            .iter()
            .map(|obligation| {
                let fingerprint = match get_fingerprint(&obligation.sequent) {
                    Ok(fingerprint) => HostValue::text(&fingerprint),
                    Err(error) => get_error(&error),
                };
                HostValue::Object(vec![
                    ("id", HostValue::Number(obligation.id as f64)),
                    ("fingerprint", fingerprint),
                ])
            })
            .collect();
        Ok(HostValue::Object(vec![
            ("kind", HostValue::text("fingerprints")),
            ("fingerprints", HostValue::Array(fingerprints)),
        ]))
    })
}

// The `[index, prover]` pairs to encode.
fn get_requests(encode: &HostValue) -> Result<Vec<(usize, String)>, String> {
    let wrong = || "what to encode must be an array of [id, prover] pairs".to_owned();
    let HostValue::Array(pairs) = encode else {
        return Err(wrong());
    };
    pairs
        .iter()
        .map(|pair| match pair {
            HostValue::Array(pair) => match pair.as_slice() {
                [HostValue::Number(index), prover] if *index >= 0.0 && index.fract() == 0.0 => {
                    Ok((*index as usize, get_text(prover, "a prover")?))
                }
                _ => Err(wrong()),
            },
            _ => Err(wrong()),
        })
        .collect()
}

#[cfg(target_arch = "wasm32")]
fn on_deep_stack(run: impl FnOnce() -> HookResult + Send) -> HookResult {
    run()
}

/// On a thread of its own with a deep stack, since the obligations recurse as deep as the proofs
/// nest, and with Prep's caches of its own, which no run of `prove` shares.
#[cfg(not(target_arch = "wasm32"))]
fn on_deep_stack(run: impl FnOnce() -> HookResult + Send) -> HookResult {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .name("prove-it obligations".into())
            .stack_size(OBLIGATIONS_STACK_BYTES)
            .spawn_scoped(scope, run)
            .expect("a thread for the obligations")
            .join()
            .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
    })
}

// Every result, or what to return in its place: the modules it needs, or the error
// getObligations throws.
fn load(
    file: String,
    source: String,
    sources: &Sources,
) -> Result<Vec<ModuleObligations>, HostValue> {
    // As a fresh process gives, whatever ran on this thread before.
    reset_caches();
    let mut reads: HashMap<String, usize> = HashMap::new();
    let modules = get_obligations(
        &[ObligationSource { file, source }],
        &mut |name| {
            let read = reads.entry(name.to_owned()).or_default();
            *read += 1;
            let Some(source) = sources.get(format!("module:{name}#{read}")) else {
                return (name == "TLAPS").then(|| ObligationSource {
                    file: "TLAPS.tla".to_owned(),
                    source: TLAPS_MODULE.to_owned(),
                });
            };
            let file = sources
                .get(format!("path:{name}#{read}"))
                .unwrap_or_else(|| format!("{name}.tla"));
            Some(ObligationSource { file, source })
        },
        None,
        &mut |_| {},
    );
    if let Some(needed) = sources.get_needed() {
        return Err(needed);
    }
    modules.map_err(|error| get_error(&error))
}

// Every result's obligations, in order.
fn get_printed(modules: Vec<ModuleObligations>) -> Vec<PrintedObligation> {
    modules
        .into_iter()
        .flat_map(|module| module.obligations)
        .collect()
}

fn get_obligation(obligation: &PrintedObligation) -> HostValue {
    let kind = match obligation.kind {
        ObligationKind::Main => "Main",
        ObligationKind::Support => "Support",
        ObligationKind::Error(_) => "Error",
        ObligationKind::Omitted(_) => "Omitted",
    };
    let methods = match find_methods(&obligation.sequent, obligation.method.as_ref()) {
        Ok(methods) => HostValue::Array(
            methods
                .provers
                .iter()
                .map(|method| {
                    HostValue::Object(vec![
                        ("prover", HostValue::text(&method.prover)),
                        ("timeLimitMs", HostValue::Number(method.time_limit_ms)),
                    ])
                })
                .collect(),
        ),
        Err(error) => get_error(&error),
    };
    HostValue::Object(vec![
        ("id", HostValue::Number(obligation.id as f64)),
        ("location", HostValue::text(&obligation.location)),
        ("kind", HostValue::text(kind)),
        ("text", HostValue::text(&obligation.text)),
        ("methods", methods),
    ])
}
