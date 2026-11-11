//! `prove(file, source, known)`, for `src/prover/prove.ts`: proves a module's obligations with the
//! Rust driver, which reads what JavaScript holds through `Sources` and returns one of:
//!
//! - `{ kind: "needed", keys, requests, reports }`, where it reads a module it doesn't know
//!   (`module:<name>`, which `loadModule` answers) or needs decisions. Each request is
//!   `{ key, prover, text, timeLimitMs }`, which JavaScript decides and answers under
//!   `decide:<key>` as `<verdict> <timeUsedMs>`, or `error:<message>` for the `TlaProverError` a
//!   backend throws. `reports` are the obligations settled so far, in order;
//! - `{ kind: "proved", reports, missingProofCount, omittedProofCount }`;
//! - `{ kind: "error", name, message, failure, exception }`, an error `getObligations` or the
//!   driver throws: `failure` and `exception` only for a `TlaProofError`.
//!
//! A report is a `ProofObligation`: `{ id, location, text, status }`, with the `prover` that proved
//! it, or the `reason` it is unproved.

use prove_it_prover::Verdict;
use prove_it_prover::driver::{Answer, Report, Status, prove_obligations};
use prove_obligations::errors::ObligationError;
use prove_obligations::index::{ObligationSource, get_obligations};
use prove_obligations::reset_caches;
use prove_obligations::tlaps_module::TLAPS_MODULE;

use crate::hooks::HookResult;
use crate::sources::{Sources, get_text};
use crate::value::HostValue;

#[cfg(not(target_arch = "wasm32"))]
const PROVE_STACK_BYTES: usize = 256 * 1024 * 1024;

/// `prove(file, source, known)`.
pub fn prove(arguments: &[HostValue]) -> HookResult {
    let [file, source, known, ..] = arguments else {
        return Err("prove takes a file name, a source and what is known".into());
    };
    let file = get_text(file, "the file name")?;
    let source = get_text(source, "the source")?;
    let sources = Sources::new(known)?;
    on_deep_stack(move || Ok(prove_here(file, source, sources)))
}

#[cfg(target_arch = "wasm32")]
fn on_deep_stack(prove: impl FnOnce() -> HookResult + Send) -> HookResult {
    prove()
}

/// On a thread with a deep stack: the obligations recurse as deep as the proofs nest.
#[cfg(not(target_arch = "wasm32"))]
fn on_deep_stack(prove: impl FnOnce() -> HookResult + Send) -> HookResult {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(PROVE_STACK_BYTES)
            .spawn_scoped(scope, prove)
            .expect("a thread for prove")
            .join()
            .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
    })
}

fn prove_here(file: String, source: String, sources: Sources) -> HostValue {
    // A run gives what a fresh process gives, whatever ran on this thread before.
    reset_caches();
    let modules = get_obligations(
        &[ObligationSource { file, source }],
        &mut |name| {
            let source = sources
                .get(format!("module:{name}"))
                .or_else(|| (name == "TLAPS").then(|| TLAPS_MODULE.to_owned()))?;
            Some(ObligationSource {
                file: format!("{name}.tla"),
                source,
            })
        },
        None,
        &mut |_| {},
    );
    if sources.has_needed() {
        let Some(HostValue::Object(mut needed)) = sources.get_needed() else {
            return HostValue::Undefined;
        };
        needed.push(("requests", HostValue::Array(Vec::new())));
        needed.push(("reports", HostValue::Array(Vec::new())));
        return HostValue::Object(needed);
    }
    let modules = match modules {
        Ok(modules) => modules,
        Err(error) => return get_error(&error),
    };
    let obligations: Vec<_> = modules
        .iter()
        .flat_map(|module| module.obligations.iter().cloned())
        .collect();
    let round = match prove_obligations(&obligations, &|key| {
        get_answer(&sources.get_answered(&format!("decide:{key}"))?)
    }) {
        Ok(round) => round,
        Err(error) => return get_error(&error),
    };
    let reports = HostValue::Array(round.reports.iter().map(get_report).collect());
    if !round.requests.is_empty() {
        let requests = round
            .requests
            .iter()
            .map(|request| {
                HostValue::Object(vec![
                    ("key", HostValue::text(&request.key)),
                    ("prover", HostValue::text(&request.prover)),
                    ("text", HostValue::text(&request.text)),
                    ("timeLimitMs", HostValue::Number(request.time_limit_ms)),
                ])
            })
            .collect();
        return HostValue::Object(vec![
            ("kind", HostValue::text("needed")),
            ("keys", HostValue::Array(Vec::new())),
            ("requests", HostValue::Array(requests)),
            ("reports", reports),
        ]);
    }
    let count = |get: fn(&prove_obligations::generate::ModuleSummary) -> usize| {
        modules
            .iter()
            .map(|module| get(&module.summary))
            .sum::<usize>() as f64
    };
    HostValue::Object(vec![
        ("kind", HostValue::text("proved")),
        ("reports", reports),
        (
            "missingProofCount",
            HostValue::Number(count(|summary| summary.absent.len())),
        ),
        (
            "omittedProofCount",
            HostValue::Number(count(|summary| summary.omitted.len())),
        ),
    ])
}

// An answer as JavaScript writes it, or None for one it can't have written.
fn get_answer(text: &str) -> Option<Answer> {
    if let Some(message) = text.strip_prefix("error:") {
        return Some(Answer::Failed(message.to_owned()));
    }
    let (verdict, time_used_ms) = text.split_once(' ')?;
    let verdict = match verdict {
        "unsat" => Verdict::Unsat,
        "sat" => Verdict::Sat,
        "unknown" => Verdict::Unknown,
        _ => return None,
    };
    Some(Answer::Decided {
        verdict,
        time_used_ms: time_used_ms.parse().ok()?,
    })
}

fn get_report(report: &Report) -> HostValue {
    let mut properties = vec![
        ("id", HostValue::Number(report.id as f64)),
        ("location", HostValue::text(&report.location)),
        ("text", HostValue::text(&report.text)),
    ];
    let (status, detail) = match &report.status {
        Status::Proved { prover } => ("proved", Some(("prover", prover))),
        Status::Trivial => ("trivial", None),
        Status::Failed { reason } => ("failed", Some(("reason", reason))),
        Status::Unsupported { reason } => ("unsupported", Some(("reason", reason))),
    };
    properties.push(("status", HostValue::text(status)));
    properties.extend(detail.map(|(name, value)| (name, HostValue::text(value))));
    HostValue::Object(properties)
}

fn get_error(error: &ObligationError) -> HostValue {
    let mut properties = vec![
        ("kind", HostValue::text("error")),
        ("name", HostValue::text(error.name())),
        ("message", HostValue::text(error.message())),
    ];
    if let ObligationError::Proof {
        failure, exception, ..
    } = error
    {
        properties.push((
            "failure",
            failure
                .as_deref()
                .map_or(HostValue::Undefined, HostValue::text),
        ));
        properties.push(("exception", HostValue::text(exception)));
    }
    HostValue::Object(properties)
}
