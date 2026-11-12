//! `prove(file, source, known)`, for `src/prover/prove.ts`: proves a module's obligations with the
//! Rust driver, which reads what JavaScript holds through `Sources` and returns one of:
//!
//! - `{ kind: "needed", keys, requests, reports }`, where it reads a module it doesn't know
//!   (`module:<name>#<n>`, the n-th time it reads it, which `loadModule` answers) or needs
//!   decisions. Each request is
//!   `{ key, prover, text, timeLimitMs }`, which JavaScript decides and answers under
//!   `decide:<key>` as `<verdict> <timeUsedMs>`, `error:<message>` for the `TlaProverError` a
//!   backend throws, or `unsupported:<message>` for a `TlaUnsupportedError`. `priority` is the
//!   obligation's position, by which JavaScript decides the earliest first. `reports` are the obligations settled so far, in order;
//! - `{ kind: "proved", reports, missingProofCount, omittedProofCount }`;
//! - `{ kind: "error", name, message, failure, exception, reports }`, an error `getObligations` or
//!   the driver throws, after the obligations settled before it: `failure` and `exception` only for
//!   a `TlaProofError`.
//!
//! An answer that isn't one of these fails the call, as JavaScript never writes one.
//!
//! A report is a `ProofObligation`: `{ id, location, text, status }`, with the `prover` that proved
//! it, or the `reason` it is unproved.

use prove_it_prover::Verdict;
use std::cell::RefCell;
use std::collections::HashMap;

use prove_it_prover::driver::{Answer, Cache, Report, Status, prove_obligations};
use prove_obligations::errors::ObligationError;
use prove_obligations::index::{
    ModuleObligations, ObligationSource, PrintedObligation, get_obligations,
};
use prove_obligations::reset_caches;
use prove_obligations::tlaps_module::TLAPS_MODULE;

use crate::hooks::HookResult;
use crate::sources::{Sources, get_text, is_well_formed};
use crate::value::HostValue;

#[cfg(not(target_arch = "wasm32"))]
const PROVE_STACK_BYTES: usize = 256 * 1024 * 1024;

/// `prove(file, source, known)`.
pub fn prove(arguments: &[HostValue]) -> HookResult {
    let [file, source, known, ..] = arguments else {
        return Err("prove takes a file name, a source and what is known".into());
    };
    let declined = [(file, "the file name"), (source, "the source")]
        .into_iter()
        .find(|(value, _)| !is_well_formed(value));
    let file = get_text(file, "the file name")?;
    let source = get_text(source, "the source")?;
    let sources = Sources::new(known)?;
    if let Some((_, what)) = declined {
        return Ok(get_ill_formed(what));
    }
    on_deep_stack(move || prove_here(file, source, sources))
}

#[cfg(target_arch = "wasm32")]
fn on_deep_stack(prove: impl FnOnce() -> HookResult + Send) -> HookResult {
    prove()
}

/// On the calling thread's prove thread, which has a deep stack, since the obligations recurse as
/// deep as the proofs nest, and which keeps a run's cache from one round to the next. Each calling
/// thread keeps its own for as long as it lives; a panic replaces it, as its cache may be half
/// built.
#[cfg(not(target_arch = "wasm32"))]
fn on_deep_stack(prove: impl FnOnce() -> HookResult + Send + 'static) -> HookResult {
    use std::panic::{AssertUnwindSafe, catch_unwind, resume_unwind};
    use std::sync::mpsc::{Receiver, Sender, channel};

    type Job = Box<dyn FnOnce() -> HookResult + Send>;

    struct ProveThread {
        jobs: Sender<Job>,
        results: Receiver<std::thread::Result<HookResult>>,
    }

    let spawn = || {
        let (jobs, received) = channel::<Job>();
        let (answered, results) = channel();
        std::thread::Builder::new()
            .name("prove-it prove".into())
            .stack_size(PROVE_STACK_BYTES)
            .spawn(move || {
                for job in received {
                    if answered.send(catch_unwind(AssertUnwindSafe(job))).is_err() {
                        break;
                    }
                }
            })
            .expect("a thread for prove");
        ProveThread { jobs, results }
    };

    thread_local! {
        static PROVE_THREAD: RefCell<Option<ProveThread>> = const { RefCell::new(None) };
    }
    let result = PROVE_THREAD.with_borrow_mut(|prove_thread| {
        let thread = prove_thread.get_or_insert_with(spawn);
        thread.jobs.send(Box::new(prove)).expect("the prove thread");
        let result = thread.results.recv().expect("the prove thread's result");
        if result.is_err() {
            *prove_thread = None;
        }
        result
    });
    result.unwrap_or_else(|panic| resume_unwind(panic))
}

// A run's obligations and cache, by what the run reads: the main module and the modules it loads.
struct Run {
    key: String,
    modules: Vec<ModuleObligations>,
    obligations: Vec<PrintedObligation>,
    cache: Cache,
}

thread_local! {
    static RUN: RefCell<Option<Run>> = const { RefCell::new(None) };
}

// Each part of a run's key with its length, so that no two runs share one.
fn push_key(key: &mut String, part: Option<&str>) {
    match part {
        Some(text) => key.push_str(&format!("{}:{text}", text.len())),
        None => key.push('-'),
    }
}

fn prove_here(file: String, source: String, sources: Sources) -> HookResult {
    let mut key = String::new();
    push_key(&mut key, Some(&file));
    push_key(&mut key, Some(&source));
    for (name, text) in sources.get_answered_with("module:") {
        push_key(&mut key, Some(&name));
        push_key(&mut key, text.as_deref());
    }
    let mut answers = HashMap::new();
    for (key, text) in sources.get_answered_with("decide:") {
        let answer = text
            .as_deref()
            .and_then(get_answer)
            .ok_or_else(|| format!("prove can't read the answer to {key}"))?;
        answers.insert(key["decide:".len()..].to_owned(), answer);
    }
    Ok(RUN.with_borrow_mut(|run| {
        if run.as_ref().is_some_and(|run| run.key == key) {
            return prove_round(run.as_mut().expect("a run"), &answers);
        }
        *run = None;
        match load_run(key, file, source, &sources) {
            Ok(loaded) => prove_round(run.insert(loaded), &answers),
            Err(result) => result,
        }
    }))
}

// A new run's obligations, or what to return in place of a round: the modules it needs, or the
// error getObligations throws.
fn load_run(
    key: String,
    file: String,
    source: String,
    sources: &Sources,
) -> Result<Run, HostValue> {
    // A run gives what a fresh process gives, whatever ran on this thread before.
    reset_caches();
    // Each time getObligations reads a module is its own key, as the TypeScript reads a module
    // named like a standard one, or a missing one, again for each module citing it.
    let mut reads: HashMap<String, usize> = HashMap::new();
    let mut ill_formed = None;
    let modules = get_obligations(
        &[ObligationSource { file, source }],
        &mut |name| {
            let read = reads.entry(name.to_owned()).or_default();
            *read += 1;
            let key = format!("module:{name}#{read}");
            if sources.is_ill_formed(&key) {
                ill_formed.get_or_insert_with(|| format!("the module {name}"));
                return None;
            }
            let source = sources
                .get(key)
                .or_else(|| (name == "TLAPS").then(|| TLAPS_MODULE.to_owned()))?;
            Some(ObligationSource {
                file: format!("{name}.tla"),
                source,
            })
        },
        None,
        &mut |_| {},
    );
    if let Some(what) = ill_formed {
        return Err(get_ill_formed(&what));
    }
    if sources.has_needed() {
        return Err(get_needed(sources));
    }
    let modules = modules.map_err(|error| get_error(&error))?;
    let obligations = modules
        .iter()
        .flat_map(|module| module.obligations.iter().cloned())
        .collect();
    Ok(Run {
        key,
        modules,
        obligations,
        cache: Cache::default(),
    })
}

// The modules the run needs, with no requests or reports yet.
fn get_needed(sources: &Sources) -> HostValue {
    let Some(HostValue::Object(mut needed)) = sources.get_needed() else {
        return HostValue::Undefined;
    };
    needed.push(("requests", HostValue::Array(Vec::new())));
    needed.push(("reports", HostValue::Array(Vec::new())));
    HostValue::Object(needed)
}

fn prove_round(run: &mut Run, answers: &HashMap<String, Answer>) -> HostValue {
    let modules = &run.modules;
    let round = match prove_obligations(
        &run.obligations,
        &|key| answers.get(key).cloned(),
        &mut run.cache,
    ) {
        Ok(round) => round,
        Err(error) => return get_error(&error),
    };
    let reports = HostValue::Array(round.reports.iter().map(get_report).collect());
    if let Some(error) = round.error {
        let HostValue::Object(mut properties) = get_error(&error) else {
            return HostValue::Undefined;
        };
        properties.push(("reports", reports));
        return HostValue::Object(properties);
    }
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
                    ("priority", HostValue::Number(request.priority as f64)),
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
    if let Some(message) = text.strip_prefix("unsupported:") {
        return Some(Answer::Unsupported(message.to_owned()));
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

// A lone surrogate, which the engine's strings can't hold: reading it as U+FFFD would make
// different strings one, and so prove what doesn't hold.
fn get_ill_formed(what: &str) -> HostValue {
    get_error(&ObligationError::unsupported(format!(
        "not native yet: {what} isn't well-formed UTF-16"
    )))
}

/// An error the obligations or the driver throw, as `{ kind: "error", name, message }`, with the
/// `failure` and `exception` of a `TlaProofError`.
pub(crate) fn get_error(error: &ObligationError) -> HostValue {
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
