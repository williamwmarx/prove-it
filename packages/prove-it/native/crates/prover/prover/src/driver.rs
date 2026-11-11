//! Prove's driver, `proveObligations` and `proveWithBackends` of `src/prover/prove.ts`: each
//! obligation's methods in tlapm's order, Prep.already_processed's reuse by fingerprint, the
//! trivial obligations, and the SMT encoder's CASE numbering across the run.
//!
//! The driver doesn't decide. It asks for each decision by its key, with the text and the time
//! limit, and the caller answers. A run starts again from the beginning with the answers it has,
//! and since it is deterministic it settles the same obligations the same way and goes on where
//! the new answers let it. An obligation waits while a decision it needs is unanswered, and so does
//! every later obligation that depends on it: one with the same fingerprint, which reuses its
//! results, and one whose SMT encoding numbers a CASE, which starts from the count it leaves. The
//! others go on, so each round asks for every decision that is ready.

use std::collections::HashMap;

use prove_decide::Verdict;
use prove_obligations::errors::{ObligationError, Result};
use prove_obligations::expression::{Expr, ExprCore, Hyp, Hyps, Sequent, get_children, map_hyp};
use prove_obligations::index::PrintedObligation;
use prove_obligations::prep::fingerprint::get_fingerprint;
use prove_obligations::prep::methods::{FoundMethods, Method, find_methods};
use prove_obligations::prep::normalize::{is_trivial, normalize_expand};
use prove_obligations::proof::ObligationKind;
use prove_obligations::ship::{ProofAttempt, encode_normalized};
use prove_obligations::smt::rewrite::EncodingSession;

/// A decision the driver needs, under the key it is answered by.
#[derive(Clone, Debug, PartialEq)]
pub struct Request {
    pub key: String,
    pub prover: String,
    pub text: String,
    pub time_limit_ms: f64,
    /// The obligation's position in the run, by which the TypeScript's pool decides the earliest
    /// first.
    pub priority: usize,
}

/// How the caller answered a request: the backend's verdict, or the message of the
/// `TlaProverError` it threw, which tlapm counts as a failure, or of a `TlaUnsupportedError`.
#[derive(Clone, Debug, PartialEq)]
pub enum Answer {
    Decided {
        verdict: Verdict,
        time_used_ms: f64,
    },
    Failed(String),
    /// The message of a `TlaUnsupportedError`: the backend couldn't take the text, which the
    /// TypeScript counts as not tried.
    Unsupported(String),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Status {
    Proved { prover: String },
    Trivial,
    Failed { reason: String },
    Unsupported { reason: String },
}

/// What one method concluded, as tlapm's toolbox messages report it.
#[derive(Clone, Debug)]
pub struct Attempt {
    pub attempt: ProofAttempt,
    pub reason: Option<String>,
    pub verdict: Option<Verdict>,
    pub time_used_ms: Option<f64>,
}

#[derive(Clone, Debug)]
pub struct Report {
    pub id: usize,
    pub location: String,
    pub text: String,
    pub status: Status,
    pub attempts: Vec<Attempt>,
}

/// A round's result: the reports of the obligations settled before the first that waits, in
/// order, and the decisions the waiting ones need. The run is done when nothing is requested.
#[derive(Debug, Default)]
pub struct Round {
    pub reports: Vec<Report>,
    pub requests: Vec<Request>,
    /// An error that is neither unsupported nor a prover's, which ends the run as
    /// `proveObligations` rethrows it, once the obligations before it are reported.
    pub error: Option<ObligationError>,
}

// Why a method left an obligation unproved: a prover decided so, or Prove It couldn't try it.
struct MethodFailure {
    reason: String,
    is_decided: bool,
}

// The backends ENCODERS has.
const ENCODED: [&str; 5] = ["smt", "z3", "zenon", "isabelle", "ls4"];

// The frontends and Prep.flatten add no CASE without OTHER, so the SMT encoder standardizes one
// only in an obligation that has one after Prep.normalize_expand.
fn has_incomplete_case(expression: &Expr) -> bool {
    matches!(expression.core, ExprCore::Case { other: None, .. })
        || get_children(expression).iter().any(has_incomplete_case)
}

fn is_incomplete_case_hyp(hyp: &Hyp) -> Result<bool> {
    let mut is_incomplete = false;
    map_hyp(
        hyp,
        &mut |inner| {
            is_incomplete |= has_incomplete_case(inner);
            Ok(inner.clone())
        },
        Hyps::All,
    )?;
    Ok(is_incomplete)
}

fn is_case_numbered(prover: &str, sequent: &Sequent) -> Result<bool> {
    if !matches!(prover, "smt" | "z3") {
        return Ok(false);
    }
    for hyp in &sequent.context {
        if is_incomplete_case_hyp(hyp)? {
            return Ok(true);
        }
    }
    Ok(has_incomplete_case(&sequent.active))
}

// Fpfile.get_timeout.
fn get_budget(method: &Method) -> f64 {
    method
        .rlimit
        .map_or(method.time_limit_ms / 1000.0, |rlimit| rlimit as f64)
}

/// FNV-1a over the text, 64 bits, in hex: the key only names a request, and a run checks that no
/// two texts share one.
fn get_digest(text: &str) -> String {
    let hash = text.bytes().fold(0xcbf2_9ce4_8422_2325_u64, |hash, byte| {
        (hash ^ u64::from(byte)).wrapping_mul(0x0100_0000_01b3)
    });
    format!("{hash:016x}")
}

/// What the rounds of one run work out the same way each time, by obligation index: its methods and
/// fingerprint, its sequent after Prep.normalize_expand, and each text a backend receives, by the
/// method and the CASE count it starts from. A round starts again from the beginning, and with it
/// costs the driver's bookkeeping and not Prep's. A caller keeps one per run, and a new run starts
/// with a new one.
#[derive(Default)]
pub struct Cache {
    heads: HashMap<usize, (FoundMethods, String)>,
    sequents: HashMap<usize, (Sequent, bool)>,
    texts: HashMap<(usize, usize, usize), (Result<String>, usize)>,
}

// What tlapm keeps across one run's obligations.
struct Run<'a> {
    answers: &'a dyn Fn(&str) -> Option<Answer>,
    cache: &'a mut Cache,
    results: HashMap<String, HashMap<String, Attempt>>,
    // The CASE errors the SMT encoder has standardized so far.
    case_errors: usize,
    // Whether an earlier obligation waits, so that later reports wait for its.
    is_waiting: bool,
    // Whether an earlier obligation that waits may still number CASE errors: one that waits before
    // its methods, or for a decision with a method after it whose SMT encoding numbers one. An
    // obligation whose encoding numbers one waits for it, as it starts from the count it leaves.
    is_count_open: bool,
    waiting_fingerprints: Vec<String>,
    texts: HashMap<String, String>,
    requests: Vec<Request>,
}

// What proving an obligation came to this round.
enum Proving {
    Settled(Report),
    // It needs these decisions first.
    Waiting,
}

impl Run<'_> {
    // The answer to a decision, or None after asking for it.
    // A decision is the obligation's, as the TypeScript decides each obligation's texts anew, even
    // one an earlier obligation sent the same backend.
    fn get_answer(
        &mut self,
        position: usize,
        method_index: usize,
        prover: &str,
        text: String,
        time_limit_ms: f64,
    ) -> Result<Option<Answer>> {
        let key = format!(
            "{position}/{method_index}/{prover}/{time_limit_ms}/{}",
            get_digest(&text)
        );
        match self.texts.get(&key) {
            // Two texts that share a key would share an answer.
            Some(known) if *known != text => return Err(ObligationError::assert_failure()),
            Some(_) => {}
            None => {
                self.texts.insert(key.clone(), text.clone());
            }
        }
        let answer = (self.answers)(&key);
        if answer.is_none() && !self.requests.iter().any(|request| request.key == key) {
            self.requests.push(Request {
                key,
                prover: prover.to_owned(),
                text,
                time_limit_ms,
                priority: position,
            });
        }
        Ok(answer)
    }

    // Prep.ship: the provers the step cites, or tlapm's default ones when it cites none, each tried
    // in turn until one proves the obligation. Prep.already_processed reuses what a prover concluded
    // for an earlier obligation with the same fingerprint: a proof, or a failure within at least as
    // much time. Unless the first prover's proof is reused, a trivial obligation needs no prover.
    fn prove(&mut self, position: usize, obligation: &PrintedObligation) -> Result<Proving> {
        let base = |status| Report {
            id: obligation.id,
            location: obligation.location.clone(),
            text: obligation.text.clone(),
            status,
            attempts: Vec::new(),
        };
        if let ObligationKind::Error(message) = &obligation.kind {
            return Ok(Proving::Settled(base(Status::Failed {
                reason: message.clone(),
            })));
        }
        let (methods, fingerprint) = match self.cache.heads.get(&position) {
            Some(head) => head.clone(),
            None => {
                let head = (
                    find_methods(&obligation.sequent, obligation.method.as_ref())?,
                    get_fingerprint(&obligation.sequent)?,
                );
                self.cache.heads.insert(position, head.clone());
                head
            }
        };
        if self.waiting_fingerprints.contains(&fingerprint) {
            self.is_count_open = true;
            return Ok(Proving::Waiting);
        }
        let mut attempts: Vec<Attempt> = Vec::new();
        let mut failures: Vec<MethodFailure> = Vec::new();
        let proved = |prover: &str, attempts: Vec<Attempt>| {
            Proving::Settled(Report {
                attempts,
                ..base(Status::Proved {
                    prover: prover.to_owned(),
                })
            })
        };
        let get_prior = |results: &HashMap<String, HashMap<String, Attempt>>, method: &Method| {
            results
                .get(&fingerprint)
                .and_then(|attempts| attempts.get(&method.prover))
                .filter(|prior| prior.attempt.method.tactic == method.tactic)
                .cloned()
        };
        let reuse = |attempts: &mut Vec<Attempt>, prior: Attempt| {
            attempts.push(Attempt {
                attempt: ProofAttempt {
                    is_reused: true,
                    ..prior.attempt
                },
                time_used_ms: None,
                ..prior
            });
        };
        if let Some(prior) = methods
            .provers
            .first()
            .and_then(|method| get_prior(&self.results, method))
            .filter(|prior| prior.attempt.is_proved)
        {
            let prover = prior.attempt.method.prover.clone();
            reuse(&mut attempts, prior);
            return Ok(proved(&prover, attempts));
        }
        let (sequent, is_numbering) = match self.cache.sequents.get(&position) {
            Some(prepared) => prepared.clone(),
            None => {
                let sequent = normalize_expand(
                    &obligation.sequent,
                    obligation.method.as_ref(),
                    Some(&methods),
                )?;
                let prepared = (sequent.clone(), is_case_numbered("smt", &sequent)?);
                self.cache.sequents.insert(position, prepared.clone());
                prepared
            }
        };
        let is_numbered_for = |prover: &str| is_numbering && matches!(prover, "smt" | "z3");
        // Fpfile.fp_writes keeps no trivial result, but adds the fingerprint.
        if matches!(obligation.kind, ObligationKind::Support) && is_trivial(&sequent)? {
            self.results.entry(fingerprint).or_default();
            return Ok(Proving::Settled(base(Status::Trivial)));
        }
        for (index, method) in methods.provers.iter().enumerate() {
            let prior = get_prior(&self.results, method);
            if let Some(prior) = prior.clone().filter(|prior| prior.attempt.is_proved) {
                reuse(&mut attempts, prior);
                return Ok(proved(&method.prover, attempts));
            }
            if let Some(prior) =
                prior.filter(|prior| get_budget(&prior.attempt.method) >= get_budget(method))
            {
                reuse(&mut attempts, prior);
                failures.push(MethodFailure {
                    reason: format!(
                        "{} failed on an obligation with the same fingerprint",
                        method.prover
                    ),
                    is_decided: true,
                });
                continue;
            }
            // Prep.prove_with: the Trivial method proves anything.
            if method.prover == "trivial" {
                return Ok(proved(&method.prover, attempts));
            }
            let skip =
                |attempts: &mut Vec<Attempt>, failures: &mut Vec<MethodFailure>, reason: String| {
                    attempts.push(Attempt {
                        attempt: ProofAttempt {
                            method: method.clone(),
                            is_proved: false,
                            is_reused: false,
                        },
                        reason: Some(reason.clone()),
                        verdict: None,
                        time_used_ms: None,
                    });
                    failures.push(MethodFailure {
                        reason,
                        is_decided: false,
                    });
                };
            if !ENCODED.contains(&method.prover.as_str()) {
                skip(
                    &mut attempts,
                    &mut failures,
                    format!("tla-ts has no {} backend", method.prover),
                );
                continue;
            }
            let is_numbered = is_numbered_for(&method.prover);
            if is_numbered && self.is_count_open {
                self.waiting_fingerprints.push(fingerprint);
                return Ok(Proving::Waiting);
            }
            let start = if is_numbered { self.case_errors } else { 0 };
            let (encoded, end) = match self.cache.texts.get(&(position, index, start)) {
                Some(encoded) => encoded.clone(),
                None => {
                    let mut session = EncodingSession { case_errors: start };
                    let encoded = encode_normalized(
                        &method.prover,
                        obligation.id,
                        &sequent,
                        method,
                        &mut session,
                    );
                    let entry = (encoded, session.case_errors);
                    self.cache
                        .texts
                        .insert((position, index, start), entry.clone());
                    entry
                }
            };
            if is_numbered {
                self.case_errors = end;
            }
            let answer = match encoded {
                Ok(text) => {
                    match self.get_answer(
                        position,
                        index,
                        &method.prover,
                        text,
                        method.time_limit_ms,
                    )? {
                        Some(answer) => answer,
                        None => {
                            self.is_count_open |= methods.provers[index + 1..]
                                .iter()
                                .any(|later| is_numbered_for(&later.prover));
                            self.waiting_fingerprints.push(fingerprint);
                            return Ok(Proving::Waiting);
                        }
                    }
                }
                Err(ObligationError::Prover(message)) => Answer::Failed(message),
                Err(ObligationError::Unsupported(message)) => {
                    skip(
                        &mut attempts,
                        &mut failures,
                        format!("{} can't encode {message}", method.prover),
                    );
                    continue;
                }
                Err(error) => return Err(error),
            };
            let attempt = match answer {
                Answer::Decided {
                    verdict,
                    time_used_ms,
                } => {
                    let is_proved = verdict == Verdict::Unsat;
                    if !is_proved {
                        failures.push(MethodFailure {
                            reason: format!("{} answered {}", method.prover, verdict.name()),
                            is_decided: true,
                        });
                    }
                    Attempt {
                        attempt: ProofAttempt {
                            method: method.clone(),
                            is_proved,
                            is_reused: false,
                        },
                        reason: (!is_proved).then(|| {
                            if time_used_ms >= method.time_limit_ms {
                                "timeout".to_owned()
                            } else {
                                "false".to_owned()
                            }
                        }),
                        verdict: Some(verdict),
                        time_used_ms: Some(time_used_ms),
                    }
                }
                Answer::Unsupported(message) => {
                    skip(
                        &mut attempts,
                        &mut failures,
                        format!("{} can't encode {message}", method.prover),
                    );
                    continue;
                }
                Answer::Failed(message) => {
                    failures.push(MethodFailure {
                        reason: format!("{} failed: {message}", method.prover),
                        is_decided: true,
                    });
                    Attempt {
                        attempt: ProofAttempt {
                            method: method.clone(),
                            is_proved: false,
                            is_reused: false,
                        },
                        reason: Some("false".to_owned()),
                        verdict: None,
                        time_used_ms: None,
                    }
                }
            };
            let is_proved = attempt.attempt.is_proved;
            attempts.push(attempt.clone());
            self.results
                .entry(fingerprint.clone())
                .or_default()
                .insert(method.prover.clone(), attempt);
            if is_proved {
                return Ok(proved(&method.prover, attempts));
            }
        }
        let is_decided = failures.iter().any(|failure| failure.is_decided);
        let reason = failures
            .iter()
            .map(|failure| failure.reason.as_str())
            .collect::<Vec<_>>()
            .join(", ");
        Ok(Proving::Settled(Report {
            attempts,
            ..base(if is_decided {
                Status::Failed { reason }
            } else {
                Status::Unsupported { reason }
            })
        }))
    }
}

/// One round of proving `obligations`, with the decisions `answers` gives by key.
pub fn prove_obligations(
    obligations: &[PrintedObligation],
    answers: &dyn Fn(&str) -> Option<Answer>,
    cache: &mut Cache,
) -> Result<Round> {
    let mut run = Run {
        answers,
        cache,
        results: HashMap::new(),
        case_errors: 0,
        is_waiting: false,
        is_count_open: false,
        waiting_fingerprints: Vec::new(),
        texts: HashMap::new(),
        requests: Vec::new(),
    };
    let mut round = Round::default();
    for (position, obligation) in obligations.iter().enumerate() {
        // An error that escapes proveWithBackends: what Prove It can't handle is unsupported, and
        // what tlapm refuses, as a frontend's soundness check, fails.
        let proving = match run.prove(position, obligation) {
            Ok(proving) => proving,
            Err(ObligationError::Unsupported(reason)) => Proving::Settled(Report {
                id: obligation.id,
                location: obligation.location.clone(),
                text: obligation.text.clone(),
                status: Status::Unsupported { reason },
                attempts: Vec::new(),
            }),
            Err(ObligationError::Prover(reason)) => Proving::Settled(Report {
                id: obligation.id,
                location: obligation.location.clone(),
                text: obligation.text.clone(),
                status: Status::Failed { reason },
                attempts: Vec::new(),
            }),
            // It surfaces once every earlier obligation is settled, as the TypeScript reports in
            // order.
            Err(_) if run.is_waiting => break,
            Err(error) => {
                round.error = Some(error);
                break;
            }
        };
        match proving {
            Proving::Settled(report) if !run.is_waiting => round.reports.push(report),
            Proving::Settled(_) => {}
            Proving::Waiting => run.is_waiting = true,
        }
    }
    round.requests = run.requests;
    Ok(round)
}
