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

use crate::tlapm_cache::{KnownAttempt, KnownAttempts, KnownResults};

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

impl Attempt {
    /// Whether Prove It couldn't try the method: it has no backend for it, or can't encode the
    /// obligation for it.
    pub fn is_skipped(&self) -> bool {
        !self.attempt.is_proved
            && !self.attempt.is_reused
            && self.verdict.is_none()
            && self
                .reason
                .as_deref()
                .is_some_and(|reason| reason != "false" && reason != "timeout")
    }
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
    /// What each prover concluded for each fingerprint: what the run started from, with what it
    /// concluded since, which the fingerprints file saves once the run is done.
    pub results: KnownResults,
}

/// What `proveObligations` takes of tlapm's command line: the results it starts from (the
/// fingerprints file), whether an obligation may reuse a result (`--nofp` and `--nofpl` forget
/// them), and whether it proves at all (`--noproving` only reuses).
pub struct Settings {
    pub known: KnownResults,
    pub is_fingerprinted: Box<dyn Fn(&PrintedObligation) -> bool>,
    pub is_proving: bool,
}

impl Default for Settings {
    fn default() -> Self {
        Settings {
            known: KnownResults::default(),
            is_fingerprinted: Box::new(|_| true),
            is_proving: true,
        }
    }
}

// Why a method left an obligation unproved: a prover decided so, or Prove It couldn't try it.
#[derive(Debug)]
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

// What tlapm keeps across one run's obligations. A round (`prove_obligations_with`) answers the
// decisions from `answers`; a `Prover` hands each to its caller.
struct Run<'a> {
    obligations: &'a [PrintedObligation],
    answers: &'a dyn Fn(&str) -> Option<Answer>,
    cache: &'a mut Cache,
    settings: &'a Settings,
    results: KnownResults,
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
    // Whether a prover's results for a fingerprint merge as tlapm's table merges them, as the
    // scheduler's do, or the last replaces the one held, as the TypeScript's rounds do.
    is_merged: bool,
}

// What proving an obligation came to this round.
enum Proving {
    Settled(Report),
    // It needs these decisions first.
    Waiting,
}

/// An obligation as Prep.ship tries it: a thunk for each of its methods, each evaluated in turn,
/// where Prep.already_processed reads what the results hold then, until one proves it.
#[derive(Debug)]
pub struct Task {
    pub position: usize,
    is_started: bool,
    next: usize,
    pending: Option<usize>,
    attempts: Vec<Attempt>,
    failures: Vec<MethodFailure>,
}

impl Task {
    pub fn new(position: usize) -> Task {
        Task {
            position,
            is_started: false,
            next: 0,
            pending: None,
            attempts: Vec::new(),
            failures: Vec::new(),
        }
    }

    /// What its methods concluded so far, in order.
    pub fn attempts(&self) -> &[Attempt] {
        &self.attempts
    }
}

/// Where a task's thunks came to: it is settled, it needs a decision, or, in a round, it waits for
/// an earlier obligation's CASE count.
pub enum Step {
    Settled(Report),
    Decide(Request),
    Blocked,
}

impl Run<'_> {
    fn get_head(&mut self, position: usize) -> Result<(FoundMethods, String)> {
        if let Some(head) = self.cache.heads.get(&position) {
            return Ok(head.clone());
        }
        let obligation = &self.obligations[position];
        let head = (
            find_methods(&obligation.sequent, obligation.method.as_ref())?,
            get_fingerprint(&obligation.sequent)?,
        );
        self.cache.heads.insert(position, head.clone());
        Ok(head)
    }

    fn get_prepared(&mut self, position: usize, methods: &FoundMethods) -> Result<(Sequent, bool)> {
        if let Some(prepared) = self.cache.sequents.get(&position) {
            return Ok(prepared.clone());
        }
        let obligation = &self.obligations[position];
        let sequent = normalize_expand(
            &obligation.sequent,
            obligation.method.as_ref(),
            Some(methods),
        )?;
        let prepared = (sequent.clone(), is_case_numbered("smt", &sequent)?);
        self.cache.sequents.insert(position, prepared.clone());
        Ok(prepared)
    }

    // The request for a decision, by a key that names it.
    // A decision is the obligation's, as the TypeScript decides each obligation's texts anew, even
    // one an earlier obligation sent the same backend.
    fn get_request(
        &mut self,
        position: usize,
        method_index: usize,
        prover: &str,
        text: String,
        time_limit_ms: f64,
    ) -> Result<Request> {
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
        Ok(Request {
            key,
            prover: prover.to_owned(),
            text,
            time_limit_ms,
            priority: position,
        })
    }

    fn get_base(&self, position: usize, status: Status, attempts: Vec<Attempt>) -> Report {
        let obligation = &self.obligations[position];
        Report {
            id: obligation.id,
            location: obligation.location.clone(),
            text: obligation.text.clone(),
            status,
            attempts,
        }
    }

    // Prep.already_processed, which forgets the fingerprint's results on each call under --nofp,
    // and keeps a result of the method's prover with its tactic.
    fn get_prior(
        &mut self,
        position: usize,
        fingerprint: &str,
        method: &Method,
    ) -> Option<Attempt> {
        if !(self.settings.is_fingerprinted)(&self.obligations[position]) {
            self.results.results.remove(fingerprint);
        }
        self.results
            .results
            .get(fingerprint)
            .and_then(|known| known.attempts.get(&method.prover))
            .map(|known| &known.attempt)
            .filter(|prior| prior.attempt.method.tactic == method.tactic)
            .cloned()
    }

    fn settle_proved(&self, task: &mut Task, prover: &str) -> Step {
        let attempts = std::mem::take(&mut task.attempts);
        Step::Settled(self.get_base(
            task.position,
            Status::Proved {
                prover: prover.to_owned(),
            },
            attempts,
        ))
    }

    // Prep.ship: the provers the step cites, or tlapm's default ones when it cites none, each tried
    // in turn until one proves the obligation. Prep.already_processed reuses what a prover concluded
    // for an obligation with the same fingerprint: a proof, or a failure within at least as much
    // time. Unless the first prover's proof is reused, a trivial obligation needs no prover. Each
    // thunk evaluated here reads the results as they are now; a decision ends the step, and the
    // next step evaluates the thunk after it. In a round (`is_round`), an obligation whose SMT
    // encoding numbers a CASE waits while an earlier obligation may still number one.
    fn step(&mut self, task: &mut Task, is_round: bool) -> Result<Step> {
        let position = task.position;
        if let ObligationKind::Error(message) = &self.obligations[position].kind {
            return Ok(Step::Settled(self.get_base(
                position,
                Status::Failed {
                    reason: message.clone(),
                },
                Vec::new(),
            )));
        }
        let (methods, fingerprint) = self.get_head(position)?;
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
        if !task.is_started {
            task.is_started = true;
            if let Some(prior) = methods
                .provers
                .first()
                .and_then(|method| self.get_prior(position, &fingerprint, method))
                .filter(|prior| prior.attempt.is_proved)
            {
                let prover = prior.attempt.method.prover.clone();
                reuse(&mut task.attempts, prior);
                return Ok(self.settle_proved(task, &prover));
            }
            let (sequent, _) = self.get_prepared(position, &methods)?;
            // Fpfile.fp_writes keeps no trivial result, but adds the fingerprint.
            if matches!(self.obligations[position].kind, ObligationKind::Support)
                && is_trivial(&sequent)?
            {
                self.results
                    .results
                    .get_or_insert_with(fingerprint, KnownAttempts::default);
                return Ok(Step::Settled(self.get_base(
                    position,
                    Status::Trivial,
                    Vec::new(),
                )));
            }
        }
        let (sequent, is_numbering) = self.get_prepared(position, &methods)?;
        let is_numbered_for = |prover: &str| is_numbering && matches!(prover, "smt" | "z3");
        while task.next < methods.provers.len() {
            let index = task.next;
            let method = &methods.provers[index];
            let prior = self.get_prior(position, &fingerprint, method);
            if let Some(prior) = prior.clone().filter(|prior| prior.attempt.is_proved) {
                reuse(&mut task.attempts, prior);
                return Ok(self.settle_proved(task, &method.prover));
            }
            if let Some(prior) =
                prior.filter(|prior| get_budget(&prior.attempt.method) >= get_budget(method))
            {
                reuse(&mut task.attempts, prior);
                task.failures.push(MethodFailure {
                    reason: format!(
                        "{} failed on an obligation with the same fingerprint",
                        method.prover
                    ),
                    is_decided: true,
                });
                task.next += 1;
                continue;
            }
            if !self.settings.is_proving {
                task.next += 1;
                continue;
            }
            // Prep.prove_with: the Trivial method proves anything.
            if method.prover == "trivial" {
                return Ok(self.settle_proved(task, &method.prover));
            }
            if !ENCODED.contains(&method.prover.as_str()) {
                skip(
                    task,
                    method,
                    format!("tla-ts has no {} backend", method.prover),
                );
                task.next += 1;
                continue;
            }
            let is_numbered = is_numbered_for(&method.prover);
            if is_round && is_numbered && self.is_count_open {
                self.waiting_fingerprints.push(fingerprint);
                return Ok(Step::Blocked);
            }
            let start = if is_numbered { self.case_errors } else { 0 };
            let (encoded, end) = match self.cache.texts.get(&(position, index, start)) {
                Some(encoded) => encoded.clone(),
                None => {
                    let mut session = EncodingSession { case_errors: start };
                    let encoded = encode_normalized(
                        &method.prover,
                        self.obligations[position].id,
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
            match encoded {
                Ok(text) => {
                    let request = self.get_request(
                        position,
                        index,
                        &method.prover,
                        text,
                        method.time_limit_ms,
                    )?;
                    task.pending = Some(index);
                    task.next += 1;
                    return Ok(Step::Decide(request));
                }
                Err(ObligationError::Prover(message)) => {
                    task.pending = Some(index);
                    task.next += 1;
                    if let Some(report) = self.answer(task, Answer::Failed(message))? {
                        return Ok(Step::Settled(report));
                    }
                }
                Err(ObligationError::Unsupported(message)) => {
                    skip(
                        task,
                        method,
                        format!("{} can't encode {message}", method.prover),
                    );
                    task.next += 1;
                }
                Err(error) => return Err(error),
            }
        }
        let is_decided = task.failures.iter().any(|failure| failure.is_decided);
        let reason = task
            .failures
            .iter()
            .map(|failure| failure.reason.as_str())
            .collect::<Vec<_>>()
            .join(", ");
        let attempts = std::mem::take(&mut task.attempts);
        Ok(Step::Settled(self.get_base(
            position,
            if is_decided {
                Status::Failed { reason }
            } else {
                Status::Unsupported { reason }
            },
            attempts,
        )))
    }

    // The answer to the task's decision, as Prep's result continuation takes it: it saves what the
    // method concluded, and settles the task where it proved it.
    fn answer(&mut self, task: &mut Task, answer: Answer) -> Result<Option<Report>> {
        let index = task
            .pending
            .take()
            .ok_or_else(ObligationError::assert_failure)?;
        let (methods, fingerprint) = self.get_head(task.position)?;
        let method = &methods.provers[index];
        let attempt = match answer {
            Answer::Decided {
                verdict,
                time_used_ms,
            } => {
                let is_proved = verdict == Verdict::Unsat;
                if !is_proved {
                    task.failures.push(MethodFailure {
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
                    task,
                    method,
                    format!("{} can't encode {message}", method.prover),
                );
                return Ok(None);
            }
            Answer::Failed(message) => {
                task.failures.push(MethodFailure {
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
        task.attempts.push(attempt.clone());
        self.save(fingerprint, attempt);
        if !is_proved {
            return Ok(None);
        }
        let Step::Settled(report) = self.settle_proved(task, &method.prover) else {
            unreachable!("a proved task settles");
        };
        Ok(Some(report))
    }

    // Fpfile.add_to_table: of a prover's results for a fingerprint, the table keeps the greatest by
    // Fpfile.order, a proof over a failure, of proofs the one with the shorter time limit, of
    // failures the one with the longer, and of two equal the one it held.
    fn save(&mut self, fingerprint: String, attempt: Attempt) {
        let attempts = &mut self
            .results
            .results
            .get_or_insert_with(fingerprint, KnownAttempts::default)
            .attempts;
        let prover = attempt.attempt.method.prover.clone();
        let is_merged = self.is_merged;
        let is_greater = !is_merged
            || attempts.get(&prover).is_none_or(|held| {
                let (new, old) = (&attempt.attempt, &held.attempt.attempt);
                let (new_budget, old_budget) = (get_budget(&new.method), get_budget(&old.method));
                match (new.is_proved, old.is_proved) {
                    (true, false) => true,
                    (false, true) => false,
                    (true, true) => old_budget > new_budget,
                    (false, false) => new_budget > old_budget,
                }
            });
        if is_greater {
            attempts.insert(prover, KnownAttempt::new(attempt));
        }
    }

    // An obligation in a round: its thunks in turn, each decision answered from `answers`. It
    // waits for an earlier obligation with the same fingerprint, whose results it may reuse.
    fn prove(&mut self, position: usize) -> Result<Proving> {
        if !matches!(self.obligations[position].kind, ObligationKind::Error(_)) {
            let (_, fingerprint) = self.get_head(position)?;
            if self.waiting_fingerprints.contains(&fingerprint) {
                self.is_count_open = true;
                return Ok(Proving::Waiting);
            }
        }
        let mut task = Task::new(position);
        loop {
            match self.step(&mut task, true)? {
                Step::Settled(report) => return Ok(Proving::Settled(report)),
                Step::Blocked => return Ok(Proving::Waiting),
                Step::Decide(request) => match (self.answers)(&request.key) {
                    Some(answer) => {
                        if let Some(report) = self.answer(&mut task, answer)? {
                            return Ok(Proving::Settled(report));
                        }
                    }
                    None => {
                        if !self.requests.iter().any(|known| known.key == request.key) {
                            self.requests.push(request);
                        }
                        let (methods, fingerprint) = self.get_head(position)?;
                        let (_, is_numbering) = self.get_prepared(position, &methods)?;
                        let index = task.next;
                        self.is_count_open |= is_numbering
                            && methods.provers[index..]
                                .iter()
                                .any(|later| matches!(later.prover.as_str(), "smt" | "z3"));
                        self.waiting_fingerprints.push(fingerprint);
                        return Ok(Proving::Waiting);
                    }
                },
            }
        }
    }
}

// A method Prove It couldn't try: it has no backend for it, or can't encode the obligation for it.
fn skip(task: &mut Task, method: &Method, reason: String) {
    task.attempts.push(Attempt {
        attempt: ProofAttempt {
            method: method.clone(),
            is_proved: false,
            is_reused: false,
        },
        reason: Some(reason.clone()),
        verdict: None,
        time_used_ms: None,
    });
    task.failures.push(MethodFailure {
        reason,
        is_decided: false,
    });
}

/// The driver as tlapm's scheduler runs it (`Schedule.run`): the caller starts each task, evaluates
/// its thunks when the scheduler would (`step`), and hands each decision's answer back when it is
/// made (`answer`), so that each thunk reads the results saved by then.
pub struct Prover<'a> {
    run: Run<'a>,
}

impl<'a> Prover<'a> {
    pub fn new(
        obligations: &'a [PrintedObligation],
        cache: &'a mut Cache,
        settings: &'a Settings,
    ) -> Prover<'a> {
        Prover {
            run: Run {
                obligations,
                answers: &|_| None,
                cache,
                settings,
                results: settings.known.clone(),
                case_errors: 0,
                is_waiting: false,
                is_count_open: false,
                waiting_fingerprints: Vec::new(),
                texts: HashMap::new(),
                requests: Vec::new(),
                is_merged: true,
            },
        }
    }

    /// Evaluates the task's thunks from where it left off, up to a decision or its end. An error
    /// that is neither unsupported nor a prover's ends the run.
    pub fn step(&mut self, task: &mut Task) -> Result<Step> {
        match self.run.step(task, false) {
            Err(error) => self.settle_error(task, error).map(Step::Settled),
            step => step,
        }
    }

    /// The answer to the decision the task's last step asked for; its report where it settles it.
    pub fn answer(&mut self, task: &mut Task, answer: Answer) -> Result<Option<Report>> {
        match self.run.answer(task, answer) {
            Err(error) => self.settle_error(task, error).map(Some),
            answered => answered,
        }
    }

    // What Prove It can't handle is unsupported, and what tlapm refuses, as a frontend's soundness
    // check, fails.
    fn settle_error(&self, task: &Task, error: ObligationError) -> Result<Report> {
        let status = match error {
            ObligationError::Unsupported(reason) => Status::Unsupported { reason },
            ObligationError::Prover(reason) => Status::Failed { reason },
            error => return Err(error),
        };
        Ok(self.run.get_base(task.position, status, Vec::new()))
    }

    /// The obligation's fingerprint and its methods' provers.
    pub fn get_methods(&mut self, position: usize) -> Result<(String, Vec<String>)> {
        if matches!(
            self.run.obligations[position].kind,
            ObligationKind::Error(_)
        ) {
            return Ok((String::new(), Vec::new()));
        }
        let (methods, fingerprint) = self.run.get_head(position)?;
        Ok((
            fingerprint,
            methods
                .provers
                .iter()
                .map(|method| method.prover.clone())
                .collect(),
        ))
    }

    /// Whether an SMT method of the obligation would number its CASE errors from the run's count.
    pub fn is_numbering(&mut self, position: usize) -> Result<bool> {
        if matches!(
            self.run.obligations[position].kind,
            ObligationKind::Error(_)
        ) {
            return Ok(false);
        }
        let (methods, _) = self.run.get_head(position)?;
        Ok(self.run.get_prepared(position, &methods)?.1)
    }

    /// The thunks of the task not evaluated yet, by index into its methods.
    pub fn get_next(&self, task: &Task) -> usize {
        task.next
    }

    /// What each prover concluded for each fingerprint, which the fingerprints file saves.
    pub fn into_results(self) -> KnownResults {
        self.run.results
    }
}

/// One round of proving `obligations`, with the decisions `answers` gives by key.
pub fn prove_obligations(
    obligations: &[PrintedObligation],
    answers: &dyn Fn(&str) -> Option<Answer>,
    cache: &mut Cache,
) -> Result<Round> {
    prove_obligations_with(obligations, answers, cache, &Settings::default())
}

/// `prove_obligations` as tlapm's command line sets it.
pub fn prove_obligations_with(
    obligations: &[PrintedObligation],
    answers: &dyn Fn(&str) -> Option<Answer>,
    cache: &mut Cache,
    settings: &Settings,
) -> Result<Round> {
    let mut run = Run {
        obligations,
        answers,
        cache,
        settings,
        results: settings.known.clone(),
        case_errors: 0,
        is_waiting: false,
        is_count_open: false,
        waiting_fingerprints: Vec::new(),
        texts: HashMap::new(),
        requests: Vec::new(),
        is_merged: false,
    };
    let mut round = Round::default();
    for (position, obligation) in obligations.iter().enumerate() {
        // An error that escapes proveWithBackends: what Prove It can't handle is unsupported, and
        // what tlapm refuses, as a frontend's soundness check, fails.
        let proving = match run.prove(position) {
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
    round.results = run.results;
    Ok(round)
}
