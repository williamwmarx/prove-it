//! Prep.ship's encoding: the text each backend receives for an obligation, after Prep.normalize_expand
//! and the backend's frontend, and the theory of the proofs Isabelle found. The encoding slice of
//! `src/prover/prove.ts`; deciding, threads and reuse are stage P6.

use crate::errors::{ObligationError, Result};
use crate::expression::Sequent;
use crate::index::PrintedObligation;
use crate::isabelle::encode::{
    IsabelleProof, encode_isabelle, join_isabelle_theory, write_isabelle_proof,
};
use crate::prep::action::process_obligation;
use crate::prep::methods::{Method, find_methods};
use crate::prep::normalize::{flatten, normalize_expand};
use crate::ptl::encode::encode_ptl;
use crate::smt::encode::encode_smt;
use crate::smt::rewrite::EncodingSession;
use crate::zenon::encode::encode_zenon;

// The text Prep.ship sends a backend after Prep.normalize_expand. It fails with an unsupported
// error for what Prove It can't encode.
type Encoder = fn(usize, &Sequent, &Method, &mut EncodingSession) -> Result<String>;

// Action.process_obligation, the frontend for every backend but LS4, Isabelle included, then
// Prep.flatten.
fn ship_first_order(sequent: &Sequent) -> Result<Sequent> {
    flatten(&process_obligation(sequent)?)
}

// Prep.gen_smt_solve writes the resource budget before the encoding.
fn encode_smt_problem(
    _id: usize,
    sequent: &Sequent,
    method: &Method,
    session: &mut EncodingSession,
) -> Result<String> {
    let budget = match method.rlimit {
        None => String::new(),
        Some(rlimit) => format!("(set-option :rlimit {rlimit})\n"),
    };
    Ok(budget + &encode_smt(&ship_first_order(sequent)?, session)?)
}

fn encode_zenon_problem(
    id: usize,
    sequent: &Sequent,
    _method: &Method,
    _session: &mut EncodingSession,
) -> Result<String> {
    encode_zenon(id, &ship_first_order(sequent)?)
}

// tlapm names the theory after its temporary file, and Prove It after the obligation.
fn encode_isabelle_problem(
    id: usize,
    sequent: &Sequent,
    method: &Method,
    _session: &mut EncodingSession,
) -> Result<String> {
    encode_isabelle(
        id,
        &ship_first_order(sequent)?,
        method.tactic.as_deref().unwrap_or("auto"),
    )
}

// Pltl.process_obligation is LS4's frontend.
fn encode_ls4_problem(
    _id: usize,
    sequent: &Sequent,
    _method: &Method,
    _session: &mut EncodingSession,
) -> Result<String> {
    encode_ptl(sequent)
}

// The ENCODERS table.
fn get_encoder(prover: &str) -> Option<Encoder> {
    match prover {
        "smt" | "z3" => Some(encode_smt_problem),
        "zenon" => Some(encode_zenon_problem),
        "isabelle" => Some(encode_isabelle_problem),
        "ls4" => Some(encode_ls4_problem),
        _ => None,
    }
}

/// The text one backend receives for an obligation, for comparing with tlapm's. The SMT encoder
/// counts in `session` the CASE errors it standardizes, so a run passes each obligation the count
/// the earlier ones leave.
pub fn encode_for_backend(
    obligation: &PrintedObligation,
    prover: &str,
    session: &mut EncodingSession,
) -> Result<String> {
    let encode = get_encoder(prover)
        .ok_or_else(|| ObligationError::unsupported(format!("the {prover} backend")))?;
    let methods = find_methods(&obligation.sequent, obligation.method.as_ref())?;
    let method = methods
        .provers
        .iter()
        .find(|candidate| candidate.prover == prover)
        .cloned()
        .unwrap_or_else(|| Method {
            prover: prover.to_owned(),
            time_limit_ms: f64::INFINITY,
            rlimit: None,
            tactic: None,
        });
    let sequent = normalize_expand(
        &obligation.sequent,
        obligation.method.as_ref(),
        Some(&methods),
    )?;
    encode(obligation.id, &sequent, &method, session)
}

/// What one method concluded about an obligation, as far as the theory needs it.
#[derive(Clone, Debug)]
pub struct ProofAttempt {
    pub method: Method,
    pub is_proved: bool,
    pub is_reused: bool,
}

/// The theory of the proofs Isabelle found, from each obligation's attempts (its report's) in
/// order. tlapm also writes Zenon's proofs there. The TypeScript makes every proof's sequent
/// before it writes any; this writes each as it makes it and keeps only its lines, which fails
/// the same way, since a sequent's error comes first and writing depends on the proof alone, but
/// holds no sequent: a module's thousands of them can take gigabytes.
pub fn encode_proof_theory(
    name: &str,
    attempts: &[Vec<ProofAttempt>],
    obligations: &[PrintedObligation],
) -> Result<String> {
    let mut proofs = Vec::new();
    for (index, report) in attempts.iter().enumerate() {
        for attempt in report {
            if attempt.method.prover != "isabelle" || !attempt.is_proved || attempt.is_reused {
                continue;
            }
            let obligation = obligations
                .get(index)
                .ok_or_else(ObligationError::assert_failure)?;
            proofs.push(write_isabelle_proof(&IsabelleProof {
                id: obligation.id,
                sequent: ship_first_order(&normalize_expand(
                    &obligation.sequent,
                    obligation.method.as_ref(),
                    None,
                )?)?,
                tactic: attempt.method.tactic.clone().unwrap_or("auto".to_owned()),
            }));
        }
    }
    join_isabelle_theory(name, proofs)
}
