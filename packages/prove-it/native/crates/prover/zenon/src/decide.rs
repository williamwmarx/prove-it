// Ported from Zenon's main.ml, as shipped in tlapm. Copyright 1997 INRIA, see LICENSE.
//! Runs Zenon on a .znn file as tlapm does, with -oisar. A proof counts only once the independent
//! checker accepts it. tlapm passes -max-time 1d and kills Zenon at its own timeout instead,
//! whether Zenon is still reading, searching or printing the proof.

use std::collections::HashSet;
use std::rc::Rc;

use prove_decide::Limits;

use crate::ZenonError;
use crate::check::{CheckContext, check_proof};
use crate::eqrel::Relations;
use crate::expr::Expressions;
use crate::index_table::Index;
use crate::isar::{IsarContext, print_isar};
use crate::limits::get_stop_reason;
use crate::parse::{Phrase, parse_zenon};
use crate::phrase::separate;
use crate::proof::Proof;
use crate::rules::SearchContext;
use crate::search::{SearchOutcome, SearchStatistics, search};
use crate::tla::{PREDEFINED_SYMBOLS, get_built_in_definitions};

pub struct ZenonRun {
    pub proof: Option<Rc<Proof>>,
    /// Why Zenon gave up: in the search, or at the limits while it checked or printed the proof.
    /// "zenon error" stands for the errors that stop Zenon mid-search.
    pub failure: Option<&'static str>,
    /// Zenon's -oisar output, once the checker accepts the proof and the printer ends within the
    /// limits.
    pub isar: Option<String>,
    pub nodes_searched: u64,
    pub max_branch_formulas: u64,
    pub proof_nodes: u64,
    pub formulas_created: u64,
}

/// The search and its statistics, which match the -stats output of the OCaml Zenon: `runZenon`.
/// Fails when the text isn't a valid .znn file.
pub fn run_zenon(text: &str, limits: &Limits) -> Result<ZenonRun, ZenonError> {
    let exprs = Expressions::new();
    let parsed = parse_zenon(&exprs, text)?;
    let phrases: Vec<Phrase> = get_built_in_definitions(&exprs)
        .into_iter()
        .chain(parsed.iter().cloned())
        .collect();
    let separated = separate(PREDEFINED_SYMBOLS, &phrases);
    let mut relations = Relations::new();
    for hypothesis in &separated.hypotheses {
        relations.analyse(&exprs, &hypothesis.formula);
    }
    let hypotheses: Vec<_> = separated
        .hypotheses
        .iter()
        .filter(|hypothesis| !relations.is_subsumed(&exprs, &hypothesis.formula))
        .cloned()
        .collect();
    let mut context = SearchContext {
        index: Index::new(),
        relations,
        exprs,
    };
    let mut statistics = SearchStatistics {
        inferences: 0,
        proof_nodes: 0,
        reused_proofs: HashSet::new(),
    };
    let outcome = search(
        &mut context,
        &separated.definitions,
        &hypotheses,
        limits,
        &mut statistics,
    );
    let search_failure = match &outcome {
        Ok(SearchOutcome::Failure(failure)) => Some(*failure),
        Ok(SearchOutcome::Proof(_)) => None,
        Err(_) => Some("zenon error"),
    };
    let proof = match outcome {
        Ok(SearchOutcome::Proof(proof)) => Some(proof),
        _ => None,
    };
    let is_checked = proof.as_ref().is_some_and(|proof| {
        let check_context = CheckContext {
            hypotheses: phrases
                .iter()
                .filter_map(|phrase| match phrase {
                    Phrase::Hyp { formula, .. } => Some(formula.clone()),
                    Phrase::Def(_) => None,
                })
                .collect(),
            definitions: separated.definitions.clone(),
        };
        check_proof(proof, &check_context, limits)
    });
    let isar = match &proof {
        Some(proof) if is_checked => print_isar(
            proof,
            IsarContext {
                exprs: &context.exprs,
                phrases: &parsed,
                shared_proofs: &statistics.reused_proofs,
                relations: &context.relations,
                limits,
            },
        )?,
        _ => None,
    };
    Ok(ZenonRun {
        failure: search_failure.or_else(|| {
            if isar.is_none() {
                get_stop_reason(limits)
            } else {
                None
            }
        }),
        proof,
        isar,
        nodes_searched: statistics.inferences,
        max_branch_formulas: context.index.get_top_formula_count(),
        proof_nodes: statistics.proof_nodes,
        formulas_created: context.exprs.get_created_count(),
    })
}

#[derive(Debug, PartialEq, Eq)]
pub enum ZenonDecision {
    /// The Isar proof that tlapm writes.
    Unsat(String),
    Unknown,
}

/// Zenon's verdict on a .znn file: `decideZenon`, with the run for its statistics.
pub fn decide_zenon(text: &str, limits: &Limits) -> Result<ZenonDecision, ZenonError> {
    Ok(match run_zenon(text, limits)?.isar {
        Some(isar) => ZenonDecision::Unsat(isar),
        None => ZenonDecision::Unknown,
    })
}

/// The length and FNV-1a hash of a text's UTF-16 code units: `getTextDigest`.
pub fn get_text_digest(text: &str) -> String {
    let (length, hash) =
        text.encode_utf16()
            .fold((0usize, 0x811c_9dc5u32), |(length, state), unit| {
                (
                    length + 1,
                    (state ^ u32::from(unit)).wrapping_mul(0x0100_0193),
                )
            });
    format!("{length}:{hash:08x}")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn digests_a_text_as_the_typescript_does() {
        assert_eq!(get_text_digest(""), "0:811c9dc5");
        assert_eq!(get_text_digest("abc"), "3:1a47e90b");
    }
}
