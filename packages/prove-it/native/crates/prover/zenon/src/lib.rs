//! A port of Zenon as tlapm ships it, with its TLA+ extension and an independent check of each
//! proof, on the .znn text tlapm writes: `src/prover/zenon` in TypeScript (design/prover.md, P2).
//! Zenon is Copyright INRIA, under the licence in `LICENSE` beside this crate; `ocaml` ports parts
//! of OCaml's standard library under the LGPL with OCaml's linking exception.

pub mod check;
pub mod decide;
pub mod eqrel;
pub mod equality_rules;
pub mod expr;
pub mod index_table;
pub mod isar;
pub mod isar_case;
pub mod limits;
pub mod llproof;
pub mod mltoll;
pub mod node;
pub mod ocaml;
pub mod parse;
pub mod phrase;
pub mod proof;
pub mod propositional_rules;
pub mod rules;
pub mod search;
pub mod tla;

use prove_decide::{DecideError, Decision, Limits, Statistic, Verdict};

/// A malformed input or a failure that stops Zenon: `TlaZenonError`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ZenonError(pub String);

impl ZenonError {
    pub fn new(message: impl Into<String>) -> ZenonError {
        ZenonError(message.into())
    }
}

/// Zenon's verdict on a .znn file, with the statistics `decideZenon` reports, in its order. Input
/// that isn't a valid .znn file is declined, so that the TypeScript reports it with its own error.
pub fn decide(text: &str, limits: &Limits) -> Result<Decision, DecideError> {
    let run = decide::run_zenon(text, limits).map_err(|error| DecideError::Declined(error.0))?;
    let mut statistics = vec![
        ("steps", Statistic::Count(limits.steps())),
        ("nodesSearched", Statistic::Count(run.nodes_searched)),
        (
            "maxBranchFormulas",
            Statistic::Count(run.max_branch_formulas),
        ),
        ("proofNodes", Statistic::Count(run.proof_nodes)),
        ("formulasCreated", Statistic::Count(run.formulas_created)),
    ];
    if let Some(failure) = run.failure {
        statistics.push(("stop", Statistic::Text(failure.to_owned())));
    }
    if let Some(isar) = &run.isar {
        statistics.push(("proof", Statistic::Text(decide::get_text_digest(isar))));
    }
    Ok(Decision {
        verdict: if run.isar.is_some() {
            Verdict::Unsat
        } else {
            Verdict::Unknown
        },
        statistics,
    })
}
