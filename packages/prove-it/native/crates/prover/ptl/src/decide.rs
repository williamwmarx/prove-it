//! Decides the text tlapm sends LS4, as `ptl_to_trp -i file | ls4` does: unsat when the clause set
//! ptl_to_trp prints for the negated obligation has no model, which proves the obligation, and
//! unknown where ptl_to_trp or LS4 stops on the text, which tlapm counts as a failure.

use prove_decide::{DecideError, Decision, Limits, Statistic, Verdict};

use crate::spec::read_spec;
use crate::tableau::get_satisfiability;
use crate::translate::translate;

/// The verdict, with the steps as its one statistic, each a check of the limits.
pub fn decide(text: &str, limits: &Limits) -> Result<Decision, DecideError> {
    let verdict = match translate(text.as_bytes()).and_then(|clauses| read_spec(&clauses)) {
        Some(spec) => get_satisfiability(&spec.to_formulas(), &mut || {
            limits.is_step_limit_reached() || limits.is_canceled() || limits.is_past_deadline()
        }),
        None => Verdict::Unknown,
    };
    Ok(Decision {
        verdict,
        statistics: vec![("steps", Statistic::Count(limits.steps()))],
    })
}
