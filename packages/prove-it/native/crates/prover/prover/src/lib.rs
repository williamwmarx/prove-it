//! Prove It's prover: the backend each of tlapm's prover names selects, as `src/prover/deciders.ts`
//! maps them, deciding the text tlapm would send that prover.

pub use prove_decide::{DecideError, Decision, Limits, Statistic, Verdict};

/// Decides `text` with the backend `prover` names. A backend not ported yet declines.
pub fn decide(prover: &str, text: &str, limits: &mut Limits) -> Result<Decision, DecideError> {
    match prover {
        "smt" | "z3" => prove_smt::decide(text, limits),
        "zenon" => prove_zenon::decide(text, limits),
        "isabelle" => prove_isabelle::decide(text, limits),
        "ls4" => prove_ptl::decide(text, limits),
        _ => Err(DecideError::Declined(format!("the {prover} backend"))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_prover_without_a_backend_is_declined() {
        let mut limits = Limits::new(f64::INFINITY, None, None);
        assert_eq!(
            decide("cvc4", "", &mut limits),
            Err(DecideError::Declined("the cvc4 backend".into()))
        );
    }
}
