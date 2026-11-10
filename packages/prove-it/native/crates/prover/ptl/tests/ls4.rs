//! The decider against the reference LS4: each formula in tests/conformance/ptl, which the corpora
//! never send LS4, beside LS4's output on it.

use std::fs;
use std::path::Path;

use prove_decide::{DecideError, Limits, Statistic, Verdict};

fn decide(text: &str, step_limit: Option<u64>) -> Result<prove_decide::Decision, DecideError> {
    prove_ptl::decide(text, &Limits::new(f64::INFINITY, step_limit, None))
}

#[test]
fn gives_ls4s_verdict_on_each_formula() {
    let directory = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../../tests/conformance/ptl");
    let mut paths: Vec<_> = fs::read_dir(&directory)
        .expect("the PTL fixtures")
        .map(|entry| entry.expect("an entry").path())
        .filter(|path| path.extension().is_some_and(|extension| extension == "ls4"))
        .collect();
    paths.sort();
    assert!(paths.len() > 20);
    for path in paths {
        let output = fs::read_to_string(path.with_extension("ls4.out")).expect("LS4's output");
        let expected = output
            .lines()
            .find_map(|line| {
                if line.starts_with("UNSAT") {
                    Some(Verdict::Unsat)
                } else if line.starts_with("SAT") {
                    Some(Verdict::Sat)
                } else {
                    None
                }
            })
            .unwrap_or(Verdict::Unknown);
        let text = fs::read_to_string(&path).expect("the formula");
        let decision = decide(&text, None).expect("a decision");
        assert_eq!(decision.verdict, expected, "{}", path.display());
    }
}

#[test]
fn counts_its_steps_and_gives_up_past_its_step_limit() {
    let text = "not (((always (p <-> q)) -> ((always p) <-> (always q))))";
    let decision = decide(text, None).expect("a decision");
    assert_eq!(decision.verdict, Verdict::Unsat);
    let [("steps", Statistic::Count(steps))] = decision.statistics[..] else {
        panic!("the steps are the statistic");
    };
    assert!(steps > 0);
    assert_eq!(decide(text, Some(steps)).expect("a decision"), decision);
    assert_eq!(
        decide(text, Some(0)).expect("a decision").verdict,
        Verdict::Unknown
    );
}

#[test]
fn a_canceled_decision_is_unknown() {
    let limits = Limits::new(f64::INFINITY, None, Some(std::sync::Arc::new(|| true)));
    let decision = prove_ptl::decide("always p -> p", &limits).expect("a decision");
    assert_eq!(decision.verdict, Verdict::Unknown);
}

#[test]
fn declines_what_isnt_ls4_input() {
    for text in [
        "not ((always h00000) ->",
        "p q",
        "(p",
        "p & ~",
        "p \u{a0} q",
        "p -> )",
    ] {
        assert!(
            matches!(decide(text, None), Err(DecideError::Declined(_))),
            "{text}"
        );
    }
}
