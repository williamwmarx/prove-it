//! The decider against the reference `ptl_to_trp | ls4`: each formula in tests/conformance/ptl,
//! which the corpora never send LS4, beside LS4's output on it (`.ls4.out`) and the clauses
//! tlapm's `translate` at b91fb6c, built from its source, writes for it (`.trp`, its standard
//! output; one with no `and([` is a parse error it printed in the clauses' place, or nothing, as
//! an exception ended it). The `syntax-` formulas are aidenybai/tla-ts's `backends/ls4/syntax`
//! suite at 0341dbe5, whose verdicts are LS4 1.0's as the suite records them.

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
        .filter(|path| path.with_extension("ls4.out").exists())
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
fn translates_each_formula_as_ptl_to_trp_does() {
    let directory = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../../tests/conformance/ptl");
    let mut paths: Vec<_> = fs::read_dir(&directory)
        .expect("the PTL fixtures")
        .map(|entry| entry.expect("an entry").path())
        .filter(|path| path.extension().is_some_and(|extension| extension == "ls4"))
        .filter(|path| path.with_extension("trp").exists())
        .collect();
    paths.sort();
    assert!(paths.len() > 90);
    for path in paths {
        let recorded = fs::read_to_string(path.with_extension("trp")).expect("ptl_to_trp's output");
        let text = fs::read_to_string(&path).expect("the formula");
        let translation = prove_ptl::translate::translate(&text, &mut || false);
        if recorded.starts_with("and([") {
            let clauses =
                translation.unwrap_or_else(|failure| panic!("{}: {failure:?}", path.display()));
            assert_eq!(clauses.text(), recorded, "{}", path.display());
        } else {
            assert!(
                matches!(
                    translation,
                    Err(prove_ptl::translate::Failure::NoClauses(_))
                ),
                "{}: {translation:?}",
                path.display()
            );
        }
    }
}

/// `ptl_to_trp` expands `(p0 & q0) | (p1 & q1) | ...` to 2^n clauses, and the port with it, so a
/// stop during the expansion has to end it: the translation checks the stop as it recurses.
#[test]
fn stops_the_translation_when_the_decision_is_canceled() {
    use std::sync::Arc;
    use std::sync::atomic::{AtomicUsize, Ordering};
    let text = (0..40)
        .map(|i| format!("(p{i} & q{i})"))
        .collect::<Vec<_>>()
        .join(" | ");
    let polls = Arc::new(AtomicUsize::new(0));
    let counted = Arc::clone(&polls);
    let cancel: prove_decide::Cancel =
        Arc::new(move || counted.fetch_add(1, Ordering::Relaxed) >= 1_000);
    let started = std::time::Instant::now();
    let decision = prove_ptl::decide(&text, &Limits::new(f64::INFINITY, None, Some(cancel)))
        .expect("a decision");
    assert_eq!(decision.verdict, Verdict::Unknown);
    assert!(started.elapsed().as_secs() < 5, "{:?}", started.elapsed());
    assert!(polls.load(Ordering::Relaxed) >= 1_000);
    let translation = prove_ptl::translate::translate(&text, &mut || true);
    assert_eq!(translation, Err(prove_ptl::translate::Failure::Stopped));
}

/// tla-ts's `backends/ls4/syntax` suite: LS4's verdict on each, `unknown` where `ptl_to_trp`
/// writes no clauses or LS4 rejects them.
#[test]
fn gives_ls4s_verdict_on_the_syntax_suite() {
    let directory = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../../tests/conformance/ptl");
    for (name, expected) in [
        ("always_binds_tighter_than_and", Verdict::Unsat),
        ("arrow_spellings", Verdict::Unsat),
        ("comment_ignored", Verdict::Unsat),
        ("disjunction_binds_looser_than_implication", Verdict::Sat),
        ("equiv_spellings", Verdict::Unsat),
        ("false_alone", Verdict::Unsat),
        ("ident_with_keyword_prefix", Verdict::Sat),
        ("implication_binds_looser_than_conjunction", Verdict::Unsat),
        ("implication_left_associative", Verdict::Unsat),
        ("lowercase_bound_variable", Verdict::Unknown),
        ("next_keyword", Verdict::Unsat),
        ("not_keyword", Verdict::Unsat),
        ("parse_error", Verdict::Unknown),
        ("past_always", Verdict::Unknown),
        ("predicate_with_arguments", Verdict::Unknown),
        ("quantifier", Verdict::Unknown),
        ("reserved_word", Verdict::Unknown),
        ("sometime_contradiction", Verdict::Unsat),
        ("sometime_false", Verdict::Sat),
        ("tla_box_not_accepted", Verdict::Unknown),
        ("true_keyword", Verdict::Sat),
        ("unless_needs_left", Verdict::Unsat),
        ("unless_without_eventuality", Verdict::Sat),
        ("until_eventually", Verdict::Unsat),
        ("until_satisfiable", Verdict::Sat),
    ] {
        let text =
            fs::read_to_string(directory.join(format!("syntax-{name}.ls4"))).expect("the formula");
        assert_eq!(
            decide(&text, None).expect("a decision").verdict,
            expected,
            "{name}"
        );
    }
}

/// The inputs the encoder prints for the obligations of tests/unit/ptl.test.ts, with the verdict and
/// the steps the TypeScript decider gave on each before it was deleted.
#[test]
fn decides_the_encoders_inputs_as_recorded() {
    for (text, verdict, steps) in [
        (
            "not (((always (h8828a -> h2f89a)) & (always ((h2f89a & (hfc35e | h18388)) -> (next h2f89a))) & (always (cc | ~ cc)) -> (((h8828a & (always (hfc35e | h18388))) & ((sometime (always hc5714)) -> (always (sometime (hfc35e & (~ h18388)))))) -> (always h2f89a))))",
            Verdict::Unsat,
            6,
        ),
        (
            "not (((always ((h2f89a & (hfc35e | h18388)) -> (next h2f89a))) & (always (cc | ~ cc)) -> (((h8828a & (always (hfc35e | h18388))) & ((sometime (always hc5714)) -> (always (sometime (hfc35e & (~ h18388)))))) -> (always h2f89a))))",
            Verdict::Sat,
            3,
        ),
        (
            "not (((always (h94a4d -> (always (h4ca64 -> (sometime h7fe4a))))) & (always (h94a4d -> (always (h7fe4a -> (sometime hda924))))) & (always (cc | ~ cc)) -> (h94a4d -> (always (h4ca64 -> (sometime hda924))))))",
            Verdict::Unsat,
            14,
        ),
        (
            "not (((always (h94a4d -> (always (h4ca64 -> (sometime h7fe4a))))) & (always (cc | ~ cc)) -> (h94a4d -> (always (h4ca64 -> (sometime hda924))))))",
            Verdict::Sat,
            7,
        ),
        (
            "not (((always (always hc5714)) & (always (cc | ~ cc)) -> (((h8828a & (always (hfc35e | h18388))) & ((sometime (always hc5714)) -> (always (sometime (hfc35e & (~ h18388)))))) -> (always (sometime (hfc35e & (~ h18388)))))))",
            Verdict::Unsat,
            15,
        ),
        (
            "not (((always (always (sometime hc5714))) & (always (cc | ~ cc)) -> (((h8828a & (always (hfc35e | h18388))) & ((sometime (always hc5714)) -> (always (sometime (hfc35e & (~ h18388)))))) -> (always (sometime (hfc35e & (~ h18388)))))))",
            Verdict::Sat,
            40,
        ),
        (
            "not (((always (always (sometime hc5714))) & (always (cc | ~ cc)) -> (((always (sometime hc5714)) -> (always (sometime (hfc35e & (~ h18388))))) -> (always (sometime (hfc35e & (~ h18388)))))))",
            Verdict::Unsat,
            31,
        ),
        (
            "not ((h7fe4a & (always (cc | ~ cc)) -> h7fe4a))",
            Verdict::Unsat,
            1,
        ),
        (
            "not ((h7fe4a & (always (cc | ~ cc)) -> h344d6))",
            Verdict::Sat,
            2,
        ),
        (
            "not (((always h38dda) & (always (cc | ~ cc)) -> (always h38dda)))",
            Verdict::Unsat,
            2,
        ),
        (
            "not ((h7fe4a & (always (cc | ~ cc)) -> (always h7fe4a)))",
            Verdict::Sat,
            3,
        ),
        (
            "not (((hbe322 -> haf23d) & ((~ hbe322) -> haf23d) & (always (cc | ~ cc)) -> haf23d))",
            Verdict::Unsat,
            1,
        ),
        (
            "not (((always ((always hbe322) -> haf23d)) & (always ((always (~ hbe322)) -> haf23d)) & (always (cc | ~ cc)) -> haf23d))",
            Verdict::Sat,
            6,
        ),
    ] {
        assert_eq!(
            decide(text, None),
            Ok(prove_decide::Decision {
                verdict,
                statistics: vec![("steps", Statistic::Count(steps))],
            }),
            "{text}"
        );
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

/// tlapm counts an LS4 that stops on its input as a failure.
#[test]
fn reaches_no_verdict_on_what_isnt_ptl_to_trps_input() {
    for text in [
        "not ((always h00000) ->",
        "p q",
        "(p",
        "p & ~",
        "p \u{a0} q",
        "p -> )",
        "p = q",
        "1 & p",
    ] {
        assert_eq!(
            decide(text, None).expect("a decision").verdict,
            Verdict::Unknown,
            "{text}"
        );
    }
}
