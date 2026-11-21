//! The decider against the reference LS4: each formula in tests/conformance/ptl, which the corpora
//! never send LS4, beside LS4's output on it, and each text of tests/fixtures/ls4 beside the verdict
//! `ptl_to_trp -i file | ls4` gave (tla-ts's recording of tlapm's backends).

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

/// The inputs the encoder prints for the obligations of tests/unit/ptl.test.ts, with the verdict
/// the TypeScript decider gave on each before it was deleted, and the steps the port takes.
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

/// ptl_to_trp prints no clause set for text its grammar rejects, and LS4 then reads nothing it
/// decides, which tlapm counts as a failure.
#[test]
fn reaches_no_verdict_where_ptl_to_trp_stops() {
    for text in [
        "not ((always h00000) ->",
        "p q",
        "(p",
        "p & ~",
        "p \u{a0} q",
        "p -> )",
    ] {
        let decision = decide(text, None).expect("a decision");
        assert_eq!(decision.verdict, Verdict::Unknown, "{text}");
    }
}

#[test]
fn gives_the_recorded_verdict_on_each_syntax_fixture() {
    let directory = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../../tests/fixtures/ls4");
    let recorded = fs::read_to_string(directory.join("recorded.txt")).expect("the record");
    let mut count = 0;
    for line in recorded.lines() {
        let (name, verdict) = line.split_once('\t').expect("a name and a verdict");
        let expected = match verdict {
            "unsat" => Verdict::Unsat,
            "sat" => Verdict::Sat,
            _ => Verdict::Unknown,
        };
        let text = fs::read_to_string(directory.join(format!("{name}.ls4"))).expect("the text");
        let decision = decide(&text, None).expect("a decision");
        assert_eq!(decision.verdict, expected, "{name}");
        count += 1;
    }
    assert_eq!(count, 25);
}
