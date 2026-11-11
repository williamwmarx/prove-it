//! The driver's rounds: what it asks for, and how the answers settle the obligations.

use std::collections::HashMap;

use prove_decide::Verdict;
use prove_it_prover::driver::{Answer, Report, Request, Round, Status, prove_obligations};
use prove_obligations::index::{ObligationSource, PrintedObligation, get_obligations};
use prove_obligations::tlaps_module::TLAPS_MODULE;

fn get_module_obligations(source: &str) -> Vec<PrintedObligation> {
    get_obligations(
        &[ObligationSource {
            file: "M.tla".to_owned(),
            source: source.to_owned(),
        }],
        &mut |name| {
            (name == "TLAPS").then(|| ObligationSource {
                file: "TLAPS.tla".to_owned(),
                source: TLAPS_MODULE.to_owned(),
            })
        },
        None,
        &mut |_| {},
    )
    .expect("the module has obligations")
    .into_iter()
    .flat_map(|result| result.obligations)
    .collect()
}

// Proves in rounds, answering each request with what `answer` gives for its prover, as JavaScript
// would, and returns the last round and every request made.
fn prove(
    obligations: &[PrintedObligation],
    answer: impl Fn(&Request) -> Answer,
) -> (Round, Vec<Request>) {
    let mut answers: HashMap<String, Answer> = HashMap::new();
    let mut requested = Vec::new();
    loop {
        let round = prove_obligations(obligations, &|key| answers.get(key).cloned())
            .expect("the run proves");
        if round.requests.is_empty() {
            return (round, requested);
        }
        for request in &round.requests {
            assert!(
                !answers.contains_key(&request.key),
                "asked again for {}",
                request.key
            );
            answers.insert(request.key.clone(), answer(request));
        }
        requested.extend(round.requests);
    }
}

// The reports of the obligations a prover had to decide, which leaves out the trivial ones.
fn get_decided(round: &Round) -> Vec<&Report> {
    round
        .reports
        .iter()
        .filter(|report| report.status != Status::Trivial)
        .collect()
}

fn decided(verdict: Verdict) -> Answer {
    Answer::Decided {
        verdict,
        time_used_ms: 1.0,
    }
}

const SPEC: &str = "---- MODULE M ----
EXTENDS Naturals, TLAPS
VARIABLE x
THEOREM One == x = 1 => x + 1 = 2
  BY SMT
THEOREM Two == x = 1 => x + 1 = 2
  BY SMT
THEOREM Three == x = 2 => x + 1 = 3
  BY Zenon, SMT
====
";

#[test]
fn a_proof_needs_its_decision_first() {
    let obligations = get_module_obligations(SPEC);
    let round = prove_obligations(&obligations, &|_| None).expect("the run proves");
    assert!(round.reports.is_empty());
    assert_eq!(
        round
            .requests
            .iter()
            .map(|request| request.prover.as_str())
            .collect::<Vec<_>>(),
        ["smt", "zenon"]
    );
}

#[test]
fn an_obligation_with_the_same_fingerprint_reuses_the_proof() {
    let obligations = get_module_obligations(SPEC);
    let (round, requested) = prove(&obligations, |_| decided(Verdict::Unsat));
    assert_eq!(requested.len(), 2);
    let reports = get_decided(&round);
    let statuses: Vec<_> = reports.iter().map(|report| &report.status).collect();
    let proved = |prover: &str| Status::Proved {
        prover: prover.to_owned(),
    };
    assert_eq!(statuses, [&proved("smt"), &proved("smt"), &proved("zenon")]);
    assert!(reports[1].attempts[0].attempt.is_reused);
}

#[test]
fn each_method_is_tried_in_turn_until_one_proves() {
    let obligations = get_module_obligations(SPEC);
    let (round, requested) = prove(&obligations, |request| {
        decided(if request.prover == "zenon" {
            Verdict::Unknown
        } else {
            Verdict::Unsat
        })
    });
    assert_eq!(
        requested
            .iter()
            .map(|request| request.prover.as_str())
            .collect::<Vec<_>>(),
        ["smt", "zenon", "smt"]
    );
    assert_eq!(
        get_decided(&round)[2].status,
        Status::Proved {
            prover: "smt".to_owned()
        }
    );
}

#[test]
fn a_failed_decision_fails_the_obligation_with_its_reason() {
    let obligations = get_module_obligations(SPEC);
    let (round, _) = prove(&obligations, |request| {
        if request.prover == "smt" {
            Answer::Failed("malformed".to_owned())
        } else {
            decided(Verdict::Sat)
        }
    });
    let reports = get_decided(&round);
    assert_eq!(
        reports[0].status,
        Status::Failed {
            reason: "smt failed: malformed".to_owned()
        }
    );
    assert_eq!(
        reports[1].status,
        Status::Failed {
            reason: "smt failed on an obligation with the same fingerprint".to_owned()
        }
    );
    assert_eq!(
        reports[2].status,
        Status::Failed {
            reason: "zenon answered sat, smt failed: malformed".to_owned()
        }
    );
}
