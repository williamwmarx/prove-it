//! SANY's validation of a PlusCal algorithm against the checksums of its translation.
//! `scripts/front-differential.ts pcal` holds it to `src/pcal/validate.ts` on every corpus module
//! with an algorithm.

use std::collections::BTreeSet;

use tla_front::TlcVersion;
use tla_front::pcal::{PcalSession, ValidationResult};

/// TLC's test-model/TESpecTest/TESpecPlusCalTest.tla.
const MODULE: &str = r#"---------- MODULE TESpecPlusCalTest -----------

EXTENDS Naturals, TLC

(* --algorithm Steps
variables x = 1, y = FALSE;
begin
    while TRUE do
        x := x + 1;
        y := ~y;
        assert x < 5;
    end while;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "2f1a7a64" /\ chksum(tla) = "93b619e3")
VARIABLES x, y

vars == << x, y >>

Init == (* Global variables *)
        /\ x = 1
        /\ y = FALSE

Next == /\ x' = x + 1
        /\ y' = ~y
        /\ Assert(x' < 5, "Failure of assertion at line 11, column 9.")

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

=============================================="#;

fn validate(source: &str) -> (BTreeSet<ValidationResult>, Vec<String>) {
    let lines: Vec<&str> = source.split('\n').collect();
    let mut session = PcalSession::new();
    let results = session
        .validate(&lines, TlcVersion::Master)
        .expect("a validation");
    (results, session.log)
}

#[test]
fn matches_the_checksums_of_an_unchanged_algorithm() {
    let (results, log) = validate(MODULE);
    assert_eq!(results, BTreeSet::from([ValidationResult::NoDivergence]));
    assert_eq!(log, ["Labels added."]);
}

#[test]
fn finds_a_changed_algorithm_or_translation() {
    let (results, _) = validate(&MODULE.replace("x = 1, y", "x = 2, y"));
    assert_eq!(
        results,
        BTreeSet::from([ValidationResult::PcalDivergenceExists])
    );
    let (results, _) = validate(&MODULE.replace("/\\ x = 1", "/\\ x = 2"));
    assert_eq!(
        results,
        BTreeSet::from([ValidationResult::TlaDivergenceExists])
    );
}

#[test]
fn reports_the_translator_errors() {
    let (results, log) = validate(&MODULE.replace("y := ~y;", "y := ;"));
    assert_eq!(
        results,
        BTreeSet::from([ValidationResult::PcalDivergenceExists])
    );
    assert_eq!(
        log,
        [
            "\nUnrecoverable error:\n -- Empty right-hand side of assignment at \n    line 10, column 11.\n"
        ]
    );
    let (_, log) = validate(&MODULE.replace("x = 1, y", "x = 1 y"));
    assert_eq!(
        log,
        [
            "Labels added.",
            "\nUnrecoverable error:\n -- Assignment to undeclared variable y\n    at line 10, column 9.\n"
        ]
    );
}
