//! The deleted `tests/unit/smt.test.ts`, case for case, on `decide` and `check_smt`: each test
//! asserts what the TypeScript test asserted, on the same inputs under `tests/fixtures/smt`.
//!
//! The TypeScript gave each decision 5 seconds; these give none and a step limit far above what
//! any case takes, so that they are deterministic. Each runs on a thread with the stack the binding
//! gives a decision.

use std::fs;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use prove_decide::{Cancel, DecideError, Decision, Limits, Statistic, Verdict};
use prove_smt::core::solver::check_smt;
use prove_smt::util::error::SmtError;
use prove_smt::util::rlimit::{ResourceLimit, StopReason};

const STEP_LIMIT: u64 = 50_000_000;
/// The step limit `tests/tables/decide.txt` was recorded under.
const REFERENCE_STEP_LIMIT: u64 = 5_000_000;
const DECIDE_STACK_BYTES: usize = 256 * 1024 * 1024;

struct Recorded {
    name: String,
    z3: String,
    source: String,
}

fn get_directory() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../../tests/fixtures/smt")
}

fn read(name: &str) -> String {
    fs::read_to_string(get_directory().join(name)).expect("a fixture")
}

/// The string value of `"key": "value"` on a line of verdicts.json.
fn get_value<'a>(line: &'a str, key: &str) -> Option<&'a str> {
    let rest = line.trim().strip_prefix(&format!("\"{key}\": \""))?;
    rest.trim_end_matches(',').strip_suffix('"')
}

/// verdicts.json: each fixture with Z3's verdict and the source of the problem.
fn get_verdicts() -> Vec<Recorded> {
    let text = read("verdicts.json");
    let mut verdicts: Vec<Recorded> = Vec::new();
    for line in text.lines() {
        if let Some(name) = line.trim().strip_suffix("\": {") {
            verdicts.push(Recorded {
                name: name.trim_start_matches('"').into(),
                z3: String::new(),
                source: String::new(),
            });
        } else if let Some(recorded) = verdicts.last_mut() {
            if let Some(z3) = get_value(line, "z3") {
                recorded.z3 = z3.into();
            } else if let Some(source) = get_value(line, "source") {
                recorded.source = source.into();
            }
        }
    }
    assert_eq!(verdicts.len(), 45);
    verdicts
}

fn get_recorded(z3: &str) -> Vec<Recorded> {
    get_verdicts()
        .into_iter()
        .filter(|recorded| recorded.z3 == z3)
        .collect()
}

fn on_deep_stack<T: Send>(run: impl FnOnce() -> T + Send) -> T {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(DECIDE_STACK_BYTES)
            .spawn_scoped(scope, run)
            .expect("a thread")
            .join()
            .expect("no panic")
    })
}

fn decide_with(text: &str, cancel: Option<Cancel>) -> Result<Decision, DecideError> {
    on_deep_stack(|| prove_smt::decide(text, &Limits::new(f64::INFINITY, Some(STEP_LIMIT), cancel)))
}

/// The verdict of the solver itself, past the subset of SMT-LIB that `decide` takes: these cases
/// are the TypeScript's, written in more of SMT-LIB than tlapm's encoder. A parse error is the
/// prover's error, as `decide` makes it.
fn decide(text: &str) -> Result<Verdict, DecideError> {
    on_deep_stack(|| {
        let limits = Limits::new(f64::INFINITY, Some(STEP_LIMIT), None);
        match check_smt(text, ResourceLimit::new(&limits)) {
            Ok(check) => Ok(check.verdict),
            Err(SmtError::Parse(message)) => Err(DecideError::Prover(message)),
            Err(SmtError::Canceled | SmtError::Unsupported(_)) => Ok(Verdict::Unknown),
            Err(error) => Err(DecideError::Declined(error.to_string())),
        }
    })
}

// (g x) is f applied depth times to x, and (g 0) is not: unsat after one instance.
fn get_deep_problem(depth: usize) -> String {
    let nest = |term: &str| format!("{}{term}{}", "(f ".repeat(depth), ")".repeat(depth));
    [
        "(declare-fun f (Int) Int)".into(),
        "(declare-fun g (Int) Int)".into(),
        format!(
            "(assert (forall ((x Int)) (! (= (g x) {}) :pattern ((g x)))))",
            nest("x")
        ),
        format!("(assert (not (= (g 0) {})))", nest("0")),
        "(check-sat)".into(),
    ]
    .join("\n")
}

fn decide_lines(lines: &[&str]) -> Result<Verdict, DecideError> {
    decide(&[lines, &["(check-sat)"]].concat().join("\n"))
}

// decideSmt proves what Z3 proves.
#[test]
fn proves_what_z3_proves() {
    for recorded in get_recorded("unsat") {
        assert_eq!(
            decide_with(&read(&recorded.name), None).map(|decision| decision.verdict),
            Ok(Verdict::Unsat),
            "proves {}",
            recorded.source
        );
    }
}

// decideSmt never proves what Z3 refutes.
#[test]
fn does_not_prove_what_z3_refutes() {
    for recorded in get_recorded("sat") {
        let verdict = decide_with(&read(&recorded.name), None).map(|decision| decision.verdict);
        assert!(verdict.is_ok(), "{}: {verdict:?}", recorded.source);
        assert_ne!(
            verdict,
            Ok(Verdict::Unsat),
            "does not prove {}",
            recorded.source
        );
    }
}

#[test]
fn answers_the_same_way_with_the_same_instances_when_run_twice() {
    let text = read("Barriers-63.smt");
    let check = || {
        on_deep_stack(|| {
            let limits = Limits::new(f64::INFINITY, Some(STEP_LIMIT), None);
            check_smt(&text, ResourceLimit::new(&limits))
        })
    };
    let first = check();
    let second = check();
    let first = first.expect("a check");
    assert!(first.num_instances > 0);
    assert_eq!(second, Ok(first));
}

#[test]
fn gives_up_when_the_signal_aborts() {
    let cancel: Cancel = Arc::new(|| true);
    let decision = decide_with(&read("Barriers-63.smt"), Some(cancel));
    assert_eq!(
        decision.map(|decision| decision.verdict),
        Ok(Verdict::Unknown)
    );
}

#[test]
fn proves_a_problem_whose_terms_are_nested_thousands_deep() {
    assert_eq!(decide(&get_deep_problem(2500)), Ok(Verdict::Unsat));
}

#[test]
fn answers_instead_of_throwing_when_a_recursion_exhausts_the_stack() {
    let verdict = decide(&get_deep_problem(20000));
    assert!(
        [Ok(Verdict::Unsat), Ok(Verdict::Unknown)].contains(&verdict),
        "{verdict:?}"
    );
}

// Doubles round 2^53 + 1 to 2^53 and 2^54 + 3 to 2^54 + 4, which flips each verdict.
#[test]
fn tells_apart_numerals_past_2_53() {
    let problem = [
        "(declare-fun x () Int)",
        "(assert (= x 9007199254740993))",
        "(assert (not (= x 9007199254740992)))",
        "(check-sat)",
    ]
    .join("\n");
    assert_eq!(decide(&problem), Ok(Verdict::Sat));
}

#[test]
fn computes_exactly_with_numerals_past_2_53() {
    let problems = [
        "(assert (= (* 2 x) 18014398509481987))",
        "(assert (= x 1180591620717411303424))\n(assert (not (= (div (- 1180591620717411303425) x) (- 2))))",
    ]
    .map(|assertions| format!("(declare-fun x () Int)\n{assertions}\n(check-sat)\n"));
    for problem in problems {
        assert_eq!(decide(&problem), Ok(Verdict::Unsat));
    }
}

// Z3: unsat. The 2 of (* 2 a) is nested in a sum before the equality needs it as a term.
#[test]
fn relates_a_numeral_to_the_arithmetic_once_a_product_has_used_it() {
    let problem = [
        "(declare-fun a () Int)",
        "(declare-fun b () Int)",
        "(assert (= (+ a b) 7))",
        "(assert (= (+ (* 2 a) (* (- 3) b)) 2))",
        "(check-sat)",
    ]
    .join("\n");
    assert_eq!(decide(&problem), Ok(Verdict::Unsat));
}

// Z3 answers both without the smt tactic, since the preprocessing decides them.
#[test]
fn decides_a_problem_that_the_preprocessing_reduces_to_false_or_to_nothing() {
    let decide_assertion = |assertion: &str| {
        decide(&format!(
            "(declare-fun x () Int)\n(assert {assertion})\n(check-sat)\n"
        ))
    };
    assert_eq!(decide_assertion("(> x x)"), Ok(Verdict::Unsat));
    assert_eq!(decide_assertion("(= x x)"), Ok(Verdict::Sat));
}

#[test]
fn rejects_an_ill_sorted_application() {
    assert_eq!(
        decide("(declare-fun p (Int) Bool)\n(assert (p true))\n(check-sat)\n"),
        Err(DecideError::Prover("ill-sorted application of p".into()))
    );
}

// decideSmt on real arithmetic: each verdict is Z3's on the same problem.

#[test]
fn finds_a_real_strictly_between_0_and_1() {
    assert_eq!(
        decide_lines(&[
            "(declare-fun x () Real)",
            "(assert (< 0.0 x))",
            "(assert (< x 1.0))",
        ]),
        Ok(Verdict::Sat)
    );
}

#[test]
fn finds_no_integer_strictly_between_0_and_1() {
    assert_eq!(
        decide_lines(&[
            "(declare-fun x () Int)",
            "(assert (< 0 x))",
            "(assert (< x 1))",
        ]),
        Ok(Verdict::Unsat)
    );
}

#[test]
fn solves_x_plus_y_is_1_and_x_minus_y_is_0_with_x_one_half() {
    let lines = [
        "(declare-fun x () Real)",
        "(declare-fun y () Real)",
        "(assert (= (+ x y) 1.0))",
        "(assert (= (- x y) 0.0))",
    ];
    assert_eq!(decide_lines(&lines), Ok(Verdict::Sat));
    assert_eq!(
        decide_lines(&[&lines[..], &["(assert (not (= x (/ 1 2))))"]].concat()),
        Ok(Verdict::Unsat)
    );
}

#[test]
fn rounds_to_int_down() {
    let lines = ["(declare-fun x () Real)", "(assert (= (to_int x) 2))"];
    assert_eq!(
        decide_lines(&[&lines[..], &["(assert (< x 2.0))"]].concat()),
        Ok(Verdict::Unsat)
    );
    assert_eq!(
        decide_lines(&[&lines[..], &["(assert (> x 2.5))", "(assert (< x 3.0))"]].concat()),
        Ok(Verdict::Sat)
    );
    assert_eq!(
        decide_lines(&["(assert (not (= (to_int (- 1.5)) (- 2))))"]),
        Ok(Verdict::Unsat)
    );
}

#[test]
fn decides_is_int() {
    let lines = [
        "(declare-fun x () Real)",
        "(assert (< 1.0 x))",
        "(assert (< x 2.0))",
    ];
    assert_eq!(
        decide_lines(&[&lines[..], &["(assert (is_int x))"]].concat()),
        Ok(Verdict::Unsat)
    );
    assert_eq!(
        decide_lines(&[&lines[..], &["(assert (not (is_int x)))"]].concat()),
        Ok(Verdict::Sat)
    );
    assert_eq!(
        decide_lines(&[
            "(declare-fun x () Real)",
            "(assert (> (* 3.0 x) 1.0))",
            "(assert (< (* 3.0 x) 2.0))",
            "(assert (is_int x))",
        ]),
        Ok(Verdict::Unsat)
    );
}

#[test]
fn keeps_strict_bounds_strict() {
    let lines = ["(declare-fun x () Real)", "(assert (> (+ x 0.1) 0.3))"];
    assert_eq!(
        decide_lines(&[&lines[..], &["(assert (<= (* 10.0 x) 2.0))"]].concat()),
        Ok(Verdict::Unsat)
    );
    assert_eq!(
        decide_lines(&[&lines[..], &["(assert (<= (* 10.0 x) 2.5))"]].concat()),
        Ok(Verdict::Sat)
    );
}

#[test]
fn refutes_an_infeasible_linear_system() {
    assert_eq!(
        decide_lines(&[
            "(declare-fun a () Real)",
            "(declare-fun b () Real)",
            "(assert (= (+ (* 3.0 a) (* 2.0 b)) 7.0))",
            "(assert (= (- (* 6.0 a) (* 4.0 b)) 2.0))",
            "(assert (< a 1.0))",
        ]),
        Ok(Verdict::Unsat)
    );
}

#[test]
fn coerces_int_terms_of_real_positions() {
    assert_eq!(
        decide_lines(&[
            "(declare-fun i () Int)",
            "(declare-fun y () Real)",
            "(assert (= (+ i y) 2.5))",
            "(assert (= y 0.25))",
        ]),
        Ok(Verdict::Unsat)
    );
}

#[test]
fn finds_a_model_of_a_nonlinear_real_problem() {
    assert_eq!(
        decide_lines(&[
            "(declare-fun x () Real)",
            "(declare-fun y () Real)",
            "(assert (= (* x y) 2.0))",
        ]),
        Ok(Verdict::Sat)
    );
}

#[test]
fn finds_no_integer_x_with_x_times_x_plus_1_below_0() {
    assert_eq!(
        decide_lines(&[
            "(declare-fun x () Int)",
            "(assert (not (>= (* x (+ x 1)) 0)))",
        ]),
        Ok(Verdict::Unsat)
    );
}

#[test]
fn finds_a_real_x_with_x_times_x_plus_1_below_0() {
    assert_eq!(
        decide_lines(&[
            "(declare-fun x () Real)",
            "(assert (not (>= (* x (+ x 1.0)) 0.0)))",
        ]),
        Ok(Verdict::Sat)
    );
}

#[test]
fn refutes_a_negative_square() {
    assert_eq!(
        decide_lines(&["(declare-fun x () Real)", "(assert (< (* x x) 0.0))"]),
        Ok(Verdict::Unsat)
    );
}

#[test]
fn refutes_a_factorization_of_a_prime() {
    assert_eq!(
        decide_lines(&[
            "(declare-fun x () Int)",
            "(declare-fun y () Int)",
            "(assert (= (* x y) 7))",
            "(assert (> x 1))",
            "(assert (> y 1))",
        ]),
        Ok(Verdict::Unsat)
    );
}

/// The verdict and the statistics as `tests/tables/decide.txt` holds them.
fn get_decision_text(decision: &Decision) -> String {
    let statistics = decision.statistics.iter().map(|entry| match &entry.1 {
        Statistic::Count(count) => format!(" {}={count}", entry.0),
        Statistic::Text(text) => format!(" {}={text}", entry.0),
    });
    format!(
        "{}{}",
        decision.verdict.name(),
        statistics.collect::<String>()
    )
}

// The decider differential in miniature: `tests/tables/decide.txt` holds the verdict and statistics
// the TypeScript decideSmt gave on every fixture under the same step limit and no deadline, before
// it was deleted. Nothing rewrites it. The port answers each with the same verdict and the same
// statistics: the same search, step for step.
#[test]
fn decides_every_fixture_as_recorded() {
    let table =
        fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/tables/decide.txt"))
            .expect("the table");
    let mut count = 0;
    for line in table.lines() {
        let (name, expected) = line.split_once(' ').expect("a fixture and its decision");
        let decision = on_deep_stack(|| {
            prove_smt::decide(
                &read(name),
                &Limits::new(f64::INFINITY, Some(REFERENCE_STEP_LIMIT), None),
            )
        })
        .map(|decision| get_decision_text(&decision));
        assert_eq!(decision, Ok(expected.into()), "{name}");
        count += 1;
    }
    assert_eq!(count, 45);
}

// smt/c0119d516427b279 of the decider corpus, reduced: MBQI's models interpret div0 and mod0,
// builtin declarations without a reference count in the TypeScript, so each model that releases
// one deletes it and frees its small id, which moves the small ids later declarations get, and so
// the models and the search. decideSmt gives this under the same step limit (with nlsat's steps
// counted, #262).
#[test]
fn releases_a_builtin_declaration_of_a_model_as_the_typescript_does() {
    let text = fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/inputs/builtin-decl-release.smt"),
    )
    .expect("the input");
    let decision =
        on_deep_stack(|| prove_smt::decide(&text, &Limits::new(f64::INFINITY, Some(20_000), None)))
            .map(|decision| get_decision_text(&decision));
    assert_eq!(
        decision,
        Ok("unknown instances=11 steps=20007 stop=steps".into())
    );
}

/// Scripts outside the SMT-LIB that tlapm's encoder writes: attributes, symbols, numerals,
/// connectives, commands and logics it never writes, and scripts that misuse what it does write.
/// Z3 answers some with an error and some with a verdict; the port declines each before any step.
const OUTSIDE_THE_ENCODER: [&str; 49] = [
    r"(declare-const i Int)(declare-fun p (Int) Bool)(assert (! (p i) :named a))(assert (forall ((z Int)) (! (=> a (p z)) :pattern (a))))(assert (not (p 7)))(check-sat)",
    r"(declare-const x Bool)(assert (! x :named a))(assert (not (a)))(check-sat)",
    r"(declare-const x Bool)(assert (! (not x) :foo))(assert x)(check-sat)",
    r"(declare-const x Bool)(assert (! x :named a :foo))(assert (not a))(check-sat)",
    r"(declare-const i Int)(declare-fun f (Int) Int)(assert (forall ((z Int)) (! (> (f z) 0) :pattern (! (f i) :named a))))(assert (< a 0))(check-sat)",
    r"(declare-const x Bool)(assert (! (not x) :named -1))(assert x)(check-sat)",
    r"(declare-fun p (Int) Bool)(assert (forall ((z Int)) (! (p z) :qid 1)))(assert (not (p 0)))(check-sat)",
    r"(declare-fun p (Int) Bool)(assert (forall ((z Int)) (! (p z) :skolemid (a b))))(assert (not (p 0)))(check-sat)",
    r"(declare-fun p (Int) Bool)(assert (forall ((z Int)) (! (p z) :weight 2.0)))(assert (not (p 0)))(check-sat)",
    r"(declare-fun p (Int) Bool)(assert (forall ((z Int)) (! (p z) :no-pattern ((p z)))))(assert (not (p 0)))(check-sat)",
    r"(declare-fun p (Int) Bool)(assert (forall ((z Int)) (! (p z) :pattern ((p z)) :no-pattern (p z))))(assert (not (p 0)))(check-sat)",
    r"(declare-const x Bool)(assert (! (not x) :a:b n))(assert x)(check-sat)",
    r"(declare-const x Bool)(assert (! (not x) :lblpos :named))(assert x)(check-sat)",
    r"(declare-const x Bool)(assert (! x :named false))(assert false)(check-sat)",
    r"(declare-const x Bool)(assert (let ((false x)) false))(check-sat)",
    r"(declare-const i Int)(assert (! (> i 0) :named <))(assert (< i 0))(check-sat)",
    r"(declare-const |as| Bool)(assert |as|)(assert (not |as|))(check-sat)",
    r"(declare-fun _ (Int) Bool)(assert (_ 1))(assert (not (_ 1)))(check-sat)",
    r"(declare-const x Bool)(assert (let ((123 x)) (not x)))(assert x)(check-sat)",
    r"(declare-const a'b Bool)(assert a'b)(assert (not a'b))(check-sat)",
    r"(declare-const x Bool)(assert (not x) {)(assert x)(check-sat)",
    r"(declare-const x Bool)(assert (not x) #)(assert x)(check-sat)",
    r"(declare-const z Bool {)(assert z)(assert (not z))(check-sat)",
    r"(declare-const x Bool)(assert (! x :named a) {)(assert (not a))(check-sat)",
    r"(')(assert false)(check-sat)",
    r"(declare-const x Bool)(assert x)(foo ({) ) (assert (not x))(check-sat)",
    r"(declare-const x Bool)(assert x)(foo (#) ) (assert (not x))(check-sat)",
    r"(set-logic UFNIA zz)(declare-const r Real)(assert (> r 0.0))(assert (< r 0.0))(check-sat)",
    r"(declare-const i Int)(assert (< i -1))(assert (> i -3))(assert (not (= i -2)))(check-sat)",
    r"(declare-fun p (Int) Bool)(assert (forall ((z Int)) (! (p z) :pattern ((p z)) :qid |\|| :skolemid |\||)))(assert (not (p 0)))(check-sat)",
    r"(declare-const |a\|b| Bool)(assert |a\|b|)(assert (not |a\|b|))(check-sat)",
    r"(declare-fun p (Int) Bool)(assert (forall ((true Int)) (p true)))(assert (not (p 0)))(check-sat)",
    r"(declare-const x Bool)(assert (! x :named |false|))(assert (not |false|))(check-sat)",
    r"(declare-const x Bool)(assert (! x :named |+|))(assert (not |+|))(check-sat)",
    r"(declare-const x Bool)(assert (iff x (not x)))(check-sat)",
    r"(declare-const x Bool)(assert (implies x (not x)))(assert x)(check-sat)",
    r"(declare-const c Int)(declare-const c Bool)(assert (and (as c Bool) (not (as c Bool))))(check-sat)",
    r"(declare-fun g ((Int)) Int)(assert (not (= (g 1) (g 1))))(check-sat)",
    r"(simplify true)(set-logic UFNIA)(declare-const r Real)(assert (> r 0.0))(assert (< r 0.0))(check-sat)",
    r"(declare-const x Bool)(assert x)(check-sat)(exit 1)(assert false)(check-sat)",
    r#"(declare-const x Bool)(assert x)(check-sat)(echo "unsat")"#,
    r"(declare-fun a (Int) Bool)(declare-const i Int)(assert (let ((c a)) (< i 1)))(assert (> i 1))(check-sat)",
    r"(set-logic QF_UF)(declare-const x Bool)(assert x)(assert (not x))(check-sat)",
    r"(declare-const true Bool)(assert false)(check-sat)",
    r"(declare-fun f (Int) Int)(declare-fun f (Int) Bool)(assert false)(check-sat)",
    r"(declare-const x Bool)(assert x)(check-sat)(assert (not x))(check-sat)",
    r"(assert (and))(assert false)(check-sat)",
    r"(set-logic UFNIA)(declare-fun smt__i () Int)(assert (let ((smt__n0 (+ smt__i 1))) (let ((smt__n1 (* smt__n0 smt__n0))) (< smt__n1 0))))(check-sat)",
    r"(set-logic UFNIA)(declare-fun smt__a () Int)(declare-fun smt__b () Int)(declare-fun smt__c () Int)(assert (= smt__a smt__b smt__c))(assert (not (= smt__a smt__c)))(check-sat)",
];

/// Scripts inside the commands and symbols the encoder writes on which Z3 4.8.9 reports an error or
/// a warning, drops what it couldn't read and answers (independent break-it round on the subset):
/// a :named name that names something else, a bound name that is `true` or applied, a pattern Z3
/// drops, and an ill-sorted term. The port declines each, never answering where Z3 read otherwise.
const MISREAD_BY_Z3: [&str; 16] = [
    "(declare-fun smt__p () Bool)(assert (! smt__p :named |a|))(assert (! (not smt__p) :named |a|))",
    "(declare-fun smt__p () Bool)(assert (! smt__p :named |smt__p|))(assert (not smt__p))",
    "(declare-fun smt__p () Bool)(assert (! smt__p :named |smt__q|))(declare-fun smt__q () Int)(assert (= smt__q 5))(assert (= smt__q 6))",
    "(declare-fun smt__q () Bool)(assert (! smt__q :named |not|))(assert (not smt__q))",
    "(assert (exists ((true Bool)) (not true)))",
    "(assert (exists ((false Bool)) false))",
    "(assert (forall ((true Bool)) true))",
    "(declare-fun smt__f (Int) Int)(assert (forall ((smt__f Int)) (= (smt__f 1) 0)))(assert (= (smt__f 1) 1))",
    "(declare-fun smt__f (Int) Int)(assert (forall ((smt__x Int)) (! (= (smt__f smt__x) 0) :pattern ((forall ((smt__y Int)) (= smt__y smt__x))))))(assert (= (smt__f 1) 1))",
    "(declare-fun smt__f (Int) Int)(assert (forall ((smt__x Int)) (! (= (smt__f smt__x) 0) :pattern ((smt__f smt__x) smt__x))))(assert (= (smt__f 1) 1))",
    "(declare-fun smt__f (Int) Int)(assert (forall ((smt__x Int)) (! (= (smt__f smt__x) 0) :pattern ((+ smt__x 1)))))(assert (= (smt__f 1) 1))",
    "(declare-fun smt__f (Int Int) Int)(assert (forall ((smt__x Int) (smt__y Int)) (! (= (smt__f smt__x smt__y) 0) :pattern ((smt__f smt__x 1)))))(assert (= (smt__f 1 2) 1))",
    "(declare-fun smt__f (Int) Int)(assert (forall ((smt__y Int)) (forall ((smt__x Int)) (! (= (smt__f smt__x) smt__y) :pattern ((smt__f smt__y))))))(assert (= (smt__f 1) 1))",
    "(declare-fun smt__p () Bool)(declare-fun smt__i () Int)(assert (= smt__p smt__i))(assert (not smt__p))",
    "(declare-fun smt__i () Int)(assert (and smt__i true))",
    "(declare-fun smt__i () Int)(assert (+ smt__i 1))",
];

#[test]
fn declines_what_z3_reads_otherwise() {
    for body in MISREAD_BY_Z3 {
        let script = format!("(set-logic UFNIA)(declare-sort Idv 0){body}(check-sat)");
        let decision = decide_with(&script, None).map(|decision| get_decision_text(&decision));
        assert_eq!(
            decision,
            Ok("unknown stop=unsupported steps=0".into()),
            "{script}"
        );
    }
}

// Z3 stops at the rlimit a script sets, in the units the port counts as steps: one step is too few
// to refute even a contradiction, and Z3 4.8.9 answers unknown.
#[test]
fn stops_at_the_rlimit() {
    let script = "(set-option :rlimit 1)(set-logic UFNIA)(declare-sort Idv 0)\
                  (declare-fun smt__p () Bool)(assert smt__p)(assert (not smt__p))(check-sat)";
    let decision = decide_with(script, None).map(|decision| get_decision_text(&decision));
    assert_eq!(decision, Ok("unknown steps=3 stop=steps".into()));
}

#[test]
fn declines_what_tlapm_does_not_write() {
    for script in OUTSIDE_THE_ENCODER {
        let decision = decide_with(script, None).map(|decision| get_decision_text(&decision));
        assert_eq!(
            decision,
            Ok("unknown stop=unsupported steps=0".into()),
            "{script}"
        );
    }
}

// What the encoder writes is decided: a goal named |Goal|, a pattern, a negative numeral as
// (- 1), tlapm's rlimit and the final (exit).
#[test]
fn decides_what_tlapm_writes() {
    let script = "(set-option :rlimit 30000000)\n(set-logic UFNIA)\n(declare-sort Idv 0)\n\
                  (declare-fun smt__p (Int) Bool)\n(declare-fun smt__i () Int)\n\
                  (assert (forall ((smt__z Int)) (! (smt__p smt__z) :pattern ((smt__p smt__z)))))\n\
                  (assert (! (not (and (smt__p smt__i) (> smt__i (- 1)))) :named |Goal|))\n\
                  (assert (= smt__i 0))\n(check-sat)\n(exit)\n";
    assert_eq!(
        decide_with(script, None).map(|decision| decision.verdict),
        Ok(Verdict::Unsat)
    );
}

// Each let names the conjunction of the term before with itself: goal::quick_process splits the
// last into 2^59 conjuncts without taking a step, as Z3 5.3.3 does (`-T:20`: timeout at 9.4 GB).
// The size cap stops the decision and says why. Lets are outside the subset `decide` takes, so the
// solver is run on its own.
#[test]
fn stops_at_the_size_cap() {
    let text = (1..60).fold(
        "(declare-const x Bool)(declare-const y Bool)(assert (let ((n0 (and x y)))".to_string(),
        |text, index| {
            format!(
                "{text} (let ((n{index} (and n{} n{})))",
                index - 1,
                index - 1
            )
        },
    ) + " n59"
        + &")".repeat(61)
        + "(check-sat)";
    let stop = on_deep_stack(|| {
        let limit = ResourceLimit::new(&Limits::new(f64::INFINITY, None, None));
        let check = check_smt(&text, limit.clone()).map(|check| check.verdict);
        (check, limit.stop_reason())
    });
    assert_eq!(stop, (Err(SmtError::Canceled), Some(StopReason::Heap)));
}

// A multi-pattern over 2,910 terms of each of its two functions, with a weight that delays every
// one of its 8.5 million instances: Z3 5.3.3 answers sat in 4.5 s at 1.2 GB, and the port, which
// holds as much, answers too, under the cap.
#[test]
fn leaves_a_large_search_to_its_answer() {
    let mut text = String::from("(declare-fun f (Int) Bool)(declare-fun g (Int) Bool)");
    for index in 0..2910 {
        text += &format!("(declare-const c{index} Int)(assert (f c{index}))(assert (g c{index}))");
    }
    text += "(assert (forall ((x Int) (y Int)) (! (or (f x) (g y)) :pattern ((f x) (g y)) \
             :weight 100)))(check-sat)";
    assert_eq!(decide(&text), Ok(Verdict::Sat));
}

// Terms that take no step to build or to simplify: a negated disjunction 10,000 wide, the distinct
// of 1,000 constants and a product of 4,096 sums. Past the deadline, or once the signal is set,
// each stops while it is read, at its first step, since the clock is read without a step too.
#[test]
fn stops_a_large_term_at_the_deadline_without_a_step() {
    let declare = |count: usize, sort: &str| {
        (0..count)
            .map(|index| format!("(declare-fun smt__c{index} () {sort})\n"))
            .collect::<String>()
    };
    let constants = |count: usize| {
        (0..count)
            .map(|index| format!(" smt__c{index}"))
            .collect::<String>()
    };
    let product = (0..12).fold("(+ smt__c0 1)".to_string(), |term, _| {
        format!("(* {term} {term})")
    });
    let scripts = [
        format!(
            "{}(assert (not (or{})))",
            declare(10_000, "Bool"),
            constants(10_000)
        ),
        format!(
            "(declare-sort Idv 0)\n{}(assert (distinct{}))",
            declare(1_000, "Idv"),
            constants(1_000)
        ),
        format!("{}(assert (< {product} 0))", declare(1, "Int")),
    ];
    for script in scripts {
        let text = format!("(set-logic UFNIA)\n{script}\n(check-sat)\n");
        for (is_signaled, stop) in [(false, "time"), (true, "signal")] {
            let decision = on_deep_stack(|| {
                let limits = if is_signaled {
                    Limits::new(f64::INFINITY, Some(STEP_LIMIT), Some(Arc::new(|| true)))
                } else {
                    Limits::new(-1.0, Some(STEP_LIMIT), None)
                };
                prove_smt::decide(&text, &limits)
            })
            .map(|decision| get_decision_text(&decision));
            assert_eq!(decision, Ok(format!("unknown steps=1 stop={stop}")));
        }
    }
}
