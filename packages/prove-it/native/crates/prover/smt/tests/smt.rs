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
use prove_smt::util::rlimit::ResourceLimit;

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

/// The verdict, or the reason the port declines the input.
fn decide(text: &str) -> Result<Verdict, DecideError> {
    decide_with(text, None).map(|decision| decision.verdict)
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
            decide(&read(&recorded.name)),
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
        let verdict = decide(&read(&recorded.name));
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

/// Scripts with (reset), each with what Z3 5.3.3 prints on it, run as tlapm runs it: `z3 -smt2
/// -v:0 AUTO_CONFIG=false smt.MBQI=true -T:5`.
const RESETS: [(&str, &str); 20] = [
    ("(assert false)(reset)(check-sat)", "sat"),
    ("(assert false)(reset)(assert false)(check-sat)", "unsat"),
    ("(reset)(reset)(assert false)(check-sat)", "unsat"),
    ("(reset)\n(assert false)\n(check-sat)", "unsat"),
    ("(assert false)(check-sat)(reset)", "unsat"),
    ("(assert false)(reset)", ""),
    (
        "(declare-const x Bool)(assert x)(reset)(assert (not x))(check-sat)",
        "(error \"line 1 column 53: unknown constant x\")\nsat",
    ),
    (
        "(declare-const x Bool)(reset)(declare-const x Int)(assert (> x 0))(check-sat)",
        "sat",
    ),
    (
        "(declare-fun f (Int) Int)(assert (= (f 1) 2))(reset)(assert (= (f 1) 3))(check-sat)",
        "(error \"line 1 column 68: unknown constant f (Int) \")\nsat",
    ),
    (
        "(set-logic UFNIA)(declare-sort U 0)(reset)(declare-const u U)(check-sat)",
        "(error \"line 1 column 60: Invalid constant declaration: unknown sort 'U'\")\nsat",
    ),
    (
        "(declare-sort U 0)(declare-fun c () U)(reset)(declare-sort U 0)(declare-fun c () U)\
         (assert (= c c))(check-sat)",
        "sat",
    ),
    (
        "(declare-const x Bool)(assert (! x :named a))(reset)(assert a)(check-sat)",
        "(error \"line 1 column 61: unknown constant a\")\nsat",
    ),
    (
        "(declare-const x Bool)(assert (! x :named a))(reset)(declare-const a Bool)\
         (assert (not a))(check-sat)",
        "sat",
    ),
    (
        "(declare-const x Int)(assert (! (> x 0) :named a))(reset)(declare-const x Int)\
         (assert (! (< x 0) :named a))(check-sat)",
        "sat",
    ),
    (
        "(set-logic UFNIA)(assert false)(reset)(set-logic UFNIA)(check-sat)",
        "sat",
    ),
    (
        "(set-option :produce-unsat-cores true)(assert false)(reset)(check-sat)",
        "sat",
    ),
    (
        "(reset 1)(assert false)(check-sat)",
        "(error \"line 1 column 8: invalid reset command, ')' expected\")\nunsat",
    ),
    ("(push 1)(assert false)(reset)(check-sat)", "sat"),
    (
        "(push 1)(assert false)(reset)(pop 1)(check-sat)",
        "(error \"line 1 column 36: invalid pop command, argument is greater than the current \
         stack depth\")\nsat",
    ),
    (
        "(reset",
        "(error \"line 2 column 0: invalid reset command, ')' expected\")",
    ),
];

// cmd_context::reset forgets the assertions, the declarations, the named terms, the scopes and the
// logic. Where Z3 prints an error, which tlapm counts as a failure, the port fails with
// DecideError::Prover. Push and pop are outside the subset the port supports.
#[test]
fn resets_as_z3_does() {
    for (script, z3) in RESETS {
        let decision = decide_with(script, None);
        if script.contains("(push") {
            assert_eq!(
                decision.map(|decision| get_decision_text(&decision)),
                Ok("unknown stop=unsupported steps=1".into()),
                "{script}"
            );
        } else if z3.contains("(error") {
            assert!(
                matches!(decision, Err(DecideError::Prover(_))),
                "{script}: {decision:?}"
            );
        } else {
            let verdict = if z3.is_empty() { "unknown" } else { z3 };
            assert_eq!(
                decision.map(|decision| decision.verdict.name()),
                Ok(verdict),
                "{script}"
            );
        }
    }
}

// cmd_context::reset deletes the manager, and the next command makes a new one with its solver and
// its resource limit, whose count starts from 0: what follows a reset is decided as a script of its
// own, with the same ids, steps and instances. Z3 counts the same rlimit on Allocator-37 with this
// prefix as without it (5085).
#[test]
fn decides_what_follows_a_reset_as_a_script_of_its_own() {
    let prefix = "(declare-sort Idv 0)(declare-fun a () Idv)(assert (forall ((x Idv)) (= x a)))\
                  (assert false)(reset)";
    let decide = |text: &str| {
        on_deep_stack(|| {
            prove_smt::decide(
                text,
                &Limits::new(f64::INFINITY, Some(REFERENCE_STEP_LIMIT), None),
            )
        })
        .map(|decision| get_decision_text(&decision))
    };
    for name in ["Allocator-37.smt", "Barriers-63.smt", "CRDT_proof-49.smt"] {
        let text = read(name);
        assert_eq!(decide(&format!("{prefix}{text}")), decide(&text), "{name}");
    }
}

// The step limit stands for tlapm's time limit, which is the whole script's: a reset starts the
// count of the new manager again, not the budget. The prefix takes 3 steps, the solver's and one
// per assertion.
#[test]
fn a_reset_keeps_the_step_limit_of_the_decision() {
    let text = read("Allocator-37.smt");
    let decide = |text: &str, step_limit: u64| {
        on_deep_stack(|| {
            prove_smt::decide(text, &Limits::new(f64::INFINITY, Some(step_limit), None))
        })
        .map(|decision| get_decision_text(&decision))
    };
    let decision = decide(&text, 1000);
    assert_eq!(decision, Ok("unknown steps=1001 stop=steps".into()));
    assert_eq!(
        decide(&format!("(assert true)(assert true)(reset){text}"), 1003),
        decision
    );
}
