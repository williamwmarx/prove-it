//! Decides a theory tlapm writes for Isabelle, as tlapm's Isabelle backend runs it: use_thy on the
//! heap of Isabelle/TLA+ succeeds or fails.
//!
//! (`decide.ts`.) The statistics are what stopped a proof that gave up, `stop`, and the steps.

use prove_decide::{DecideError, Decision, Limits, Statistic, Verdict};

use crate::error::{Error, Res};
use crate::isar::method::{parse_proof_text, terminal_proof};
use crate::isar::proof::{get_facts, init_goal};
use crate::isar::statement::read_statement;
use crate::isar::theory::parse_theory;
use crate::pure::interrupt::with_limits;
use crate::pure::logic::protect;
use crate::pure::seq::seq_head;
use crate::pure::term::aconv;
use crate::tla::context::load_proof_context;
use crate::tla::logic::load_logic;

/// Whether the proof proves the statement.
fn is_proved(text: &str) -> Res<bool> {
    let theory = parse_theory(text)?;
    let logic = load_logic();
    let statement = read_statement(&logic, &theory)?;
    let facts = if theory.is_using_assms {
        get_facts(&statement)?
    } else {
        Vec::new()
    };
    let context = load_proof_context()?;
    let proof = parse_proof_text(&theory.method)?;
    let result = seq_head(&terminal_proof(
        &context,
        &proof,
        &facts,
        init_goal(&statement)?,
    )?)?;
    // Proof.conclude_goal: the theorem must be the statement, from its assumptions only.
    Ok(result.is_some_and(|result| {
        result.tpairs.is_empty()
            && aconv(&result.prop, &protect(statement.conclusion.clone()))
            && result.hyps.iter().all(|hyp| {
                statement
                    .assumptions
                    .iter()
                    .any(|assumption| aconv(hyp, assumption))
            })
    }))
}

/// decideIsabelle: unsat when the proof proves the statement, unknown when it fails or gives up.
pub fn decide(text: &str, limits: &Limits) -> Result<Decision, DecideError> {
    if !text.is_ascii() {
        return Err(DecideError::Prover(
            "Isabelle's port reads ASCII theories only".into(),
        ));
    }
    let outcome = with_limits(limits, || is_proved(text));
    let (verdict, stop) = match outcome {
        Ok(true) => (Verdict::Unsat, None),
        Ok(false) => (Verdict::Unknown, None),
        Err(Error::Isabelle(exception, _)) => (Verdict::Unknown, Some(exception.name())),
        // Poly/ML grows its stack instead, until Isabelle runs out of memory, which tlapm counts
        // as a failure. The TypeScript answers unknown on JavaScript's stack overflow; in
        // WebAssembly the host's stack is the limit, so the port doesn't guess.
        #[cfg(not(target_arch = "wasm32"))]
        Err(Error::Stack) => (Verdict::Unknown, Some("stack")),
        #[cfg(target_arch = "wasm32")]
        Err(Error::Stack) => {
            return Err(DecideError::Declined(
                "Isabelle's proof recursed deeper than WebAssembly's stack allows".into(),
            ));
        }
        // Only a local exception that escaped its handler can be anything else, which is a bug
        // of the port and a failure, as an Isabelle that breaks down is to tlapm.
        Err(error) => {
            return Err(DecideError::Prover(format!(
                "Isabelle's port let an internal exception escape: {error:?}"
            )));
        }
    };
    let mut statistics = Vec::new();
    if let Some(stop) = stop {
        statistics.push(("stop", Statistic::Text(stop.into())));
    }
    statistics.push(("steps", Statistic::Count(limits.steps())));
    Ok(Decision {
        verdict,
        statistics,
    })
}

#[cfg(test)]
mod tests {
    use std::time::Instant;

    use super::*;

    macro_rules! fixtures {
        ($($name:literal),* $(,)?) => {
            [$((
                $name,
                include_str!(concat!("../../../../../tests/fixtures/isabelle/", $name, ".thy")),
            )),*]
        };
    }

    /// Theories tlapm wrote for Isabelle, named after their module and obligation
    /// (`tests/fixtures/isabelle`).
    const FIXTURES: [(&str, &str); 12] = fixtures!(
        "AllocatorImplementation_proof-127",
        "AllocatorImplementation_proof-33",
        "AtomicBakeryWithoutSMT-465",
        "AtomicBakeryWithoutSMT-6",
        "FiniteSetTheorems_proofs-453",
        "Level_test-1",
        "NaturalsInduction_proofs-1",
        "Paxos-109",
        "Sets-183",
        "TLAPS-2",
        "constantfcn_test-1",
        "function_except_tuple_soundness_gh201_test-1",
    );

    fn read_theory(name: &str) -> &'static str {
        FIXTURES
            .iter()
            .find(|(known, _)| *known == name)
            .unwrap_or_else(|| panic!("no fixture {name}"))
            .1
    }

    /// `text.replace(/^shows ".*?"/m, replacement)`.
    fn replace_shows(text: &str, replacement: &str) -> String {
        let start = text.find("\nshows \"").unwrap() + 1;
        let end = start + "shows \"".len();
        let close = end + text[end..].find('"').unwrap() + 1;
        format!("{}{replacement}{}", &text[..start], &text[close..])
    }

    /// `text.replace(/^assumes .*\n/m, "")`.
    fn remove_assumes(text: &str) -> String {
        let start = text.find("\nassumes ").unwrap() + 1;
        let end = start + text[start..].find('\n').unwrap() + 1;
        format!("{}{}", &text[..start], &text[end..])
    }

    fn false_goal() -> String {
        remove_assumes(read_theory("function_except_tuple_soundness_gh201_test-1"))
    }

    /// A case of the unit test and the differential by name: `thy:` a fixture, `and:` a fixture
    /// with a symbol that never closes, `noassms:` a fixture without its assumptions, `false:` FALSE
    /// by a method.
    fn case_text(name: &str) -> String {
        let (kind, argument) = name.split_once(':').unwrap();
        match kind {
            "thy" => read_theory(argument).into(),
            "and" => replace_shows(read_theory(argument), "shows \"\\<and\""),
            "noassms" => read_theory(argument).replace("using assms by", "by"),
            "false" => false_goal().replace("using assms by auto", &format!("by {argument}")),
            _ => panic!("no case {name}"),
        }
    }

    /// Runs decide as prove-it-host does, on a thread with DECIDE_STACK_BYTES of stack.
    fn decide_on_stack(text: String, time_limit: f64, step_limit: Option<u64>) -> Decision {
        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(move || {
                decide(&text, &Limits::new(time_limit, step_limit, None))
                    .unwrap_or_else(|error| panic!("declined: {error:?}"))
            })
            .unwrap()
            .join()
            .unwrap()
    }

    /// The unit test's decide: a time limit of 30 seconds.
    fn decide_text(text: String) -> Decision {
        decide_on_stack(text, 30_000.0, None)
    }

    fn get_stop(decision: &Decision) -> Option<&str> {
        decision
            .statistics
            .iter()
            .find_map(|(name, statistic)| match (name, statistic) {
                (&"stop", Statistic::Text(stop)) => Some(stop.as_str()),
                _ => None,
            })
    }

    // decideIsabelle gives Isabelle's verdict on tlapm's theories.
    #[test]
    fn gives_isabelles_verdict_on_tlapms_theories() {
        let cases = [
            ("AllocatorImplementation_proof-33", "auto", Verdict::Unsat),
            (
                "AllocatorImplementation_proof-127",
                "iprover",
                Verdict::Unsat,
            ),
            ("FiniteSetTheorems_proofs-453", "blast", Verdict::Unsat),
            ("Sets-183", "force", Verdict::Unsat),
            ("TLAPS-2", "(auto intro: inIrrefl)", Verdict::Unsat),
            (
                "NaturalsInduction_proofs-1",
                "(intro natInduct, auto)",
                Verdict::Unsat,
            ),
            (
                "AtomicBakeryWithoutSMT-6",
                "(auto dest: int_leq_less_trans)",
                Verdict::Unsat,
            ),
            (
                "AtomicBakeryWithoutSMT-465",
                "clarsimp auto?",
                Verdict::Unsat,
            ),
            (
                "function_except_tuple_soundness_gh201_test-1",
                "auto",
                Verdict::Unknown,
            ),
            ("constantfcn_test-1", "auto", Verdict::Unknown),
        ];
        for (name, method, verdict) in cases {
            let text = read_theory(name);
            assert!(text.contains(&format!("by {method}\n")), "{name}");
            assert_eq!(decide_text(text.into()).verdict, verdict, "{name}");
        }
    }

    #[test]
    fn answers_unknown_for_a_theory_tlapm_stopped_writing_partway() {
        assert_eq!(
            decide_text(read_theory("Level_test-1").into()).verdict,
            Verdict::Unknown
        );
    }

    #[test]
    fn answers_unknown_for_a_symbol_that_never_closes() {
        let text = case_text("and:constantfcn_test-1");
        assert!(text.contains("shows \"\\<and\""));
        let decision = decide_text(text);
        assert_eq!(decision.verdict, Verdict::Unknown);
        assert_eq!(get_stop(&decision), Some("ERROR"));
    }

    // tla-ts's encoder wrote this one, since tlapm proved the obligation with SMT. The simplifier
    // keeps growing the goal, and Isabelle breaks down after two minutes.
    #[test]
    fn answers_unknown_when_the_simplifier_runs_out_of_stack() {
        assert_eq!(
            decide_text(read_theory("Paxos-109").into()).verdict,
            Verdict::Unknown
        );
    }

    // decideIsabelle doesn't prove what doesn't follow. Isabelle fails on each of these too.
    #[test]
    fn doesnt_prove_a_theory_without_its_assumptions() {
        for name in [
            "AllocatorImplementation_proof-33",
            "AllocatorImplementation_proof-127",
            "FiniteSetTheorems_proofs-453",
            "Sets-183",
        ] {
            assert!(read_theory(name).contains("using assms by"), "{name}");
            assert_eq!(
                decide_text(case_text(&format!("noassms:{name}"))).verdict,
                Verdict::Unknown,
                "{name}"
            );
        }
    }

    #[test]
    fn doesnt_prove_false() {
        assert!(false_goal().contains("shows \"(FALSE)\""));
        for method in ["auto", "blast", "iprover", "force", "clarsimp auto?"] {
            assert_eq!(
                decide_text(case_text(&format!("false:{method}"))).verdict,
                Verdict::Unknown,
                "{method}"
            );
        }
    }

    // tlapm counts an Isabelle that stops on its input as a failure.
    #[test]
    fn fails_on_a_theory_that_is_not_ascii() {
        let limits = Limits::new(f64::INFINITY, None, None);
        assert_eq!(
            decide("theory \u{e9}", &limits),
            Err(DecideError::Prover(
                "Isabelle's port reads ASCII theories only".into()
            ))
        );
    }

    /// The decider differential on the fixtures: the TypeScript's verdict and statistics under a
    /// step limit (`testdata/decide.txt`), which the port must give step for step. Where the
    /// TypeScript overflowed JavaScript's stack (`stop` stack, Paxos-109 under its natural steps),
    /// the steps depend on the runtime, so the port must only answer unknown, having given up on
    /// its own depth bound or the step limit.
    #[test]
    fn matches_the_typescript_under_a_step_limit() {
        let mut differences = Vec::new();
        for line in include_str!("../testdata/decide.txt").lines() {
            if line.starts_with('#') {
                continue;
            }
            let fields: Vec<&str> = line.split('\t').collect();
            let [name, limit, verdict, stop, steps] = fields[..] else {
                panic!("a malformed line: {line}");
            };
            let start = Instant::now();
            let decision =
                decide_on_stack(case_text(name), f64::INFINITY, Some(limit.parse().unwrap()));
            let actual_stop = get_stop(&decision).unwrap_or("-");
            let actual_steps = match decision.statistics.last() {
                Some(("steps", Statistic::Count(count))) => count.to_string(),
                _ => panic!("no steps for {name}"),
            };
            let actual = format!("{}\t{actual_stop}\t{actual_steps}", decision.verdict.name());
            eprintln!("{name}\t{limit}\t{actual}\t{:?}", start.elapsed());
            let is_same = if stop == "stack" {
                decision.verdict == Verdict::Unknown
                    && ["stack", "Interrupt"].contains(&actual_stop)
            } else {
                actual == format!("{verdict}\t{stop}\t{steps}")
            };
            if !is_same {
                differences.push(format!(
                    "{name} under {limit}: TypeScript {verdict} {stop} {steps}, Rust {actual}"
                ));
            }
        }
        assert!(differences.is_empty(), "{}", differences.join("\n"));
    }
}
