//! Helpers for the provers' tests, whose expectations in `testdata/provers` are recorded from the
//! TypeScript (classical.ts, intuitionistic.ts and blast) by a script that runs the same tactics on
//! the same goals under the same step limit.
//!
//! The rules are the logic's (`tla::logic`), set up as `tla::classical_setup` and `tla::context`
//! set them up.

use std::rc::Rc;

use prove_decide::Limits;

use crate::error::{Error, Res};
use crate::isar::method::ProofContext;
use crate::pure::interrupt::with_limits;
use crate::pure::seq::Seq;
use crate::pure::simp_testing::fixture_goal;
use crate::pure::tactical::append_tac;
use crate::pure::term::Term;
use crate::pure::testing::{check_problems, show_error};
use crate::pure::thm::tests::{digest, show_thm};
use crate::pure::thm::{Thm, trivial};
use crate::tla::classical_setup::get_fact;
use crate::tla::context::get_proof_context;
use crate::tla::logic::load_logic;
use crate::tools::intuitionistic::prover_tac;

use super::classical::{
    ClassicalContext, add_unsafe_dest, add_unsafe_intro, app_wrappers, clarify_tac, first_best_tac,
    inst0_step_tac, instp_step_tac, safe_tac, unsafe_step_tac, with_claset,
};

/// The proof context of tla/context.ts, which the provers' tests run in.
pub(crate) fn proof_context() -> Rc<ProofContext> {
    thread_local!(static CONTEXT: Rc<ProofContext> = Rc::new(get_proof_context(&load_logic()).unwrap()));
    CONTEXT.with(Rc::clone)
}

fn fact(name: &str) -> Thm {
    get_fact(&load_logic(), name).unwrap()
}

/// A goal by the name the script gives it: `thy:` a fixture theory's statement, `fact:` a fact of
/// the logic, `rule:` a rule of the claset's lists.
pub(crate) fn goal_of(name: &str) -> Term {
    if let Some(file) = name.strip_prefix("thy:") {
        return fixture_goal(file);
    }
    if let Some(name) = name.strip_prefix("fact:") {
        return fact(name).prop.clone();
    }
    let parts: Vec<&str> = name.split(':').collect();
    assert_eq!(parts[0], "rule");
    let index: usize = parts[2].parse().unwrap();
    let claset = &load_logic().claset;
    let list = match parts[1] {
        "safeIs" => &claset.safe_is,
        "safeEs" => &claset.safe_es,
        "unsafeIs" => &claset.unsafe_is,
        "unsafeEs" => &claset.unsafe_es,
        other => panic!("no rule list {other}"),
    };
    list[index].rule.prop.clone()
}

pub(crate) fn classical_context() -> ClassicalContext {
    proof_context().classical.clone()
}

/// An exception as the script prints it, with a stack overflow as `error Stack`.
fn show_outcome(error: &Error) -> String {
    match error {
        Error::Stack => "error Stack".into(),
        other => show_error(other),
    }
}

/// The first count results of a sequence, as the script prints them.
fn many(lines: &mut Vec<String>, label: &str, count: usize, run: impl FnOnce() -> Res<Seq<Thm>>) {
    lines.push(label.into());
    let result = (|| {
        let mut seq = run()?;
        for index in 0.. {
            if index == count {
                lines.push("stop".into());
                return Ok(());
            }
            let Some((result, rest)) = seq.pull()? else {
                lines.push("end".into());
                return Ok(());
            };
            lines.push(format!("result {index}"));
            lines.extend(show_thm(&result));
            seq = rest;
        }
        Ok(())
    })();
    if let Err(error) = result {
        lines.push(show_outcome(&error));
    }
}

fn run(kind: &str, goal: &Term) -> Res<Seq<Thm>> {
    let proof = proof_context();
    let context = classical_context();
    let state = trivial(goal)?;
    match kind {
        "safe" => safe_tac(&context)(state),
        "clarify" => clarify_tac(&context)(1)(state),
        "best" => first_best_tac(&context, &proof.atomize_rules)?(1)(state),
        "steps" => {
            let inner = context.clone();
            append_tac(
                inst0_step_tac(&context)(1),
                app_wrappers(
                    &context,
                    Rc::new(move |index| {
                        append_tac(
                            instp_step_tac(&inner)(index),
                            unsafe_step_tac(&inner)(index),
                        )
                    }),
                )(1),
            )(state)
        }
        "blast" => (proof.blast_tac)(&context)?(1)(state),
        "depth" => (proof.blast_depth_tac)(&context, 2)?(1)(state),
        "iprover" => prover_tac(&proof.intuitionistic)(1)(state),
        other => panic!("unknown kind {other}"),
    }
}

/// add_unsafe_intro or add_unsafe_dest of a fact, then an unsafe step with the new claset.
fn add_problem(kind: &str, name: &str, lines: &mut Vec<String>) -> Res<()> {
    let context = classical_context();
    let fact = fact(name.strip_prefix("fact:").unwrap());
    let claset = if kind == "intro" {
        add_unsafe_intro(&context, &fact)?
    } else {
        add_unsafe_dest(&context, &fact)?
    };
    let entries = if kind == "intro" {
        &claset.unsafe_is
    } else {
        &claset.unsafe_es
    };
    lines.push(format!("count {}", entries.len()));
    let entry = &entries[0];
    lines.push(format!("internal {}", digest(&entry.internal.prop)));
    lines.push(format!("dup {}", digest(&entry.dup.prop)));
    for swapped in &entry.swapped {
        lines.push(format!("swapped {}", digest(&swapped.prop)));
    }
    for swapped in &entry.dup_swapped {
        lines.push(format!("dupSwapped {}", digest(&swapped.prop)));
    }
    let new_context = with_claset(&context, claset);
    let goal = fact.prop.clone();
    many(lines, "results", 2, || {
        unsafe_step_tac(&new_context)(1)(trivial(&goal)?)
    });
    Ok(())
}

/// Solves a problem of the script: `kind<TAB>goal<TAB>step limit`.
fn solve(kind: &str, fields: &[&str]) -> Vec<String> {
    let limits = Limits::new(f64::INFINITY, Some(fields[1].parse().unwrap()), None);
    let mut lines = Vec::new();
    with_limits(&limits, || {
        if kind == "intro" || kind == "dest" {
            if let Err(error) = add_problem(kind, fields[0], &mut lines) {
                lines.push(show_outcome(&error));
            }
        } else {
            let goal = goal_of(fields[0]);
            many(&mut lines, "results", 2, || run(kind, &goal));
        }
    });
    lines.push(format!("steps {}", limits.steps()));
    lines
}

/// Checks the problems of a test file on a thread with the stack a decision runs on
/// (prove-it-host's DECIDE_STACK_BYTES), since blast's search recurses at each choice point.
pub(crate) fn check_provers(text: &'static str) {
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || check_problems(text, solve))
        .unwrap()
        .join()
        .unwrap();
}
