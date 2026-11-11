//! Ported from Z3 (src/smt/smt_solver.cpp, src/smt/smt_kernel.cpp, src/smt/smt_setup.cpp), MIT
//! license, see z3-license.txt, through `solver.ts`. Decides an SMT-LIB problem the way `z3 -smt2
//! AUTO_CONFIG=false smt.MBQI=true` does for tlapm's UFNIA obligations.

use prove_decide::{Decision, Limits, Statistic, Verdict};

use crate::core::asserted_formulas::AssertedFormulas;
use crate::core::ast::AstManager;
use crate::core::context::{Context, SmtParams};
use crate::core::quant_tactics::apply_ufnia_tactic;
use crate::core::script_subset::check_script;
use crate::core::smtlib_parser::parse_smtlib;
use crate::util::error::SmtError;
use crate::util::lbool::LBool;
use crate::util::rlimit::ResourceLimit;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SmtCheck {
    pub verdict: Verdict,
    pub num_instances: u32,
}

/// The verdict, and the number of quantifier instances the search made. `limit` is the resource
/// limit of the manager, which the caller may keep a clone of to read its count.
pub fn check_smt(text: &str, limit: ResourceLimit) -> Result<SmtCheck, SmtError> {
    let mut manager = AstManager::new(limit);
    // combined_solver gives each assertion to the incremental smt kernel as well, which rewrites
    // it when it is asserted and keeps it, though check-sat then runs the tactic on the assertions.
    // The kernel's model finder counts a step of the resource limit when it is made, and
    // solver::assert_expr counts one for each assertion.
    let mut incremental = AssertedFormulas::new(&manager);
    manager.limit.inc();
    let problem = parse_smtlib(text, &mut manager, |manager, assertion| {
        manager.limit.inc();
        incremental.assert_expr(manager, assertion)
    })?;
    if !problem.has_check_sat {
        return Ok(SmtCheck {
            verdict: Verdict::Unknown,
            num_instances: 0,
        });
    }
    let goal = apply_ufnia_tactic(&mut manager, &problem.assertions)?;
    // and_then runs smt_tactic only on a goal that the preprocessing left undecided.
    if goal.is_inconsistent || goal.forms.is_empty() {
        return Ok(SmtCheck {
            verdict: if goal.is_inconsistent {
                Verdict::Unsat
            } else {
                Verdict::Sat
            },
            num_instances: 0,
        });
    }
    // smt_tactic makes the context, which makes its asserted formulas first, and asserts the goal.
    // setup_context then makes the theories, before the formulas are reduced.
    let mut asserted = AssertedFormulas::new(&manager);
    let mut context = Context::new(
        manager,
        SmtParams {
            is_mbqi: true,
            relevancy_level: 2,
        },
    )?;
    for assertion in goal.forms.items.iter().copied() {
        asserted.assert_expr(&mut context.m, assertion)?;
    }
    context.setup_context()?;
    context.internalize_assertions(&mut asserted)?;
    let result = context.search()?;
    Ok(SmtCheck {
        verdict: match result {
            LBool::False => Verdict::Unsat,
            LBool::True => Verdict::Sat,
            LBool::Undef => Verdict::Unknown,
        },
        num_instances: context.qmanager.get_num_instances(),
    })
}

/// Sets a statistic as a JavaScript object's property is set: in place if it is there, else last.
fn set_statistic(
    statistics: &mut Vec<(&'static str, Statistic)>,
    name: &'static str,
    value: Statistic,
) {
    match statistics.iter_mut().find(|entry| entry.0 == name) {
        Some(entry) => entry.1 = value,
        None => statistics.push((name, value)),
    }
}

/// Fails with `SmtError::Parse` on malformed input, where the TypeScript throws `SmtParseError`.
/// Input outside the subset the solver supports is unknown, and so is a search that runs past the
/// time or step limit or that another thread cancels. The statistics are the steps of Z3's
/// resource limit, the quantifier instances, and what stopped a search that gave up, in the order
/// the TypeScript writes them. Every other error, which the TypeScript rethrows, fails as well.
pub fn decide_smt(text: &str, limits: &Limits) -> Result<Decision, SmtError> {
    let limit = ResourceLimit::new(limits);
    let mut statistics = Vec::new();
    // Only the SMT-LIB tlapm's encoder writes is decided; anything else is declined.
    if check_script(text).is_err() {
        set_statistic(
            &mut statistics,
            "stop",
            Statistic::Text("unsupported".into()),
        );
        set_statistic(&mut statistics, "steps", Statistic::Count(0));
        return Ok(Decision {
            verdict: Verdict::Unknown,
            statistics,
        });
    }
    let verdict = match check_smt(text, limit.clone()) {
        Ok(check) => {
            set_statistic(
                &mut statistics,
                "instances",
                Statistic::Count(u64::from(check.num_instances)),
            );
            check.verdict
        }
        Err(SmtError::Canceled) => Verdict::Unknown,
        Err(SmtError::Unsupported(_)) => {
            set_statistic(
                &mut statistics,
                "stop",
                Statistic::Text("unsupported".into()),
            );
            Verdict::Unknown
        }
        Err(error) => return Err(error),
    };
    set_statistic(&mut statistics, "steps", Statistic::Count(limit.count()));
    if let Some(reason) = limit.stop_reason() {
        set_statistic(
            &mut statistics,
            "stop",
            Statistic::Text(reason.name().into()),
        );
    }
    Ok(Decision {
        verdict,
        statistics,
    })
}

#[cfg(test)]
mod tests {
    //! The statistics `decideSmt` writes, in its order, on what stops a decision early: each
    //! expectation is the TypeScript's on the same input and limits.

    use std::sync::Arc;

    use prove_decide::{Cancel, Decision, Limits, Statistic, Verdict};

    use super::decide_smt;

    fn read(name: &str) -> String {
        let path = format!(
            "{}/../../../../tests/fixtures/smt/{name}",
            env!("CARGO_MANIFEST_DIR")
        );
        std::fs::read_to_string(path).unwrap()
    }

    fn decide(text: &str, step_limit: Option<u64>, cancel: Option<Cancel>) -> Decision {
        decide_smt(text, &Limits::new(f64::INFINITY, step_limit, cancel)).unwrap()
    }

    fn count(count: u64) -> Statistic {
        Statistic::Count(count)
    }

    fn text(text: &str) -> Statistic {
        Statistic::Text(text.into())
    }

    // A script outside what tlapm's encoder writes is declined before any step.
    #[test]
    fn unsupported_input_is_unknown_and_says_so_before_the_steps() {
        for script in [
            "(declare-sort U 0)\n(push 1)\n(check-sat)\n",
            "(set-logic UFNIA)(declare-fun smt__p () Bool)(assert smt__p)\n",
        ] {
            let decision = decide(script, None, None);
            assert_eq!(decision.verdict, Verdict::Unknown);
            assert_eq!(
                decision.statistics,
                [("stop", text("unsupported")), ("steps", count(0))]
            );
        }
    }

    // The parser reads the cancel on its 256th check, which takes no step, at step 174.
    #[test]
    fn a_canceled_decision_stops_where_it_reads_the_cancel() {
        let cancel: Cancel = Arc::new(|| true);
        let decision = decide(&read("Barriers-63.smt"), None, Some(cancel));
        assert_eq!(decision.verdict, Verdict::Unknown);
        assert_eq!(
            decision.statistics,
            [("steps", count(174)), ("stop", text("signal"))]
        );
    }

    #[test]
    fn the_step_limit_stops_the_decision() {
        let decision = decide(&read("Allocator-37.smt"), Some(1000), None);
        assert_eq!(decision.verdict, Verdict::Unknown);
        assert_eq!(
            decision.statistics,
            [("steps", count(1001)), ("stop", text("steps"))]
        );
    }
}
