//! Ported from Isabelle2025's Tools/intuitionistic.ML and the rule order of
//! Pure/Isar/context_rules.ML. Copyright (c) 1986-2025 University of Cambridge, Technische
//! Universitaet Muenchen, and contributors, see LICENSE.
//!
//! iprover: intuitionistic proof search with the context rules, the rules declared intro, elim and
//! dest. Isabelle/TLA+ declares no context rule wrappers, so Swrap and wrap leave tactics as they
//! are.

use std::rc::Rc;

use crate::pure::drule::remdups_rl;
use crate::pure::goal::select_goal;
use crate::pure::list::{List, cons, list_iter};
use crate::pure::logic::{strip_assums_concl, strip_assums_hyp};
use crate::pure::search::deepen;
use crate::pure::tactic::{
    Brl, NetPair, assume_tac, biresolution_from_nets_tac, ematch_tac, eq_assume_tac,
};
use crate::pure::tactical::{
    GoalTactic, append_goal, no_tac, or_else, or_else_goal, repeat_determ_n, repeat_determ1,
    subgoal, then_all_new, then_tac,
};
use crate::pure::term::{Term, aconv};
use crate::pure::thm::{BiresRule, Thm};

#[derive(Clone)]
pub struct ContextRule {
    pub weight: i64,
    pub tag: i64,
    pub is_elim: bool,
    pub rule: Thm,
}

impl Brl for ContextRule {
    fn is_elim(&self) -> bool {
        self.is_elim
    }
    fn rule(&self) -> &Thm {
        &self.rule
    }
}

#[derive(Clone)]
pub struct IntuitionisticContext {
    /// Context_Rules.netpair_bang and Context_Rules.netpair.
    pub safe_rules: NetPair<ContextRule>,
    pub rules: NetPair<ContextRule>,
}

struct Visited {
    hyps: Vec<Term>,
    concl: Term,
}

/// Context_Rules.orderlist: by weight, then by tag, dropping all but the last of equal keys.
fn order_rules(rules: Vec<ContextRule>) -> Vec<BiresRule> {
    let mut sorted = rules;
    sorted.sort_by(|left, right| {
        left.weight
            .cmp(&right.weight)
            .then(left.tag.cmp(&right.tag))
    });
    sorted
        .iter()
        .enumerate()
        .filter(|(index, rule)| {
            index + 1 >= sorted.len()
                || sorted[index + 1].weight != rule.weight
                || sorted[index + 1].tag != rule.tag
        })
        .map(|(_, rule)| BiresRule {
            is_elim: rule.is_elim,
            rule: rule.rule.clone(),
        })
        .collect()
}

fn count_distinct(terms: &[Term]) -> usize {
    terms
        .iter()
        .fold(Vec::<&Term>::new(), |mut result, term| {
            if !result.iter().any(|other| aconv(other, term)) {
                result.push(term);
            }
            result
        })
        .len()
}

fn is_subset(left: &[Term], right: &[Term]) -> bool {
    left.iter()
        .all(|term| right.iter().any(|other| aconv(term, other)))
}

fn remdups_tac() -> GoalTactic {
    subgoal(|goal, index| {
        let prems = strip_assums_hyp(goal);
        Ok(repeat_determ_n(
            (prems.len() - count_distinct(&prems)) as i32,
            then_tac(ematch_tac(&[remdups_rl()])(index), eq_assume_tac()(index)),
        ))
    })
}

fn step_tac(context: &IntuitionisticContext) -> GoalTactic {
    let bires_tac = |is_match: bool, netpair: &NetPair<ContextRule>| {
        biresolution_from_nets_tac(order_rules, is_match, netpair.clone())
    };
    let safe_step_tac = then_all_new(
        or_else_goal(eq_assume_tac(), bires_tac(true, &context.safe_rules)),
        remdups_tac(),
    );
    let unsafe_step_tac = then_all_new(
        append_goal(
            assume_tac(),
            append_goal(
                bires_tac(false, &context.safe_rules),
                bires_tac(false, &context.rules),
            ),
        ),
        remdups_tac(),
    );
    Rc::new(move |index| or_else(repeat_determ1(safe_step_tac(index)), unsafe_step_tac(index)))
}

fn intprover_tac(
    context: IntuitionisticContext,
    visited: List<Visited>,
    depth: i32,
    limit: i32,
) -> GoalTactic {
    subgoal(move |goal, index| {
        if depth > limit {
            return Ok(no_tac());
        }
        let hyps = strip_assums_hyp(goal);
        let concl = strip_assums_concl(goal).clone();
        let is_visited = list_iter(&visited).any(|other| {
            aconv(&other.concl, &concl)
                && other.hyps.len() == hyps.len()
                && is_subset(&other.hyps, &hyps)
                && is_subset(&hyps, &other.hyps)
        });
        if is_visited {
            return Ok(no_tac());
        }
        Ok(then_all_new(
            step_tac(&context),
            intprover_tac(
                context.clone(),
                cons(Visited { hyps, concl }, visited.clone()),
                depth + 1,
                limit,
            ),
        )(index))
    })
}

/// Intuitionistic.prover_tac with the default depth limit.
pub fn prover_tac(context: &IntuitionisticContext) -> GoalTactic {
    let context = context.clone();
    select_goal(deepen(
        2,
        20,
        Rc::new(move |limit| intprover_tac(context.clone(), None, 0, limit)),
        4,
    )(1))
}

#[cfg(test)]
mod tests {
    use crate::provers::testing::check_provers;

    // The expectations are recorded from the TypeScript on the fixture theories' statements and on
    // facts and rules of the logic, under a step limit.
    #[test]
    fn iprover_matches_the_typescript() {
        check_provers(include_str!("../../testdata/provers/iprover.txt"));
    }
}
