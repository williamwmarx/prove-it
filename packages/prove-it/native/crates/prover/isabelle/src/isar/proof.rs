//! Ported from Isabelle2025's Pure/goal.ML (init), Pure/Isar/method.ML (insert_tac, finish) and the
//! terminal proof of Pure/Isar/proof.ML. Copyright (c) 1986-2025 University of Cambridge,
//! Technische Universitaet Muenchen, and contributors, see LICENSE.
//!
//! The goal of show "C" is C ==> #C, and using assms makes the assumptions its facts.
//! Goal.conjunction_tac, which METHOD runs first, changes nothing here: tlapm's goals have no Pure
//! conjunctions.
//!
//! (`isar/proof.ts`.)

use crate::error::Res;
use crate::pure::drule::{comp_incr, forall_intr_vars, protect_i, revcut_rl};
use crate::pure::simplifier::norm_hhf;
use crate::pure::tactic::resolve_tac;
use crate::pure::tactical::{Tactic, every};
use crate::pure::term::{mk_var, prop_t};
use crate::pure::thm::{Instantiation, Thm, assume, instantiate};

use super::statement::Statement;

/// Goal.init: C ==> #C.
pub fn init_goal(statement: &Statement) -> Res<Thm> {
    instantiate(
        &[Instantiation {
            variable: mk_var("A", 0, prop_t()),
            term: statement.conclusion.clone(),
        }],
        &protect_i(),
    )
}

/// Assumption.assume: an assumption in hhf normal form.
pub fn get_facts(statement: &Statement) -> Res<Vec<Thm>> {
    statement
        .assumptions
        .iter()
        .map(|assumption| norm_hhf(&assume(assumption.clone())?))
        .collect()
}

/// Method.insert_tac: each fact becomes a premise of the goal, in order.
pub fn insert_tac(facts: &[Thm], index: i32) -> Res<Tactic> {
    Ok(every(
        facts
            .iter()
            .map(|fact| {
                Ok(resolve_tac(&[comp_incr(
                    &forall_intr_vars(fact)?,
                    &revcut_rl(),
                )?])(index))
            })
            .collect::<Res<Vec<_>>>()?,
    ))
}
