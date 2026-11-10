//! Ported from Isabelle2025's Pure/goal.ML: focusing a tactic on one subgoal. Copyright (c)
//! 1986-2025 University of Cambridge, Technische Universitaet Muenchen, and contributors, see
//! LICENSE.

use std::rc::Rc;

use crate::error::{Res, thm_exn};

use super::drule::{comp_no_flatten, protect_d, protect_i};
use super::seq::empty_seq;
use super::tactical::{GoalTactic, Tactic, primitive, then_tac};
use super::thm::{Thm, nprems, permute_prems};

/// A ==> ... ==> C becomes A ==> #(... ==> C), keeping count premises.
fn protect(count: usize, thm: &Thm) -> Res<Thm> {
    comp_no_flatten(thm, count, 1, &protect_i())
}

/// A ==> ... ==> #C becomes A ==> ... ==> C.
fn conclude(thm: &Thm) -> Res<Thm> {
    comp_no_flatten(thm, nprems(thm), 1, &protect_d())
}

fn restrict(index: i32, count: i32, state: &Thm) -> Res<Thm> {
    if index < 1 || count < 1 || index + count - 1 > nprems(state) as i32 {
        return Err(thm_exn("Goal.restrict"));
    }
    protect(count as usize, &permute_prems(0, index - 1, state)?)
}

fn unrestrict(index: i32, state: &Thm) -> Res<Thm> {
    permute_prems(0, 1 - index, &conclude(state)?)
}

/// SELECT_GOAL: runs the tactic on goal index alone.
pub fn select_goal(tactic: Tactic) -> GoalTactic {
    Rc::new(move |index| {
        let tactic = tactic.clone();
        Rc::new(move |state: Thm| {
            if nprems(&state) == 1 && index == 1 {
                return tactic(state);
            }
            then_tac(
                then_tac(
                    primitive(move |current| restrict(index, 1, &current)),
                    tactic.clone(),
                ),
                primitive(move |current| unrestrict(index, &current)),
            )(state)
        })
    })
}

/// PREFER_GOAL: runs the tactic with goal index moved to the front.
pub fn prefer_goal(tactic: Tactic) -> GoalTactic {
    Rc::new(move |index| {
        let tactic = tactic.clone();
        Rc::new(move |state: Thm| {
            if index < 1 || index > nprems(&state) as i32 {
                return Ok(empty_seq());
            }
            then_tac(
                then_tac(
                    primitive(move |current| permute_prems(0, index - 1, &current)),
                    tactic.clone(),
                ),
                primitive(move |current| permute_prems(0, 1 - index, &current)),
            )(state)
        })
    })
}
