//! Ported from Isabelle2025's Pure/tactical.ML and Pure/search.ML. Copyright (c) 1986-2025
//! University of Cambridge, Technische Universitaet Muenchen, and contributors, see LICENSE.
//!
//! (`pure/tactical.ts`.) A tactic may raise when applied, before its sequence is pulled, so it
//! returns a `Res`. A goal tactic takes a goal index, `i32` as the TypeScript's number: callers may
//! pass an index out of range, which the tactics reject.

use std::rc::Rc;

use crate::error::{Exception, Res};

use super::interrupt::check_stack;
use super::list::{List, cons, list_iter};
use super::seq::{
    Cell, Seq, Step, append_seq, defer_seq, empty_seq, filter_seq, make_seq, maps_seq, of_cell,
    single_seq,
};
use super::term::{Term, aconv};
use super::thm::{Thm, nprems, prem_of};

pub type Tactic = Rc<dyn Fn(Thm) -> Res<Seq<Thm>>>;
pub type GoalTactic = Rc<dyn Fn(i32) -> Tactic>;

pub fn all_tac() -> Tactic {
    Rc::new(|state| Ok(single_seq(state)))
}

pub fn no_tac() -> Tactic {
    Rc::new(|_| Ok(empty_seq()))
}

pub fn then_tac(first: Tactic, second: Tactic) -> Tactic {
    Rc::new(move |state| {
        let second = second.clone();
        Ok(maps_seq(move |result| second(result), first(state)?))
    })
}

pub fn or_else(first: Tactic, second: Tactic) -> Tactic {
    Rc::new(move |state: Thm| {
        let cell = first(state.clone())?.pull()?;
        match cell {
            None => second(state),
            cell => Ok(of_cell(cell)),
        }
    })
}

pub fn append_tac(first: Tactic, second: Tactic) -> Tactic {
    Rc::new(move |state: Thm| {
        let second = second.clone();
        let deferred = state.clone();
        Ok(append_seq(
            first(state)?,
            defer_seq(move || Ok(Step::Seq(second(deferred.clone())?))),
        ))
    })
}

pub fn then_else(test: Tactic, on_success: Tactic, on_failure: Tactic) -> Tactic {
    Rc::new(move |state: Thm| {
        let cell = test(state.clone())?.pull()?;
        match cell {
            None => on_failure(state),
            cell => {
                let on_success = on_success.clone();
                Ok(maps_seq(move |result| on_success(result), of_cell(cell)))
            }
        }
    })
}

pub fn then_goal(first: GoalTactic, second: GoalTactic) -> GoalTactic {
    Rc::new(move |index| then_tac(first(index), second(index)))
}

pub fn or_else_goal(first: GoalTactic, second: GoalTactic) -> GoalTactic {
    Rc::new(move |index| or_else(first(index), second(index)))
}

pub fn append_goal(first: GoalTactic, second: GoalTactic) -> GoalTactic {
    Rc::new(move |index| append_tac(first(index), second(index)))
}

pub fn determ(tactic: Tactic) -> Tactic {
    Rc::new(move |state: Thm| {
        let tactic = tactic.clone();
        Ok(make_seq(move || {
            let cell = tactic(state.clone())?.pull()?;
            Ok(cell.map(|(result, _)| (result, empty_seq())))
        }))
    })
}

pub fn try_tac(tactic: Tactic) -> Tactic {
    or_else(tactic, all_tac())
}

/// Thm.eq_thm: equal hypotheses, flex-flex pairs and propositions.
pub fn eq_thm(left: &Thm, right: &Thm) -> bool {
    Thm::ptr_eq(left, right)
        || (aconv(&left.prop, &right.prop)
            && left.hyps.len() == right.hyps.len()
            && left
                .hyps
                .iter()
                .all(|hyp| right.hyps.iter().any(|other| aconv(hyp, other)))
            && left.tpairs.len() == right.tpairs.len()
            && left
                .tpairs
                .iter()
                .zip(right.tpairs.iter())
                .all(|(pair, other)| aconv(&pair.0, &other.0) && aconv(&pair.1, &other.1)))
}

pub fn eq_thm_prop(left: &Thm, right: &Thm) -> bool {
    aconv(&left.prop, &right.prop)
}

/// A choice point of EVERY: the state a tactic returned, its alternatives, and the tactics after
/// it (from `start` on).
#[derive(Clone)]
struct Trail {
    state: Thm,
    rest: Seq<Thm>,
    start: usize,
}

fn evy(tactics: Rc<[Tactic]>, trail: List<Trail>, start: usize, state: Thm) -> Res<Seq<Thm>> {
    let _depth = check_stack()?;
    let Some(tactic) = tactics.get(start) else {
        return Ok(make_seq(move || {
            Ok(Some((
                state.clone(),
                make_seq({
                    let tactics = tactics.clone();
                    let trail = trail.clone();
                    move || evy_back(tactics.clone(), trail.clone())?.pull()
                }),
            )))
        }));
    };
    let Some((result, rest)) = tactic(state)?.pull()? else {
        return evy_back(tactics, trail);
    };
    evy(
        tactics.clone(),
        cons(
            Trail {
                state: result.clone(),
                rest,
                start: start + 1,
            },
            trail,
        ),
        start + 1,
        result,
    )
}

fn evy_back(tactics: Rc<[Tactic]>, trail: List<Trail>) -> Res<Seq<Thm>> {
    let mut current = trail;
    while let Some(top) = current.clone() {
        let cell = top.head.rest.pull()?;
        match cell {
            None => current = top.tail.clone(),
            Some((state, rest)) if eq_thm(&top.head.state, &state) => {
                current = cons(
                    Trail {
                        rest,
                        ..top.head.clone()
                    },
                    top.tail.clone(),
                );
            }
            Some((state, rest)) => {
                return evy(
                    tactics,
                    cons(
                        Trail {
                            state: state.clone(),
                            rest,
                            start: top.head.start,
                        },
                        top.tail.clone(),
                    ),
                    top.head.start,
                    state,
                );
            }
        }
    }
    Ok(empty_seq())
}

/// EVERY: tac1 THEN ... THEN tacn, without backtracking over repeated states.
pub fn every(tactics: Vec<Tactic>) -> Tactic {
    let tactics: Rc<[Tactic]> = tactics.into();
    Rc::new(move |state| evy(tactics.clone(), None, 0, state))
}

pub fn first(tactics: Vec<Tactic>) -> Tactic {
    tactics
        .into_iter()
        .rev()
        .fold(no_tac(), |rest, tactic| or_else(tactic, rest))
}

pub fn first_goal(tactics: Vec<GoalTactic>) -> GoalTactic {
    Rc::new(move |index| first(tactics.iter().map(|tactic| tactic(index)).collect()))
}

pub fn repeat_determ_n(count: i32, tactic: Tactic) -> Tactic {
    Rc::new(move |state: Thm| {
        let tactic = tactic.clone();
        Ok(make_seq(move || {
            let mut current = state.clone();
            let mut remaining = i64::from(count);
            while remaining != 0 {
                let Some((result, _)) = tactic(current.clone())?.pull()? else {
                    break;
                };
                current = result;
                remaining -= 1;
            }
            Ok(Some((current, empty_seq())))
        }))
    })
}

pub fn repeat_determ(tactic: Tactic) -> Tactic {
    repeat_determ_n(-1, tactic)
}

pub fn repeat_determ1(tactic: Tactic) -> Tactic {
    then_tac(determ(tactic.clone()), repeat_determ(tactic))
}

pub fn changed(tactic: Tactic) -> Tactic {
    Rc::new(move |state: Thm| {
        let original = state.clone();
        Ok(filter_seq(
            move |result| Ok(!eq_thm(&original, result)),
            tactic(state)?,
        ))
    })
}

pub fn changed_prop(tactic: Tactic) -> Tactic {
    Rc::new(move |state: Thm| {
        let original = state.clone();
        Ok(filter_seq(
            move |result| Ok(!eq_thm_prop(&original, result)),
            tactic(state)?,
        ))
    })
}

pub fn all_goals(tactic: GoalTactic) -> Tactic {
    fn doall(tactic: &GoalTactic, index: i32) -> Tactic {
        if index == 0 {
            all_tac()
        } else {
            then_tac(tactic(index), doall(tactic, index - 1))
        }
    }
    Rc::new(move |state: Thm| doall(&tactic, nprems(&state) as i32)(state))
}

pub fn first_goal_tac(tactic: GoalTactic) -> Tactic {
    fn find(tactic: &GoalTactic, count: i32, index: i32) -> Tactic {
        if index > count {
            no_tac()
        } else {
            or_else(tactic(index), find(tactic, count, index + 1))
        }
    }
    Rc::new(move |state: Thm| {
        let count = nprems(&state) as i32;
        find(&tactic, count, 1)(state)
    })
}

/// SUBGOAL: a tactic built from goal index of the state, failing if there is no such goal.
pub fn subgoal(build: impl Fn(&Term, i32) -> Res<Tactic> + 'static) -> GoalTactic {
    let build = Rc::new(build);
    Rc::new(move |index| {
        let build = build.clone();
        Rc::new(move |state: Thm| {
            if index < 1 || index > nprems(&state) as i32 {
                return Ok(empty_seq());
            }
            build(&prem_of(&state, index)?, index)?(state)
        })
    })
}

/// Seq.INTERVAL: applies tactic to goals last down to first.
fn interval(tactic: &GoalTactic, first_index: i32, last_index: i32) -> Tactic {
    if last_index < first_index {
        all_tac()
    } else {
        then_tac(
            tactic(last_index),
            interval(tactic, first_index, last_index - 1),
        )
    }
}

pub fn then_all_new(first: GoalTactic, second: GoalTactic) -> GoalTactic {
    Rc::new(move |index| {
        let first = first.clone();
        let second = second.clone();
        Rc::new(move |state: Thm| {
            let second = second.clone();
            let count = nprems(&state) as i32;
            then_tac(
                first(index),
                Rc::new(move |result: Thm| {
                    interval(&second, index, index + nprems(&result) as i32 - count)(result)
                }),
            )(state)
        })
    })
}

pub fn repeat_all_new(tactic: GoalTactic) -> GoalTactic {
    let repeated = tactic.clone();
    then_all_new(
        tactic,
        Rc::new(move |index| try_tac(repeat_all_new(repeated.clone())(index))),
    )
}

pub fn prim_seq(apply: impl Fn(Thm) -> Res<Seq<Thm>> + 'static) -> Tactic {
    Rc::new(move |state| match apply(state) {
        Err(error) if error.is(Exception::Thm) => Ok(empty_seq()),
        result => result,
    })
}

pub fn primitive(apply: impl Fn(Thm) -> Res<Thm> + 'static) -> Tactic {
    prim_seq(move |state| Ok(single_seq(apply(state)?)))
}

pub fn cond_tac(
    test: impl Fn(&Thm) -> bool + 'static,
    on_true: Tactic,
    on_false: Tactic,
) -> Tactic {
    Rc::new(move |state| {
        if test(&state) {
            on_true(state)
        } else {
            on_false(state)
        }
    })
}

/// What Search.DEPTH_FIRST's sequence shares.
struct DepthFirst {
    test: Rc<dyn Fn(&Thm) -> bool>,
    tactic: Tactic,
}

fn is_used(used: &List<Thm>, state: &Thm) -> bool {
    list_iter(used).any(|other| eq_thm(other, state))
}

fn depth(search: Rc<DepthFirst>, used: List<Thm>, stack: List<Seq<Thm>>) -> Res<Cell<Thm>> {
    let mut current = stack;
    while let Some(top) = current {
        let Some((state, rest)) = top.head.pull()? else {
            current = top.tail.clone();
            continue;
        };
        let rest = cons(rest, top.tail.clone());
        if (search.test)(&state) && !is_used(&used, &state) {
            let used = cons(state.clone(), used);
            let search = search.clone();
            return Ok(Some((
                state,
                make_seq(move || depth(search.clone(), used.clone(), rest.clone())),
            )));
        }
        current = cons((search.tactic)(state)?, rest);
    }
    Ok(None)
}

/// Search.DEPTH_FIRST: depth-first search for a state satisfying the test. The stack of
/// alternatives and the states already returned are lists, as in Isabelle, since the stack can grow
/// as deep as the search goes.
fn depth_first(test: impl Fn(&Thm) -> bool + 'static, tactic: Tactic) -> Tactic {
    let search = Rc::new(DepthFirst {
        test: Rc::new(test),
        tactic,
    });
    Rc::new(move |state| {
        let search = search.clone();
        Ok(make_seq(move || {
            depth(search.clone(), None, cons(single_seq(state.clone()), None))
        }))
    })
}

pub fn has_fewer_prems(count: i32) -> impl Fn(&Thm) -> bool + Clone + 'static {
    move |state| (nprems(state) as i32) < count
}

/// Search.DEPTH_SOLVE: depth-first search until no goals remain.
pub fn depth_solve(tactic: Tactic) -> Tactic {
    depth_first(has_fewer_prems(1), tactic)
}
