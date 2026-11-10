//! Ported from Isabelle2025's Pure/search.ML, iterative deepening and best-first search.
//! Copyright (c) 1986-2025 University of Cambridge, Technische Universitaet Muenchen, and
//! contributors, see LICENSE.

use std::cmp::Ordering;
use std::rc::Rc;

use crate::error::Res;

use super::seq::{list_of_seq, make_seq, seq_of_list};
use super::tactical::{GoalTactic, Tactic, eq_thm, has_fewer_prems, no_tac, or_else};
use super::term_ord::term_ord;
use super::thm::Thm;

/// DEEPEN: tries the tactic with limits from start up to limit in steps of increment.
pub fn deepen(
    increment: i32,
    limit: i32,
    tactic: Rc<dyn Fn(i32) -> GoalTactic>,
    start: i32,
) -> GoalTactic {
    Rc::new(move |index| {
        let tactic = tactic.clone();
        Rc::new(move |state: Thm| {
            if has_fewer_prems(index)(&state) || start > limit {
                return no_tac()(state);
            }
            or_else(
                tactic(start)(index),
                deepen(increment, limit, tactic.clone(), start + increment)(index),
            )(state)
        })
    })
}

struct Sized {
    size: usize,
    thm: Thm,
}

/// Thm_Heap's order: by size, then by proposition.
fn compare_sized(left: &Sized, right: &Sized) -> Ordering {
    left.size
        .cmp(&right.size)
        .then_with(|| term_ord(&left.thm.prop, &right.thm.prop))
}

/// BEST_FIRST: searches the states the tactic produces, smallest first, for one that satisfies
/// the predicate. A sorted list stands in for Thm_Heap: both yield the least state under the same
/// total order.
pub fn best_first(
    is_satisfied: impl Fn(&Thm) -> bool + 'static,
    size: impl Fn(&Thm) -> usize + 'static,
    tactic: Tactic,
) -> Tactic {
    let search = Rc::new(move |state: &Thm| -> Res<Option<Vec<Thm>>> {
        let insert = |mut heap: Vec<Sized>, thm: Thm| {
            let entry = Sized {
                size: size(&thm),
                thm,
            };
            match heap
                .iter()
                .position(|other| compare_sized(&entry, other) == Ordering::Less)
            {
                None => heap.push(entry),
                Some(position) => heap.insert(position, entry),
            }
            heap
        };
        let mut news = vec![state.clone()];
        let mut heap: Vec<Sized> = Vec::new();
        loop {
            let satisfied: Vec<Thm> = news
                .iter()
                .filter(|news| is_satisfied(news))
                .cloned()
                .collect();
            if !satisfied.is_empty() {
                return Ok(Some(satisfied));
            }
            let mut next = news.into_iter().rev().fold(heap, insert);
            if next.is_empty() {
                return Ok(None);
            }
            let best = next.remove(0).thm;
            let first_other = next.iter().position(|entry| !eq_thm(&best, &entry.thm));
            news = list_of_seq(&tactic(best)?)?;
            heap = match first_other {
                None => Vec::new(),
                Some(position) => next.split_off(position),
            };
        }
    });
    Rc::new(move |state: Thm| {
        let search = search.clone();
        Ok(make_seq(move || match search(&state)? {
            None => Ok(None),
            Some(results) => seq_of_list(results).pull(),
        }))
    })
}
