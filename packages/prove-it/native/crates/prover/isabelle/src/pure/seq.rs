//! Ported from Isabelle2025's Pure/General/seq.ML. Copyright (c) 1986-2025 University of
//! Cambridge, Technische Universitaet Muenchen, and contributors, see LICENSE.
//!
//! Lazy sequences (`pure/seq.ts`). As in Isabelle, pulling a sequence twice computes its head
//! twice. A pull may raise (an Interrupt, or a tactic's exception), so it returns a `Res`.
//!
//! A sequence is one closure that returns a `Step`: either its first cell, or another sequence
//! that it hands over to where Isabelle would pull that sequence in tail position. Pulling follows
//! the hand-overs in a loop, so a long run of empty alternatives, which Poly/ML's growing stack
//! absorbs, doesn't exhaust this one. `make_seq`'s closures always return a cell; `defer_seq`'s may
//! hand over, as the TypeScript's `DeferredSeq`.

use std::rc::Rc;

use crate::error::Res;

/// The first item and the rest, or `None` for the empty sequence.
pub type Cell<T> = Option<(T, Seq<T>)>;

pub enum Step<T> {
    Cell(Cell<T>),
    Seq(Seq<T>),
}

pub struct Seq<T>(Rc<dyn Fn() -> Res<Step<T>>>);

impl<T> Clone for Seq<T> {
    fn clone(&self) -> Self {
        Seq(self.0.clone())
    }
}

impl<T: Clone + 'static> Seq<T> {
    pub fn pull(&self) -> Res<Cell<T>> {
        let mut step = (self.0)()?;
        loop {
            match step {
                Step::Cell(cell) => return Ok(cell),
                Step::Seq(seq) => step = (seq.0)()?,
            }
        }
    }
}

pub fn make_seq<T: 'static>(pull: impl Fn() -> Res<Cell<T>> + 'static) -> Seq<T> {
    Seq(Rc::new(move || pull().map(Step::Cell)))
}

pub fn defer_seq<T: 'static>(step: impl Fn() -> Res<Step<T>> + 'static) -> Seq<T> {
    Seq(Rc::new(step))
}

pub fn empty_seq<T: 'static>() -> Seq<T> {
    make_seq(|| Ok(None))
}

pub fn cons_seq<T: Clone + 'static>(item: T, rest: Seq<T>) -> Seq<T> {
    make_seq(move || Ok(Some((item.clone(), rest.clone()))))
}

pub fn single_seq<T: Clone + 'static>(item: T) -> Seq<T> {
    cons_seq(item, empty_seq())
}

pub fn of_cell<T: Clone + 'static>(cell: Cell<T>) -> Seq<T> {
    make_seq(move || Ok(cell.clone()))
}

pub fn seq_of_list<T: Clone + 'static>(items: Vec<T>) -> Seq<T> {
    items
        .into_iter()
        .rev()
        .fold(empty_seq(), |rest, item| cons_seq(item, rest))
}

pub fn seq_head<T: Clone + 'static>(seq: &Seq<T>) -> Res<Option<T>> {
    Ok(seq.pull()?.map(|(item, _)| item))
}

/// Seq.chop: the first count elements and the rest of the sequence.
pub fn chop_seq<T: Clone + 'static>(count: usize, seq: &Seq<T>) -> Res<(Vec<T>, Seq<T>)> {
    let mut items = Vec::new();
    let mut current = seq.clone();
    while items.len() < count {
        let Some((item, rest)) = current.pull()? else {
            return Ok((items, current));
        };
        items.push(item);
        current = rest;
    }
    Ok((items, current))
}

pub fn list_of_seq<T: Clone + 'static>(seq: &Seq<T>) -> Res<Vec<T>> {
    let mut items = Vec::new();
    let mut cell = seq.pull()?;
    while let Some((item, rest)) = cell {
        items.push(item);
        cell = rest.pull()?;
    }
    Ok(items)
}

pub fn append_seq<T: Clone + 'static>(first: Seq<T>, second: Seq<T>) -> Seq<T> {
    defer_seq(move || {
        Ok(match first.pull()? {
            None => Step::Seq(second.clone()),
            Some((item, rest)) => Step::Cell(Some((item, append_seq(rest, second.clone())))),
        })
    })
}

pub fn mapp_seq<T: Clone + 'static, R: Clone + 'static>(
    map: impl Fn(T) -> Res<R> + 'static,
    first: Seq<T>,
    second: Seq<R>,
) -> Seq<R> {
    fn copy<T: Clone + 'static, R: Clone + 'static>(
        map: Rc<dyn Fn(T) -> Res<R>>,
        current: Seq<T>,
        second: Seq<R>,
    ) -> Seq<R> {
        defer_seq(move || {
            Ok(match current.pull()? {
                None => Step::Seq(second.clone()),
                Some((item, rest)) => {
                    Step::Cell(Some((map(item)?, copy(map.clone(), rest, second.clone()))))
                }
            })
        })
    }
    copy(Rc::new(map), first, second)
}

pub fn filter_seq<T: Clone + 'static>(
    predicate: impl Fn(&T) -> Res<bool> + 'static,
    seq: Seq<T>,
) -> Seq<T> {
    fn copy<T: Clone + 'static>(predicate: Rc<dyn Fn(&T) -> Res<bool>>, current: Seq<T>) -> Seq<T> {
        make_seq(move || {
            let mut cell = current.pull()?;
            while let Some((item, rest)) = &cell {
                if predicate(item)? {
                    break;
                }
                cell = rest.pull()?;
            }
            Ok(cell.map(|(item, rest)| (item, copy(predicate.clone(), rest))))
        })
    }
    copy(Rc::new(predicate), seq)
}

pub fn flat_seq<T: Clone + 'static>(seqs: Seq<Seq<T>>) -> Seq<T> {
    maps_seq(Ok, seqs)
}

pub fn map_seq<T: Clone + 'static, R: Clone + 'static>(
    map: impl Fn(T) -> Res<R> + 'static,
    seq: Seq<T>,
) -> Seq<R> {
    fn go<T: Clone + 'static, R: Clone + 'static>(
        map: Rc<dyn Fn(T) -> Res<R>>,
        seq: Seq<T>,
    ) -> Seq<R> {
        make_seq(move || {
            Ok(match seq.pull()? {
                None => None,
                Some((item, rest)) => Some((map(item)?, go(map.clone(), rest))),
            })
        })
    }
    go(Rc::new(map), seq)
}

pub fn maps_seq<T: Clone + 'static, R: Clone + 'static>(
    map: impl Fn(T) -> Res<Seq<R>> + 'static,
    seq: Seq<T>,
) -> Seq<R> {
    fn go<T: Clone + 'static, R: Clone + 'static>(
        map: Rc<dyn Fn(T) -> Res<Seq<R>>>,
        seq: Seq<T>,
    ) -> Seq<R> {
        defer_seq(move || {
            Ok(match seq.pull()? {
                None => Step::Cell(None),
                Some((item, rest)) => Step::Seq(append_seq(map(item)?, go(map.clone(), rest))),
            })
        })
    }
    go(Rc::new(map), seq)
}

/// Seq.it_right: accumulates lazily from the right.
pub fn it_right_seq<T: Clone + 'static, R: Clone + 'static>(
    combine: impl Fn(T, Seq<R>) -> Res<Seq<R>> + 'static,
    seq: Seq<T>,
    tail: Seq<R>,
) -> Seq<R> {
    fn its<T: Clone + 'static, R: Clone + 'static>(
        combine: Rc<dyn Fn(T, Seq<R>) -> Res<Seq<R>>>,
        current: Seq<T>,
        tail: Seq<R>,
    ) -> Seq<R> {
        defer_seq(move || {
            Ok(match current.pull()? {
                None => Step::Seq(tail.clone()),
                Some((item, rest)) => {
                    Step::Seq(combine(item, its(combine.clone(), rest, tail.clone()))?)
                }
            })
        })
    }
    its(Rc::new(combine), seq, tail)
}
