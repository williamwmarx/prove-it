//! The answers to the liveness checker's questions about a search's states, as `live.ts`'s
//! `createLiveOracle` gives them, computed for every state and step at once so that the
//! interpreter crosses into the engine once for all of them (DESIGN.md 5.1). Each answer is 1 for
//! true, 0 for false, or [`UNKNOWN`] where the engine stops, which the interpreter answers itself,
//! failing where TLC fails.

use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::{Arc, Mutex, PoisonError};

use tla_live::{Answers, Declined, Slot};
use tla_values::store::{FALSE, Outcome, TRUE};
use tla_values::{Id, NESTING_STACK_BYTES, Store};

use crate::compile::{DIAMETER_SLOT, LEVEL_SLOT, NEXT_LEVEL_SLOT};
use crate::context::{Atom, EnabledSteps, Split, SubscriptKey};
use crate::machine::{Eval, Machine, Printed, UNASSIGNED};

pub const UNKNOWN: u8 = 2;

/// The most answers an atom that reads TLCGet("diameter") takes, one per state or step for each
/// diameter: past them the interpreter answers it.
const MAXIMUM_DIAMETER_ANSWERS: usize = 1 << 26;

/// What PROVE_IT_LIVE_CHECK finds when ENABLED from the steps the search took differs from
/// ENABLED run.
pub const ENABLED_DIFFERS: &str = "ENABLED from the steps the search took differs from ENABLED run";

/// What PROVE_IT_LIVE_CHECK finds when an action the steps the search took answer, evaluated on a
/// step, differs.
pub const STEPS_DIFFER: &str = "an action the steps the search took answer differs from its run";

/// What PROVE_IT_LIVE_CHECK finds when a subscript's variables tell a step from the subscript's
/// values otherwise.
pub const SUBSCRIPT_DIFFERS: &str = "a subscript's variables on a step differ from its values";

/// The states of a search and its steps: those from state i between `edge_offsets[i]` and
/// `edge_offsets[i + 1]`, for the first `expanded` states, each labelled with the position of the
/// action that took it when the search took TLC's actions one by one.
pub struct LiveGraph<'g> {
    pub states: &'g [Id],
    pub width: usize,
    pub count: usize,
    pub expanded: usize,
    pub edge_offsets: &'g [u32],
    pub edges: &'g [u32],
    pub labels: Option<&'g [u32]>,
    /// Whether a state's steps are those TLC's ENABLED finds when it runs an action from it.
    pub is_enabled_exact: bool,
    /// Whether TLC's predicate evaluation of the next-state relation holds of every step, without
    /// failing: no walk took the shortcut, and no comparison of a value a walk assigned can fail.
    pub is_next_taken: bool,
    /// The expanded state whose next states failed, whose steps are only those the next-state
    /// relation took before it failed: ENABLED is evaluated on it, not answered from them.
    pub partial: Option<usize>,
    /// Each step's bits of the action atoms made of pieces of Next whose pieces the walks that took
    /// it passed through, where the search recorded them, and how many bytes a step's are.
    pub pieces: Option<(&'g [u8], usize)>,
    /// The level TLC gives each state, where an atom reads TLCGet("level"): 1 for an initial
    /// state, else one past its parent's.
    pub levels: Option<&'g [u32]>,
    /// By atom, the answers on the first states from an earlier check of the same states, of each
    /// state predicate that answers a state the same in every check, which a check takes and
    /// extends.
    pub known: Option<&'g Mutex<Vec<Option<Vec<u8>>>>>,
    /// Whether no two of the states are equal and no comparison of two values of a variable can
    /// fail: a step then changes a tuple of every variable just where it reaches another state.
    pub is_distinct: bool,
}

/// How a step is told to leave a subscript unchanged: by the subscript's value on each of its
/// states, by the values of the state variables it is a tuple of, or, where it is a tuple of every
/// variable and equal states are one state, by whether the step reaches another state.
#[derive(Clone, Copy)]
enum Subscript<'a> {
    Value(&'a Eval),
    Slots(&'a [u32]),
    State,
}

impl<'a> Subscript<'a> {
    fn of(graph: &LiveGraph<'_>, eval: &'a Eval, slots: Option<&'a [u32]>) -> Subscript<'a> {
        match slots {
            Some(slots)
                if graph.is_distinct
                    && (0..graph.width as u32).all(|slot| slots.contains(&slot)) =>
            {
                Subscript::State
            }
            Some(slots) => Subscript::Slots(slots),
            None => Subscript::Value(eval),
        }
    }
}

// Whether a step leaves the variables of the slots unchanged, as TLC's `equals` of the two tuples
// finds: v' with v, element by element, up to the first pair that differs or fails to compare.
fn are_slots_unchanged(
    store: &mut Store,
    graph: &LiveGraph<'_>,
    slots: &[u32],
    index: usize,
    next: usize,
) -> Outcome<bool> {
    let before = &graph.states[index * graph.width..(index + 1) * graph.width];
    let after = &graph.states[next * graph.width..(next + 1) * graph.width];
    for &slot in slots {
        let (after, before) = (after[slot as usize], before[slot as usize]);
        if after != before || store.comparison_can_fail(after) {
            return store.equals(after, before);
        }
    }
    Ok(true)
}

/// What the steps the search took answer of an action atom on each step whose subscript changed:
/// true of every step where the action is Next or all of TLC's actions, or of the steps the
/// actions it splits into took, or a walk through its pieces took.
enum Taken {
    All,
    Steps(Vec<bool>),
}

/// Which of the steps the search took an action atom's split or pieces mark as the action's: all
/// of them where the action is Next or all of TLC's actions, the steps labelled with one of the
/// actions it splits into, or the steps a walk through its pieces took; or none it can tell.
#[derive(Clone, Copy)]
enum Marks<'a> {
    Unknown,
    All,
    Labels {
        actions: &'a [bool],
        labels: &'a [u32],
    },
    Pieces {
        pieces: &'a [u8],
        width: usize,
        byte: usize,
        mask: u8,
    },
}

impl<'a> Marks<'a> {
    fn of(
        graph: &LiveGraph<'a>,
        is_next: bool,
        split: Option<&'a Split>,
        piece: Option<u32>,
    ) -> Marks<'a> {
        if !graph.is_next_taken {
            return Marks::Unknown;
        }
        if is_next || matches!(split, Some(Split::All)) {
            return Marks::All;
        }
        match (split, graph.labels, piece, graph.pieces) {
            (Some(Split::Some(actions)), Some(labels), _, _) => Marks::Labels { actions, labels },
            (_, _, Some(bit), Some((pieces, width))) => Marks::Pieces {
                pieces,
                width,
                byte: bit as usize / 8,
                mask: 1 << (bit % 8),
            },
            _ => Marks::Unknown,
        }
    }

    /// The successors the marked steps from a state reach, sorted into `marked`: TLC evaluates
    /// the action once for each successor, so it holds of every step to a successor one marked
    /// step reaches.
    fn successors(&self, graph: &LiveGraph<'_>, index: usize, marked: &mut Vec<u32>) {
        let steps = graph.edge_offsets[index] as usize..graph.edge_offsets[index + 1] as usize;
        marked.clear();
        // A loop for each kind of mark, read once a step; where every step is marked or none can
        // be told, `taken` reads no successors.
        match *self {
            Marks::Unknown | Marks::All => return,
            Marks::Labels { actions, labels } => marked.extend(
                steps
                    .filter(|&edge| actions.get(labels[edge] as usize).copied().unwrap_or(false))
                    .map(|edge| graph.edges[edge]),
            ),
            Marks::Pieces {
                pieces,
                width,
                byte,
                mask,
            } => marked.extend(
                steps
                    .filter(|&edge| pieces[edge * width + byte] & mask != 0)
                    .map(|edge| graph.edges[edge]),
            ),
        }
        marked.sort_unstable();
    }

    /// Whether the steps answer the action on a step from the state, given its `successors`.
    fn taken(&self, graph: &LiveGraph<'_>, edge: usize, marked: &[u32]) -> Option<bool> {
        match self {
            Marks::Unknown => None,
            Marks::All => Some(true),
            _ => Some(marked.binary_search(&graph.edges[edge]).is_ok()),
        }
    }
}

impl Taken {
    fn of(
        graph: &LiveGraph<'_>,
        is_next: bool,
        split: Option<&Split>,
        piece: Option<u32>,
        threads: usize,
    ) -> Option<Taken> {
        match Marks::of(graph, is_next, split, piece) {
            Marks::Unknown => None,
            Marks::All => Some(Taken::All),
            marks => Some(Self::of_steps(graph, marks, threads)),
        }
    }

    // Each state's steps are read on their own, so the states are split between the threads,
    // each writing the answers of its states' steps.
    fn of_steps(graph: &LiveGraph<'_>, marks: Marks<'_>, threads: usize) -> Taken {
        let mut answers = vec![false; graph.edges.len()];
        let of_states = |states: std::ops::Range<usize>, answers: &mut [bool]| {
            let first = graph.edge_offsets[states.start] as usize;
            let mut marked = Vec::new();
            for index in states {
                marks.successors(graph, index, &mut marked);
                if marked.is_empty() {
                    continue;
                }
                let steps =
                    graph.edge_offsets[index] as usize..graph.edge_offsets[index + 1] as usize;
                for edge in steps {
                    answers[edge - first] = marked.binary_search(&graph.edges[edge]).is_ok();
                }
            }
        };
        let ends = split_states(graph.expanded, |_| 1, threads);
        if ends.len() < 2 {
            of_states(0..graph.expanded, &mut answers);
            return Taken::Steps(answers);
        }
        std::thread::scope(|scope| {
            let mut rest = &mut answers[..];
            let mut start = 0;
            for &end in &ends {
                let first = graph.edge_offsets[start] as usize;
                let last = graph.edge_offsets[end] as usize;
                let (own, left) = rest.split_at_mut(last - first);
                rest = left;
                let of_states = &of_states;
                scope.spawn(move || of_states(start..end, own));
                start = end;
            }
        });
        Taken::Steps(answers)
    }

    fn at(&self, edge: usize) -> bool {
        match self {
            Taken::All => true,
            Taken::Steps(answers) => answers[edge],
        }
    }
}

/// An action atom the helpers answer with the others of its subscript: its action, its subscript,
/// what marks the steps its split or pieces take, and the ENABLED of its fairness on each state,
/// where the checker asks about no step from a state where that is false.
struct Member<'a> {
    action: &'a Eval,
    subscript: Option<Subscript<'a>>,
    marks: Marks<'a>,
    disabled: Option<&'a [u8]>,
}

/// The answers to one atom: for a state predicate or ENABLED, one per state; for an action, one
/// per step, then one per state for its stuttering step.
pub struct Table {
    pub answers: Vec<u8>,
    /// For ENABLED, whether the steps the search took answer it.
    pub is_from_steps: bool,
    /// Why the engine doesn't answer the atom at all, if it doesn't.
    pub unknown: Option<String>,
    /// What evaluating the atom printed, by position, in the order of the positions.
    pub prints: Vec<(usize, Vec<Printed>)>,
}

impl Table {
    /// What evaluating the atom at the position printed.
    pub fn printed(&self, position: usize) -> &[Printed] {
        self.prints
            .binary_search_by_key(&position, |printed| printed.0)
            .map_or(&[], |found| &self.prints[found].1)
    }
}

// Keeps what the evaluation at the position printed.
fn keep_printed(
    machine: &mut Machine<'_>,
    prints: &mut Vec<(usize, Vec<Printed>)>,
    position: usize,
) {
    if !machine.output.is_empty() {
        prints.push((position, std::mem::take(&mut machine.output)));
    }
}

fn answer(value: Outcome<Id>) -> u8 {
    match value {
        Ok(TRUE) => 1,
        Ok(FALSE) => 0,
        _ => UNKNOWN,
    }
}

struct Evaluator<'m, 'p, 'g> {
    machine: &'m mut Machine<'p>,
    graph: &'g LiveGraph<'g>,
    unassigned: Vec<Id>,
    // The epoch each state is current under, 0 until it first is: a state keeps one epoch for the
    // whole of the answers, so what its steps evaluate of it is cached across them.
    epochs: Vec<u64>,
    current: Option<usize>,
    // Under PROVE_IT_LIVE_CHECK, whether a subscript's variables told a step otherwise than its
    // values, which are then compared too.
    is_checked: bool,
    differs: bool,
}

impl Evaluator<'_, '_, '_> {
    fn set_current(&mut self, index: usize) {
        if self.current == Some(index) {
            return;
        }
        if self.epochs[index] == 0 {
            self.epochs[index] = self.machine.next_epoch();
        }
        let graph = self.graph;
        self.machine.set_current(
            &graph.states[index * graph.width..(index + 1) * graph.width],
            self.epochs[index],
        );
        self.current = Some(index);
    }

    // An atom that reads TLCGet("level") on a state at a level, and the next state's on a step,
    // under an epoch of its own, which caches nothing the level decides across them.
    fn at_level(
        &mut self,
        index: usize,
        next: Option<usize>,
        levels: (u32, u32),
        eval: &Eval,
    ) -> u8 {
        let graph = self.graph;
        let epoch = self.machine.next_epoch();
        self.machine.set_current(
            &graph.states[index * graph.width..(index + 1) * graph.width],
            epoch,
        );
        self.current = None;
        match next {
            Some(next) => self
                .machine
                .set_next(&graph.states[next * graph.width..(next + 1) * graph.width]),
            None => self.machine.set_next(&self.unassigned),
        }
        let (Ok(level), Ok(next_level)) = (
            self.machine.store.int(i64::from(levels.0)),
            self.machine.store.int(i64::from(levels.1)),
        ) else {
            return UNKNOWN;
        };
        self.machine.set_slot(LEVEL_SLOT, level);
        self.machine.set_slot(NEXT_LEVEL_SLOT, next_level);
        answer(eval(self.machine))
    }

    fn evaluate_state(&mut self, index: usize, eval: &Eval) -> u8 {
        self.set_current(index);
        self.machine.set_next(&self.unassigned);
        answer(eval(self.machine))
    }

    // A subscript's value on each state, evaluated once each.
    fn subscript_value(
        &mut self,
        values: &mut [Id],
        subscript: &Eval,
        index: usize,
    ) -> Outcome<Id> {
        if values[index] != UNASSIGNED {
            return Ok(values[index]);
        }
        self.set_current(index);
        self.machine.set_next(&self.unassigned);
        let value = subscript(self.machine)?;
        values[index] = value;
        Ok(value)
    }

    // UNCHANGED v of a step, evaluating v' before v as the compiled UNCHANGED does.
    fn is_unchanged(
        &mut self,
        values: &mut [Id],
        subscript: Subscript<'_>,
        index: usize,
        next: usize,
    ) -> Outcome<bool> {
        match subscript {
            Subscript::State => Ok(index == next),
            Subscript::Slots(slots) => {
                are_slots_unchanged(&mut self.machine.store, self.graph, slots, index, next)
            }
            Subscript::Value(subscript) => {
                let after = self.subscript_value(values, subscript, next)?;
                let before = self.subscript_value(values, subscript, index)?;
                self.machine.store.equals(after, before)
            }
        }
    }

    // `is_unchanged`, compared under PROVE_IT_LIVE_CHECK with what the subscript's values give.
    fn is_step_unchanged(
        &mut self,
        values: &mut [Id],
        (subscript, eval): (Subscript<'_>, &Eval),
        index: usize,
        next: usize,
    ) -> Outcome<bool> {
        let unchanged = self.is_unchanged(values, subscript, index, next);
        if self.is_checked && !matches!(subscript, Subscript::Value(_)) {
            let valued = self.is_unchanged(values, Subscript::Value(eval), index, next);
            self.differs |= valued.ok() != unchanged.as_ref().ok().copied();
        }
        unchanged
    }

    // An action on a step, false where the subscript's value is unchanged, and else what the steps
    // the search took answer of it (`taken`), where they do.
    fn action(
        &mut self,
        values: &mut [Id],
        action: &Eval,
        subscript: Option<(Subscript<'_>, &Eval)>,
        index: usize,
        next: usize,
        taken: Option<bool>,
    ) -> u8 {
        if let Some(subscript) = subscript {
            match self.is_step_unchanged(values, subscript, index, next) {
                Ok(true) => return 0,
                Ok(false) => {}
                Err(_) => return UNKNOWN,
            }
        }
        if let Some(taken) = taken {
            return u8::from(taken);
        }
        self.set_current(index);
        let graph = self.graph;
        self.machine
            .set_next(&graph.states[next * graph.width..(next + 1) * graph.width]);
        answer(action(self.machine))
    }

    // The actions, as bits of `words` words for each expanded state, that took a step from the
    // state changing the subscript, and the states where the subscript failed on a step, which
    // `enabled_from_steps` scans instead. A step of an action already found isn't evaluated.
    fn changed_actions(
        &mut self,
        values: &mut [Id],
        subscript: (Subscript<'_>, &Eval),
        words: usize,
    ) -> (Vec<u64>, Vec<bool>) {
        let graph = self.graph;
        let mut changed = vec![0; graph.expanded * words];
        let mut failed = vec![false; graph.expanded];
        for (index, is_failed) in failed.iter_mut().enumerate() {
            let start = graph.edge_offsets[index] as usize;
            let end = graph.edge_offsets[index + 1] as usize;
            for edge in start..end {
                let label = graph.labels.map_or(0, |labels| labels[edge] as usize);
                let (word, bit) = (index * words + label / 64, 1 << (label % 64));
                if changed[word] & bit != 0 {
                    continue;
                }
                match self.is_step_unchanged(values, subscript, index, graph.edges[edge] as usize) {
                    Ok(false) => changed[word] |= bit,
                    Ok(true) => {}
                    Err(_) => *is_failed = true,
                }
            }
        }
        (changed, failed)
    }

    // Whether a step from the state that the steps' actions take changes the subscript, scanning
    // the steps in the order generated.
    fn enabled_from_steps(&mut self, values: &mut [Id], steps: &EnabledSteps, index: usize) -> u8 {
        let graph = self.graph;
        let subscript = Subscript::of(graph, &steps.subscript, steps.slots.as_deref());
        let start = graph.edge_offsets[index] as usize;
        let end = graph.edge_offsets[index + 1] as usize;
        for edge in start..end {
            if let (Some(actions), Some(labels)) = (&steps.actions, graph.labels)
                && !actions.get(labels[edge] as usize).copied().unwrap_or(false)
            {
                continue;
            }
            match self.is_unchanged(values, subscript, index, graph.edges[edge] as usize) {
                Ok(false) => return 1,
                Ok(true) => {}
                Err(_) => return UNKNOWN,
            }
        }
        0
    }
}

// A run of states a helper answers, from `start` on, each current under an epoch of the helper's,
// so that what the state's steps evaluate of it is cached across them.
struct Run<'m, 'p, 'g> {
    machine: &'m mut Machine<'p>,
    graph: &'g LiveGraph<'g>,
    start: usize,
    epochs: Vec<u64>,
    unassigned: Vec<Id>,
    // A subscript's value on each state the helper evaluated it on, in the helper's store, once
    // it evaluates one.
    subscripts: Vec<Id>,
    // The successors a state's marked steps reach, for the action atom being answered.
    marked: Vec<u32>,
}

impl Run<'_, '_, '_> {
    fn set_current(&mut self, index: usize) {
        // A state past the run, the target of a step, is current under an epoch of its own.
        let epoch = match self.epochs.get_mut(index.wrapping_sub(self.start)) {
            Some(epoch) => {
                if *epoch == 0 {
                    *epoch = self.machine.next_epoch();
                }
                *epoch
            }
            None => self.machine.next_epoch(),
        };
        let graph = self.graph;
        self.machine.set_current(
            &graph.states[index * graph.width..(index + 1) * graph.width],
            epoch,
        );
    }

    fn subscript_value(&mut self, subscript: &Eval, index: usize) -> Outcome<Id> {
        if self.subscripts.is_empty() {
            self.subscripts.resize(self.graph.count, UNASSIGNED);
        }
        if self.subscripts[index] != UNASSIGNED {
            return Ok(self.subscripts[index]);
        }
        self.set_current(index);
        self.machine.set_next(&self.unassigned);
        let value = subscript(self.machine)?;
        self.subscripts[index] = value;
        Ok(value)
    }

    // UNCHANGED v of a step: `Evaluator::is_unchanged` on a helper.
    fn is_unchanged(
        &mut self,
        subscript: Subscript<'_>,
        index: usize,
        next: usize,
    ) -> Outcome<bool> {
        match subscript {
            Subscript::State => Ok(index == next),
            Subscript::Slots(slots) => {
                are_slots_unchanged(&mut self.machine.store, self.graph, slots, index, next)
            }
            Subscript::Value(subscript) => {
                let after = self.subscript_value(subscript, next)?;
                let before = self.subscript_value(subscript, index)?;
                self.machine.store.equals(after, before)
            }
        }
    }

    fn state(&mut self, index: usize, eval: &Eval) -> u8 {
        self.set_current(index);
        self.machine.set_next(&self.unassigned);
        answer(eval(self.machine))
    }

    // An action on a step, false where the subscript's value is unchanged, and else what the steps
    // the search took answer of it, where they do. Only the states asked
    // about have their subscript evaluated, as on one thread, and an evaluation that fails leaves
    // the step unknown on either.
    fn action(
        &mut self,
        action: &Eval,
        subscript: Option<Subscript<'_>>,
        index: usize,
        next: usize,
        taken: Option<bool>,
    ) -> u8 {
        if let Some(subscript) = subscript {
            match self.is_unchanged(subscript, index, next) {
                Ok(true) => return 0,
                Ok(false) => {}
                Err(_) => return UNKNOWN,
            }
        }
        if let Some(taken) = taken {
            return u8::from(taken);
        }
        self.set_current(index);
        let graph = self.graph;
        self.machine
            .set_next(&graph.states[next * graph.width..(next + 1) * graph.width]);
        answer(action(self.machine))
    }

    // The actions that took a step from the state changing the subscript, as bits of `words`
    // words pushed to `changed`, and whether the subscript failed on one of its steps, pushed to
    // `failed`: `Evaluator::changed_actions` for one state, on a helper.
    fn changed_actions(
        &mut self,
        subscript: Subscript<'_>,
        index: usize,
        words: usize,
        (changed, failed): &mut (Vec<u64>, Vec<bool>),
    ) {
        let graph = self.graph;
        let at = changed.len();
        changed.resize(at + words, 0);
        let mut is_failed = false;
        let start = graph.edge_offsets[index] as usize;
        let end = graph.edge_offsets[index + 1] as usize;
        for edge in start..end {
            let label = graph.labels.map_or(0, |labels| labels[edge] as usize);
            let (word, bit) = (at + label / 64, 1 << (label % 64));
            if changed[word] & bit != 0 {
                continue;
            }
            match self.is_unchanged(subscript, index, graph.edges[edge] as usize) {
                Ok(false) => changed[word] |= bit,
                Ok(true) => {}
                Err(_) => is_failed = true,
            }
        }
        failed.push(is_failed);
    }
}

// Where the first `count` states split into `threads` runs of about the same `weight`: the end of
// each run, the last of them `count`.
fn split_states(count: usize, weight: impl Fn(usize) -> usize, threads: usize) -> Vec<usize> {
    let total: usize = (0..count).map(&weight).sum();
    let share = total.div_ceil(threads.max(1)).max(1);
    let mut ends = Vec::with_capacity(threads);
    let mut sum = 0;
    for index in 0..count {
        sum += weight(index);
        if sum >= share * (ends.len() + 1) {
            ends.push(index + 1);
        }
    }
    ends.resize(threads.max(1), count);
    ends
}

// What `answer` gives for each of the first `count` states, on the helpers: each answers a run of
// the states, of about the same `weight`, on the store of the machine that answers the rest, into
// answers of its own, which come back in the runs' order. Each evaluation is the same on any
// thread, since none prints, draws or reads what the search keeps. Each helper's overlay copies
// the store's values, as each thread of a parallel search does.
fn on_helpers<T: Default + Send>(
    machine: &mut Machine<'_>,
    helpers: &mut [Machine<'_>],
    graph: &LiveGraph<'_>,
    count: usize,
    weight: impl Fn(usize) -> usize,
    answer: impl Fn(&mut Run<'_, '_, '_>, usize, &mut T) + Sync,
) -> Vec<T> {
    let ends = split_states(count, weight, helpers.len());
    let store = Arc::new(std::mem::take(&mut machine.store));
    // The values of the definitions TLC computed once at startup, which may have drawn or printed:
    // a helper reads them, as every evaluation after startup does, rather than computing them
    // again with its own generator.
    let onces = &machine.onces;
    let deep_onces = &machine.deep_onces;
    // Each helper writes files for the check this thread runs ([`tla_values::written`]).
    let journal = tla_values::written::current();
    let parts: Vec<T> = std::thread::scope(|scope| {
        let threads: Vec<_> = helpers
            .iter_mut()
            .zip(ends.iter().enumerate())
            .map(|(helper, (position, &end))| {
                let start = if position == 0 { 0 } else { ends[position - 1] };
                let (store, answer, journal) = (&store, &answer, &journal);
                std::thread::Builder::new()
                    .stack_size(NESTING_STACK_BYTES)
                    .spawn_scoped(scope, move || {
                        let _entered = journal.as_ref().map(tla_values::written::Journal::enter);
                        // What the helper cached in an earlier run may name values of the
                        // overlay it lays again, or ids the store has given since.
                        helper.forget_from(0);
                        helper.onces.clone_from(onces);
                        helper.deep_onces.clone_from(deep_onces);
                        helper.store.attach(store.clone());
                        let mut run = Run {
                            machine: helper,
                            graph,
                            start,
                            epochs: vec![0; end - start],
                            unassigned: vec![UNASSIGNED; graph.width],
                            subscripts: Vec::new(),
                            marked: Vec::new(),
                        };
                        let mut answers = T::default();
                        for index in start..end {
                            answer(&mut run, index, &mut answers);
                        }
                        run.machine.store.detach();
                        answers
                    })
                    .expect("a thread for the liveness checker's atoms")
            })
            .collect();
        threads
            .into_iter()
            .map(|thread| {
                thread
                    .join()
                    .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
            })
            .collect()
    });
    machine.store = Arc::into_inner(store).expect("the store, once the helpers let go of it");
    parts
}

/// A subscript's values on the states and, for each expanded state, the actions that took a step
/// changing it, as bits, unless it failed on one of the state's steps.
struct Changes {
    values: Vec<Id>,
    actions: Vec<u64>,
    failed: Vec<bool>,
}

/// Which atoms read TLCGet("diameter"), and the last diameter of a complete search, which they are
/// answered for each diameter up to.
pub struct Diameters<'d> {
    pub atoms: &'d [bool],
    pub last: Option<u32>,
}

/// The answers to every atom, or the reason PROVE_IT_LIVE_CHECK found the steps' answer to ENABLED
/// wrong. With helpers, the atoms that neither print nor read TLC's diameter are answered on them
/// too.
pub fn answer_atoms(
    machine: &mut Machine<'_>,
    graph: &LiveGraph<'_>,
    atoms: &[Atom],
    is_live_checked: bool,
    is_printing: bool,
    diameters: &Diameters<'_>,
    helpers: &mut [Machine<'_>],
) -> Result<Vec<Table>, &'static str> {
    let mut known = graph
        .known
        .map(|known| known.lock().unwrap_or_else(PoisonError::into_inner));
    let known: &mut [Option<Vec<u8>>] = match &mut known {
        Some(known) => known,
        None => &mut [],
    };
    let (diameter_atoms, last_diameter) = (diameters.atoms, diameters.last);
    let mut evaluator = Evaluator {
        machine,
        graph,
        unassigned: vec![UNASSIGNED; graph.width],
        epochs: vec![0; graph.count],
        current: None,
        is_checked: is_live_checked,
        differs: false,
    };
    let mut tables = Vec::with_capacity(atoms.len());
    // For each subscript the steps answer ENABLED with, its values on the states and the actions
    // that changed it from each, which atoms with the same subscript share.
    let mut changes: HashMap<SubscriptKey, Changes> = HashMap::new();
    // The tables of the action atoms answered on the helpers with an earlier one, by position.
    let mut pending: HashMap<usize, Table> = HashMap::new();
    let words = graph
        .labels
        .and_then(|labels| labels.iter().max())
        .map_or(1, |&last| last as usize / 64 + 1);
    let is_self_stepped = (0..graph.expanded).any(|index| {
        let start = graph.edge_offsets[index] as usize;
        let end = graph.edge_offsets[index + 1] as usize;
        graph.edges[start..end].contains(&(index as u32))
    });
    for (position, atom) in atoms.iter().enumerate() {
        if let Some(table) = pending.remove(&position) {
            tables.push(table);
            continue;
        }
        // An atom that reads TLCGet("diameter") is answered for each diameter from 1 to the last,
        // and left to the interpreter where the search isn't complete or the answers for every
        // diameter wouldn't fit in memory.
        let is_diameter_read = diameter_atoms.get(position) == Some(&true);
        let is_too_deep = last_diameter.is_some_and(|last| {
            (graph.edges.len() + graph.count).saturating_mul(last as usize)
                > MAXIMUM_DIAMETER_ANSWERS
        });
        if is_diameter_read && (last_diameter.is_none() || is_too_deep) {
            tables.push(Table {
                answers: Vec::new(),
                is_from_steps: false,
                unknown: Some("TLCGet(\"diameter\") as the search goes".into()),
                prints: Vec::new(),
            });
            continue;
        }
        // Atoms that print, draw or read TLC's diameter are answered here in TLC's order.
        let is_shared = helpers.len() > 1 && !is_printing && !is_diameter_read && !is_live_checked;
        let rounds = match last_diameter {
            Some(last) if is_diameter_read => 1..=last,
            _ => 0..=0,
        };
        let mut whole: Option<Table> = None;
        for diameter in rounds {
            if diameter > 0 {
                let value = evaluator
                    .machine
                    .store
                    .int(i64::from(diameter))
                    .map_err(|_| "a diameter the store doesn't hold")?;
                evaluator.machine.set_slot(DIAMETER_SLOT, value);
                evaluator.epochs.fill(0);
                evaluator.current = None;
            }
            let mut values = vec![UNASSIGNED; graph.count];
            let mut prints = Vec::new();
            let table = match atom {
                // TLC keeps the successor a step back to its state generated, one level past it, as
                // the stuttering step's state, which the checker doesn't tell apart.
                Atom::LevelState(_) | Atom::LevelAction { .. }
                    if graph.levels.is_none()
                        || is_printing
                        || is_diameter_read
                        || is_self_stepped =>
                {
                    Table {
                        answers: Vec::new(),
                        is_from_steps: false,
                        unknown: Some(
                            "TLCGet(\"level\") without the levels, or with a step to its state"
                                .into(),
                        ),
                        prints,
                    }
                }
                // TLC evaluates a state predicate at the level of the state it adds, and of each
                // successor it generated, one past its source's (`TLCGet`): the states, then the
                // states each step reached.
                Atom::LevelState(eval) => {
                    let levels = graph.levels.expect("the levels");
                    let mut answers: Vec<u8> = (0..graph.count)
                        .map(|index| {
                            let level = levels[index];
                            evaluator.at_level(index, None, (level, level + 1), eval)
                        })
                        .collect();
                    for (index, &level) in levels[..graph.expanded].iter().enumerate() {
                        let level = level + 1;
                        let start = graph.edge_offsets[index] as usize;
                        let end = graph.edge_offsets[index + 1] as usize;
                        for edge in start..end {
                            let next = graph.edges[edge] as usize;
                            answers.push(evaluator.at_level(next, None, (level, level + 1), eval));
                        }
                    }
                    Table {
                        answers,
                        is_from_steps: false,
                        unknown: None,
                        prints,
                    }
                }
                // An action at its step's first state's level, and the next state's one past it,
                // but for the stuttering step, whose next state is the first.
                Atom::LevelAction { action, subscript } => {
                    let levels = graph.levels.expect("the levels");
                    let mut answers = Vec::with_capacity(graph.edges.len() + graph.count);
                    let steps = (0..graph.expanded).flat_map(|index| {
                        let start = graph.edge_offsets[index] as usize;
                        let end = graph.edge_offsets[index + 1] as usize;
                        (start..end).map(move |edge| (index, graph.edges[edge] as usize))
                    });
                    let stutters = (0..graph.count).map(|index| (index, index));
                    for (index, next) in steps.chain(stutters) {
                        let level = levels[index];
                        let next_level = if index == next { level } else { level + 1 };
                        let is_unchanged = subscript.as_ref().map(|subscript| {
                            let subscript = Subscript::Value(subscript);
                            evaluator.is_unchanged(&mut values, subscript, index, next)
                        });
                        answers.push(match is_unchanged {
                            Some(Ok(true)) => 0,
                            Some(Err(_)) => UNKNOWN,
                            _ => evaluator.at_level(index, Some(next), (level, next_level), action),
                        });
                    }
                    Table {
                        answers,
                        is_from_steps: false,
                        unknown: None,
                        prints,
                    }
                }
                Atom::Unknown(reason) => Table {
                    answers: Vec::new(),
                    is_from_steps: false,
                    unknown: Some(reason.clone()),
                    prints,
                },
                Atom::State(eval) => {
                    let known = known.get_mut(position).and_then(Option::as_mut);
                    let from = known
                        .as_ref()
                        .map_or(0, |known| known.len().min(graph.count));
                    let mut answers = Vec::with_capacity(graph.count);
                    if let Some(known) = &known {
                        answers.extend_from_slice(&known[..from]);
                    }
                    if is_shared && from < graph.count {
                        let parts = on_helpers(
                            evaluator.machine,
                            helpers,
                            graph,
                            graph.count,
                            |index| usize::from(index >= from),
                            |run, index, answers: &mut Vec<u8>| {
                                if index >= from {
                                    answers.push(run.state(index, eval));
                                }
                            },
                        );
                        answers.extend(parts.concat());
                    } else if !is_shared {
                        answers.extend((from..graph.count).map(|index| {
                            let answer = evaluator.evaluate_state(index, eval);
                            keep_printed(evaluator.machine, &mut prints, index);
                            answer
                        }));
                    }
                    if let Some(known) = known {
                        known.clone_from(&answers);
                    }
                    Table {
                        answers,
                        is_from_steps: false,
                        unknown: None,
                        prints,
                    }
                }
                Atom::Action { key, .. } if is_shared => {
                    // This atom and the action atoms after it whose subscripts share its values,
                    // each with the ENABLED of its fairness answered already, in one pass of the
                    // helpers: a helper evaluates the subscript on each of its states once for
                    // them all, and marks the state's steps once for each.
                    let group: Vec<usize> = (position..atoms.len())
                        .filter(|&at| match &atoms[at] {
                            Atom::Action {
                                key: other,
                                enabled,
                                ..
                            } => {
                                at == position
                                    || other == key
                                        && enabled.is_none_or(|enabled| enabled < position)
                                        && diameter_atoms.get(at) != Some(&true)
                            }
                            _ => false,
                        })
                        .collect();
                    let members: Vec<Member<'_>> = group
                        .iter()
                        .map(|&at| {
                            let Atom::Action {
                                action,
                                subscript,
                                slots,
                                enabled,
                                is_next,
                                split,
                                piece,
                                ..
                            } = &atoms[at]
                            else {
                                unreachable!("an action atom of the group");
                            };
                            let disabled = enabled
                                .and_then(|position| tables.get(position))
                                .filter(|table: &&Table| table.answers.len() == graph.count)
                                .map(|table| &table.answers[..]);
                            Member {
                                action,
                                subscript: subscript
                                    .as_ref()
                                    .map(|eval| Subscript::of(graph, eval, slots.as_deref())),
                                marks: Marks::of(graph, *is_next, split.as_ref(), *piece),
                                disabled,
                            }
                        })
                        .collect();
                    let members = &members;
                    // A state's steps and its stuttering step in one run, so that the helper
                    // evaluates the subscript on the state once for them all.
                    let parts: Vec<Vec<(Vec<u8>, Vec<u8>)>> = on_helpers(
                        evaluator.machine,
                        helpers,
                        graph,
                        graph.count,
                        |index| {
                            graph
                                .edge_offsets
                                .get(index + 1)
                                .map_or(0, |&end| (end - graph.edge_offsets[index]) as usize)
                                + 1
                        },
                        |run, index, answers: &mut Vec<(Vec<u8>, Vec<u8>)>| {
                            if answers.is_empty() {
                                answers.resize_with(members.len(), Default::default);
                            }
                            for (member, (steps, stutters)) in
                                members.iter().zip(answers.iter_mut())
                            {
                                let Member {
                                    action,
                                    subscript,
                                    marks,
                                    disabled,
                                } = *member;
                                let is_asked = disabled.is_none_or(|answers| answers[index] != 0);
                                if index < graph.expanded {
                                    let start = graph.edge_offsets[index] as usize;
                                    let end = graph.edge_offsets[index + 1] as usize;
                                    if is_asked {
                                        marks.successors(graph, index, &mut run.marked);
                                    }
                                    for edge in start..end {
                                        steps.push(if is_asked {
                                            let next = graph.edges[edge] as usize;
                                            let taken = marks.taken(graph, edge, &run.marked);
                                            run.action(action, subscript, index, next, taken)
                                        } else {
                                            UNKNOWN
                                        });
                                    }
                                }
                                stutters.push(if is_asked {
                                    run.action(action, subscript, index, index, None)
                                } else {
                                    UNKNOWN
                                });
                            }
                        },
                    );
                    let mut own = None;
                    // A helper that had no states answered nothing.
                    for (member, &at) in group.iter().enumerate() {
                        let mut answers = Vec::with_capacity(graph.edges.len() + graph.count);
                        for part in parts.iter().filter_map(|part| part.get(member)) {
                            answers.extend_from_slice(&part.0);
                        }
                        for part in parts.iter().filter_map(|part| part.get(member)) {
                            answers.extend_from_slice(&part.1);
                        }
                        let table = Table {
                            answers,
                            is_from_steps: false,
                            unknown: None,
                            prints: Vec::new(),
                        };
                        if at == position {
                            own = Some(table);
                        } else {
                            pending.insert(at, table);
                        }
                    }
                    own.expect("the atom's own table")
                }
                Atom::Action {
                    action,
                    subscript,
                    slots,
                    enabled,
                    is_next,
                    split,
                    piece,
                    ..
                } => {
                    let subscript = subscript
                        .as_ref()
                        .map(|eval| (Subscript::of(graph, eval, slots.as_deref()), eval));
                    let taken = Taken::of(graph, *is_next, split.as_ref(), *piece, helpers.len());
                    // The checker asks about no step from a state where the ENABLED of the action's
                    // fairness is false, and the interpreter answers any it does; where the atom
                    // prints, it evaluates the action on every step TLC does.
                    let disabled = enabled
                        .filter(|_| !is_printing)
                        .and_then(|position| tables.get(position))
                        .filter(|table: &&Table| table.answers.len() == graph.count)
                        .map(|table| &table.answers);
                    let is_asked =
                        |index: usize| disabled.is_none_or(|answers| answers[index] != 0);
                    let mut answers = Vec::with_capacity(graph.edges.len() + graph.count);
                    for index in 0..graph.expanded {
                        let start = graph.edge_offsets[index] as usize;
                        let end = graph.edge_offsets[index + 1] as usize;
                        if !is_asked(index) {
                            answers.resize(answers.len() + end - start, UNKNOWN);
                            continue;
                        }
                        for edge in start..end {
                            let next = graph.edges[edge] as usize;
                            let is_taken = taken.as_ref().map(|taken| taken.at(edge));
                            let answer = evaluator.action(
                                &mut values,
                                action,
                                subscript,
                                index,
                                next,
                                is_taken,
                            );
                            if is_taken.is_some() && is_live_checked {
                                let run = evaluator.action(
                                    &mut values,
                                    action,
                                    subscript,
                                    index,
                                    next,
                                    None,
                                );
                                if run != UNKNOWN && run != answer {
                                    return Err(STEPS_DIFFER);
                                }
                            }
                            answers.push(answer);
                            keep_printed(evaluator.machine, &mut prints, edge);
                        }
                    }
                    for index in 0..graph.count {
                        answers.push(if is_asked(index) {
                            evaluator.action(&mut values, action, subscript, index, index, None)
                        } else {
                            UNKNOWN
                        });
                        keep_printed(evaluator.machine, &mut prints, graph.edges.len() + index);
                    }
                    Table {
                        answers,
                        is_from_steps: false,
                        unknown: None,
                        prints,
                    }
                }
                Atom::Enabled { run, steps } => {
                    // TLC's ENABLED walks what the shortcut evaluated, so only a search that took no
                    // shortcut past a walk found the successors ENABLED finds.
                    // Where it prints, TLC runs it on each state.
                    let steps = steps.as_ref().filter(|steps| {
                        !is_printing
                            && graph.is_enabled_exact
                            && (steps.actions.is_none() || graph.labels.is_some())
                    });
                    let mut changed = steps.map(|steps| {
                        let subscript =
                            Subscript::of(graph, &steps.subscript, steps.slots.as_deref());
                        changes.remove(&steps.key).unwrap_or_else(|| {
                            if is_shared {
                                // The helpers evaluate the subscript in overlays of their own, so
                                // its values stay unassigned here: a state whose subscript
                                // failed on a step, which `enabled_from_steps` scans, evaluates
                                // them again on this thread.
                                let parts: Vec<(Vec<u64>, Vec<bool>)> = on_helpers(
                                    evaluator.machine,
                                    helpers,
                                    graph,
                                    graph.expanded,
                                    |index| {
                                        (graph.edge_offsets[index + 1] - graph.edge_offsets[index])
                                            as usize
                                            + 1
                                    },
                                    |run, index, changed: &mut (Vec<u64>, Vec<bool>)| {
                                        run.changed_actions(subscript, index, words, changed);
                                    },
                                );
                                let mut actions = Vec::with_capacity(graph.expanded * words);
                                let mut failed = Vec::with_capacity(graph.expanded);
                                for (words, states) in parts {
                                    actions.extend(words);
                                    failed.extend(states);
                                }
                                return Changes {
                                    values: std::mem::take(&mut values),
                                    actions,
                                    failed,
                                };
                            }
                            let (actions, failed) = evaluator.changed_actions(
                                &mut values,
                                (subscript, &steps.subscript),
                                words,
                            );
                            Changes {
                                values: std::mem::take(&mut values),
                                actions,
                                failed,
                            }
                        })
                    });
                    // The actions A splits into, as bits, or all of them.
                    let mask: Vec<u64> = match steps.and_then(|steps| steps.actions.as_ref()) {
                        Some(actions) => (0..words)
                            .map(|word| {
                                (0..64)
                                    .filter(|bit| actions.get(word * 64 + bit) == Some(&true))
                                    .fold(0, |mask, bit| mask | 1 << bit)
                            })
                            .collect(),
                        None => vec![u64::MAX; words],
                    };
                    // What the steps answer of each state, UNKNOWN where ENABLED must run.
                    let mut answers: Vec<u8> = (0..graph.count)
                        .map(|index| match (steps, &mut changed) {
                            (Some(steps), Some(changed))
                                if index < graph.expanded && graph.partial != Some(index) =>
                            {
                                if changed.failed[index] {
                                    evaluator.enabled_from_steps(&mut changed.values, steps, index)
                                } else {
                                    let row = &changed.actions[index * words..(index + 1) * words];
                                    u8::from(
                                        row.iter().zip(&mask).any(|(row, mask)| row & mask != 0),
                                    )
                                }
                            }
                            _ => UNKNOWN,
                        })
                        .collect();
                    match run {
                        // ENABLED run on the states the steps don't answer, on the helpers, each
                        // state's evaluation the same on any thread.
                        Ok(eval) if is_shared && answers.contains(&UNKNOWN) => {
                            let asked = &answers;
                            let ran = on_helpers(
                                evaluator.machine,
                                helpers,
                                graph,
                                graph.count,
                                |index| usize::from(asked[index] == UNKNOWN),
                                |run, index, ran: &mut Vec<u8>| {
                                    ran.push(if asked[index] == UNKNOWN {
                                        run.state(index, eval)
                                    } else {
                                        UNKNOWN
                                    });
                                },
                            )
                            .concat();
                            for (answer, ran) in answers.iter_mut().zip(ran) {
                                if *answer == UNKNOWN {
                                    *answer = ran;
                                }
                            }
                        }
                        Ok(eval) if !is_shared => {
                            for (index, answer) in answers.iter_mut().enumerate() {
                                let from_steps = *answer;
                                let ran = if from_steps == UNKNOWN || is_live_checked {
                                    evaluator.evaluate_state(index, eval)
                                } else {
                                    UNKNOWN
                                };
                                keep_printed(evaluator.machine, &mut prints, index);
                                if from_steps != UNKNOWN && ran != UNKNOWN && from_steps != ran {
                                    return Err(ENABLED_DIFFERS);
                                }
                                if from_steps == UNKNOWN {
                                    *answer = ran;
                                }
                            }
                        }
                        _ => {}
                    }
                    if let (Some(steps), Some(changed)) = (steps, changed) {
                        changes.insert(steps.key, changed);
                    }
                    Table {
                        answers,
                        is_from_steps: steps.is_some(),
                        unknown: match (run, steps) {
                            (Err(reason), None) => Some(reason.clone()),
                            _ => None,
                        },
                        prints,
                    }
                }
            };
            whole = Some(match whole {
                None => table,
                Some(mut whole) => {
                    let offset = whole.answers.len();
                    whole.answers.extend(table.answers);
                    whole.prints.extend(
                        table
                            .prints
                            .into_iter()
                            .map(|(at, printed)| (at + offset, printed)),
                    );
                    whole
                }
            });
        }
        tables.push(whole.expect("an answer for each diameter"));
        if evaluator.differs {
            return Err(SUBSCRIPT_DIFFERS);
        }
    }
    Ok(tables)
}

/// The atoms' answers as TLC evaluates them while it searches: each evaluated when the checker
/// asks, on the machine as it is then, so an atom reads the registers the search has set and the
/// search those the atom sets.
pub struct LiveAnswers<'m, 'p, 'g> {
    pub machine: RefCell<&'m mut Machine<'p>>,
    pub atoms: &'g [Atom],
    /// The states found so far, `width` ids each, and the steps taken.
    pub states: &'g [Id],
    pub width: usize,
    pub edges: &'g [u32],
}

impl LiveAnswers<'_, '_, '_> {
    fn state(&self, index: u32) -> &[Id] {
        &self.states[index as usize * self.width..(index as usize + 1) * self.width]
    }

    // An atom of a state, with no next state.
    fn of_state(&self, index: u32, eval: &Eval) -> Outcome<Id> {
        let machine = &mut **self.machine.borrow_mut();
        let epoch = machine.next_epoch();
        machine.set_current(self.state(index), epoch);
        machine.set_next(&vec![UNASSIGNED; self.width]);
        eval(machine)
    }

    // `<<A>>_v` of a step as TLC's `LNAction#eval` evaluates it: v of each state, and A only
    // where they differ.
    fn of_step(
        &self,
        action: &Eval,
        subscript: Option<&Eval>,
        index: u32,
        next: u32,
    ) -> Outcome<Id> {
        if let Some(subscript) = subscript {
            let before = self.of_state(index, subscript)?;
            let after = self.of_state(next, subscript)?;
            if self.machine.borrow_mut().store.equals(before, after)? {
                return Ok(FALSE);
            }
        }
        let machine = &mut **self.machine.borrow_mut();
        let epoch = machine.next_epoch();
        machine.set_current(self.state(index), epoch);
        machine.set_next(self.state(next));
        action(machine)
    }
}

impl Answers for LiveAnswers<'_, '_, '_> {
    fn answer(&self, atom: u32, slot: Slot, _diameter: u32) -> Result<bool, Declined> {
        match self.evaluate(atom, slot)? {
            Ok(TRUE) => Ok(true),
            Ok(FALSE) => Ok(false),
            _ => Err(Declined::from(
                "a predicate the engine leaves to the interpreter",
            )),
        }
    }

    fn position(&self, _atom: u32, slot: Slot, _diameter: u32) -> usize {
        match slot {
            Slot::State(state) | Slot::Reached { state, .. } => state as usize,
            Slot::Step { edge, .. } => edge as usize,
            Slot::Stutter(state) => self.edges.len() + state as usize,
        }
    }
}

impl LiveAnswers<'_, '_, '_> {
    /// What evaluating the atom at the slot gives, or why the engine has no evaluation of it.
    pub fn evaluate(&self, atom: u32, slot: Slot) -> Result<Outcome<Id>, Declined> {
        Ok(match (self.atoms.get(atom as usize), slot) {
            (
                Some(Atom::State(eval) | Atom::Enabled { run: Ok(eval), .. }),
                Slot::State(index) | Slot::Reached { state: index, .. },
            ) => self.of_state(index, eval),
            (
                Some(Atom::Action {
                    action, subscript, ..
                }),
                Slot::Step { state, edge },
            ) => self.of_step(action, subscript.as_ref(), state, self.edges[edge as usize]),
            (
                Some(Atom::Action {
                    action, subscript, ..
                }),
                Slot::Stutter(state),
            ) => self.of_step(action, subscript.as_ref(), state, state),
            (
                Some(
                    Atom::Unknown(reason)
                    | Atom::Enabled {
                        run: Err(reason), ..
                    },
                ),
                _,
            ) => {
                return Err(Declined(reason.clone()));
            }
            _ => return Err(Declined::from("an atom the engine doesn't answer")),
        })
    }
}
