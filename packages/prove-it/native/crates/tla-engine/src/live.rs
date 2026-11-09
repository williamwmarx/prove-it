//! The answers to the liveness checker's questions about a search's states, as `live.ts`'s
//! `createLiveOracle` gives them, computed for every state and step at once so that the
//! interpreter crosses into the engine once for all of them (DESIGN.md 5.1). Each answer is 1 for
//! true, 0 for false, or [`UNKNOWN`] where the engine stops, which the interpreter answers itself,
//! failing where TLC fails.

use std::sync::Arc;

use tla_values::store::{FALSE, Outcome, TRUE};
use tla_values::{Id, NESTING_STACK_BYTES};

use crate::compile::DIAMETER_SLOT;
use crate::context::{Atom, EnabledSteps};
use crate::machine::{Eval, Machine, Printed, UNASSIGNED};

pub const UNKNOWN: u8 = 2;

/// The most answers an atom that reads TLCGet("diameter") takes, one per state or step for each
/// diameter: past them the interpreter answers it.
const MAXIMUM_DIAMETER_ANSWERS: usize = 1 << 26;

/// What PROVE_IT_LIVE_CHECK finds when ENABLED from the steps the search took differs from
/// ENABLED run.
pub const ENABLED_DIFFERS: &str = "ENABLED from the steps the search took differs from ENABLED run";

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
        subscript: &Eval,
        index: usize,
        next: usize,
    ) -> Outcome<bool> {
        let after = self.subscript_value(values, subscript, next)?;
        let before = self.subscript_value(values, subscript, index)?;
        self.machine.store.equals(after, before)
    }

    fn action(
        &mut self,
        values: &mut [Id],
        action: &Eval,
        subscript: Option<&Eval>,
        index: usize,
        next: usize,
    ) -> u8 {
        if let Some(subscript) = subscript {
            match self.is_unchanged(values, subscript, index, next) {
                Ok(true) => return 0,
                Ok(false) => {}
                Err(_) => return UNKNOWN,
            }
        }
        self.set_current(index);
        let graph = self.graph;
        self.machine
            .set_next(&graph.states[next * graph.width..(next + 1) * graph.width]);
        answer(action(self.machine))
    }

    // Whether a step from the state that the steps' actions take changes the subscript, scanning
    // the steps in the order generated.
    fn enabled_from_steps(&mut self, values: &mut [Id], steps: &EnabledSteps, index: usize) -> u8 {
        let graph = self.graph;
        let start = graph.edge_offsets[index] as usize;
        let end = graph.edge_offsets[index + 1] as usize;
        for edge in start..end {
            if let (Some(actions), Some(labels)) = (&steps.actions, graph.labels)
                && !actions.get(labels[edge] as usize).copied().unwrap_or(false)
            {
                continue;
            }
            match self.is_unchanged(values, &steps.subscript, index, graph.edges[edge] as usize) {
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
}

impl Run<'_, '_, '_> {
    fn set_current(&mut self, index: usize) {
        let epoch = &mut self.epochs[index - self.start];
        if *epoch == 0 {
            *epoch = self.machine.next_epoch();
        }
        let graph = self.graph;
        self.machine.set_current(
            &graph.states[index * graph.width..(index + 1) * graph.width],
            *epoch,
        );
    }

    fn state(&mut self, index: usize, eval: &Eval) -> u8 {
        self.set_current(index);
        self.machine.set_next(&self.unassigned);
        answer(eval(self.machine))
    }

    // An action on a step, false where the subscript's value, `values` of each state where it
    // has one, is unchanged.
    fn action(
        &mut self,
        action: &Eval,
        values: Option<&[Option<Id>]>,
        index: usize,
        next: usize,
    ) -> u8 {
        if let Some(values) = values {
            let (Some(after), Some(before)) = (values[next], values[index]) else {
                return UNKNOWN;
            };
            match self.machine.store.equals(after, before) {
                Ok(true) => return 0,
                Ok(false) => {}
                Err(_) => return UNKNOWN,
            }
        }
        self.set_current(index);
        let graph = self.graph;
        self.machine
            .set_next(&graph.states[next * graph.width..(next + 1) * graph.width]);
        answer(action(self.machine))
    }
}

// The answers `answer` gives for each of the first `count` states, on the helpers: each answers a
// run of the states, of about the same `weight`, on the store of the machine that answers the
// rest, and the runs' answers follow one another in the states' order. Each evaluation is the
// same on any thread, since none prints, draws or reads what the search keeps. Each helper's
// overlay copies the store's values, as each thread of a parallel search does.
fn on_helpers(
    machine: &mut Machine<'_>,
    helpers: &mut [Machine<'_>],
    graph: &LiveGraph<'_>,
    count: usize,
    weight: impl Fn(usize) -> usize,
    answer: impl Fn(&mut Run<'_, '_, '_>, usize, &mut Vec<u8>) + Sync,
) -> Vec<u8> {
    let total: usize = (0..count).map(&weight).sum();
    let share = total.div_ceil(helpers.len()).max(1);
    let mut ends = Vec::with_capacity(helpers.len());
    let mut sum = 0;
    for index in 0..count {
        sum += weight(index);
        if sum >= share * (ends.len() + 1) {
            ends.push(index + 1);
        }
    }
    ends.resize(helpers.len(), count);
    let store = Arc::new(std::mem::take(&mut machine.store));
    let parts: Vec<Vec<u8>> = std::thread::scope(|scope| {
        let threads: Vec<_> = helpers
            .iter_mut()
            .zip(ends.iter().enumerate())
            .map(|(helper, (position, &end))| {
                let start = if position == 0 { 0 } else { ends[position - 1] };
                let (store, answer) = (&store, &answer);
                std::thread::Builder::new()
                    .stack_size(NESTING_STACK_BYTES)
                    .spawn_scoped(scope, move || {
                        helper.store.attach(store.clone());
                        let mut run = Run {
                            machine: helper,
                            graph,
                            start,
                            epochs: vec![0; end - start],
                            unassigned: vec![UNASSIGNED; graph.width],
                        };
                        let mut answers = Vec::new();
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
    parts.concat()
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
    let (diameter_atoms, last_diameter) = (diameters.atoms, diameters.last);
    let mut evaluator = Evaluator {
        machine,
        graph,
        unassigned: vec![UNASSIGNED; graph.width],
        epochs: vec![0; graph.count],
        current: None,
    };
    let mut tables = Vec::with_capacity(atoms.len());
    for (position, atom) in atoms.iter().enumerate() {
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
                Atom::Unknown(reason) => Table {
                    answers: Vec::new(),
                    is_from_steps: false,
                    unknown: Some(reason.clone()),
                    prints,
                },
                Atom::State(eval) if is_shared => Table {
                    answers: on_helpers(
                        evaluator.machine,
                        helpers,
                        graph,
                        graph.count,
                        |_| 1,
                        |run, index, answers| answers.push(run.state(index, eval)),
                    ),
                    is_from_steps: false,
                    unknown: None,
                    prints,
                },
                Atom::State(eval) => Table {
                    answers: (0..graph.count)
                        .map(|index| {
                            let answer = evaluator.evaluate_state(index, eval);
                            keep_printed(evaluator.machine, &mut prints, index);
                            answer
                        })
                        .collect(),
                    is_from_steps: false,
                    unknown: None,
                    prints,
                },
                Atom::Action {
                    action,
                    subscript,
                    enabled,
                } if is_shared => {
                    let disabled = enabled
                        .and_then(|position| tables.get(position))
                        .filter(|table: &&Table| table.answers.len() == graph.count)
                        .map(|table| &table.answers[..]);
                    let is_asked =
                        |index: usize| disabled.is_none_or(|answers| answers[index] != 0);
                    // Each state's subscript value, found on this thread, which the helpers compare.
                    let values: Option<Vec<Option<Id>>> = subscript.as_ref().map(|subscript| {
                        (0..graph.count)
                            .map(|index| {
                                evaluator
                                    .subscript_value(&mut values, subscript, index)
                                    .ok()
                            })
                            .collect()
                    });
                    let values = values.as_deref();
                    let steps = on_helpers(
                        evaluator.machine,
                        helpers,
                        graph,
                        graph.expanded,
                        |index| {
                            (graph.edge_offsets[index + 1] - graph.edge_offsets[index]) as usize
                        },
                        |run, index, answers| {
                            let start = graph.edge_offsets[index] as usize;
                            let end = graph.edge_offsets[index + 1] as usize;
                            for edge in start..end {
                                answers.push(if is_asked(index) {
                                    run.action(action, values, index, graph.edges[edge] as usize)
                                } else {
                                    UNKNOWN
                                });
                            }
                        },
                    );
                    let stutters = on_helpers(
                        evaluator.machine,
                        helpers,
                        graph,
                        graph.count,
                        |_| 1,
                        |run, index, answers| {
                            answers.push(if is_asked(index) {
                                run.action(action, values, index, index)
                            } else {
                                UNKNOWN
                            });
                        },
                    );
                    Table {
                        answers: [steps, stutters].concat(),
                        is_from_steps: false,
                        unknown: None,
                        prints,
                    }
                }
                Atom::Action {
                    action,
                    subscript,
                    enabled,
                } => {
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
                            answers.push(evaluator.action(
                                &mut values,
                                action,
                                subscript.as_ref(),
                                index,
                                next,
                            ));
                            keep_printed(evaluator.machine, &mut prints, edge);
                        }
                    }
                    for index in 0..graph.count {
                        answers.push(if is_asked(index) {
                            evaluator.action(&mut values, action, subscript.as_ref(), index, index)
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
                    let mut answers = Vec::with_capacity(graph.count);
                    for index in 0..graph.count {
                        let from_steps = match steps {
                            Some(steps) if index < graph.expanded => {
                                evaluator.enabled_from_steps(&mut values, steps, index)
                            }
                            _ => UNKNOWN,
                        };
                        let ran = match run {
                            Ok(eval) if from_steps == UNKNOWN || is_live_checked => {
                                evaluator.evaluate_state(index, eval)
                            }
                            _ => UNKNOWN,
                        };
                        keep_printed(evaluator.machine, &mut prints, index);
                        if from_steps != UNKNOWN && ran != UNKNOWN && from_steps != ran {
                            return Err(ENABLED_DIFFERS);
                        }
                        answers.push(if from_steps == UNKNOWN {
                            ran
                        } else {
                            from_steps
                        });
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
    }
    Ok(tables)
}
