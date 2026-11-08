//! The answers to the liveness checker's questions about a search's states, as `live.ts`'s
//! `createLiveOracle` gives them, computed for every state and step at once so that the
//! interpreter crosses into the engine once for all of them (DESIGN.md 5.1). Each answer is 1 for
//! true, 0 for false, or [`UNKNOWN`] where the engine stops, which the interpreter answers itself,
//! failing where TLC fails.

use tla_values::Id;
use tla_values::store::{FALSE, Outcome, TRUE};

use crate::context::{Atom, EnabledSteps};
use crate::machine::{Eval, Machine, UNASSIGNED};

pub const UNKNOWN: u8 = 2;

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

/// The answers to every atom, or the reason PROVE_IT_LIVE_CHECK found the steps' answer to ENABLED
/// wrong.
pub fn answer_atoms(
    machine: &mut Machine<'_>,
    graph: &LiveGraph<'_>,
    atoms: &[Atom],
    is_live_checked: bool,
) -> Result<Vec<Table>, &'static str> {
    let mut evaluator = Evaluator {
        machine,
        graph,
        unassigned: vec![UNASSIGNED; graph.width],
        epochs: vec![0; graph.count],
        current: None,
    };
    let mut tables = Vec::with_capacity(atoms.len());
    for atom in atoms {
        let mut values = vec![UNASSIGNED; graph.count];
        let table = match atom {
            Atom::Unknown(reason) => Table {
                answers: Vec::new(),
                is_from_steps: false,
                unknown: Some(reason.clone()),
            },
            Atom::State(eval) => Table {
                answers: (0..graph.count)
                    .map(|index| evaluator.evaluate_state(index, eval))
                    .collect(),
                is_from_steps: false,
                unknown: None,
            },
            Atom::Action {
                action,
                subscript,
                enabled,
            } => {
                // The checker asks about no step from a state where the ENABLED of the action's
                // fairness is false, and the interpreter answers any it does.
                let disabled = enabled
                    .and_then(|position| tables.get(position))
                    .filter(|table: &&Table| table.answers.len() == graph.count)
                    .map(|table| &table.answers);
                let is_asked = |index: usize| disabled.is_none_or(|answers| answers[index] != 0);
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
                    }
                }
                for index in 0..graph.count {
                    answers.push(if is_asked(index) {
                        evaluator.action(&mut values, action, subscript.as_ref(), index, index)
                    } else {
                        UNKNOWN
                    });
                }
                Table {
                    answers,
                    is_from_steps: false,
                    unknown: None,
                }
            }
            Atom::Enabled { run, steps } => {
                // TLC's ENABLED walks what the shortcut evaluated, so only a search that took no
                // shortcut past a walk found the successors ENABLED finds.
                let steps = steps.as_ref().filter(|steps| {
                    graph.is_enabled_exact && (steps.actions.is_none() || graph.labels.is_some())
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
                }
            }
        };
        tables.push(table);
    }
    Ok(tables)
}
