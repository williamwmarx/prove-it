//! TLC's recovery of a trace (`TLCTrace.getTrace`, `Tool.getState`): the first state is the first
//! initial state, in TLC's order, that is the search's first state; each next state is the first
//! successor of the previous one, by the step's action, that is the search's next state. TLC
//! fingerprints each state it recovers, which sorts its records, and so does the search with each
//! state it keeps, so every state but the last prints sorted. The last state of a violation is
//! one the search didn't keep, and TLC fingerprinted it only if it satisfies the constraints.

use tla_ir::{AtomKind, Ir, NodeId};
use tla_values::fingerprint::Fingerprints;
use tla_values::random::JavaRandom;
use tla_values::{Id, Store};

use crate::eval::{Context, Evaluator, Registers};
use std::rc::Rc;

use crate::value::{
    Evaluated, Text, Value, compare, equals, from_store, matches, permute, settle, settle_built,
    settle_deep, settle_normalized,
};
use crate::{Ending, Trace, TraceState, Unsupported};

/// Rebuilds traces of one model.
pub struct Rebuilder<'ir> {
    evaluator: Evaluator<'ir>,
    key: Key,
    /// The state of the generator TLC's startup left, which the initial predicate draws from.
    startup_random: u64,
    /// The state of the generator where an invariant of the trace's last state stopped the
    /// search, where the caller gave it.
    violation_random: Option<u64>,
    /// TLC's set of fingerprints when the search stopped, sorted, where the caller gave it.
    pub(crate) fingerprints: Option<Vec<u64>>,
}

/// How TLC tells a candidate is the state it looks for: by its fingerprint, which is of the state,
/// of its VIEW, or of the least state in its orbit under SYMMETRY.
enum Key {
    State,
    /// The body of the VIEW's definition.
    View(NodeId),
    /// The permutations of the symmetry group, as the model values each one renames.
    Symmetry(Vec<Vec<(Rc<Text>, Rc<Text>)>>),
    /// The VIEW of the least state of the orbit.
    ViewOfSymmetry(NodeId, Vec<Vec<(Rc<Text>, Rc<Text>)>>),
}

fn unsupported<T>(reason: impl Into<String>) -> Result<T, Unsupported> {
    Err(Unsupported(reason.into()))
}

impl<'ir> Rebuilder<'ir> {
    /// Whether TLC computes the definition at this index of the IR's definitions as it starts,
    /// as `Evaluator::is_precomputed` says.
    pub fn is_precomputed(&mut self, definition: u32) -> bool {
        let node = self.evaluator.ir.definitions[definition as usize];
        self.evaluator.is_precomputed(node)
    }

    pub(crate) fn evaluator(&mut self) -> &mut Evaluator<'ir> {
        &mut self.evaluator
    }

    pub fn new(ir: &'ir Ir) -> Result<Rebuilder<'ir>, Unsupported> {
        let model = &ir.model;
        let evaluator = Evaluator::new(ir);
        let view = match &model.view {
            Some(view) => match view.definition {
                Some(index) => Some(evaluator.definition(ir.definitions[index as usize]).body),
                None => return unsupported("a VIEW without a definition"),
            },
            None => None,
        };
        let key = match view {
            Some(view) => Key::View(view),
            None => Key::State,
        };
        Ok(Rebuilder {
            evaluator,
            key,
            startup_random: JavaRandom::seeded(ir.model.random_seed).state(),
            violation_random: None,
            fingerprints: None,
        })
    }

    /// Takes TLC's set of fingerprints when the search stopped at an invariant that fails to
    /// evaluate, sorted (`Violation::fingerprints`), which TLC's replay of the expansion tests
    /// each successor against.
    pub fn set_fingerprints(&mut self, fingerprints: &[u64]) {
        self.fingerprints = Some(fingerprints.to_vec());
    }

    /// Whether TLC fingerprints the state itself, with no VIEW or SYMMETRY.
    pub(crate) fn is_keyed_by_state(&self) -> bool {
        matches!(self.key, Key::State)
    }

    /// Takes the values the search computed at startup, ids of `store`, which TLC's trace reads
    /// as it computed them, and the state of the generator the startup left.
    pub fn set_startup(
        &mut self,
        store: &Store,
        values: &[Id],
        random: u64,
    ) -> Result<(), Unsupported> {
        self.evaluator.set_startup(store, values)?;
        self.startup_random = random;
        Ok(())
    }

    /// Takes the state of the generator where an invariant of the trace's last state stopped the
    /// search (`Violation::random`), which TLC goes on drawing from as it finds that state again.
    pub fn set_violation_random(&mut self, random: u64) {
        self.violation_random = Some(random);
    }

    /// Takes TLC's registers as the search left them, which TLC's trace reads and sets again as
    /// TLC rebuilds it.
    pub fn set_registers(&mut self, registers: Registers) {
        self.evaluator.registers = registers;
    }

    /// What a state of a rebuilt lasso, or its step to the next, answers of the liveness checker's
    /// atom at `atom` (`evaluateLive`), as TLC's `Liveness.findViolatedProperties` asks it: a
    /// state predicate or ENABLED of the state, an action of the step, false where the step leaves
    /// the action's subscript unchanged.
    pub fn answer_atom(
        &mut self,
        atom: u32,
        state: &[Value],
        next: &[Value],
    ) -> Result<bool, Unsupported> {
        let evaluator = &mut self.evaluator;
        let Some(atom) = evaluator.ir.model.atoms.get(atom as usize) else {
            return unsupported("an atom the checker asks nothing of");
        };
        let context = run(evaluator.scope_context(atom.scope))?;
        let values = |values: &[Value]| values.iter().cloned().map(Some).collect();
        evaluator.printed.clear();
        evaluator.current = values(state);
        evaluator.next = vec![None; state.len()];
        match &atom.kind {
            AtomKind::State => run(evaluator.boolean(atom.expression, &context)),
            AtomKind::Enabled { .. } => Ok(matches!(
                run(evaluator.enabled(atom.expression, &context))?,
                Value::Bool(true)
            )),
            AtomKind::Action { unchanged, .. } => {
                evaluator.next = values(next);
                if let Some(unchanged) = unchanged
                    && run(evaluator.boolean(*unchanged, &context))?
                {
                    return Ok(false);
                }
                run(evaluator.boolean(atom.expression, &context))
            }
        }
    }

    /// Takes how many workers TLC runs, which TLCGet("config") reads.
    pub fn set_workers(&mut self, workers: usize) {
        self.evaluator.workers = Some(workers);
    }

    /// Takes the symmetry group the search reduced by, each permutation as the names of the model
    /// values it moves, each with its image's.
    pub fn set_symmetry(&mut self, group: &[Vec<(Vec<u16>, Vec<u16>)>]) {
        let text = |units: &[u16]| self.evaluator.text_of(units.into());
        let group = group
            .iter()
            .map(|permutation| {
                permutation
                    .iter()
                    .map(|(name, image)| (text(name), text(image)))
                    .collect()
            })
            .collect();
        self.key = match &self.key {
            Key::View(view) | Key::ViewOfSymmetry(view, _) => Key::ViewOfSymmetry(*view, group),
            Key::State | Key::Symmetry(_) => Key::Symmetry(group),
        };
    }

    /// The states of a path the search found, as TLC prints them. `states` holds each state's
    /// values as ids of `store`, in the IR's order of the variables; `actions[i]` is the position
    /// in the model's actions of the step from `states[i]` to `states[i + 1]` (`label_path`), or
    /// `None` to try each action in turn, as `Tool.getState` does. A step to the same state is a
    /// stuttering step. `ending` says what the last state is to TLC.
    pub fn rebuild(
        &mut self,
        store: &Store,
        states: &[&[Id]],
        actions: &[Option<u32>],
        ending: Ending,
    ) -> Result<Trace, Unsupported> {
        self.rebuild_checked(store, states, actions, ending, true)
    }

    /// `rebuild`, with TLC's checks of a violating state outside the model replayed only when
    /// `is_checked`: a failure replays the check that failed itself.
    pub(crate) fn rebuild_checked(
        &mut self,
        store: &Store,
        states: &[&[Id]],
        actions: &[Option<u32>],
        ending: Ending,
        is_checked: bool,
    ) -> Result<Trace, Unsupported> {
        let Some(first) = self.rebuild_pass(store, states, actions, ending, is_checked, true)?
        else {
            return Ok(Trace {
                states: Vec::new(),
                trace_output: Vec::new(),
            });
        };
        // TLC rebuilds a violation's trace once more after it has printed it, for the
        // counterexample its postconditions read: the spec prints again, as the registers then
        // are, and sets them again.
        let ir = self.evaluator.ir;
        let is_effectful = ir.builtins.iter().any(|builtin| {
            matches!(
                &*ir.texts[builtin.name as usize],
                "Print" | "PrintT" | "TLCSet"
            )
        });
        let again = if !matches!(ending, Ending::Lasso) && first.rebuilt.len() > 1 && is_effectful {
            // TLC's second rebuild resets the generator with the thread's current state set, so
            // it draws from a seed this rebuild doesn't follow: what it prints or sets then isn't
            // followed.
            let is_drawing = ir.builtins.iter().any(|builtin| {
                matches!(
                    &*ir.texts[builtin.name as usize],
                    "RandomElement" | "RandomSubset"
                )
            });
            let registers = format!("{:?}", self.evaluator.registers);
            let output: Option<Vec<Vec<String>>> = self
                .rebuild_pass(store, states, actions, ending, false, false)?
                .map(|pass| {
                    pass.initial_output
                        .into_iter()
                        .chain(pass.outputs.into_iter().flatten())
                        .collect()
                });
            let is_effective = output.as_ref().is_some_and(|output| !output.is_empty())
                || format!("{:?}", self.evaluator.registers) != registers;
            if is_drawing && is_effective {
                return Err(Unsupported(
                    "the second rebuild of a trace of a spec that draws at random".into(),
                ));
            }
            output
        } else {
            None
        };
        Ok(compose(first, again, ending))
    }

    // One rebuild of the path, with what the spec printed finding the first state and each step.
    fn rebuild_pass(
        &mut self,
        store: &Store,
        states: &[&[Id]],
        actions: &[Option<u32>],
        ending: Ending,
        is_checked: bool,
        is_first: bool,
    ) -> Result<Option<Pass>, Unsupported> {
        let evaluator = &mut self.evaluator;
        let ir = evaluator.ir;
        let width = ir.variables.len();
        if states.iter().any(|state| state.len() != width) {
            return unsupported("a state of another width than the model's");
        }
        let Some(&first) = states.first() else {
            return Ok(None);
        };
        // What the spec prints depends on every state TLC enumerates, so where it prints, each
        // walk runs to its end, and each step tries TLC's actions in order, as `findStepAction`
        // does; elsewhere a walk stops at the state it looks for.
        let is_drawing = ir.builtins.iter().any(|builtin| {
            matches!(
                &*ir.texts[builtin.name as usize],
                "RandomElement" | "RandomSubset"
            )
        });
        // A random draw depends on every draw before it in the expansion, as what the spec prints
        // and the registers it sets do.
        let is_printing = is_drawing
            || ir.builtins.iter().any(|builtin| {
                matches!(
                    &*ir.texts[builtin.name as usize],
                    "Print" | "PrintT" | "TLCSet"
                )
            });
        // TLC's worker seeds the draws of each expansion with the fingerprint of the state it
        // expands, which is of the state itself where TLC fingerprints no other key.
        let order: Vec<usize> = ir.tlc_order.iter().map(|&index| index as usize).collect();
        let mut fingerprints = Fingerprints::new();
        let mut seeded = |state: &[Id]| -> Result<Option<JavaRandom>, Unsupported> {
            if !is_drawing || !matches!(self.key, Key::State) {
                return Ok(None);
            }
            match fingerprints.get_state(store, state, &order) {
                Ok(fingerprint) => Ok(Some(JavaRandom::seeded(fingerprint ^ ir.model.random_seed))),
                Err(bail) => unsupported(bail.0),
            }
        };
        evaluator.printed.clear();
        let mut rebuilt: Vec<Vec<Value>> = Vec::with_capacity(states.len());
        let context = run(evaluator.scope_context(ir.model.scope))?;
        evaluator.level = 0;
        evaluator.current = vec![None; width];
        // TLC prints a violating state as it found it, not as it recovers a state, so it is the
        // candidate equal to the search's, whatever the VIEW or SYMMETRY.
        let is_held = matches!(ending, Ending::Violation);
        // TLC's first rebuild of a violation's trace of two states prints the initial state as it
        // holds it (`printTrace`), so the walk of the initial predicate sets no register of TLC's.
        let is_initial_held = is_first && is_held && states.len() == 2;
        let key_of = |position: usize| {
            if is_held && position + 1 == states.len() {
                &Key::State
            } else {
                &self.key
            }
        };
        // The search's initial states draw from the generator startup left. TLC rebuilds the
        // initial state of a trace from the seed instead (`TLCTrace.getTrace` resets the
        // generator, and a lasso's prefix is rebuilt on a thread of its own): where startup drew,
        // a drawing initial predicate finds no initial state, and TLC fails. It holds the initial
        // state of a violation of two states and of a trace of one state, which it doesn't rebuild.
        let is_initial_rebuilt = is_first
            && match ending {
                Ending::Violation => states.len() > 2,
                Ending::Kept => states.len() > 1,
                Ending::Lasso => true,
            };
        evaluator.random = is_drawing.then(|| {
            if is_initial_rebuilt {
                JavaRandom::seeded(ir.model.random_seed)
            } else {
                JavaRandom::from_state(self.startup_random)
            }
        });
        let violation_random = self
            .violation_random
            .filter(|_| matches!(self.key, Key::State));
        let registers = evaluator.registers.clone();
        let initial = find(
            evaluator,
            key_of(0),
            (ir.model.init, &context, true),
            is_printing,
            store,
            first,
        )?;
        if is_initial_held {
            evaluator.registers = registers;
        }
        let Some(initial) = initial else {
            if is_initial_rebuilt && is_drawing {
                return unsupported(
                    "a trace whose initial state TLC fails to rebuild from the generator it resets",
                );
            }
            return unsupported("no initial state is the trace's first");
        };
        let initial_output = std::mem::take(&mut evaluator.printed);
        let mut outputs: Vec<Vec<Vec<String>>> = vec![Vec::new()];
        rebuilt.push(initial);
        // Each candidate action, with its position in the model's actions: the next-state
        // relation, which is none of them, when the IR has none.
        let Some(next) = ir.model.next else {
            return unsupported("a trace of a model without a next-state relation");
        };
        let all_actions: Vec<(NodeId, Option<u32>, Option<u32>)> = if ir.model.actions.is_empty() {
            vec![(next, ir.model.scope, None)]
        } else {
            ir.model
                .actions
                .iter()
                .enumerate()
                .map(|(index, action)| (action.expression, action.scope, Some(index as u32)))
                .collect()
        };
        let mut steps: Vec<Option<u32>> = vec![None];
        for (position, pair) in states.windows(2).enumerate() {
            // TLC recovers a state, and so fingerprints it, before it takes its step.
            settle_recovered(evaluator, &self.key, &rebuilt[position])?;
            let previous = rebuilt[position].clone();
            if pair[0] == pair[1] {
                rebuilt.push(previous);
                outputs.push(Vec::new());
                steps.push(None);
                continue;
            }
            evaluator.current = previous.into_iter().map(Some).collect();
            evaluator.level = position as i32 + 1;
            // TLC finds the successor of an initial state it holds by its worker's generator as
            // the search left it, still seeded for that state (`TLCTrace.printTrace`,
            // `Tool.getState`, `TLCStateRandom.initialize`): where the search drew, the walk may
            // find no such successor, and TLC fails.
            evaluator.random = if is_initial_held {
                violation_random.map(JavaRandom::from_state)
            } else {
                seeded(pair[0])?
            };
            let candidates = match actions.get(position).copied().flatten() {
                Some(index) if !is_printing => match ir.model.actions.get(index as usize) {
                    Some(action) => vec![(action.expression, action.scope, Some(index))],
                    None => return unsupported("an action the model doesn't have"),
                },
                _ => all_actions.clone(),
            };
            let mut found = None;
            let mut step = None;
            for (expression, scope, index) in candidates {
                let context = run(evaluator.scope_context(scope))?;
                evaluator.next = vec![None; width];
                found = find(
                    evaluator,
                    key_of(position + 1),
                    (expression, &context, false),
                    is_printing,
                    store,
                    pair[1],
                )?;
                if found.is_some() {
                    step = index;
                    break;
                }
            }
            let Some(state) = found else {
                if is_initial_held && is_drawing && violation_random.is_some() {
                    return unsupported(
                        "a violating successor TLC fails to find again from its generator",
                    );
                }
                return unsupported(format!(
                    "no step from state {} is the trace's next",
                    position + 1
                ));
            };
            rebuilt.push(state);
            outputs.push(std::mem::take(&mut evaluator.printed));
            steps.push(step);
        }
        // The draws of the checks after the expansion follow those of the steps TLC tried, which
        // the rebuild doesn't take.
        evaluator.random = None;
        let last = &rebuilt[rebuilt.len() - 1];
        let is_reducing = !matches!(self.key, Key::State);
        if is_held && is_reducing {
            // TLC finds the violating state among the successors by equality, which sorts it.
            last.iter().for_each(settle_deep);
        } else {
            // TLC's rebuild evaluates neither the constraints nor the invariants
            // (`Tool.getState`): what these checks set of its registers is undone.
            let registers = evaluator.registers.clone();
            if is_in_model(evaluator, &rebuilt)? {
                settle_recovered(evaluator, &self.key, &rebuilt[rebuilt.len() - 1])?;
            } else if is_held && is_checked {
                // A violating state outside the model isn't fingerprinted, but TLC's checks of it
                // sort what their comparisons reach.
                check_violation(evaluator, &rebuilt)?;
            }
            evaluator.registers = registers;
        }
        evaluator.printed.clear();
        Ok(Some(Pass {
            rebuilt,
            steps,
            initial_output,
            outputs,
        }))
    }
}

// What a rebuild of a path gives: its states, the action of each step, and what the spec printed
// finding the first state and then each step.
struct Pass {
    rebuilt: Vec<Vec<Value>>,
    steps: Vec<Option<u32>>,
    initial_output: Vec<Vec<String>>,
    outputs: Vec<Vec<Vec<String>>>,
}

// What TLC's fingerprint of a recovered state sorts, as `settleRecoveredState` gives it: under
// SYMMETRY each value deeply, but a lambda; under a VIEW the state as `deepNormalize` does and the
// view deeply; otherwise each value, a lambda becoming the function it enumerates.
fn settle_recovered(
    evaluator: &mut Evaluator<'_>,
    key: &Key,
    state: &[Value],
) -> Result<(), Unsupported> {
    match key {
        Key::State => state.iter().for_each(settle),
        // TLC permutes the state to find the least in its orbit, which sorts each value it
        // permutes and builds each lambda in it, then fingerprints the state itself where it is
        // the least, or else deep-normalizes it.
        Key::Symmetry(group) => {
            if run(permute_settled(evaluator.ir, group, state))? {
                state.iter().for_each(settle_built);
            } else {
                state.iter().for_each(settle_deep);
            }
        }
        // Under a VIEW too, TLC deep-normalizes the state and fingerprints the view of the
        // least state.
        Key::ViewOfSymmetry(view, group) => {
            run(permute_settled(evaluator.ir, group, state))?;
            state.iter().for_each(settle_normalized);
            let least = run(least_in_orbit(evaluator.ir, group, state))?;
            settle_deep(&run(view_of(evaluator, *view, &least))?);
        }
        Key::View(view) => {
            state.iter().for_each(settle_normalized);
            settle_deep(&run(view_of(evaluator, *view, state))?);
        }
    }
    Ok(())
}

// What TLC prints with each state, as `toTrace` gives it. TLC rebuilds the states it doesn't keep
// before it prints the trace, all but the last of a violation's and all of a lasso's, and then
// prints each later state with what finding its step printed. A trace of one state prints only
// what the initial predicate printed, after it. A violation's trace is rebuilt once more after it
// is printed, which `again` holds what the spec printed in where it may differ.
fn compose(pass: Pass, again: Option<Vec<Vec<String>>>, ending: Ending) -> Trace {
    let Pass {
        rebuilt,
        steps,
        initial_output,
        outputs,
    } = pass;
    let count = rebuilt.len();
    if count == 1 {
        return Trace {
            states: rebuilt
                .into_iter()
                .map(|values| TraceState {
                    values,
                    action: None,
                    printed: Vec::new(),
                })
                .collect(),
            trace_output: initial_output,
        };
    }
    // The states TLC holds rather than rebuilds at the trace's end (`known` in `toTrace`).
    let known = match ending {
        Ending::Kept => 1,
        Ending::Violation => 2,
        Ending::Lasso => 0,
    };
    let recovered = count - known;
    let trace_output = match again {
        Some(again) => again,
        None if known > 0 => initial_output
            .iter()
            .chain(outputs.iter().flatten())
            .cloned()
            .collect(),
        None => Vec::new(),
    };
    let mut prefix = Some(if recovered > 0 {
        initial_output
            .into_iter()
            .chain(outputs[1..recovered].iter().flatten().cloned())
            .collect::<Vec<_>>()
    } else {
        Vec::new()
    });
    let states = rebuilt
        .into_iter()
        .zip(outputs)
        .zip(steps)
        .enumerate()
        .map(|(position, ((values, output), action))| TraceState {
            values,
            action,
            printed: match position {
                0 => prefix.take().unwrap_or_default(),
                _ if position < recovered => Vec::new(),
                _ => output,
            },
        })
        .collect();
    Trace {
        states,
        trace_output,
    }
}

pub(crate) fn run<T>(evaluated: Evaluated<T>) -> Result<T, Unsupported> {
    evaluated.map_err(|error| Unsupported(format!("rebuilding a trace: {}", error.reason)))
}

// The first state the walk of an action completes that TLC takes for the search's state.
// With `is_exhaustive`, the walk runs to its end, for what it prints.
fn find(
    evaluator: &mut Evaluator<'_>,
    key: &Key,
    (expression, context, is_init): (NodeId, &Context, bool),
    is_exhaustive: bool,
    store: &Store,
    target: &[Id],
) -> Result<Option<Vec<Value>>, Unsupported> {
    let target_view = match key {
        Key::View(view) => {
            let state: Vec<Value> = target
                .iter()
                .map(|&id| from_store(store, id))
                .collect::<Result<_, _>>()?;
            Some(run(view_of(evaluator, *view, &state))?)
        }
        Key::ViewOfSymmetry(view, group) => {
            let state: Vec<Value> = target
                .iter()
                .map(|&id| from_store(store, id))
                .collect::<Result<_, _>>()?;
            let least = run(least_in_orbit(evaluator.ir, group, &state))?;
            Some(run(view_of(evaluator, *view, &least))?)
        }
        _ => None,
    };
    let is_reducing = !matches!(key, Key::State);
    let mut found = None;
    let mut is_ambiguous = false;
    run(
        evaluator.walk_action(expression, context, is_init, &mut |evaluator| {
            let state: Vec<Value> = if is_init {
                evaluator.current.iter().flatten().cloned().collect()
            } else {
                evaluator.next.iter().flatten().cloned().collect()
            };
            let is_match = match key {
                Key::State => is_same(store, target, &state),
                Key::View(view) => equals(
                    &view_of(evaluator, *view, &state)?,
                    target_view.as_ref().expect("the target's view"),
                )?,
                Key::ViewOfSymmetry(view, group) => {
                    let least = least_in_orbit(evaluator.ir, group, &state)?;
                    equals(
                        &view_of(evaluator, *view, &least)?,
                        target_view.as_ref().expect("the target's view"),
                    )?
                }
                Key::Symmetry(group) => {
                    is_same(store, target, &state) || {
                        let mut is_found = false;
                        for permutation in group {
                            let permuted = state
                                .iter()
                                .map(|value| permute(value, permutation))
                                .collect::<Evaluated<Vec<_>>>()?;
                            if is_same(store, target, &permuted) {
                                is_found = true;
                                break;
                            }
                        }
                        is_found
                    }
                }
            };
            if is_match {
                match &found {
                    None => found = Some((state, evaluator.choices.clone())),
                    Some((first, choices)) => {
                        // TLC takes the first too where the walk first chose between them in
                        // TLC's order.
                        let is_same_state = first
                            .iter()
                            .zip(&state)
                            .all(|(left, right)| crate::value::is_same(left, right));
                        let is_in_order = choices
                            .iter()
                            .zip(&evaluator.choices)
                            .find(|(left, right)| left != right)
                            .is_some_and(|(left, _)| left.1);
                        is_ambiguous |= !is_same_state && !is_in_order;
                    }
                }
            }
            // A state matched by its value is the search's; one matched by its view or orbit is
            // walked past, for the ambiguity check.
            Ok(is_exhaustive || is_reducing || !is_match)
        }),
    )?;
    // Under VIEW or SYMMETRY, TLC takes the first of the states its view or orbit matches, in the
    // order it streams them, which the evaluator doesn't follow for every set yet; it takes the
    // first state only where the walk reached the others through a choice in TLC's order.
    if is_ambiguous {
        return unsupported("several states TLC may take for the search's under VIEW or SYMMETRY");
    }
    Ok(found.map(|(state, _)| state))
}

// The VIEW of a state, evaluated with the state as the current one.
fn view_of(evaluator: &mut Evaluator<'_>, view: NodeId, state: &[Value]) -> Evaluated<Value> {
    let saved = std::mem::replace(
        &mut evaluator.current,
        state.iter().cloned().map(Some).collect(),
    );
    let value = evaluator.evaluate(view, &Context::default());
    evaluator.current = saved;
    value
}

// The least state of a state's orbit, as `TLCStateMut.fingerPrint` finds it: each permutation's
// values compared with the least so far in TLC's order of the variables.
// TLC's search of a state's orbit in `TLCStateMut.fingerPrint`: each permutation, in the group's
// order, permutes the values in TLC's order of the variables until one compares greater than the
// least so far, or all of them where one compares less. Permuting a value sorts it and builds the
// lambdas in it, which this does to the state's own values; it returns whether the state is the
// least of its orbit.
fn permute_settled(
    ir: &Ir,
    group: &[Vec<(Rc<Text>, Rc<Text>)>],
    state: &[Value],
) -> Evaluated<bool> {
    let mut is_permuted = vec![false; state.len()];
    let mut least: Option<Vec<Value>> = None;
    for permutation in group {
        let mut order = std::cmp::Ordering::Equal;
        let mut permuted = state.to_vec();
        for &position in &ir.tlc_order {
            let position = position as usize;
            permuted[position] = permute(&state[position], permutation)?;
            is_permuted[position] = true;
            if order == std::cmp::Ordering::Equal {
                let smallest = least
                    .as_ref()
                    .map_or(&state[position], |least| &least[position]);
                order = compare(&permuted[position], smallest)?;
                if order == std::cmp::Ordering::Greater {
                    break;
                }
            }
        }
        if order == std::cmp::Ordering::Less {
            least = Some(permuted);
        }
    }
    for (value, is_permuted) in state.iter().zip(is_permuted) {
        if is_permuted {
            settle_built(value);
        }
    }
    Ok(least.is_none())
}

fn least_in_orbit(
    ir: &Ir,
    group: &[Vec<(Rc<Text>, Rc<Text>)>],
    state: &[Value],
) -> Evaluated<Vec<Value>> {
    let mut least = state.to_vec();
    for permutation in group {
        let permuted = state
            .iter()
            .map(|value| permute(value, permutation))
            .collect::<Evaluated<Vec<_>>>()?;
        for &position in &ir.tlc_order {
            let position = position as usize;
            match compare(&permuted[position], &least[position])? {
                std::cmp::Ordering::Less => {
                    least = permuted;
                    break;
                }
                std::cmp::Ordering::Greater => break,
                std::cmp::Ordering::Equal => {}
            }
        }
    }
    Ok(least)
}

pub(crate) fn is_same(store: &Store, target: &[Id], state: &[Value]) -> bool {
    state
        .iter()
        .zip(target)
        .all(|(value, &id)| matches(store, id, value))
}

// Whether the last state satisfies the model's constraints and, if a step reached it, its action
// constraints, as TLC's `isInModel` and `isInActions` find before it fingerprints a state.
pub(crate) fn is_in_model(
    evaluator: &mut Evaluator<'_>,
    rebuilt: &[Vec<Value>],
) -> Result<bool, Unsupported> {
    let ir = evaluator.ir;
    let state = |values: &[Value]| values.iter().cloned().map(Some).collect();
    let last = rebuilt.len() - 1;
    let constraints = ir.model.constraints.iter().map(|name| (name, false));
    let action_constraints = ir.model.action_constraints.iter().map(|name| (name, true));
    for (name, is_action) in constraints.chain(action_constraints) {
        if is_action && last == 0 {
            continue;
        }
        let Some(index) = name.definition else {
            return unsupported("a constraint without a definition");
        };
        // TLCGet("level") reads the level of the state that is current: the predecessor's for an
        // action constraint, and the last state's own, one past it, for a constraint.
        if is_action {
            evaluator.current = state(&rebuilt[last - 1]);
            evaluator.next = state(&rebuilt[last]);
            evaluator.level = last as i32;
        } else {
            evaluator.current = state(&rebuilt[last]);
            evaluator.level = last as i32 + 1;
        }
        let body = evaluator.definition(ir.definitions[index as usize]).body;
        if !run(evaluator.boolean(body, &Context::default()))? {
            return Ok(false);
        }
    }
    Ok(true)
}

// TLC's checks of a violating state, as `doNextCheckInvariants` and `doNextCheckImplied` make
// them: the invariants in order until one fails, then, past an initial state, the action
// properties in order until one fails.
fn check_violation(
    evaluator: &mut Evaluator<'_>,
    rebuilt: &[Vec<Value>],
) -> Result<(), Unsupported> {
    let ir = evaluator.ir;
    let state = |values: &[Value]| values.iter().cloned().map(Some).collect();
    let last = rebuilt.len() - 1;
    evaluator.current = state(&rebuilt[last]);
    evaluator.level = last as i32 + 1;
    let mut invariants = Vec::new();
    for invariant in &ir.model.invariants {
        let Some(index) = invariant.root.definition else {
            return unsupported("an invariant without a definition");
        };
        invariants.push((
            evaluator.definition(ir.definitions[index as usize]).body,
            None,
        ));
    }
    invariants.extend(
        ir.model
            .property_invariants
            .iter()
            .zip(&ir.model.property_invariant_scopes)
            .map(|(invariant, &scope)| (invariant.root, scope)),
    );
    for (invariant, scope) in invariants {
        let context = run(evaluator.scope_context(scope))?;
        if !run(evaluator.boolean(invariant, &context))? {
            return Ok(());
        }
    }
    if last == 0 {
        return Ok(());
    }
    evaluator.current = state(&rebuilt[last - 1]);
    evaluator.next = state(&rebuilt[last]);
    evaluator.level = last as i32;
    for property in &ir.model.action_properties {
        // `[A]_v`: A, or else v unchanged.
        let context = run(evaluator.scope_context(property.scope))?;
        if run(evaluator.boolean(property.action, &context))? {
            continue;
        }
        let now = run(evaluator.evaluate(property.subscript, &context))?;
        let after = run(evaluator.evaluate(property.subscript, &context.primed(true)))?;
        if !run(equals(&now, &after))? {
            return Ok(());
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn print(text: &str) -> Vec<String> {
        vec![text.to_string()]
    }

    // The prints of a trace of states 0..count: Init printed "i", and the step to state n "n".
    fn composed(count: usize, ending: Ending) -> Trace {
        let outputs = (0..count)
            .map(|position| match position {
                0 => Vec::new(),
                _ => vec![print(&position.to_string())],
            })
            .collect();
        compose(
            Pass {
                rebuilt: vec![Vec::new(); count],
                steps: vec![None; count],
                initial_output: vec![print("i")],
                outputs,
            },
            None,
            ending,
        )
    }

    fn printed(trace: &Trace) -> Vec<Vec<Vec<String>>> {
        trace
            .states
            .iter()
            .map(|state| state.printed.clone())
            .collect()
    }

    #[test]
    fn composes_what_tlc_prints_as_it_rebuilds_a_trace() {
        // A deadlock: every state but the last is recovered before the trace prints.
        let kept = composed(3, Ending::Kept);
        assert_eq!(
            printed(&kept),
            [vec![print("i"), print("1")], vec![], vec![print("2")]]
        );
        assert_eq!(kept.trace_output, [print("i"), print("1"), print("2")]);
        // A violation: TLC holds the last two states, so nothing is recovered from two.
        let violation = composed(2, Ending::Violation);
        assert_eq!(printed(&violation), [vec![], vec![print("1")]]);
        assert_eq!(violation.trace_output, [print("i"), print("1")]);
        // A lasso: everything is recovered first, and the trace isn't rebuilt again.
        let lasso = composed(3, Ending::Lasso);
        assert_eq!(
            printed(&lasso),
            [vec![print("i"), print("1"), print("2")], vec![], vec![]]
        );
        assert!(lasso.trace_output.is_empty());
    }
}
