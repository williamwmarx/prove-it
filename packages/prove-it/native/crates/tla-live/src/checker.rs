//! TLC's behavior graphs and its search of them (`liveness-checker.ts`): a graph per solution of
//! the formula, a node per state or per state and tableau node, built state by state in the order
//! of the search with each state's successors in the order of TLC's `SetOfStates`, then TLC's
//! `LiveWorker#checkSccs` and `printTrace` on each.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::hash::{BuildHasherDefault, Hasher};

use crate::tableau::{Kind, Model, Solution, Tableau, TermId, Terms};
use crate::{Declined, Event, Graph, Verdict};

const NO_NODE: u32 = u32::MAX;
const UNWRITTEN: usize = usize::MAX;
const SUCCESSOR_CAPACITY: usize = 16;
const SCC_MARKER: i64 = -42;
const UNVISITED: i64 = -1;
const MAXIMUM_LINK: i64 = 0x7fff_ffff;
const UNKNOWN_RESULT: u8 = 0;
const KNOWN_FALSE: u8 = 1;
const KNOWN_TRUE: u8 = 2;

/// A multiplicative hash of the integer keys of the maps below.
#[derive(Default)]
struct IntegerHasher(u64);

impl Hasher for IntegerHasher {
    fn finish(&self) -> u64 {
        self.0
    }

    fn write(&mut self, bytes: &[u8]) {
        for &byte in bytes {
            self.write_u64(u64::from(byte));
        }
    }

    fn write_u32(&mut self, value: u32) {
        self.write_u64(u64::from(value));
    }

    fn write_u64(&mut self, value: u64) {
        self.0 = (self.0.rotate_left(5) ^ value).wrapping_mul(0x51_7c_c1_b7_27_22_0a_95);
    }

    fn write_usize(&mut self, value: usize) {
        self.write_u64(value as u64);
    }
}

/// A counterexample's states: the prefix, then the cycle.
type Lasso = (Vec<u32>, Vec<u32>);

type IntegerMap<Key, Value> = HashMap<Key, Value, BuildHasherDefault<IntegerHasher>>;

/// A step of the search: a successor of a state, the state the step reached (the successor itself
/// unless SYMMETRY or a VIEW told it apart from the state stored for it), and the position of the
/// step's answers in the engine's tables of actions.
#[derive(Clone, Copy)]
struct Step {
    target: u32,
    real: u32,
    answer: usize,
}

struct Behavior {
    solution: usize,
    /// One id per distinct action check across the solutions.
    action_ids: Vec<usize>,
    node_states: Vec<u32>,
    node_tableaux: Vec<u32>,
    edge_starts: Vec<usize>,
    edge_counts: Vec<u32>,
    edge_targets: Vec<u32>,
    edge_steps: Vec<u32>,
    state_results: Vec<u8>,
    /// Whether the behaviors before this one have every action check of this one.
    is_covered: bool,
    consistency: Vec<u8>,
    initial: Vec<u32>,
    first_nodes: Vec<u32>,
    last_nodes: Vec<u32>,
    next_siblings: Vec<u32>,
    node_ids: IntegerMap<(u32, u32), u32>,
    /// The state each late node reached, where it isn't the state stored for the node.
    node_reals: IntegerMap<u32, u32>,
    is_done: Vec<bool>,
    error_node: Option<u32>,
}

impl Behavior {
    fn is_written(&self, node: u32) -> bool {
        self.edge_starts
            .get(node as usize)
            .is_some_and(|&start| start != UNWRITTEN)
    }

    fn successors(&self, node: u32) -> &[u32] {
        let start = self.edge_starts[node as usize];
        &self.edge_targets[start..start + self.edge_counts[node as usize] as usize]
    }

    fn push_node(&mut self, state: u32, tableau_node: u32) -> u32 {
        self.node_states.push(state);
        self.node_tableaux.push(tableau_node);
        self.edge_starts.push(UNWRITTEN);
        self.edge_counts.push(0);
        self.next_siblings.push(NO_NODE);
        (self.node_states.len() - 1) as u32
    }

    fn record_node(&mut self, state: u32, tableau_node: u32) -> u32 {
        let node = self.push_node(state, tableau_node);
        self.node_ids.insert((state, tableau_node), node);
        let state = state as usize;
        if self.last_nodes.len() <= state {
            self.last_nodes.resize(state + 1, NO_NODE);
            self.first_nodes.resize(state + 1, NO_NODE);
        }
        match self.last_nodes[state] {
            NO_NODE => self.first_nodes[state] = node,
            last => self.next_siblings[last as usize] = node,
        }
        self.last_nodes[state] = node;
        node
    }

    fn write_node(&mut self, node: u32, targets: &[u32], steps: &[u32]) {
        self.edge_starts[node as usize] = self.edge_targets.len();
        self.edge_counts[node as usize] = targets.len() as u32;
        self.edge_targets.extend_from_slice(targets);
        self.edge_steps.extend_from_slice(steps);
    }
}

pub struct Checker<'c> {
    terms: Terms,
    solutions: Vec<Solution>,
    graph: &'c Graph<'c>,
    tables: &'c [Option<&'c [u8]>],
    behaviors: Vec<Behavior>,
    action_count: usize,
    /// The results of the action checks on each step, a row of action ids per step: -1 until
    /// checked, then 0 or 1.
    steps: Vec<i8>,
    step_count: usize,
    /// TLC's SetOfStates grows its capacity with every set that outgrows it.
    capacity_multiplier: usize,
    slots: Vec<u32>,
    is_cycle_constrained: Vec<bool>,
    /// Where an atom's evaluation has effects, which TLC has each time it evaluates the atom: the
    /// checks keep no results across evaluations and log each evaluation of an atom.
    effects: RefCell<Option<Effects>>,
}

/// The evaluations of atoms so far, and the atoms' answers within the evaluation of one check, as
/// `evaluateLive`'s cache keeps them.
#[derive(Default)]
struct Effects {
    events: Vec<Event>,
    known: Vec<(u32, bool)>,
}

impl<'c> Checker<'c> {
    pub fn new(
        mut terms: Terms,
        formula: TermId,
        graph: &'c Graph<'c>,
        tables: &'c [Option<&'c [u8]>],
    ) -> Result<Self, Declined> {
        let solutions = terms.solutions(formula)?;
        let mut action_ids: HashMap<TermId, usize> = HashMap::new();
        let mut behaviors: Vec<Behavior> = Vec::with_capacity(solutions.len());
        for (position, solution) in solutions.iter().enumerate() {
            let ids: Vec<usize> = solution
                .action_checks
                .iter()
                .map(|&check| {
                    let next = action_ids.len();
                    *action_ids.entry(check).or_insert(next)
                })
                .collect();
            let is_covered = ids.iter().all(|id| {
                behaviors
                    .iter()
                    .any(|behavior| behavior.action_ids.contains(id))
            });
            behaviors.push(Behavior {
                solution: position,
                action_ids: ids,
                node_states: Vec::new(),
                node_tableaux: Vec::new(),
                edge_starts: Vec::new(),
                edge_counts: Vec::new(),
                edge_targets: Vec::new(),
                edge_steps: Vec::new(),
                state_results: Vec::new(),
                is_covered,
                consistency: Vec::new(),
                initial: Vec::new(),
                first_nodes: Vec::new(),
                last_nodes: Vec::new(),
                next_siblings: Vec::new(),
                node_ids: IntegerMap::default(),
                node_reals: IntegerMap::default(),
                is_done: vec![false; graph.count()],
                error_node: None,
            });
        }
        let is_cycle_constrained = solutions
            .iter()
            .map(|solution| {
                solution
                    .promises
                    .iter()
                    .any(|&promise| terms.contains_always(terms.body(promise)))
                    || solution.models.iter().any(|model| {
                        !model.eventually_always.is_empty()
                            || !model.infinitely_often_states.is_empty()
                            || !model.infinitely_often_actions.is_empty()
                    })
            })
            .collect();
        Ok(Self {
            terms,
            solutions,
            graph,
            tables,
            behaviors,
            action_count: action_ids.len(),
            steps: Vec::new(),
            step_count: 0,
            capacity_multiplier: 1,
            slots: Vec::new(),
            is_cycle_constrained,
            effects: RefCell::new(None),
        })
    }

    // --- evaluation: `evaluateLive` over the engine's tables ---

    fn answer(&self, atom: u32, position: usize) -> Result<bool, Declined> {
        let table = self
            .tables
            .get(atom as usize)
            .copied()
            .flatten()
            .ok_or_else(|| Declined::from("an atom the engine doesn't answer"))?;
        match table.get(position) {
            Some(0) => Ok(false),
            Some(1) => Ok(true),
            _ => Err(Declined::from(
                "a predicate the engine leaves to the interpreter",
            )),
        }
    }

    fn evaluate(&self, term: TermId, state: u32, step: Option<Step>) -> Result<bool, Declined> {
        match self.terms.kind(term) {
            Kind::Boolean(value) => Ok(value),
            Kind::State(atom) | Kind::Enabled(atom) => {
                let mut effects = self.effects.borrow_mut();
                let Some(effects) = effects.as_mut() else {
                    return self.answer(atom, state as usize);
                };
                if let Some(&(_, known)) = effects.known.iter().find(|known| known.0 == atom) {
                    return Ok(known);
                }
                let answer = self.answer(atom, state as usize)?;
                effects.events.push(Event::Atom {
                    atom,
                    slot: state as usize,
                });
                effects.known.push((atom, answer));
                Ok(answer)
            }
            Kind::Action { atom, enabled } if self.effects.borrow().is_some() => {
                let mut effects = self.effects.borrow_mut();
                let effects = effects.as_mut().expect("effects");
                if enabled.is_some_and(|enabled| effects.known.contains(&(enabled, false))) {
                    return Ok(false);
                }
                let step = step.ok_or_else(|| Declined::from("an action without a step"))?;
                let answer = self.answer(atom, step.answer)?;
                effects.events.push(Event::Atom {
                    atom,
                    slot: step.answer,
                });
                Ok(answer)
            }
            Kind::Action { atom, enabled } => {
                if let Some(enabled) = enabled
                    && let Some(Some(table)) = self.tables.get(enabled as usize)
                    && table.get(state as usize) == Some(&0)
                {
                    return Ok(false);
                }
                let step = step.ok_or_else(|| Declined::from("an action without a step"))?;
                self.answer(atom, step.answer)
            }
            Kind::Not => Ok(!self.evaluate(self.terms.body(term), state, step)?),
            Kind::And => {
                for &operand in self.terms.children(term) {
                    if !self.evaluate(operand, state, step)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Kind::Or => {
                for &operand in self.terms.children(term) {
                    if self.evaluate(operand, state, step)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            Kind::Next => {
                let outer = self.start_evaluation();
                let result = self.evaluate(
                    self.terms.body(term),
                    step.map_or(state, |step| step.real),
                    None,
                );
                if let Some(effects) = self.effects.borrow_mut().as_mut() {
                    effects.known = outer;
                }
                result
            }
            Kind::Always | Kind::Eventually => {
                Err(Declined::from("a temporal formula in a single step"))
            }
        }
    }

    // Starts the evaluation of a check, which TLC evaluates without the atoms' answers so far: the
    // answers known before.
    fn start_evaluation(&self) -> Vec<(u32, bool)> {
        self.effects
            .borrow_mut()
            .as_mut()
            .map(|effects| std::mem::take(&mut effects.known))
            .unwrap_or_default()
    }

    fn log(&self, event: Event) {
        if let Some(effects) = self.effects.borrow_mut().as_mut() {
            effects.events.push(event);
        }
    }

    fn is_effectful(&self) -> bool {
        self.effects.borrow().is_some()
    }

    /// Has the checks evaluate each atom each time TLC does, and log the evaluations.
    pub fn log_effects(&mut self) {
        *self.effects.get_mut() = Some(Effects::default());
    }

    /// The evaluations logged, which ends the log.
    pub fn take_events(&mut self) -> Vec<Event> {
        self.effects
            .get_mut()
            .take()
            .map(|effects| effects.events)
            .unwrap_or_default()
    }

    fn self_step(&self, state: u32, real: u32) -> Step {
        Step {
            target: state,
            real,
            answer: self.graph.edges.len() + real as usize,
        }
    }

    fn edge_step(&self, state: u32, edge: usize) -> Step {
        let target = self.graph.edges[edge];
        let real = self.graph.reals.map_or(target, |reals| reals[edge]);
        if target == state && real == state {
            self.self_step(state, state)
        } else {
            Step {
                target,
                real,
                answer: edge,
            }
        }
    }

    fn add_steps(&mut self, count: usize) -> usize {
        let first = self.step_count;
        self.step_count += count;
        self.steps.resize(self.step_count * self.action_count, -1);
        first
    }

    fn check_step(
        &mut self,
        behavior: usize,
        state: u32,
        step: Step,
        row: usize,
    ) -> Result<(), Declined> {
        let solution = &self.solutions[self.behaviors[behavior].solution];
        for (position, &check) in solution.action_checks.iter().enumerate() {
            let slot = row * self.action_count + self.behaviors[behavior].action_ids[position];
            if self.steps[slot] != -1 {
                continue;
            }
            self.start_evaluation();
            self.steps[slot] = i8::from(self.evaluate(check, state, Some(step))?);
        }
        Ok(())
    }

    fn check_action(&mut self, behavior: usize, state: u32, step: Step) -> Result<u32, Declined> {
        let row = self.add_steps(1);
        self.check_step(behavior, state, step, row)?;
        Ok(row as u32)
    }

    // The state checks of a state the search reached, kept for the nodes of the state it reached.
    fn check_state(&mut self, behavior: usize, real: u32) -> Result<(), Declined> {
        let solution = &self.solutions[self.behaviors[behavior].solution];
        let count = solution.state_checks.len();
        let offset = real as usize * count;
        let results: Vec<u8> = solution
            .state_checks
            .iter()
            .map(|&check| {
                self.start_evaluation();
                self.evaluate(check, real, None).map(u8::from)
            })
            .collect::<Result<_, _>>()?;
        let stored = &mut self.behaviors[behavior].state_results;
        if stored.len() < offset + count {
            stored.resize(offset + count, 0);
        }
        stored[offset..offset + count].copy_from_slice(&results);
        Ok(())
    }

    fn tableau(&self, behavior: usize) -> Option<&Tableau> {
        self.solutions[self.behaviors[behavior].solution]
            .tableau
            .as_ref()
    }

    // Whether a reached state is consistent with a tableau node.
    fn is_consistent(&mut self, behavior: usize, node: u32, state: u32) -> Result<bool, Declined> {
        let Some(tableau) = self.tableau(behavior) else {
            return Ok(true);
        };
        let slot = state as usize * tableau.nodes.len() + node as usize;
        let is_effectful = self.is_effectful();
        if !is_effectful
            && let Some(&known) = self.behaviors[behavior].consistency.get(slot)
            && known != UNKNOWN_RESULT
        {
            return Ok(known == KNOWN_TRUE);
        }
        self.start_evaluation();
        let mut is_held = true;
        for &predicate in &tableau.nodes[node as usize].state_predicates {
            if !self.evaluate(predicate, state, None)? {
                is_held = false;
                break;
            }
        }
        if is_effectful {
            return Ok(is_held);
        }
        let size = self.tableau_size(behavior);
        let consistency = &mut self.behaviors[behavior].consistency;
        if consistency.len() <= slot {
            consistency.resize((state as usize + 1) * size, UNKNOWN_RESULT);
        }
        consistency[slot] = if is_held { KNOWN_TRUE } else { KNOWN_FALSE };
        Ok(is_held)
    }

    fn tableau_size(&self, behavior: usize) -> usize {
        self.tableau(behavior)
            .map_or(0, |tableau| tableau.nodes.len())
    }

    fn is_accepting(&self, behavior: usize, node: u32) -> bool {
        let Some(tableau) = self.tableau(behavior) else {
            return false;
        };
        let tableau_node = &tableau.nodes[node as usize];
        tableau_node.particle.is_empty() && tableau_node.successors == [node]
    }

    fn has_empty_model(&self, behavior: usize) -> bool {
        self.solutions[self.behaviors[behavior].solution]
            .models
            .iter()
            .any(|model| {
                model.eventually_always.is_empty()
                    && model.infinitely_often_states.is_empty()
                    && model.infinitely_often_actions.is_empty()
            })
    }

    fn node_id(&self, behavior: usize, state: u32, tableau_node: u32) -> Option<u32> {
        self.behaviors[behavior]
            .node_ids
            .get(&(state, tableau_node))
            .copied()
    }

    // --- building the graphs: TLC's TableauLiveChecker and LiveChecker ---

    /// TLC collects a state's successors and the state itself in a SetOfStates, a hash set it
    /// iterates in slot order, keyed by the states' fingerprints.
    fn successor_set(&mut self, state: u32) -> Vec<Step> {
        let graph = self.graph;
        let start = graph.edge_offsets[state as usize] as usize;
        let end = graph.edge_offsets[state as usize + 1] as usize;
        let mut entries: Vec<Step> = (start..end)
            .map(|edge| self.edge_step(state, edge))
            .collect();
        entries.push(self.self_step(state, state));
        let fingerprint =
            |step: &Step| (graph.fingerprints[step.target as usize] as u32 & 0x7fff_ffff) as usize;
        let insert = |slots: &mut [u32], position: usize| {
            let entry = entries[position];
            let size = slots.len();
            let mut slot = fingerprint(&entry) % size;
            loop {
                match slots[slot] {
                    0 => {
                        slots[slot] = position as u32 + 1;
                        return true;
                    }
                    stored
                        if entries[stored as usize - 1].target == entry.target
                            && entries[stored as usize - 1].real == entry.real =>
                    {
                        return false;
                    }
                    _ => slot = (slot + 1) % size,
                }
            }
        };
        let mut size = SUCCESSOR_CAPACITY * self.capacity_multiplier;
        let mut count = 0;
        self.slots.clear();
        self.slots.resize(size, 0);
        for position in 0..entries.len() {
            if count >= size >> 1 {
                let old = std::mem::take(&mut self.slots);
                size = 2 * size + 1;
                self.slots.resize(size, 0);
                for stored in old.into_iter().filter(|&stored| stored != 0) {
                    insert(&mut self.slots, stored as usize - 1);
                }
            }
            if insert(&mut self.slots, position) {
                count += 1;
            }
        }
        if size > SUCCESSOR_CAPACITY * self.capacity_multiplier {
            self.capacity_multiplier += 1;
        }
        self.slots
            .iter()
            .filter(|&&stored| stored != 0)
            .map(|&stored| entries[stored as usize - 1])
            .collect()
    }

    fn add_initial_state(&mut self, state: u32) -> Result<(), Declined> {
        self.log(Event::Initial(state));
        for behavior in 0..self.behaviors.len() {
            let Some(initial_count) = self.tableau(behavior).map(|tableau| tableau.initial_count)
            else {
                self.behaviors[behavior].initial.push(state);
                continue;
            };
            for node in 0..initial_count as u32 {
                if !self.is_consistent(behavior, node, state)? {
                    continue;
                }
                let target = match self.node_id(behavior, state, node) {
                    Some(existing) => existing,
                    None => self.behaviors[behavior].record_node(state, node),
                };
                self.behaviors[behavior].initial.push(target);
            }
        }
        Ok(())
    }

    /// Adds a state with its successors to every graph, and returns the path to a node of a
    /// tableau that accepts every behavior, when TLC finds one.
    fn add_state(&mut self, state: u32) -> Result<Option<Vec<u32>>, Declined> {
        self.log(Event::Expanded(state));
        let set = self.successor_set(state);
        // With effects, each behavior checks its actions on each step anew, as TLC does.
        let is_effectful = self.is_effectful();
        let shared_step = self.add_steps(if is_effectful { 0 } else { set.len() });
        for behavior in 0..self.behaviors.len() {
            let first_step = if is_effectful {
                self.add_steps(set.len())
            } else {
                shared_step
            };
            if is_effectful || !self.behaviors[behavior].is_covered {
                for (position, &step) in set.iter().enumerate() {
                    self.check_step(behavior, state, step, first_step + position)?;
                }
            }
            self.check_state(behavior, state)?;
            if self.tableau(behavior).is_none() {
                self.add_plain_state(behavior, &set, first_step, state);
                continue;
            }
            if let Some(path) = self.add_tableau_state(behavior, &set, first_step, state)? {
                return Ok(Some(path));
            }
        }
        Ok(None)
    }

    fn add_plain_state(&mut self, behavior: usize, set: &[Step], first_step: usize, state: u32) {
        let behavior = &mut self.behaviors[behavior];
        while behavior.node_states.len() <= state as usize {
            let next = behavior.node_states.len() as u32;
            behavior.push_node(next, NO_NODE);
        }
        let mut targets = Vec::with_capacity(set.len());
        let mut steps = Vec::with_capacity(set.len());
        for (position, step) in set.iter().enumerate() {
            if behavior.is_written(step.target) && targets.contains(&step.target) {
                continue;
            }
            targets.push(step.target);
            steps.push((first_step + position) as u32);
        }
        behavior.write_node(state, &targets, &steps);
    }

    fn tableau_successors(&self, behavior: usize, node: u32) -> Vec<u32> {
        let tableau = self.tableau(behavior).expect("a tableau");
        tableau.nodes[self.behaviors[behavior].node_tableaux[node as usize] as usize]
            .successors
            .clone()
    }

    fn add_tableau_state(
        &mut self,
        behavior: usize,
        set: &[Step],
        first_step: usize,
        state: u32,
    ) -> Result<Option<Vec<u32>>, Declined> {
        let node_count = self.tableau_size(behavior);
        let mut consistency = vec![false; node_count * set.len()];
        for node in 0..node_count {
            for (position, step) in set.iter().enumerate() {
                consistency[node * set.len() + position] =
                    self.is_consistent(behavior, node as u32, step.real)?;
            }
        }
        self.behaviors[behavior].is_done[state as usize] = true;
        // TLC expands the nodes recorded before the loop, not the ones the loop records.
        let last = self.behaviors[behavior]
            .last_nodes
            .get(state as usize)
            .copied()
            .unwrap_or(NO_NODE);
        let mut node = if last == NO_NODE {
            NO_NODE
        } else {
            self.behaviors[behavior].first_nodes[state as usize]
        };
        while node != NO_NODE {
            let tableau_successors = self.tableau_successors(behavior, node);
            let mut targets = Vec::new();
            let mut steps = Vec::new();
            for (position, step) in set.iter().enumerate() {
                let is_done = self.behaviors[behavior].is_done[step.target as usize];
                for &next in &tableau_successors {
                    if !consistency[next as usize * set.len() + position] {
                        continue;
                    }
                    let existing = self.node_id(behavior, step.target, next);
                    if existing.is_some_and(|existing| targets.contains(&existing)) {
                        continue;
                    }
                    let target = match existing {
                        Some(existing) => existing,
                        None => self.behaviors[behavior].record_node(step.target, next),
                    };
                    targets.push(target);
                    steps.push((first_step + position) as u32);
                    if existing.is_none() && is_done {
                        self.expand_late(behavior, step.target, step.real, target)?;
                    }
                }
            }
            self.behaviors[behavior].write_node(node, &targets, &steps);
            node = if node == last {
                NO_NODE
            } else {
                self.behaviors[behavior].next_siblings[node as usize]
            };
        }
        let Some(error_node) = self.behaviors[behavior].error_node else {
            return Ok(None);
        };
        let path = self.path(behavior, error_node)?;
        let behavior = &self.behaviors[behavior];
        Ok(Some(remove_repeats(
            path.iter()
                .rev()
                .map(|&node| behavior.node_states[node as usize]),
        )))
    }

    /// TLC's TableauLiveChecker#addNextState for a node it finds after it expanded the node's
    /// state: it checks the state the step reached, `real`, and runs Next from it.
    fn expand_late(
        &mut self,
        behavior: usize,
        state: u32,
        real: u32,
        node: u32,
    ) -> Result<(), Declined> {
        if real as usize + 1 >= self.graph.edge_offsets.len() {
            return Err(Declined::from(crate::UNEXPANDED));
        }
        if real != state {
            self.behaviors[behavior].node_reals.insert(node, real);
        }
        self.check_state(behavior, real)?;
        let tableau_successors = self.tableau_successors(behavior, node);
        let mut targets = Vec::new();
        let mut steps = Vec::new();
        let self_step = if tableau_successors.is_empty() {
            u32::MAX
        } else {
            self.check_action(behavior, real, self.self_step(state, real))?
        };
        for &next in &tableau_successors {
            if !self.is_consistent(behavior, next, real)? {
                continue;
            }
            if self.is_accepting(behavior, next)
                && self.behaviors[behavior].error_node.is_none()
                && self.has_empty_model(behavior)
            {
                self.behaviors[behavior].error_node = Some(node);
                return Ok(());
            }
            let existing = self.node_id(behavior, state, next);
            if existing.is_some_and(|existing| targets.contains(&existing)) {
                continue;
            }
            let target = match existing {
                Some(existing) => existing,
                None => self.behaviors[behavior].record_node(state, next),
            };
            targets.push(target);
            steps.push(self_step);
            if existing.is_none() {
                self.expand_late(behavior, state, real, target)?;
            }
        }
        self.log(Event::Late(real));
        let start = self.graph.edge_offsets[real as usize] as usize;
        let end = self.graph.edge_offsets[real as usize + 1] as usize;
        for edge in start..end {
            let step = self.edge_step(real, edge);
            let successor_step = self.check_action(behavior, real, step)?;
            let is_done = self.behaviors[behavior].is_done[step.target as usize];
            for &next in &tableau_successors {
                if !self.is_consistent(behavior, next, step.real)? {
                    continue;
                }
                let existing = self.node_id(behavior, step.target, next);
                if existing.is_some_and(|existing| targets.contains(&existing)) {
                    continue;
                }
                let target = match existing {
                    Some(existing) => existing,
                    None => self.behaviors[behavior].record_node(step.target, next),
                };
                targets.push(target);
                steps.push(successor_step);
                if existing.is_none() && is_done {
                    self.expand_late(behavior, step.target, step.real, target)?;
                }
            }
        }
        if !targets.is_empty() {
            self.behaviors[behavior].write_node(node, &targets, &steps);
        }
        Ok(())
    }

    /// The shortest path from an initial node to the node, last node first, as TLC's getPath
    /// finds it.
    fn path(&self, behavior: usize, target: u32) -> Result<Vec<u32>, Declined> {
        let graph = &self.behaviors[behavior];
        if graph.initial.contains(&target) {
            return Ok(vec![target]);
        }
        let is_tableau = self.tableau(behavior).is_some();
        let mut parents: IntegerMap<u32, u32> = IntegerMap::default();
        let mut queue = Vec::new();
        for &node in &graph.initial {
            if !graph.is_written(node) {
                continue;
            }
            queue.push(node);
            parents.insert(node, NO_NODE);
        }
        let mut position = 0;
        while position < queue.len() {
            let current = queue[position];
            position += 1;
            for &next in graph.successors(current) {
                if next == current && is_tableau {
                    continue;
                }
                if next == target {
                    let mut path = vec![target];
                    let mut node = current;
                    while node != NO_NODE {
                        path.push(node);
                        node = parents.get(&node).copied().unwrap_or(NO_NODE);
                    }
                    return Ok(path);
                }
                if !graph.is_written(next) || parents.contains_key(&next) {
                    continue;
                }
                parents.insert(next, current);
                queue.push(next);
            }
        }
        Err(Declined::from("a liveness trace TLC couldn't re-create"))
    }

    // --- the search: TLC's LiveWorker#checkSccs and printTrace ---

    /// How many solutions TLC checks, which it calls branches.
    pub fn branches(&self) -> usize {
        self.solutions.len()
    }

    // The step from one state to another, as the first of the search's steps between them.
    fn step_to(&self, state: u32, target: u32) -> Result<Step, Declined> {
        if state == target {
            return Ok(self.self_step(state, state));
        }
        let start = self.graph.edge_offsets[state as usize] as usize;
        let end = self.graph.edge_offsets[state as usize + 1] as usize;
        (start..end)
            .find(|&edge| self.graph.edges[edge] == target)
            .map(|edge| self.edge_step(state, edge))
            .ok_or_else(|| Declined::from("a step the search didn't take"))
    }

    /// Whether a formula holds of the lasso from the position on, as `evaluateOnLasso` finds it.
    fn evaluate_on_lasso(
        &self,
        term: TermId,
        path: &[u32],
        cycle_start: usize,
        position: usize,
    ) -> Result<bool, Declined> {
        let next = |index: usize| {
            if index + 1 < path.len() {
                index + 1
            } else {
                cycle_start
            }
        };
        let future = position.min(cycle_start)..path.len();
        match self.terms.kind(term) {
            Kind::Not => {
                Ok(!self.evaluate_on_lasso(self.terms.body(term), path, cycle_start, position)?)
            }
            Kind::And => {
                for &operand in self.terms.children(term) {
                    if !self.evaluate_on_lasso(operand, path, cycle_start, position)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Kind::Or => {
                for &operand in self.terms.children(term) {
                    if self.evaluate_on_lasso(operand, path, cycle_start, position)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            Kind::Next => {
                self.evaluate_on_lasso(self.terms.body(term), path, cycle_start, next(position))
            }
            Kind::Always => {
                for index in future {
                    if !self.evaluate_on_lasso(self.terms.body(term), path, cycle_start, index)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Kind::Eventually => {
                for index in future {
                    if self.evaluate_on_lasso(self.terms.body(term), path, cycle_start, index)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            _ => {
                let state = path[position];
                let step = self.step_to(state, path[next(position)])?;
                self.evaluate(term, state, Some(step))
            }
        }
    }

    /// The positions of the properties the lasso violates, in order.
    pub fn violated(
        &self,
        properties: &[TermId],
        path: &[u32],
        loop_start: usize,
    ) -> Result<Vec<usize>, Declined> {
        let mut violated = Vec::new();
        for (position, &property) in properties.iter().enumerate() {
            if !self.evaluate_on_lasso(property, path, loop_start, 0)? {
                violated.push(position);
            }
        }
        Ok(violated)
    }

    pub fn find_violation(&self) -> Result<Option<(Vec<u32>, usize, bool)>, Declined> {
        for behavior in 0..self.behaviors.len() {
            let solution = &self.solutions[self.behaviors[behavior].solution];
            for model in &solution.models {
                if let Some(lasso) = Search::new(self, behavior, model).find_lasso()? {
                    let (prefix, cycle) = lasso;
                    let loop_start = prefix.len();
                    let mut path = prefix;
                    path.extend(cycle);
                    return Ok(Some((
                        path,
                        loop_start,
                        self.is_cycle_constrained[self.behaviors[behavior].solution],
                    )));
                }
            }
        }
        Ok(None)
    }
}

fn remove_repeats(states: impl Iterator<Item = u32>) -> Vec<u32> {
    let mut path: Vec<u32> = Vec::new();
    for state in states {
        if path.last() != Some(&state) {
            path.push(state);
        }
    }
    path
}

/// The search of one model of one behavior graph for a strongly connected component that
/// violates it.
struct Search<'s, 'c> {
    checker: &'s Checker<'c>,
    index: usize,
    behavior: &'s Behavior,
    solution: &'s Solution,
    model: &'s Model,
    allowed_ids: Vec<usize>,
    links: Vec<i64>,
    components: Vec<u32>,
    members: Vec<u32>,
    member_marks: Vec<u32>,
    mark: u32,
    /// Whether each tableau node fulfills each promise.
    fulfilling: Vec<bool>,
}

impl<'s, 'c> Search<'s, 'c> {
    fn new(checker: &'s Checker<'c>, behavior: usize, model: &'s Model) -> Self {
        let graph = &checker.behaviors[behavior];
        let solution = &checker.solutions[graph.solution];
        let node_count = graph.node_states.len();
        let fulfilling = solution
            .tableau
            .iter()
            .flat_map(|tableau| &tableau.nodes)
            .flat_map(|node| {
                solution
                    .promises
                    .iter()
                    .map(|&promise| checker.terms.is_fulfilling(&node.particle, promise))
            })
            .collect();
        Self {
            checker,
            index: behavior,
            behavior: graph,
            solution,
            model,
            allowed_ids: model
                .eventually_always
                .iter()
                .map(|&position| graph.action_ids[position])
                .collect(),
            links: vec![UNVISITED; node_count],
            components: Vec::new(),
            members: Vec::new(),
            member_marks: vec![0; node_count],
            mark: 0,
            fulfilling,
        }
    }

    fn row(&self, node: u32, edge: usize) -> usize {
        let behavior = self.behavior;
        behavior.edge_steps[behavior.edge_starts[node as usize] + edge] as usize
            * self.checker.action_count
    }

    fn is_action(&self, node: u32, edge: usize, position: usize) -> bool {
        self.checker.steps[self.row(node, edge) + self.behavior.action_ids[position]] == 1
    }

    fn is_allowed(&self, node: u32, edge: usize) -> bool {
        let row = self.row(node, edge);
        self.allowed_ids
            .iter()
            .all(|&id| self.checker.steps[row + id] == 1)
    }

    fn is_member(&self, node: u32) -> bool {
        self.member_marks[node as usize] == self.mark
    }

    fn state_result(&self, node: u32, position: usize) -> bool {
        let count = self.solution.state_checks.len();
        let real = self.behavior.node_reals.get(&node).copied();
        let state = real.unwrap_or(self.behavior.node_states[node as usize]);
        self.behavior.state_results[state as usize * count + position] == 1
    }

    fn is_fulfilled(&self, node: u32, promise: usize) -> bool {
        self.solution.tableau.is_some()
            && self.fulfilling[self.behavior.node_tableaux[node as usize] as usize
                * self.solution.promises.len()
                + promise]
    }

    fn is_stuttering(&self, node: u32) -> bool {
        self.behavior
            .successors(node)
            .iter()
            .position(|&next| next == node)
            .is_some_and(|edge| self.is_allowed(node, edge))
    }

    // Whether the component's edges that stay in it take every action that the model requires
    // infinitely often.
    fn is_action_satisfied(&self) -> bool {
        let actions = &self.model.infinitely_often_actions;
        let mut satisfied = vec![false; actions.len()];
        let mut remaining = actions.len();
        for &node in &self.members {
            let successors = self.behavior.successors(node);
            for (edge, &next) in successors.iter().enumerate() {
                if remaining == 0 {
                    break;
                }
                if !self.is_member(next) || !self.is_allowed(node, edge) {
                    continue;
                }
                for (slot, &position) in actions.iter().enumerate() {
                    if !satisfied[slot] && self.is_action(node, edge, position) {
                        satisfied[slot] = true;
                        remaining -= 1;
                    }
                }
            }
        }
        remaining == 0
    }

    fn check_component(&mut self, root: u32) -> Result<Option<Lasso>, Declined> {
        let top = self.components.pop().unwrap_or(root);
        if top == root && !self.is_stuttering(top) {
            self.links[top as usize] = MAXIMUM_LINK;
            return Ok(None);
        }
        self.members.clear();
        self.mark += 1;
        let mut member = top;
        loop {
            self.members.push(member);
            self.member_marks[member as usize] = self.mark;
            self.links[member as usize] = MAXIMUM_LINK;
            if member == root {
                break;
            }
            member = self.components.pop().unwrap_or(root);
        }
        let is_state_satisfied = self.model.infinitely_often_states.iter().all(|&position| {
            self.members
                .iter()
                .any(|&node| self.state_result(node, position))
        });
        if !is_state_satisfied || !self.is_action_satisfied() {
            return Ok(None);
        }
        let is_promised = (0..self.solution.promises.len()).all(|promise| {
            self.members
                .iter()
                .any(|&node| self.is_fulfilled(node, promise))
        });
        if !is_promised {
            return Ok(None);
        }
        let mut members_by_state: IntegerMap<u32, Vec<u32>> = IntegerMap::default();
        for &member in &self.members {
            members_by_state
                .entry(self.behavior.node_states[member as usize])
                .or_default()
                .push(member);
        }
        self.lasso(root, &members_by_state).map(Some)
    }

    fn states_of(&self, nodes: impl Iterator<Item = u32>) -> Vec<u32> {
        remove_repeats(nodes.map(|node| self.behavior.node_states[node as usize]))
    }

    // TLC's LiveWorker#printTrace: a prefix to the root, a greedy walk through the component
    // until it satisfies every check, and a breadth-first path back to the root.
    fn lasso(
        &self,
        root: u32,
        members_by_state: &IntegerMap<u32, Vec<u32>>,
    ) -> Result<Lasso, Declined> {
        let failed = || Declined::from("a liveness counterexample TLC failed to build");
        let behavior = self.behavior;
        let model = self.model;
        let prefix = self.states_of(self.checker.path(self.index, root)?.into_iter().rev());
        let mut cycle_stack: Vec<u32> = Vec::new();
        let mut seen: HashSet<u32> = HashSet::from([root]);
        let mut state_done = vec![false; model.infinitely_often_states.len()];
        let mut action_done = vec![false; model.infinitely_often_actions.len()];
        let mut promise_done = vec![false; self.solution.promises.len()];
        let mut remaining = state_done.len() + action_done.len() + promise_done.len();
        let mut current = root;
        while remaining > 0 {
            let count_at_start = remaining;
            loop {
                for (slot, &position) in model.infinitely_often_states.iter().enumerate() {
                    if !state_done[slot] && self.state_result(current, position) {
                        state_done[slot] = true;
                        remaining -= 1;
                    }
                }
                for (position, done) in promise_done.iter_mut().enumerate() {
                    if !*done && self.is_fulfilled(current, position) {
                        *done = true;
                        remaining -= 1;
                    }
                }
                if remaining == 0 {
                    break;
                }
                let mut last = None;
                let mut unvisited = None;
                let count_before_actions = remaining;
                let mut taken = None;
                for (edge, &next) in behavior.successors(current).iter().enumerate() {
                    if members_by_state.contains_key(&behavior.node_states[next as usize]) {
                        if !self.is_member(next) || !self.is_allowed(current, edge) {
                            continue;
                        }
                        last = Some(next);
                        for (slot, &position) in model.infinitely_often_actions.iter().enumerate() {
                            if !action_done[slot] && self.is_action(current, edge, position) {
                                action_done[slot] = true;
                                remaining -= 1;
                            }
                        }
                    }
                    if remaining < count_before_actions {
                        taken = Some(next);
                        break;
                    }
                    if self.is_member(next) && !seen.contains(&next) {
                        unvisited = Some(next);
                    }
                }
                if let Some(next) = taken {
                    cycle_stack.push(current);
                    current = next;
                    seen.clear();
                    break;
                }
                if remaining < count_at_start {
                    cycle_stack.push(current);
                    current = last.ok_or_else(failed)?;
                    seen.clear();
                    break;
                }
                while unvisited.is_none() {
                    let previous = cycle_stack.pop().ok_or_else(failed)?;
                    current = previous;
                    unvisited = behavior
                        .successors(previous)
                        .iter()
                        .copied()
                        .find(|&next| self.is_member(next) && !seen.contains(&next));
                }
                let next = unvisited.ok_or_else(failed)?;
                cycle_stack.push(current);
                current = next;
                seen.insert(next);
            }
        }
        let mut postfix = self.closing_path(root, current, members_by_state)?;
        for &node in cycle_stack.iter().rev() {
            let state = behavior.node_states[node as usize];
            if postfix.last() != Some(&state) {
                postfix.push(state);
            }
        }
        let cycle_state = *prefix.last().ok_or_else(failed)?;
        if postfix.last() == Some(&cycle_state) {
            postfix.pop();
        }
        let mut cycle = vec![cycle_state];
        cycle.extend(postfix.iter().rev());
        Ok((prefix[..prefix.len() - 1].to_vec(), cycle))
    }

    // TLC's LiveWorker#bfsPostFix, the states from the walk's end back to the root, last first.
    fn closing_path(
        &self,
        root: u32,
        end: u32,
        members_by_state: &IntegerMap<u32, Vec<u32>>,
    ) -> Result<Vec<u32>, Declined> {
        if end == root {
            return Ok(Vec::new());
        }
        let behavior = self.behavior;
        let start = behavior.node_states[end as usize];
        let mut parents: IntegerMap<u32, u32> = IntegerMap::default();
        let mut seen: HashSet<u32> = HashSet::from([start]);
        let mut queue: Vec<(u32, u32)> = Vec::new();
        let (mut state, mut parent) = (start, NO_NODE);
        let mut position = 0;
        loop {
            for &node in members_by_state.get(&state).map_or(&[][..], Vec::as_slice) {
                for (edge, &next) in behavior.successors(node).iter().enumerate() {
                    if next == node || !self.is_allowed(node, edge) {
                        continue;
                    }
                    if next == root {
                        let mut path = Vec::new();
                        let (mut item, mut item_parent) = (state, parent);
                        while item != start {
                            path.push(item);
                            item = item_parent;
                            item_parent = parents.get(&item).copied().unwrap_or(NO_NODE);
                        }
                        path.push(start);
                        return Ok(path);
                    }
                    let next_state = behavior.node_states[next as usize];
                    if !members_by_state.contains_key(&next_state) || !seen.insert(next_state) {
                        continue;
                    }
                    queue.push((next_state, state));
                }
            }
            parents.insert(state, parent);
            (state, parent) = *queue
                .get(position)
                .ok_or_else(|| Declined::from("a liveness counterexample TLC failed to build"))?;
            position += 1;
        }
    }

    // TLC's LiveWorker#checkSccs, a Tarjan search that pushes every successor of a node at once.
    fn find_lasso(mut self) -> Result<Option<Lasso>, Declined> {
        let behavior = self.behavior;
        let mut queue: Vec<u32> = behavior
            .initial
            .iter()
            .copied()
            .filter(|&node| behavior.is_written(node))
            .collect();
        let mut stack: Vec<i64> = Vec::new();
        let mut position = 0;
        while position < queue.len() {
            stack.extend([i64::from(queue[position]), UNVISITED, 0]);
            position += 1;
            let mut counter: i64 = 0;
            while stack.len() >= 3 {
                let low_link = stack.pop().unwrap_or(0);
                let location = stack.pop().unwrap_or(0);
                let node = stack.pop().unwrap_or(0) as u32;
                if location == SCC_MARKER {
                    if self.links[node as usize] == low_link
                        && let Some(lasso) = self.check_component(node)?
                    {
                        return Ok(Some(lasso));
                    }
                    let below = stack.pop().unwrap_or(low_link);
                    stack.push(below.min(low_link));
                    continue;
                }
                if self.links[node as usize] != UNVISITED {
                    stack.push(low_link.min(self.links[node as usize]));
                    continue;
                }
                self.links[node as usize] = counter;
                stack.extend([low_link, i64::from(node), SCC_MARKER]);
                self.components.push(node);
                let mut next_low_link = counter;
                counter += 1;
                for (edge, &next) in behavior.successors(node).iter().enumerate() {
                    if !behavior.is_written(next) {
                        continue;
                    }
                    if !self.is_allowed(node, edge) {
                        if self.links[next as usize] == UNVISITED {
                            queue.push(next);
                        }
                        continue;
                    }
                    if self.links[next as usize] == UNVISITED {
                        stack.extend([i64::from(next), UNVISITED]);
                    } else {
                        next_low_link = next_low_link.min(self.links[next as usize]);
                    }
                }
                stack.push(next_low_link);
            }
            stack.clear();
        }
        Ok(None)
    }
}

/// Checks the formula on the search's graph, and names the properties a lasso violates.
/// Builds the behavior graphs, into `events` the evaluations it logged, and searches them.
pub fn check(
    checker: &mut Checker<'_>,
    properties: &[TermId],
    events: &mut Vec<Event>,
) -> Result<Verdict, Declined> {
    let graph = checker.graph;
    for (state, &parent) in graph.parents.iter().enumerate() {
        if parent == -1 {
            checker.add_initial_state(state as u32)?;
        }
    }
    for state in 0..graph.count() as u32 {
        if let Some(path) = checker.add_state(state)? {
            *events = checker.take_events();
            return Ok(Verdict::Accepted { state, path });
        }
    }
    *events = checker.take_events();
    Ok(match checker.find_violation()? {
        Some((path, loop_start, is_cycle_constrained)) => Verdict::Lasso {
            violated: checker.violated(properties, &path, loop_start)?,
            path,
            loop_start,
            is_cycle_constrained,
        },
        None => Verdict::Holds,
    })
}
