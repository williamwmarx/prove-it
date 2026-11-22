//! TLC's behavior graphs and its search of them (`liveness-checker.ts`): a graph per solution of
//! the formula, a node per state or per state and tableau node, built state by state in the order
//! of the search with each state's successors in the order of TLC's `SetOfStates`, then TLC's
//! `LiveWorker#checkSccs` and `printTrace` on each.

use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet};
use std::hash::{BuildHasherDefault, Hasher};
use std::sync::Arc;

pub(crate) mod trace;

use crate::tableau::{Kind, Model, Solution, Tableau, TermId, Terms};
use crate::{Answers, Declined, Event, Graph, Slot, Source, Unanswered, Verdict};

const NO_NODE: u32 = u32::MAX;
/// The most words of a state's row of consistency the checker reads from the tables: tableaux of
/// up to 256 nodes.
const READ_WORDS: usize = 4;
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

/// A check's value without its step: known, read from the step, or not answered in the tables.
#[derive(Clone, Copy)]
enum Partial {
    Known(bool),
    Stepped,
    Unknown,
}

/// Buffers kept between the states the checker adds, so that adding one allocates nothing.
#[derive(Default)]
struct Scratch {
    consistency: Vec<u64>,
    successors: Vec<u32>,
    targets: Vec<u32>,
    steps: Vec<u32>,
    rows: Vec<u32>,
    order: Vec<u32>,
}

/// What checkers that share the behaviors between threads read ahead, on every thread: the action
/// checks' results the tables answer on each step of the graph, by its position, and the order
/// of each state's successor set.
struct Shared {
    steps: StepResults,
    orders: Orders,
}

/// Each expanded state's successor set in TLC's order, as positions among its entries: its steps
/// in the order generated, then its stuttering step. TLC's SetOfStates orders a set by a capacity
/// that grows with every set that outgrows it, which a scan of the sets' sizes finds ahead of
/// building them, so that threads build the sets, each a run of states.
#[derive(Default)]
struct Orders {
    offsets: Vec<usize>,
    positions: Vec<u32>,
}

impl Orders {
    fn of(&self, state: u32) -> &[u32] {
        &self.positions[self.offsets[state as usize]..self.offsets[state as usize + 1]]
    }
}

/// What the tables answer of a behavior's state checks and of each state's consistency with its
/// tableau's nodes, read ahead on threads for the states in order.
#[derive(Default)]
struct StateReads {
    results: Vec<u8>,
    is_checked: Vec<bool>,
    consistency: Vec<u64>,
    is_read: Vec<bool>,
}

/// The results of the action checks on each step, a row of bits per step by the checks' ids:
/// whether each was checked, and what it found. A row takes the checks' count rounded up to a
/// power of two, so that one of up to 64 checks lies in one word, or else whole words.
#[derive(Default)]
struct StepResults {
    stride: usize,
    count: usize,
    checked: Vec<u64>,
    values: Vec<u64>,
}

impl StepResults {
    fn new(checks: usize) -> Self {
        Self {
            stride: if checks > 64 {
                checks.div_ceil(64) * 64
            } else {
                checks.next_power_of_two()
            },
            ..Self::default()
        }
    }

    /// Adds rows for `count` steps, and returns the first.
    fn add(&mut self, count: usize) -> usize {
        let first = self.count;
        self.count += count;
        let length = (self.count * self.stride).div_ceil(64);
        self.checked.resize(length, 0);
        self.values.resize(length, 0);
        first
    }

    fn is_checked(&self, row: usize, id: usize) -> bool {
        let bit = row * self.stride + id;
        self.checked[bit / 64] >> (bit % 64) & 1 == 1
    }

    fn set(&mut self, row: usize, id: usize, value: bool) {
        let bit = row * self.stride + id;
        self.checked[bit / 64] |= 1 << (bit % 64);
        self.values[bit / 64] |= u64::from(value) << (bit % 64);
    }

    fn value(&self, row: usize, id: usize) -> bool {
        let bit = row * self.stride + id;
        self.values[bit / 64] >> (bit % 64) & 1 == 1
    }

    /// A word of a row's results, as a mask from `mask` reads it.
    fn word(&self, row: usize, word: usize) -> u64 {
        Self::word_of(&self.values, self.stride, row, word)
    }

    /// Whether a row has every check a mask from `mask` names.
    fn is_complete(&self, row: usize, mask: &[u64]) -> bool {
        mask.iter().enumerate().all(|(word, &mask)| {
            mask == 0 || Self::word_of(&self.checked, self.stride, row, word) & mask == mask
        })
    }

    fn word_of(bits: &[u64], stride: usize, row: usize, word: usize) -> u64 {
        let bit = row * stride;
        if stride >= 64 {
            bits[bit / 64 + word]
        } else {
            bits[bit / 64] >> (bit % 64) & ((1 << stride) - 1)
        }
    }

    /// Copies a row of another's, of the same width, into a row of this one's that has nothing
    /// set.
    fn copy_row(&mut self, row: usize, from: &StepResults, from_row: usize) {
        let (bit, from_bit) = (row * self.stride, from_row * from.stride);
        if self.stride >= 64 {
            let words = self.stride / 64;
            for word in 0..words {
                self.checked[bit / 64 + word] = from.checked[from_bit / 64 + word];
                self.values[bit / 64 + word] = from.values[from_bit / 64 + word];
            }
            return;
        }
        let mask = (1 << self.stride) - 1;
        let read = |words: &[u64]| words[from_bit / 64] >> (from_bit % 64) & mask;
        self.checked[bit / 64] |= read(&from.checked) << (bit % 64);
        self.values[bit / 64] |= read(&from.values) << (bit % 64);
    }

    /// Copies every row of another's, of the same width, into the rows from `row` on, which have
    /// nothing set: whole words at a time, each shifted to where the rows start.
    fn copy_rows(&mut self, row: usize, from: &StepResults) {
        let (start, length) = (row * self.stride, from.count * from.stride);
        let (first, shift) = (start / 64, start % 64);
        let words = length.div_ceil(64);
        let copy = |into: &mut [u64], bits: &[u64]| {
            for (at, &word) in bits[..words].iter().enumerate() {
                let word = if at + 1 == words && length % 64 != 0 {
                    word & ((1 << (length % 64)) - 1)
                } else {
                    word
                };
                into[first + at] |= word << shift;
                if shift != 0 && word >> (64 - shift) != 0 {
                    into[first + at + 1] |= word >> (64 - shift);
                }
            }
        };
        copy(&mut self.checked, &from.checked);
        copy(&mut self.values, &from.values);
    }

    fn mask(&self, ids: impl Iterator<Item = usize>) -> Vec<u64> {
        let mut mask = vec![0; self.stride.div_ceil(64)];
        for id in ids {
            mask[id / 64] |= 1 << (id % 64);
        }
        mask
    }
}

/// A counterexample's states: the prefix, then the cycle.
type Lasso = (Vec<u32>, Vec<u32>);

/// A lasso's states, where its cycle starts, and whether its solution constrains the cycle.
type Violation = (Vec<u32>, usize, bool);

/// The stack of a thread that builds behavior graphs, whose late nodes it adds by recursion:
/// reserved, not committed, as the engine's search thread.
const STACK_BYTES: usize = 256 * 1024 * 1024;

type IntegerMap<Key, Value> = HashMap<Key, Value, BuildHasherDefault<IntegerHasher>>;

/// A step of the search: a successor of a state, the state the step reached (the successor itself
/// unless SYMMETRY or a VIEW told it apart from the state stored for it), and where the engine
/// answers the actions of the step.
#[derive(Clone, Copy)]
struct Step {
    target: u32,
    real: u32,
    slot: Slot,
}

struct Behavior {
    solution: usize,
    /// One id per distinct action check across the solutions.
    action_ids: Vec<usize>,
    /// The action checks as a mask of a row of `StepResults`.
    action_mask: Vec<u64>,
    node_states: Vec<u32>,
    node_tableaux: Vec<u32>,
    edge_starts: Vec<usize>,
    edge_counts: Vec<u32>,
    edge_targets: Vec<u32>,
    edge_steps: Vec<u32>,
    state_results: Vec<u8>,
    /// Whether a state's checks were read ahead into `state_results`.
    state_checked: Vec<bool>,
    /// Whether the behaviors before this one have every action check of this one.
    is_covered: bool,
    consistency: Vec<u8>,
    /// Each state's consistency with the tableau's nodes as the tables answer it, a row of
    /// `words` words of bits by node, where `is_read` says the state has its row.
    read_consistency: Vec<u64>,
    is_read: Vec<bool>,
    initial: Vec<u32>,
    first_nodes: Vec<u32>,
    last_nodes: Vec<u32>,
    next_siblings: Vec<u32>,
    /// The state each late node reached, where it isn't the state stored for the node.
    node_reals: IntegerMap<u32, u32>,
    is_done: Vec<bool>,
    /// TLC's `AbstractDiskGraph#size`: the states its node table has a key for. A graph without
    /// a tableau has those of the nodes written, the states added; one with a tableau has those
    /// done and those with a node recorded, such as a successor still to expand.
    size: usize,
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
        let state = state as usize;
        if self.last_nodes.len() <= state {
            self.last_nodes.resize(state + 1, NO_NODE);
            self.first_nodes.resize(state + 1, NO_NODE);
        }
        if self.last_nodes[state] == NO_NODE && !self.is_done.get(state).is_some_and(|&done| done) {
            self.size += 1;
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

pub struct Checker {
    terms: Terms,
    solutions: Vec<Solution>,
    behaviors: Vec<Behavior>,
    /// The action checks' results on the steps this checker checked itself, in the rows after
    /// the shared table's.
    steps: StepResults,
    /// Each action check, by its id.
    action_terms: Vec<TermId>,
    /// What a checker that shares the behaviors with others reads rather than computes again:
    /// a step's row of action checks is its position in the shared table where that has every
    /// check `needed` names, and the successor sets come in their order.
    shared: Option<Arc<Shared>>,
    /// Every action check of the behaviors this checker builds, as a mask of a row.
    needed: Vec<u64>,
    /// TLC's SetOfStates grows its capacity with every set that outgrows it.
    capacity_multiplier: usize,
    slots: Vec<u32>,
    scratch: Scratch,
    is_cycle_constrained: Vec<bool>,
    /// Where an atom's evaluation has effects, which TLC has each time it evaluates the atom: the
    /// checks keep no results across evaluations and log each evaluation of an atom.
    effects: RefCell<Option<Effects>>,
    /// TLC's diameter as it evaluates, for the atoms that read it.
    diameter: Cell<u32>,
    /// The state being added, with whether as an initial state, and the first atom found
    /// unanswered while adding one.
    adding: Cell<Option<(u32, bool)>>,
    /// The edge of the step that reached the state the checker checks against a tableau node, as
    /// TLC checks a successor, whose level is one past its source's.
    reached: Cell<Option<u32>>,
    pub(crate) unanswered: Cell<Option<Unanswered>>,
    /// The position among all the behaviors of each this checker builds, which a checker that
    /// shares them with others builds only some of.
    global: Vec<usize>,
    /// Where adding the states got to, in TLC's order: whether past the initial states, the
    /// state, and the behavior.
    at: Cell<(bool, u32, usize)>,
}

/// The evaluations of atoms so far, and the atoms' answers within the evaluation of one check, as
/// `evaluateLive`'s cache keeps them.
#[derive(Default)]
struct Effects {
    events: Vec<Event>,
    known: Vec<(u32, bool)>,
}

impl Checker {
    pub fn new(mut terms: Terms, formula: TermId) -> Result<Self, Declined> {
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
            let is_covered = is_covered(&behaviors, &ids);
            behaviors.push(Behavior {
                solution: position,
                action_mask: Vec::new(),
                action_ids: ids,
                node_states: Vec::new(),
                node_tableaux: Vec::new(),
                edge_starts: Vec::new(),
                edge_counts: Vec::new(),
                edge_targets: Vec::new(),
                edge_steps: Vec::new(),
                state_results: Vec::new(),
                state_checked: Vec::new(),
                is_covered,
                consistency: Vec::new(),
                read_consistency: Vec::new(),
                is_read: Vec::new(),
                initial: Vec::new(),
                first_nodes: Vec::new(),
                last_nodes: Vec::new(),
                next_siblings: Vec::new(),
                node_reals: IntegerMap::default(),
                is_done: Vec::new(),
                size: 0,
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
        let global = (0..behaviors.len()).collect();
        let steps = StepResults::new(action_ids.len());
        for behavior in &mut behaviors {
            behavior.action_mask = steps.mask(behavior.action_ids.iter().copied());
        }
        let needed = steps.mask(0..action_ids.len());
        Ok(Self {
            terms,
            solutions,
            behaviors,
            steps,
            action_terms: {
                let mut terms = vec![0; action_ids.len()];
                for (&term, &id) in &action_ids {
                    terms[id] = term;
                }
                terms
            },
            shared: None,
            needed,
            capacity_multiplier: 1,
            slots: Vec::new(),
            scratch: Scratch::default(),
            is_cycle_constrained,
            effects: RefCell::new(None),
            diameter: Cell::new(1),
            adding: Cell::new(None),
            reached: Cell::new(None),
            unanswered: Cell::new(None),
            global,
            at: Cell::new((false, 0, 0)),
        })
    }

    // --- evaluation: `evaluateLive` over the engine's answers ---

    fn answer(&self, source: &Source<'_>, atom: u32, slot: Slot) -> Result<bool, Declined> {
        let answer = source.answers.answer(atom, slot, self.diameter.get());
        if answer.is_err()
            && let Some((state, is_initial)) = self.adding.get()
            && self.unanswered.get().is_none()
        {
            self.unanswered.set(Some(Unanswered {
                state,
                atom,
                slot: source.answers.position(atom, slot, self.diameter.get()) as u32,
                is_initial,
            }));
        }
        answer
    }

    fn evaluate(
        &self,
        source: &Source<'_>,
        term: TermId,
        state: u32,
        step: Option<Step>,
    ) -> Result<bool, Declined> {
        match self.terms.kind(term) {
            Kind::Boolean(value) => Ok(value),
            Kind::State(atom) | Kind::Enabled(atom) => {
                let mut effects = self.effects.borrow_mut();
                let slot = match self.reached.get() {
                    Some(edge) => Slot::Reached { state, edge },
                    None => Slot::State(state),
                };
                let Some(effects) = effects.as_mut() else {
                    return self.answer(source, atom, slot);
                };
                if let Some(&(_, known)) = effects.known.iter().find(|known| known.0 == atom) {
                    return Ok(known);
                }
                let answer = self.answer(source, atom, slot)?;
                effects.events.push(Event::Atom {
                    atom,
                    slot: source.answers.position(atom, slot, self.diameter.get()),
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
                let answer = self.answer(source, atom, step.slot)?;
                effects.events.push(Event::Atom {
                    atom,
                    slot: source
                        .answers
                        .position(atom, step.slot, self.diameter.get()),
                });
                Ok(answer)
            }
            Kind::Action { atom, enabled } => {
                if enabled.is_some_and(|enabled| source.answers.is_disabled(enabled, state)) {
                    return Ok(false);
                }
                let step = step.ok_or_else(|| Declined::from("an action without a step"))?;
                self.answer(source, atom, step.slot)
            }
            Kind::Not => Ok(!self.evaluate(source, self.terms.body(term), state, step)?),
            Kind::And => {
                for &operand in self.terms.children(term) {
                    if !self.evaluate(source, operand, state, step)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Kind::Or => {
                for &operand in self.terms.children(term) {
                    if self.evaluate(source, operand, state, step)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            Kind::Next => {
                let outer = self.start_evaluation();
                let result = self.evaluate(
                    source,
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

    /// A check's value: read straight from the answer tables where nothing is logged and every
    /// atom it reads has an answer, and otherwise as `evaluate` finds it.
    fn evaluate_check(
        &self,
        source: &Source<'_>,
        term: TermId,
        state: u32,
        step: Option<Step>,
    ) -> Result<bool, Declined> {
        if !self.is_effectful()
            && let Some(tables) = source.answers.tables()
            && let Some(value) = self.read(tables, source.graph, term, state, step)
        {
            return Ok(value);
        }
        self.evaluate(source, term, state, step)
    }

    fn read(
        &self,
        tables: &[Option<&[u8]>],
        graph: &Graph<'_>,
        term: TermId,
        state: u32,
        step: Option<Step>,
    ) -> Option<bool> {
        read(&self.terms, tables, graph, term, state, step)
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

    /// The evaluations logged so far, which the log goes on from.
    pub fn drain_events(&mut self) -> Vec<Event> {
        self.effects
            .get_mut()
            .as_mut()
            .map(|effects| std::mem::take(&mut effects.events))
            .unwrap_or_default()
    }

    /// Whether TLC evaluates an atom as it adds an initial state: a state predicate of an initial
    /// node of a tableau.
    pub fn asks_initial_states(&self) -> bool {
        self.solutions
            .iter()
            .filter_map(|solution| solution.tableau.as_ref())
            .any(|tableau| {
                tableau.nodes[..tableau.initial_count]
                    .iter()
                    .any(|node| !node.state_predicates.is_empty())
            })
    }

    /// Adds an initial state, or a state the search expanded, naming the first atom left
    /// unanswered as `add_states` does.
    pub fn add_one(
        &mut self,
        source: &Source<'_>,
        state: u32,
        is_initial: bool,
    ) -> Result<Option<Vec<u32>>, Declined> {
        self.adding.set(Some((state, is_initial)));
        let added = if is_initial {
            self.add_initial_state(source, state).map(|()| None)
        } else {
            self.add_state(source, state)
        };
        self.adding.set(None);
        added
    }

    /// The evaluations logged, which ends the log.
    pub fn take_events(&mut self) -> Vec<Event> {
        self.effects
            .get_mut()
            .take()
            .map(|effects| effects.events)
            .unwrap_or_default()
    }

    fn self_step(state: u32, real: u32) -> Step {
        Step {
            target: state,
            real,
            slot: Slot::Stutter(real),
        }
    }

    fn edge_step(source: &Source<'_>, state: u32, edge: usize) -> Step {
        edge_step(source.graph, state, edge)
    }

    // --- the rows of the action checks' results: the shared table's, then this checker's ---

    fn shared_rows(&self) -> usize {
        self.shared.as_ref().map_or(0, |shared| shared.steps.count)
    }

    fn add_steps(&mut self, count: usize) -> usize {
        self.shared_rows() + self.steps.add(count)
    }

    fn is_step_complete(&self, row: usize, mask: &[u64]) -> bool {
        match &self.shared {
            Some(shared) if row < shared.steps.count => shared.steps.is_complete(row, mask),
            _ => self.steps.is_complete(row - self.shared_rows(), mask),
        }
    }

    fn step_value(&self, row: usize, id: usize) -> bool {
        match &self.shared {
            Some(shared) if row < shared.steps.count => shared.steps.value(row, id),
            _ => self.steps.value(row - self.shared_rows(), id),
        }
    }

    fn step_word(&self, row: usize, word: usize) -> u64 {
        match &self.shared {
            Some(shared) if row < shared.steps.count => shared.steps.word(row, word),
            _ => self.steps.word(row - self.shared_rows(), word),
        }
    }

    /// The rows of a successor set's steps, in `rows`: the shared table's where it has every
    /// check this checker's behaviors make, and otherwise rows of this checker's own, copied from
    /// the shared table's for the checks to fill in.
    fn share_rows(&mut self, graph: &Graph<'_>, set: &[Step], rows: &mut Vec<u32>) {
        let Self {
            shared,
            steps,
            needed,
            ..
        } = self;
        let Some(shared) = shared
            .as_ref()
            .map(|shared| &shared.steps)
            .filter(|shared| shared.count > 0)
        else {
            let first = steps.add(set.len());
            rows.extend((first..first + set.len()).map(|row| row as u32));
            return;
        };
        for step in set {
            let position = graph.position(step.slot);
            if shared.is_complete(position, needed) {
                rows.push(position as u32);
                continue;
            }
            let row = steps.add(1);
            steps.copy_row(row, shared, position);
            rows.push((shared.count + row) as u32);
        }
    }

    fn check_step(
        &mut self,
        source: &Source<'_>,
        behavior: usize,
        state: u32,
        step: Step,
        row: usize,
    ) -> Result<(), Declined> {
        // A shared row has every check the behaviors make.
        let Some(row) = row.checked_sub(self.shared_rows()) else {
            return Ok(());
        };
        let solution = &self.solutions[self.behaviors[behavior].solution];
        for (position, &check) in solution.action_checks.iter().enumerate() {
            let id = self.behaviors[behavior].action_ids[position];
            if self.steps.is_checked(row, id) {
                continue;
            }
            self.start_evaluation();
            let value = self.evaluate_check(source, check, state, Some(step))?;
            self.steps.set(row, id, value);
        }
        Ok(())
    }

    // The action checks on each step of a successor set, in its `rows`, where the rows don't
    // have them all: each check's part that reads only the state once for all the steps, where
    // the tables answer it.
    fn check_steps(
        &mut self,
        source: &Source<'_>,
        behavior: usize,
        state: u32,
        set: &[Step],
        rows: &[u32],
    ) -> Result<(), Declined> {
        if !self.is_effectful() {
            let mask = &self.behaviors[behavior].action_mask;
            if rows
                .iter()
                .all(|&row| self.is_step_complete(row as usize, mask))
            {
                return Ok(());
            }
            if let Some(tables) = source.answers.tables()
                && self.read_steps(tables, source.graph, behavior, state, set, rows)
            {
                return Ok(());
            }
        }
        for (&step, &row) in set.iter().zip(rows) {
            self.check_step(source, behavior, state, step, row as usize)?;
        }
        Ok(())
    }

    // Fills what the tables answer of the action checks on the steps, and whether they answer all.
    fn read_steps(
        &mut self,
        tables: &[Option<&[u8]>],
        graph: &Graph<'_>,
        behavior: usize,
        state: u32,
        set: &[Step],
        rows: &[u32],
    ) -> bool {
        let shared = self.shared_rows();
        let solution = &self.solutions[self.behaviors[behavior].solution];
        let mut is_complete = true;
        for (position, &check) in solution.action_checks.iter().enumerate() {
            let id = self.behaviors[behavior].action_ids[position];
            let partial = self.read_partially(tables, check, state);
            for (&step, &row) in set.iter().zip(rows) {
                // A shared row has every check the behaviors make.
                let Some(row) = (row as usize).checked_sub(shared) else {
                    continue;
                };
                if self.steps.is_checked(row, id) {
                    continue;
                }
                let value = match partial {
                    Partial::Known(value) => Some(value),
                    Partial::Stepped => self.read(tables, graph, check, state, Some(step)),
                    Partial::Unknown => None,
                };
                match value {
                    Some(value) => self.steps.set(row, id, value),
                    None => is_complete = false,
                }
            }
        }
        is_complete
    }

    fn read_partially(&self, tables: &[Option<&[u8]>], term: TermId, state: u32) -> Partial {
        read_partially(&self.terms, tables, term, state)
    }

    fn check_action(
        &mut self,
        source: &Source<'_>,
        behavior: usize,
        state: u32,
        step: Step,
    ) -> Result<u32, Declined> {
        let row = self.add_steps(1);
        self.check_step(source, behavior, state, step, row)?;
        Ok(row as u32)
    }

    // The state checks of a state the search reached, kept for the nodes of the state it reached.
    fn check_state(
        &mut self,
        source: &Source<'_>,
        behavior: usize,
        real: u32,
    ) -> Result<(), Declined> {
        if self.behaviors[behavior].state_checked.get(real as usize) == Some(&true) {
            return Ok(());
        }
        let solution = &self.solutions[self.behaviors[behavior].solution];
        let count = solution.state_checks.len();
        let offset = real as usize * count;
        let results: Vec<u8> = solution
            .state_checks
            .iter()
            .map(|&check| {
                self.start_evaluation();
                self.evaluate_check(source, check, real, None).map(u8::from)
            })
            .collect::<Result<_, _>>()?;
        let stored = &mut self.behaviors[behavior].state_results;
        if stored.len() < offset + count {
            stored.resize(offset + count, 0);
        }
        stored[offset..offset + count].copy_from_slice(&results);
        Ok(())
    }

    /// The atoms `add_initial_state` may read: those under the state predicates of each tableau's
    /// initial nodes.
    pub(crate) fn initially_read(&self) -> Vec<u32> {
        let mut atoms = Vec::new();
        let mut pending: Vec<TermId> = (0..self.behaviors.len())
            .filter_map(|behavior| self.tableau(behavior))
            .flat_map(|tableau| {
                tableau.nodes[..tableau.initial_count]
                    .iter()
                    .flat_map(|node| node.state_predicates.iter().copied())
            })
            .collect();
        while let Some(term) = pending.pop() {
            match self.terms.kind(term) {
                Kind::State(atom) | Kind::Enabled(atom) => atoms.push(atom),
                Kind::Action { atom, enabled } => {
                    atoms.extend([Some(atom), enabled].into_iter().flatten())
                }
                _ => pending.extend_from_slice(self.terms.children(term)),
            }
        }
        atoms.sort_unstable();
        atoms.dedup();
        atoms
    }

    fn tableau(&self, behavior: usize) -> Option<&Tableau> {
        self.solutions[self.behaviors[behavior].solution]
            .tableau
            .as_ref()
    }

    // Whether the state a step reached is consistent with a tableau node, at the step: TLC checks
    // the successor it generated, whose level is one past its source's, where the step is to
    // another state, and the state itself for its stuttering step.
    fn is_reached_consistent(
        &mut self,
        source: &Source<'_>,
        behavior: usize,
        node: u32,
        step: &Step,
    ) -> Result<bool, Declined> {
        let edge = match step.slot {
            Slot::Step { edge, .. } => Some(edge),
            _ => None,
        };
        self.reached.set(edge);
        let consistent = self.is_consistent(source, behavior, node, step.real);
        self.reached.set(None);
        consistent
    }

    // Whether a reached state is consistent with a tableau node.
    fn is_consistent(
        &mut self,
        source: &Source<'_>,
        behavior: usize,
        node: u32,
        state: u32,
    ) -> Result<bool, Declined> {
        let Some(tableau) = self.tableau(behavior) else {
            return Ok(true);
        };
        let slot = state as usize * tableau.nodes.len() + node as usize;
        // TLC evaluates each time, which keeping nothing matches where an atom has effects or
        // reads TLC's diameter, which grows as the states are added, or the level, which is the
        // step's that reached the state.
        let is_effectful = self.is_effectful()
            || source.graph.diameters.is_some()
            || source.graph.levels.is_some();
        if !is_effectful
            && let Some(&known) = self.behaviors[behavior].consistency.get(slot)
            && known != UNKNOWN_RESULT
        {
            return Ok(known == KNOWN_TRUE);
        }
        self.start_evaluation();
        let mut is_held = true;
        for &predicate in &tableau.nodes[node as usize].state_predicates {
            if !self.evaluate_check(source, predicate, state, None)? {
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

    // Reads a state's row of consistency from the tables, where they answer every node's
    // predicates, and whether they did.
    fn read_consistency(
        &mut self,
        tables: &[Option<&[u8]>],
        graph: &Graph<'_>,
        behavior: usize,
        state: u32,
        words: usize,
    ) -> bool {
        let index = state as usize;
        if self.behaviors[behavior].is_read.get(index) == Some(&true) {
            return true;
        }
        let Some(tableau) = self.tableau(behavior) else {
            return false;
        };
        let Some(row) = read_consistency_row(&self.terms, tables, graph, tableau, state, words)
        else {
            return false;
        };
        let behavior = &mut self.behaviors[behavior];
        if behavior.is_read.len() <= index {
            behavior.is_read.resize(index + 1, false);
            behavior.read_consistency.resize((index + 1) * words, 0);
        }
        behavior.is_read[index] = true;
        behavior.read_consistency[index * words..(index + 1) * words]
            .copy_from_slice(&row[..words]);
        true
    }

    fn tableau_size(&self, behavior: usize) -> usize {
        self.tableau(behavior)
            .map_or(0, |tableau| tableau.nodes.len())
    }

    fn is_done(&self, behavior: usize, state: u32) -> bool {
        self.behaviors[behavior]
            .is_done
            .get(state as usize)
            .copied()
            .unwrap_or(false)
    }

    fn set_done(&mut self, behavior: usize, state: u32) {
        let graph = &mut self.behaviors[behavior];
        let index = state as usize;
        if graph.is_done.len() <= index {
            graph.is_done.resize(index + 1, false);
        }
        if !graph.is_done[index]
            && graph
                .last_nodes
                .get(index)
                .is_none_or(|&last| last == NO_NODE)
        {
            graph.size += 1;
        }
        graph.is_done[index] = true;
    }

    fn is_accepting(&self, behavior: usize, node: u32) -> bool {
        let Some(tableau) = self.tableau(behavior) else {
            return false;
        };
        let tableau_node = &tableau.nodes[node as usize];
        tableau_node.particle.is_empty() && tableau_node.successors == [node]
    }

    // Whether a state may reach a tableau node that accepts every behavior, which TLC stops at as
    // it adds the state: one with no particle that leads only to itself, of a solution with a
    // model that asks nothing of the cycle.
    fn may_accept(&self) -> bool {
        (0..self.behaviors.len()).any(|behavior| {
            self.has_empty_model(behavior)
                && (0..self.tableau_size(behavior) as u32)
                    .any(|node| self.is_accepting(behavior, node))
        })
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

    // The node of a state and tableau node, among the state's nodes, which are few.
    fn node_id(&self, behavior: usize, state: u32, tableau_node: u32) -> Option<u32> {
        let graph = &self.behaviors[behavior];
        let mut node = *graph.first_nodes.get(state as usize)?;
        while node != NO_NODE && graph.node_tableaux[node as usize] != tableau_node {
            node = graph.next_siblings[node as usize];
        }
        (node != NO_NODE).then_some(node)
    }

    // --- building the graphs: TLC's TableauLiveChecker and LiveChecker ---

    /// TLC collects a state's successors and the state itself in a SetOfStates, a hash set it
    /// iterates in slot order, keyed by the states' fingerprints.
    fn successor_set(&mut self, source: &Source<'_>, state: u32) -> Vec<Step> {
        let graph = source.graph;
        let start = graph.edge_offsets[state as usize] as usize;
        let end = graph.edge_offsets[state as usize + 1] as usize;
        let step = |position: u32| {
            if position as usize == end - start {
                Self::self_step(state, state)
            } else {
                Self::edge_step(source, state, start + position as usize)
            }
        };
        if let Some(shared) = &self.shared {
            return shared
                .orders
                .of(state)
                .iter()
                .map(|&position| step(position))
                .collect();
        }
        let entries: Vec<(u32, u32)> = (start..end)
            .map(|edge| {
                let step = Self::edge_step(source, state, edge);
                (step.target, step.real)
            })
            .chain([(state, state)])
            .collect();
        let mut order = std::mem::take(&mut self.scratch.order);
        if slot_order(
            &entries,
            graph.fingerprints,
            self.capacity_multiplier,
            &mut self.slots,
            &mut order,
        ) {
            self.capacity_multiplier += 1;
        }
        let set = order.iter().map(|&position| step(position)).collect();
        self.scratch.order = order;
        set
    }

    fn add_initial_state(&mut self, source: &Source<'_>, state: u32) -> Result<(), Declined> {
        self.log(Event::Initial(state));
        self.diameter.set(1);
        for behavior in 0..self.behaviors.len() {
            self.at.set((false, state, self.global[behavior]));
            let Some(initial_count) = self.tableau(behavior).map(|tableau| tableau.initial_count)
            else {
                self.behaviors[behavior].initial.push(state);
                continue;
            };
            for node in 0..initial_count as u32 {
                if !self.is_consistent(source, behavior, node, state)? {
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
    fn add_state(&mut self, source: &Source<'_>, state: u32) -> Result<Option<Vec<u32>>, Declined> {
        self.log(Event::Expanded(state));
        if let Some(diameters) = &source.graph.diameters {
            self.diameter.set(diameters.states[state as usize]);
        }
        let set = self.successor_set(source, state);
        // With effects, each behavior checks its actions on each step anew, as TLC does.
        let is_effectful = self.is_effectful();
        let mut rows = std::mem::take(&mut self.scratch.rows);
        rows.clear();
        if !is_effectful {
            self.share_rows(source.graph, &set, &mut rows);
        }
        let mut found = None;
        for behavior in 0..self.behaviors.len() {
            self.at.set((true, state, self.global[behavior]));
            if is_effectful {
                rows.clear();
                let first = self.add_steps(set.len());
                rows.extend((first..first + set.len()).map(|row| row as u32));
            }
            if is_effectful || !self.behaviors[behavior].is_covered {
                self.check_steps(source, behavior, state, &set, &rows)?;
            }
            self.check_state(source, behavior, state)?;
            if self.tableau(behavior).is_none() {
                self.add_plain_state(behavior, &set, &rows, state);
                continue;
            }
            found = self.add_tableau_state(source, behavior, &set, &rows, state)?;
            if found.is_some() {
                break;
            }
        }
        self.scratch.rows = rows;
        Ok(found)
    }

    fn add_plain_state(&mut self, behavior: usize, set: &[Step], rows: &[u32], state: u32) {
        let behavior = &mut self.behaviors[behavior];
        // A node for the state and each successor, which stays undone until its state is added.
        let last = set.iter().map(|step| step.target).fold(state, u32::max);
        while behavior.node_states.len() <= last as usize {
            let next = behavior.node_states.len() as u32;
            behavior.push_node(next, NO_NODE);
        }
        let mut targets = Vec::with_capacity(set.len());
        let mut steps = Vec::with_capacity(set.len());
        for (step, &row) in set.iter().zip(rows) {
            if behavior.is_written(step.target) && targets.contains(&step.target) {
                continue;
            }
            targets.push(step.target);
            steps.push(row);
        }
        behavior.write_node(state, &targets, &steps);
        behavior.size += 1;
    }

    fn tableau_successors(&self, behavior: usize, node: u32) -> &[u32] {
        let tableau = self.tableau(behavior).expect("a tableau");
        &tableau.nodes[self.behaviors[behavior].node_tableaux[node as usize] as usize].successors
    }

    fn add_tableau_state(
        &mut self,
        source: &Source<'_>,
        behavior: usize,
        set: &[Step],
        rows: &[u32],
        state: u32,
    ) -> Result<Option<Vec<u32>>, Declined> {
        let node_count = self.tableau_size(behavior);
        let words = node_count.div_ceil(64).max(1);
        let mut consistency = std::mem::take(&mut self.scratch.consistency);
        consistency.clear();
        consistency.resize(set.len() * words, 0);
        let tables = source.answers.tables().filter(|_| !self.is_effectful());
        let is_read = tables.is_some_and(|tables| {
            set.iter()
                .all(|step| self.read_consistency(tables, source.graph, behavior, step.real, words))
        });
        if is_read {
            let rows = &self.behaviors[behavior].read_consistency;
            for (position, step) in set.iter().enumerate() {
                let row = step.real as usize * words;
                consistency[position * words..(position + 1) * words]
                    .copy_from_slice(&rows[row..row + words]);
            }
        } else {
            // In TLC's order, which decides the first atom left unanswered.
            for node in 0..node_count {
                for (position, step) in set.iter().enumerate() {
                    if self.is_reached_consistent(source, behavior, node as u32, step)? {
                        consistency[position * words + node / 64] |= 1 << (node % 64);
                    }
                }
            }
        }
        let mut tableau_successors = std::mem::take(&mut self.scratch.successors);
        let mut targets = std::mem::take(&mut self.scratch.targets);
        let mut steps = std::mem::take(&mut self.scratch.steps);
        self.set_done(behavior, state);
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
            tableau_successors.clear();
            tableau_successors.extend_from_slice(self.tableau_successors(behavior, node));
            targets.clear();
            steps.clear();
            for (position, step) in set.iter().enumerate() {
                let is_done = self.is_done(behavior, step.target);
                for &next in &tableau_successors {
                    let next_bit = next as usize;
                    if consistency[position * words + next_bit / 64] >> (next_bit % 64) & 1 == 0 {
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
                    steps.push(rows[position]);
                    if existing.is_none() && is_done {
                        self.expand_late(source, behavior, step.target, step.real, target)?;
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
        self.scratch.consistency = consistency;
        self.scratch.successors = tableau_successors;
        self.scratch.targets = targets;
        self.scratch.steps = steps;
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
        source: &Source<'_>,
        behavior: usize,
        state: u32,
        real: u32,
        node: u32,
    ) -> Result<(), Declined> {
        if real as usize + 1 >= source.graph.edge_offsets.len() {
            return Err(Declined::from(crate::UNEXPANDED));
        }
        // TLC checks a late node at the diameter then, which the checks kept for the state may
        // not have read.
        if let Some(diameters) = &source.graph.diameters
            && diameters.states.get(real as usize) != Some(&self.diameter.get())
        {
            return Err(Declined::from("a late node TLC adds at another diameter"));
        }
        if real != state {
            self.behaviors[behavior].node_reals.insert(node, real);
        }
        self.check_state(source, behavior, real)?;
        let tableau_successors = self.tableau_successors(behavior, node).to_vec();
        let mut targets = Vec::new();
        let mut steps = Vec::new();
        let self_step = if tableau_successors.is_empty() {
            u32::MAX
        } else {
            self.check_action(source, behavior, real, Self::self_step(state, real))?
        };
        for &next in &tableau_successors {
            if !self.is_consistent(source, behavior, next, real)? {
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
                self.expand_late(source, behavior, state, real, target)?;
            }
        }
        self.log(Event::Late(real));
        let start = source.graph.edge_offsets[real as usize] as usize;
        let end = source.graph.edge_offsets[real as usize + 1] as usize;
        for edge in start..end {
            let step = Self::edge_step(source, real, edge);
            let successor_step = self.check_action(source, behavior, real, step)?;
            let is_done = self.is_done(behavior, step.target);
            for &next in &tableau_successors {
                if !self.is_reached_consistent(source, behavior, next, &step)? {
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
                    self.expand_late(source, behavior, step.target, step.real, target)?;
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

    /// The states of the behavior graphs, summed over the branches, which TLC reports as it
    /// checks them (`LiveCheck.check0`).
    pub fn size(&self) -> u64 {
        self.behaviors
            .iter()
            .map(|behavior| behavior.size as u64)
            .sum()
    }

    // The step from one state to another, as the first of the search's steps between them.
    fn step_to(source: &Source<'_>, state: u32, target: u32) -> Result<Step, Declined> {
        if state == target {
            return Ok(Self::self_step(state, state));
        }
        let start = source.graph.edge_offsets[state as usize] as usize;
        let end = source.graph.edge_offsets[state as usize + 1] as usize;
        (start..end)
            .find(|&edge| source.graph.edges[edge] == target)
            .map(|edge| Self::edge_step(source, state, edge))
            .ok_or_else(|| Declined::from("a step the search didn't take"))
    }

    /// Whether a formula holds of the lasso from the position on, as `evaluateOnLasso` finds it.
    fn evaluate_on_lasso(
        &self,
        source: &Source<'_>,
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
            Kind::Not => Ok(!self.evaluate_on_lasso(
                source,
                self.terms.body(term),
                path,
                cycle_start,
                position,
            )?),
            Kind::And => {
                for &operand in self.terms.children(term) {
                    if !self.evaluate_on_lasso(source, operand, path, cycle_start, position)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Kind::Or => {
                for &operand in self.terms.children(term) {
                    if self.evaluate_on_lasso(source, operand, path, cycle_start, position)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            Kind::Next => self.evaluate_on_lasso(
                source,
                self.terms.body(term),
                path,
                cycle_start,
                next(position),
            ),
            Kind::Always => {
                for index in future {
                    if !self.evaluate_on_lasso(
                        source,
                        self.terms.body(term),
                        path,
                        cycle_start,
                        index,
                    )? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Kind::Eventually => {
                for index in future {
                    if self.evaluate_on_lasso(
                        source,
                        self.terms.body(term),
                        path,
                        cycle_start,
                        index,
                    )? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            _ => {
                let state = path[position];
                let step = Self::step_to(source, state, path[next(position)])?;
                // TLC evaluates each atom of a property anew.
                self.start_evaluation();
                self.evaluate(source, term, state, Some(step))
            }
        }
    }

    /// The positions of the properties the lasso violates, in order.
    pub fn violated(
        &self,
        source: &Source<'_>,
        properties: &[TermId],
        path: &[u32],
        loop_start: usize,
    ) -> Result<Vec<usize>, Declined> {
        let mut violated = Vec::new();
        for (position, &property) in properties.iter().enumerate() {
            if !self.evaluate_on_lasso(source, property, path, loop_start, 0)? {
                violated.push(position);
            }
        }
        Ok(violated)
    }

    pub fn find_violation(&self) -> Result<Option<Violation>, Declined> {
        self.first_violation().1
    }

    // The search of the behaviors in order up to the first that finds a lasso or fails, with its
    // position among all the behaviors.
    fn first_violation(&self) -> (usize, Result<Option<Violation>, Declined>) {
        for behavior in 0..self.behaviors.len() {
            let solution = &self.solutions[self.behaviors[behavior].solution];
            for model in &solution.models {
                let found = match Search::new(self, behavior, model).find_lasso() {
                    Ok(None) => continue,
                    Ok(Some((prefix, cycle))) => {
                        let loop_start = prefix.len();
                        let mut path = prefix;
                        path.extend(cycle);
                        Ok(Some((
                            path,
                            loop_start,
                            self.is_cycle_constrained[self.behaviors[behavior].solution],
                        )))
                    }
                    Err(declined) => Err(declined),
                };
                return (self.global[behavior], found);
            }
        }
        (self.behaviors.len(), Ok(None))
    }

    /// Keeps only the behaviors at these positions, in order, for a checker that builds them
    /// while others build the rest.
    fn keep(&mut self, positions: Vec<usize>) {
        let mut kept: Vec<Behavior> = Vec::with_capacity(positions.len());
        for (position, mut behavior) in std::mem::take(&mut self.behaviors).into_iter().enumerate()
        {
            if positions.contains(&position) {
                behavior.is_covered = is_covered(&kept, &behavior.action_ids);
                kept.push(behavior);
            }
        }
        self.behaviors = kept;
        self.global = positions;
        self.needed = self.steps.mask(
            self.behaviors
                .iter()
                .flat_map(|behavior| behavior.action_ids.iter().copied()),
        );
    }

    /// Takes what was read ahead of each behavior's state checks and consistency, in order.
    fn adopt(&mut self, reads: Vec<StateReads>) {
        for (behavior, reads) in self.behaviors.iter_mut().zip(reads) {
            behavior.state_results = reads.results;
            behavior.state_checked = reads.is_checked;
            behavior.read_consistency = reads.consistency;
            behavior.is_read = reads.is_read;
        }
    }
}

/// Whether the behaviors before one have every action check of it.
fn is_covered(before: &[Behavior], ids: &[usize]) -> bool {
    ids.iter().all(|id| {
        before
            .iter()
            .any(|behavior| behavior.action_ids.contains(id))
    })
}

// `evaluate` on the tables, or None where it reads an atom without an answer there or would
// fail: `evaluate` then finds what fails, in its order.
fn read(
    terms: &Terms,
    tables: &[Option<&[u8]>],
    graph: &Graph<'_>,
    term: TermId,
    state: u32,
    step: Option<Step>,
) -> Option<bool> {
    let answer =
        |atom: u32, position: usize| match tables.get(atom as usize)?.as_ref()?.get(position) {
            Some(0) => Some(false),
            Some(1) => Some(true),
            _ => None,
        };
    match terms.kind(term) {
        Kind::Boolean(value) => Some(value),
        Kind::State(atom) | Kind::Enabled(atom) => answer(atom, state as usize),
        Kind::Action { atom, enabled } => {
            if let Some(enabled) = enabled
                && let Some(Some(table)) = tables.get(enabled as usize)
                && table.get(state as usize) == Some(&0)
            {
                return Some(false);
            }
            answer(atom, graph.position(step?.slot))
        }
        Kind::Not => read(terms, tables, graph, terms.body(term), state, step).map(|value| !value),
        Kind::And | Kind::Or => {
            let is_and = terms.kind(term) == Kind::And;
            for &operand in terms.children(term) {
                if read(terms, tables, graph, operand, state, step)? != is_and {
                    return Some(!is_and);
                }
            }
            Some(is_and)
        }
        Kind::Next => read(
            terms,
            tables,
            graph,
            terms.body(term),
            step.map_or(state, |step| step.real),
            None,
        ),
        Kind::Always | Kind::Eventually => None,
    }
}

// `read` of a check without its step: its value where that doesn't depend on the step.
fn read_partially(terms: &Terms, tables: &[Option<&[u8]>], term: TermId, state: u32) -> Partial {
    let answer = |atom: u32| match tables
        .get(atom as usize)
        .and_then(|table| table.as_ref()?.get(state as usize))
    {
        Some(0) => Partial::Known(false),
        Some(1) => Partial::Known(true),
        _ => Partial::Unknown,
    };
    match terms.kind(term) {
        Kind::Boolean(value) => Partial::Known(value),
        Kind::State(atom) | Kind::Enabled(atom) => answer(atom),
        Kind::Action {
            enabled: Some(enabled),
            ..
        } if matches!(
            tables.get(enabled as usize),
            Some(Some(table)) if table.get(state as usize) == Some(&0)
        ) =>
        {
            Partial::Known(false)
        }
        Kind::Action { .. } | Kind::Next => Partial::Stepped,
        Kind::Not => match read_partially(terms, tables, terms.body(term), state) {
            Partial::Known(value) => Partial::Known(!value),
            other => other,
        },
        // An operand that reads the step comes first, so the others decide nothing alone.
        Kind::And | Kind::Or => {
            let is_and = terms.kind(term) == Kind::And;
            for &operand in terms.children(term) {
                match read_partially(terms, tables, operand, state) {
                    Partial::Known(value) if value == is_and => {}
                    Partial::Known(_) => return Partial::Known(!is_and),
                    other => return other,
                }
            }
            Partial::Known(is_and)
        }
        Kind::Always | Kind::Eventually => Partial::Unknown,
    }
}

/// `read` of each run of `count` items in order, one run a thread, as many runs as threads.
fn on_runs<T: Send>(
    count: usize,
    threads: usize,
    read: impl Fn(usize, usize) -> T + Sync,
) -> Vec<T> {
    let share = count.div_ceil(threads.max(1)).max(1);
    std::thread::scope(|scope| {
        let handles: Vec<_> = (0..count)
            .step_by(share)
            .map(|start| {
                let read = &read;
                std::thread::Builder::new()
                    .stack_size(STACK_BYTES)
                    .spawn_scoped(scope, move || read(start, (start + share).min(count)))
                    .expect("a thread for the liveness checker")
            })
            .collect();
        handles
            .into_iter()
            .map(|handle| {
                handle
                    .join()
                    .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
            })
            .collect()
    })
}

/// The entries of a successor set in TLC's order, as positions in `order`: each step's (target,
/// real) then the stuttering step's go into `slots`, `SUCCESSOR_CAPACITY` times the multiplier of
/// them, by the target's fingerprint and linear probing, as TLC's SetOfStates keys its states,
/// which doubles its slots and one when half full and puts the entries back in slot order; the
/// order is the slots' without the duplicates. Returns whether the slots grew.
fn slot_order(
    entries: &[(u32, u32)],
    fingerprints: &[u64],
    multiplier: usize,
    slots: &mut Vec<u32>,
    order: &mut Vec<u32>,
) -> bool {
    let insert = |slots: &mut [u32], position: usize| {
        let entry = entries[position];
        let size = slots.len();
        let mut slot = (fingerprints[entry.0 as usize] as u32 & 0x7fff_ffff) as usize % size;
        loop {
            match slots[slot] {
                0 => {
                    slots[slot] = position as u32 + 1;
                    return true;
                }
                stored if entries[stored as usize - 1] == entry => return false,
                _ => slot = (slot + 1) % size,
            }
        }
    };
    let initial = SUCCESSOR_CAPACITY * multiplier;
    let mut size = initial;
    let mut count = 0;
    slots.clear();
    slots.resize(size, 0);
    for position in 0..entries.len() {
        if count >= size >> 1 {
            let old = std::mem::take(slots);
            size = 2 * size + 1;
            slots.resize(size, 0);
            for stored in old.into_iter().filter(|&stored| stored != 0) {
                insert(slots, stored as usize - 1);
            }
        }
        if insert(slots, position) {
            count += 1;
        }
    }
    order.clear();
    order.extend(
        slots
            .iter()
            .filter(|&&stored| stored != 0)
            .map(|&stored| stored - 1),
    );
    size > initial
}

/// The successor sets of the expanded states in TLC's order, built on threads: first how many
/// distinct steps each state has, which says whether its set outgrows the slots, since the
/// stuttering step goes in last, and how long its set is; then the multiplier as each set is
/// built, which the sets before it grew; then each run of states' sets with theirs, written where
/// the lengths before it put it.
fn order_sets(graph: &Graph<'_>, threads: usize) -> Orders {
    let expanded = graph.expanded();
    let entries_of = |state: usize, entries: &mut Vec<(u32, u32)>| {
        entries.clear();
        let start = graph.edge_offsets[state] as usize;
        let end = graph.edge_offsets[state + 1] as usize;
        entries.extend((start..end).map(|edge| {
            let step = edge_step(graph, state as u32, edge);
            (step.target, step.real)
        }));
    };
    // Each state's distinct steps, and whether one of them is its stuttering step.
    let distinct: Vec<Vec<(u32, bool)>> = on_runs(expanded, threads, |start, end| {
        let (mut entries, mut slots, mut order) = (Vec::new(), Vec::new(), Vec::new());
        (start..end)
            .map(|state| {
                entries_of(state, &mut entries);
                slot_order(&entries, graph.fingerprints, 1, &mut slots, &mut order);
                let stutter = (state as u32, state as u32);
                (order.len() as u32, entries.contains(&stutter))
            })
            .collect()
    });
    let mut changes = vec![(0, 1)];
    let mut multiplier = 1;
    let mut offsets = Vec::with_capacity(expanded + 1);
    let mut length = 0;
    for (state, &(distinct, is_stuttering)) in distinct.iter().flatten().enumerate() {
        if distinct as usize >= (SUCCESSOR_CAPACITY * multiplier) >> 1 {
            multiplier += 1;
            changes.push((state + 1, multiplier));
        }
        offsets.push(length);
        length += distinct as usize + usize::from(!is_stuttering);
    }
    offsets.push(length);
    let mut positions = vec![0; length];
    let (changes, offsets_of) = (&changes, &offsets);
    let order_run = |start: usize, end: usize, positions: &mut [u32]| {
        let mut next = changes.partition_point(|&(at, _)| at <= start);
        let mut multiplier = changes[next - 1].1;
        let (mut entries, mut slots, mut order) = (Vec::new(), Vec::new(), Vec::new());
        for state in start..end {
            while changes.get(next).is_some_and(|&(at, _)| at <= state) {
                multiplier = changes[next].1;
                next += 1;
            }
            entries_of(state, &mut entries);
            entries.push((state as u32, state as u32));
            slot_order(
                &entries,
                graph.fingerprints,
                multiplier,
                &mut slots,
                &mut order,
            );
            let at = offsets_of[state] - offsets_of[start];
            positions[at..at + order.len()].copy_from_slice(&order);
        }
    };
    let share = expanded.div_ceil(threads.max(1)).max(1);
    std::thread::scope(|scope| {
        let mut rest = &mut positions[..];
        let handles: Vec<_> = (0..expanded)
            .step_by(share)
            .map(|start| {
                let end = (start + share).min(expanded);
                let (own, left) =
                    std::mem::take(&mut rest).split_at_mut(offsets_of[end] - offsets_of[start]);
                rest = left;
                let order_run = &order_run;
                std::thread::Builder::new()
                    .stack_size(STACK_BYTES)
                    .spawn_scoped(scope, move || order_run(start, end, own))
                    .expect("a thread for the liveness checker")
            })
            .collect();
        for handle in handles {
            handle
                .join()
                .unwrap_or_else(|panic| std::panic::resume_unwind(panic));
        }
    });
    Orders { offsets, positions }
}

/// A state's row of consistency with a tableau's nodes as the tables answer it, where they answer
/// every node's predicates, in `words` words of bits by node.
fn read_consistency_row(
    terms: &Terms,
    tables: &[Option<&[u8]>],
    graph: &Graph<'_>,
    tableau: &Tableau,
    state: u32,
    words: usize,
) -> Option<[u64; READ_WORDS]> {
    if words > READ_WORDS {
        return None;
    }
    let mut row = [0u64; READ_WORDS];
    for (node, tableau_node) in tableau.nodes.iter().enumerate() {
        let mut is_held = true;
        for &predicate in &tableau_node.state_predicates {
            match read(terms, tables, graph, predicate, state, None) {
                Some(true) => {}
                Some(false) => {
                    is_held = false;
                    break;
                }
                None => return None,
            }
        }
        if is_held {
            row[node / 64] |= 1 << (node % 64);
        }
    }
    Some(row)
}

/// What the tables answer of each behavior's state checks and consistency on each state the
/// search stored or reached, read on threads, each a run of the states.
fn read_states(
    terms: &Terms,
    solutions: &[Solution],
    behaviors: &[Behavior],
    graph: &Graph<'_>,
    tables: &[Option<&[u8]>],
    threads: usize,
) -> Vec<StateReads> {
    let count = graph
        .count()
        .max(graph.edge_offsets.len().saturating_sub(1));
    let runs: Vec<Vec<StateReads>> = on_runs(count, threads, |start, end| {
        behaviors
            .iter()
            .map(|behavior| {
                let solution = &solutions[behavior.solution];
                let checks = solution.state_checks.len();
                let tableau = solution.tableau.as_ref();
                let words = tableau.map_or(0, |tableau| tableau.nodes.len().div_ceil(64).max(1));
                let mut reads = StateReads {
                    results: vec![0; (end - start) * checks],
                    is_checked: vec![false; end - start],
                    consistency: vec![0; (end - start) * words],
                    is_read: vec![false; end - start],
                };
                for state in start..end {
                    let at = state - start;
                    let answered = solution.state_checks.iter().enumerate().try_for_each(
                        |(position, &check)| {
                            let value = read(terms, tables, graph, check, state as u32, None)?;
                            reads.results[at * checks + position] = u8::from(value);
                            Some(())
                        },
                    );
                    reads.is_checked[at] = answered.is_some();
                    if let Some(tableau) = tableau
                        && let Some(row) =
                            read_consistency_row(terms, tables, graph, tableau, state as u32, words)
                    {
                        reads.consistency[at * words..(at + 1) * words]
                            .copy_from_slice(&row[..words]);
                        reads.is_read[at] = true;
                    }
                }
                reads
            })
            .collect()
    });
    let mut all: Vec<StateReads> = behaviors.iter().map(|_| StateReads::default()).collect();
    for run in runs {
        for (all, part) in all.iter_mut().zip(run) {
            all.results.extend(part.results);
            all.is_checked.extend(part.is_checked);
            all.consistency.extend(part.consistency);
            all.is_read.extend(part.is_read);
        }
    }
    all
}

/// The action checks' results that the tables answer on each step of the graph, by its position:
/// each step from a state the search expanded, then each state's stuttering step. Threads read
/// them, each a run of the states, and the runs follow one another.
fn read_positions(
    terms: &Terms,
    action_terms: &[TermId],
    graph: &Graph<'_>,
    tables: &[Option<&[u8]>],
    threads: usize,
) -> StepResults {
    let (count, expanded) = (graph.count(), graph.expanded());
    // A run's steps from its states and its states' stuttering steps.
    let read_run = |start: usize, end: usize| {
        let first_edge = graph.edge_offsets[start.min(expanded)] as usize;
        let last_edge = graph.edge_offsets[end.min(expanded)] as usize;
        let mut edges = StepResults::new(action_terms.len());
        edges.add(last_edge - first_edge);
        let mut stutters = StepResults::new(action_terms.len());
        stutters.add(end - start);
        for state in start..end {
            let mut steps: Vec<Step> = Vec::new();
            if state < expanded {
                let from = graph.edge_offsets[state] as usize;
                let to = graph.edge_offsets[state + 1] as usize;
                steps.extend((from..to).map(|edge| edge_step(graph, state as u32, edge)));
            }
            steps.push(Checker::self_step(state as u32, state as u32));
            for (id, &term) in action_terms.iter().enumerate() {
                let partial = read_partially(terms, tables, term, state as u32);
                for &step in &steps {
                    let value = match partial {
                        Partial::Known(value) => value,
                        Partial::Stepped => {
                            match read(terms, tables, graph, term, state as u32, Some(step)) {
                                Some(value) => value,
                                None => continue,
                            }
                        }
                        Partial::Unknown => break,
                    };
                    match graph.position(step.slot) {
                        position if position < graph.edges.len() => {
                            edges.set(position - first_edge, id, value);
                        }
                        position => stutters.set(position - graph.edges.len() - start, id, value),
                    }
                }
            }
        }
        (edges, stutters)
    };
    let runs: Vec<(StepResults, StepResults)> = on_runs(count, threads, read_run);
    let mut positions = StepResults::new(action_terms.len());
    positions.add(graph.edges.len() + count);
    let mut row = 0;
    for (edges, _) in &runs {
        positions.copy_rows(row, edges);
        row += edges.count;
    }
    row = graph.edges.len();
    for (_, stutters) in &runs {
        positions.copy_rows(row, stutters);
        row += stutters.count;
    }
    positions
}

// The step of an edge of the search's graph from a state, its stuttering step where it leads back
// to the very state.
fn edge_step(graph: &Graph<'_>, state: u32, edge: usize) -> Step {
    let target = graph.edges[edge];
    let real = graph.reals.map_or(target, |reals| reals[edge]);
    if target == state && real == state {
        Checker::self_step(state, state)
    } else {
        Step {
            target,
            real,
            slot: Slot::Step {
                state,
                edge: edge as u32,
            },
        }
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
struct Search<'s> {
    checker: &'s Checker,
    index: usize,
    behavior: &'s Behavior,
    solution: &'s Solution,
    model: &'s Model,
    /// The action checks the edges of a cycle must all pass, and those its edges must pass
    /// between them, as masks of a row of `StepResults`.
    allowed: Vec<u64>,
    required: Vec<u64>,
    links: Vec<i64>,
    components: Vec<u32>,
    members: Vec<u32>,
    member_marks: Vec<u32>,
    mark: u32,
    /// Whether each tableau node fulfills each promise.
    fulfilling: Vec<bool>,
}

impl<'s> Search<'s> {
    fn new(checker: &'s Checker, behavior: usize, model: &'s Model) -> Self {
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
            allowed: checker.steps.mask(
                model
                    .eventually_always
                    .iter()
                    .map(|&position| graph.action_ids[position]),
            ),
            required: checker.steps.mask(
                model
                    .infinitely_often_actions
                    .iter()
                    .map(|&position| graph.action_ids[position]),
            ),
            links: vec![UNVISITED; node_count],
            components: Vec::new(),
            members: Vec::new(),
            member_marks: vec![0; node_count],
            mark: 0,
            fulfilling,
        }
    }

    // The row of the action checks' results on the step of a node's edge.
    fn row(&self, node: u32, edge: usize) -> usize {
        let behavior = self.behavior;
        behavior.edge_steps[behavior.edge_starts[node as usize] + edge] as usize
    }

    fn is_action(&self, node: u32, edge: usize, position: usize) -> bool {
        self.checker
            .step_value(self.row(node, edge), self.behavior.action_ids[position])
    }

    fn is_allowed(&self, node: u32, edge: usize) -> bool {
        let row = self.row(node, edge);
        self.allowed
            .iter()
            .enumerate()
            .all(|(word, &mask)| mask == 0 || self.checker.step_word(row, word) & mask == mask)
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
        let mut satisfied = vec![0u64; self.required.len()];
        let is_done = |satisfied: &[u64]| satisfied == self.required.as_slice();
        if is_done(&satisfied) {
            return true;
        }
        for &node in &self.members {
            for (edge, &next) in self.behavior.successors(node).iter().enumerate() {
                if !self.is_member(next) || !self.is_allowed(node, edge) {
                    continue;
                }
                let row = self.row(node, edge);
                for (word, (satisfied, mask)) in
                    satisfied.iter_mut().zip(&self.required).enumerate()
                {
                    *satisfied |= self.checker.step_word(row, word) & mask;
                }
                if is_done(&satisfied) {
                    return true;
                }
            }
        }
        false
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

/// The first atom the engine didn't answer that TLC evaluates as it adds the states to the
/// behavior graphs, unless it stops first at a node that accepts every behavior.
pub fn find_unanswered(checker: &mut Checker, source: &Source<'_>) -> Option<Unanswered> {
    add_states(checker, source)
        .is_err()
        .then(|| checker.unanswered.get())
        .flatten()
}

/// Where no state may reach a tableau node that accepts every behavior, none: otherwise as
/// `add_states`.
pub fn find_accepted(
    checker: &mut Checker,
    source: &Source<'_>,
) -> Result<Option<(u32, Vec<u32>)>, Declined> {
    if !checker.may_accept() {
        return Ok(None);
    }
    add_states(checker, source)
}

/// Adds the states to the behavior graphs as TLC does as it searches, and returns the evaluations
/// logged, unless a tableau node accepts every behavior.
pub fn add_logged(checker: &mut Checker, source: &Source<'_>) -> Result<Vec<Event>, Declined> {
    if add_states(checker, source)?.is_some() {
        return Err(Declined::from("a node that accepts every behavior"));
    }
    Ok(checker.take_events())
}

/// Adds the states to the behavior graphs as TLC does as it searches: the first whose tableau node
/// accepts every behavior, and the path to it.
fn add_states(
    checker: &mut Checker,
    source: &Source<'_>,
) -> Result<Option<(u32, Vec<u32>)>, Declined> {
    let graph = source.graph;
    for (state, &parent) in graph.parents.iter().enumerate() {
        if parent == -1 {
            checker.adding.set(Some((state as u32, true)));
            checker.add_initial_state(source, state as u32)?;
        }
    }
    // A check part way through the search, as TLC's periodic one, adds the states it expanded:
    // the nodes of the others are undone, and the search for a cycle passes them by.
    for state in 0..graph.expanded() as u32 {
        checker.adding.set(Some((state, false)));
        if let Some(path) = checker.add_state(source, state)? {
            checker.adding.set(None);
            return Ok(Some((state, path)));
        }
    }
    checker.adding.set(None);
    Ok(None)
}

/// The path to a node that accepts every behavior, and the properties it violates, which TLC
/// names from the path with its last state stuttering.
pub fn accepted(
    checker: &Checker,
    source: &Source<'_>,
    properties: &[TermId],
    state: u32,
    path: Vec<u32>,
) -> Result<Verdict, Declined> {
    let loop_start = path.len().saturating_sub(1);
    Ok(Verdict::Accepted {
        violated: checker.violated(source, properties, &path, loop_start)?,
        state,
        path,
    })
}

/// Checks the formula on the search's graph, and names the properties a lasso violates.
/// Builds the behavior graphs, into `events` the evaluations it logged, and searches them.
pub fn check(
    checker: &mut Checker,
    source: &Source<'_>,
    properties: &[TermId],
    events: &mut Vec<Event>,
) -> Result<Verdict, Declined> {
    let found = add_states(checker, source)?;
    let is_effectful = checker.is_effectful();
    *events = checker.take_events();
    if let Some((state, path)) = found {
        return accepted(checker, source, properties, state, path);
    }
    finish(checker, source, properties, events, is_effectful)
}

/// What one thread of `check_shared` found: its checker, what adding the states stopped at, and
/// what the search of its graphs found.
struct Part {
    checker: Checker,
    added: Result<Option<(u32, Vec<u32>)>, Declined>,
    violation: Option<(usize, Result<Option<Violation>, Declined>)>,
}

/// `check` where nothing has effects, with the behaviors shared between threads: each thread
/// builds and searches the graphs of some of them in a checker of its own, made by `build`. Each
/// behavior's graph depends on no other's, so what the check finds is what the thread found first
/// in TLC's order: the first state and behavior where adding the states stopped, or else the lasso
/// of the first behavior that has one.
pub fn check_shared(
    checker: &mut Checker,
    build: &(dyn Fn() -> Result<Checker, Declined> + Sync),
    graph: &Graph<'_>,
    answers: &(dyn Answers + Sync),
    properties: &[TermId],
    threads: usize,
) -> Result<Verdict, Declined> {
    let count = checker.behaviors.len();
    let groups = threads.clamp(1, count.max(1));
    let shared = Arc::new(Shared {
        steps: answers.tables().map_or_else(
            || StepResults::new(checker.action_terms.len()),
            |tables| {
                read_positions(
                    &checker.terms,
                    &checker.action_terms,
                    graph,
                    tables,
                    threads,
                )
            },
        ),
        orders: order_sets(graph, threads),
    });
    let shared = &shared;
    // What each group's behaviors have read ahead, the behaviors a group builds being every
    // `groups`th from its own.
    let mut reads: Vec<Vec<StateReads>> = (0..groups).map(|_| Vec::new()).collect();
    if let Some(tables) = answers.tables() {
        let read = read_states(
            &checker.terms,
            &checker.solutions,
            &checker.behaviors,
            graph,
            tables,
            threads,
        );
        for (behavior, read) in read.into_iter().enumerate() {
            reads[behavior % groups].push(read);
        }
    }
    let parts = std::thread::scope(|scope| {
        let handles: Vec<_> = reads
            .into_iter()
            .enumerate()
            .map(|(group, reads)| {
                std::thread::Builder::new()
                    .stack_size(STACK_BYTES)
                    .spawn_scoped(scope, move || -> Result<Part, Declined> {
                        let mut checker = build()?;
                        checker.keep((group..count).step_by(groups).collect());
                        checker.shared = Some(Arc::clone(shared));
                        checker.adopt(reads);
                        let source = Source { graph, answers };
                        let added = add_states(&mut checker, &source);
                        let violation =
                            matches!(added, Ok(None)).then(|| checker.first_violation());
                        Ok(Part {
                            checker,
                            added,
                            violation,
                        })
                    })
                    .expect("a thread for the liveness checker")
            })
            .collect();
        handles
            .into_iter()
            .map(|handle| {
                handle
                    .join()
                    .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
            })
            .collect::<Result<Vec<_>, _>>()
    })?;
    for part in &parts {
        for (behavior, &global) in part.checker.behaviors.iter().zip(&part.checker.global) {
            checker.behaviors[global].size = behavior.size;
        }
    }
    let source = Source { graph, answers };
    let stopped = parts
        .iter()
        .enumerate()
        .filter(|(_, part)| !matches!(part.added, Ok(None)))
        .min_by_key(|(_, part)| part.checker.at.get())
        .map(|(position, _)| position);
    if let Some(position) = stopped {
        let part = parts.into_iter().nth(position).expect("the part");
        checker.unanswered.set(part.checker.unanswered.get());
        let (state, path) = part.added?.expect("a state adding stopped at");
        return accepted(&part.checker, &source, properties, state, path);
    }
    let Some(part) = parts
        .into_iter()
        .filter(|part| matches!(&part.violation, Some((_, found)) if !matches!(found, Ok(None))))
        .min_by_key(|part| part.violation.as_ref().map(|violation| violation.0))
    else {
        return Ok(Verdict::Holds);
    };
    let (_, found) = part.violation.expect("a violation");
    let (path, loop_start, is_cycle_constrained) = found?.expect("a lasso");
    Ok(Verdict::Lasso {
        violated: part
            .checker
            .violated(&source, properties, &path, loop_start)?,
        path,
        loop_start,
        is_cycle_constrained,
    })
}

/// TLC's check of the behavior graphs once the states are added: the search of each for a
/// counterexample, whose properties it names, logging what it evaluates for that into `events`
/// where the atoms have effects.
pub fn finish(
    checker: &mut Checker,
    source: &Source<'_>,
    properties: &[TermId],
    events: &mut Vec<Event>,
    is_effectful: bool,
) -> Result<Verdict, Declined> {
    if let Some(diameters) = &source.graph.diameters {
        checker.diameter.set(diameters.last);
    }
    let Some((path, loop_start, is_cycle_constrained)) = checker.find_violation()? else {
        return Ok(Verdict::Holds);
    };
    if is_effectful {
        checker.log_effects();
        checker.log(Event::Lasso);
    }
    let violated = checker.violated(source, properties, &path, loop_start)?;
    events.extend(checker.take_events());
    Ok(Verdict::Lasso {
        violated,
        path,
        loop_start,
        is_cycle_constrained,
    })
}

#[cfg(test)]
mod tests {
    use super::StepResults;

    #[test]
    fn keeps_each_steps_results_apart_in_rows_of_any_width() {
        for checks in [1, 3, 60, 64, 130] {
            let mut results = StepResults::new(checks);
            let first = results.add(5);
            assert_eq!(results.add(4), first + 5);
            for row in 0..9 {
                for id in (row % 2..checks).step_by(3) {
                    results.set(row, id, id % 2 == 0);
                }
            }
            let mask = results.mask((0..checks).filter(|id| id % 2 == 0));
            for row in 0..9 {
                for id in 0..checks {
                    let is_set = id >= row % 2 && (id - row % 2) % 3 == 0;
                    assert_eq!(results.is_checked(row, id), is_set);
                    assert_eq!(results.value(row, id), is_set && id % 2 == 0);
                }
                for (word, &mask) in mask.iter().enumerate() {
                    let found = results.word(row, word) & mask;
                    let expected = (0..checks)
                        .filter(|&id| id / 64 == word && results.value(row, id))
                        .fold(0, |bits, id| bits | 1 << (id % 64));
                    assert_eq!(found, expected, "{checks} checks, row {row}");
                }
            }
        }
    }

    #[test]
    fn copies_rows_together_as_it_copies_them_one_by_one() {
        for checks in [1, 3, 60, 64, 130] {
            for (before, count) in [(0, 70), (1, 1), (5, 0), (21, 150), (64, 64)] {
                let mut from = StepResults::new(checks);
                from.add(count);
                for row in 0..count {
                    for id in (row % 3..checks).step_by(2) {
                        from.set(row, id, (row + id) % 3 == 0);
                    }
                }
                let (mut together, mut apart) =
                    (StepResults::new(checks), StepResults::new(checks));
                for results in [&mut together, &mut apart] {
                    results.add(before + count + 3);
                    if before > 0 {
                        results.set(before - 1, 0, true);
                    }
                    results.set(before + count, checks - 1, true);
                }
                together.copy_rows(before, &from);
                for row in 0..count {
                    apart.copy_row(before + row, &from, row);
                }
                assert_eq!(
                    together.checked, apart.checked,
                    "{checks} checks from {before}"
                );
                assert_eq!(
                    together.values, apart.values,
                    "{checks} checks from {before}"
                );
            }
        }
    }
}
