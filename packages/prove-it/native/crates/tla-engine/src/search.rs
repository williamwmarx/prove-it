//! The engine's breadth-first search, `runEngine` in `search.ts` step for step on one thread. It
//! explores states in TLC's order, counts them as TLC does, and tells states apart by TLC's
//! fingerprint of their key: the state, or its VIEW. Anything else it meets (a violation, an
//! error, a feature it doesn't implement) ends the run with a checkpoint, from which the reference
//! interpreter goes on.

use std::fmt::Write as _;
use std::io::Write as _;
use std::time::{Duration, Instant};

use tla_ir::Ir;
use tla_values::fingerprint::Fingerprints;
use tla_values::store::Outcome;
use tla_values::transfer::{EncodedStates, StateEncoder};
use tla_values::{Bail, Id, Store};

use crate::compile::{CompileError, Compiler, DISTINCT_SLOT, LEVEL_SLOT, NEXT_LEVEL_SLOT, Options};
use crate::context::{EngineContext, holds_all, holds_all_changed};
use crate::live::{LiveGraph, Table, answer_atoms};
use crate::machine::{Machine, UNASSIGNED};
use crate::symmetry::Canonicalizer;

pub const OUT_DEGREE_BUCKETS: usize = 32;
const PROGRESS_INTERVAL: Duration = Duration::from_secs(60);
const FIRST_PROGRESS: Duration = Duration::from_secs(3);

/// What the caller asks of a search besides the model.
#[derive(Clone, Debug, Default)]
pub struct Settings {
    pub compile: Options,
    /// PROVE_IT_STOP_AT: the state before whose expansion the search stops.
    pub stop_at: Option<usize>,
    /// PROVE_IT_FP_VERIFY=1: compare the keys of states whose fingerprints are equal.
    pub is_fingerprint_verified: bool,
    /// PROVE_IT_STATE_LOG: the file the search writes its states to.
    pub state_log: Option<String>,
    /// PROVE_IT_LIVE_CHECK=1: take each state's steps through the next-state relation as well as
    /// through TLC's actions, and run each ENABLED answered from the steps, and fail where the two
    /// differ.
    pub is_live_checked: bool,
}

/// What a search tells its caller as it runs, as `runEngine`'s callbacks.
pub trait Reporter {
    fn initial_states_started(&mut self);
    fn initial_states_progress(&mut self, count: u64);
    fn initial_states(&mut self, generated: u64, distinct: u64);
    fn progress(&mut self, generated: u64, distinct: u64, queued: u64, depth: u64);
}

/// The counts TLC reports of a search, so far or in all.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Counts {
    pub generated: u64,
    pub distinct: u64,
    pub depth: u64,
    pub initial_generated: u64,
    pub initial_distinct: u64,
    pub out_degrees: [u64; OUT_DEGREE_BUCKETS],
}

/// The search up to the state it was expanding when it stopped (`EngineCheckpoint`): the states
/// found before that expansion, with their parents and the counts so far.
pub struct Checkpoint {
    pub expanding: u64,
    pub count: u64,
    pub generated: u64,
    pub initial_generated: u64,
    pub out_degrees: [u64; OUT_DEGREE_BUCKETS],
    pub states: EncodedStates,
    pub parents: Vec<i32>,
    /// What TLC fingerprints in place of each state when that isn't the state, its view, with
    /// the width of each.
    pub keys: Option<(EncodedStates, u32)>,
    /// The steps of the states expanded, for the interpreter to replay and check temporal
    /// properties on, when the search records them.
    pub graph: Option<GraphCheckpoint>,
}

/// The steps of a search (`EngineGraph`): for each of the first `expanded` states, how many
/// successors it generated, how many of them were new, and the states, in the model, its steps went
/// to in the order generated, each labelled with its action when the search took TLC's actions.
pub struct GraphCheckpoint {
    pub expanded: u64,
    pub successor_counts: Vec<u32>,
    pub new_counts: Vec<u32>,
    pub edge_offsets: Vec<u32>,
    pub edges: Vec<u32>,
    pub labels: Option<Vec<u32>>,
    /// How many initial states the search had generated when it found each it kept.
    pub initial_counts: Vec<u64>,
    /// Whether the steps are those TLC's ENABLED finds: no shortcut passed a walk.
    pub is_enabled_exact: bool,
    /// The answers to each of the liveness checker's atoms.
    pub tables: Vec<Table>,
}

pub enum SearchOutcome {
    /// The engine doesn't take the model, for this reason, before producing any state.
    Declined(String),
    Complete {
        counts: Box<Counts>,
        /// With temporal properties, the whole search for the interpreter to replay.
        checkpoint: Option<Box<Checkpoint>>,
        /// TLC's fingerprint of each state's key, in the order found.
        fingerprints: Vec<u64>,
        value_count: usize,
        /// Under PROVE_IT_FP_VERIFY, how many fingerprints two different keys shared.
        collisions: u64,
    },
    /// The search stopped, with a checkpoint unless it stopped computing the initial states, as
    /// the TypeScript engine computes them before the part of its search that hands over a
    /// checkpoint: the interpreter then starts from scratch.
    Stopped {
        reason: String,
        checkpoint: Option<Box<Checkpoint>>,
        collisions: u64,
    },
    /// The engine broke one of its own invariants, or a self-check failed
    /// (`EngineInvariantError`).
    Invariant(String),
}

/// What PROVE_IT_LIVE_CHECK finds when TLC's actions take other steps than the next-state relation.
const OTHER_STEPS: &str = "the actions took other steps than the next-state relation";

// Past this many states the search hands its graph over and the interpreter goes on, since the
// interpreter checks temporal properties on the graph as it grows and may find a violation early
// in a state space the engine would search without end.
const MAXIMUM_GRAPH_STATES: usize = 4_000_000;

// The steps recorded so far.
#[derive(Default)]
struct Graph {
    successor_counts: Vec<u32>,
    new_counts: Vec<u32>,
    edge_offsets: Vec<u32>,
    edges: Vec<u32>,
    labels: Option<Vec<u32>>,
    initial_counts: Vec<u64>,
}

/// The fingerprints found, each with the index of its state: open addressing, keyed by TLC's
/// FP64 of the key (DESIGN.md 2.3).
struct FingerprintSet {
    slots: Vec<(u64, u32)>,
    mask: usize,
    len: usize,
}

const EMPTY: u32 = u32::MAX;

impl FingerprintSet {
    fn new() -> FingerprintSet {
        FingerprintSet {
            slots: vec![(0, EMPTY); 1 << 12],
            mask: (1 << 12) - 1,
            len: 0,
        }
    }

    fn home(&self, fingerprint: u64) -> usize {
        (fingerprint.wrapping_mul(0x9e37_79b9_7f4a_7c15) >> 32) as usize & self.mask
    }

    /// The state with this fingerprint, or the slot to put it in.
    fn find(&self, fingerprint: u64) -> Result<u32, usize> {
        let mut slot = self.home(fingerprint);
        loop {
            let (stored, index) = self.slots[slot];
            if index == EMPTY {
                return Err(slot);
            }
            if stored == fingerprint {
                return Ok(index);
            }
            slot = (slot + 1) & self.mask;
        }
    }

    fn insert(&mut self, slot: usize, fingerprint: u64, index: u32) {
        self.slots[slot] = (fingerprint, index);
        self.len += 1;
        if self.len * 2 > self.slots.len() {
            let capacity = self.slots.len() * 2;
            let old = std::mem::replace(&mut self.slots, vec![(0, EMPTY); capacity]);
            self.mask = self.slots.len() - 1;
            for (stored, index) in old {
                if index != EMPTY {
                    let mut slot = self.home(stored);
                    while self.slots[slot].1 != EMPTY {
                        slot = (slot + 1) & self.mask;
                    }
                    self.slots[slot] = (stored, index);
                }
            }
        }
    }
}

// The states found so far and how the search tells them apart.
struct States {
    width: usize,
    // The key's width, when the key isn't the state.
    key_width: Option<usize>,
    ids: Vec<Id>,
    keys: Vec<Id>,
    parents: Vec<i32>,
    fingerprints: Vec<u64>,
    set: FingerprintSet,
    order: Vec<usize>,
    is_verified: bool,
    collisions: u64,
}

impl States {
    fn count(&self) -> usize {
        self.parents.len()
    }

    fn key_of(&self, index: usize) -> &[Id] {
        match self.key_width {
            Some(width) => &self.keys[index * width..(index + 1) * width],
            None => &self.ids[index * self.width..(index + 1) * self.width],
        }
    }

    // The index of the state with this key's fingerprint, or the slot to add it at.
    fn find(&mut self, key: &[Id], fingerprint: u64) -> Result<u32, usize> {
        let found = self.set.find(fingerprint);
        if self.is_verified
            && let Ok(index) = found
            && self.key_of(index as usize) != key
        {
            self.collisions += 1;
        }
        found
    }

    fn add(&mut self, state: &[Id], key: &[Id], fingerprint: u64, slot: usize, parent: i32) {
        let index = self.count() as u32;
        self.ids.extend_from_slice(state);
        if self.key_width.is_some() {
            self.keys.extend_from_slice(key);
        }
        self.parents.push(parent);
        self.fingerprints.push(fingerprint);
        self.set.insert(slot, fingerprint, index);
    }

    fn encode(&self, store: &Store, ids: &[Id], width: usize, count: usize) -> EncodedStates {
        let mut encoder = StateEncoder::new();
        for index in 0..count {
            encoder.encode(store, &ids[index * width..(index + 1) * width]);
        }
        encoder.finish()
    }
}

// The search's state besides the machine, which the walks' continuations update.
struct Search<'r> {
    states: States,
    reporter: &'r mut dyn Reporter,
    is_distinct_read: bool,
    generated: u64,
    initial_generated: u64,
    depth: u64,
    level: u64,
    successors: u64,
    new_states: u64,
    expanding: usize,
    current: Vec<Id>,
    successor: Vec<Id>,
    key: Vec<Id>,
    expansion_epoch: u64,
    level_id: Id,
    next_level_id: Id,
    fingerprints: Fingerprints,
    canonicalizer: Option<Canonicalizer>,
    graph: Option<Graph>,
    // The position of the action whose steps the search is taking.
    action: u32,
    // Under PROVE_IT_LIVE_CHECK, the steps the next-state relation took from the state.
    checked: Option<Vec<Vec<Id>>>,
}

impl Search<'_> {
    // TLCGet("distinct") counts the states found so far, and a new state before its checks.
    fn set_distinct(&self, machine: &mut Machine<'_>, count: usize) -> Outcome<()> {
        if self.is_distinct_read {
            let id = machine.store.int(count as i64)?;
            machine.set_slot(DISTINCT_SLOT, id);
        }
        Ok(())
    }

    // The key of the state that is current, and its fingerprint.
    // TLC fingerprints the view of the representative when it has both.
    fn compute_key(&mut self, machine: &mut Machine<'_>, context: &EngineContext) -> Outcome<u64> {
        self.key.clear();
        self.key.extend_from_slice(machine.current());
        if let Some(canonicalizer) = &mut self.canonicalizer {
            canonicalizer.canonicalize(&mut machine.store, &mut self.key)?;
        }
        if let Some(view) = &context.view {
            let value = if self.canonicalizer.is_some() {
                let epoch = machine.epoch();
                let state = machine.current().to_vec();
                machine.set_current(&self.key, 0);
                let value = view(machine);
                machine.set_current(&state, epoch);
                value?
            } else {
                view(machine)?
            };
            self.key.clear();
            self.key.push(value);
        }
        Ok(self
            .fingerprints
            .get_state(&machine.store, &self.key, &self.states.order))
    }

    fn visit_initial(&mut self, machine: &mut Machine<'_>, context: &EngineContext) -> Outcome<()> {
        if machine.current().contains(&UNASSIGNED) {
            return Err(Bail("an initial state that isn't complete"));
        }
        let one = machine.store.int(1)?;
        machine.set_slot(LEVEL_SLOT, one);
        let count = self.initial_generated;
        if count > 1 && count.is_power_of_two() {
            self.reporter.initial_states_progress(count);
        }
        self.generated += 1;
        self.initial_generated += 1;
        let is_in_model = holds_all_changed_none(machine, context)?;
        let found = if is_in_model {
            let fingerprint = self.compute_key(machine, context)?;
            Some((
                fingerprint,
                self.states.find(&self.key.clone(), fingerprint),
            ))
        } else {
            None
        };
        if !matches!(found, Some((_, Ok(_)))) {
            if is_in_model {
                self.set_distinct(machine, self.states.count() + 1)?;
            }
            if !holds_all(machine, &context.initial_invariants)? {
                return Err(Bail("an invariant violated in an initial state"));
            }
            if !holds_all(machine, &context.initial_predicates)? {
                return Err(Bail("a property violated in an initial state"));
            }
            if let Some((fingerprint, Err(slot))) = found {
                let state = machine.current().to_vec();
                let key = std::mem::take(&mut self.key);
                self.states.add(&state, &key, fingerprint, slot, -1);
                self.key = key;
                if let Some(graph) = &mut self.graph {
                    graph.initial_counts.push(self.initial_generated);
                }
                self.depth = 1;
            }
        }
        let zero = machine.store.int(0)?;
        machine.set_slot(LEVEL_SLOT, zero);
        Ok(())
    }

    fn set_successor_current(&self, machine: &mut Machine<'_>, epoch: u64) {
        machine.set_current(&self.successor, epoch);
        machine.set_slot(LEVEL_SLOT, self.next_level_id);
    }

    fn set_expanded_current(&self, machine: &mut Machine<'_>) {
        machine.set_current(&self.current, self.expansion_epoch);
        machine.set_slot(LEVEL_SLOT, self.level_id);
    }

    fn visit_successor(
        &mut self,
        machine: &mut Machine<'_>,
        context: &EngineContext,
    ) -> Outcome<()> {
        if machine.next().contains(&UNASSIGNED) {
            return Err(Bail("a successor that isn't complete"));
        }
        if let Some(checked) = &self.checked
            && checked.get(self.successors as usize).map(Vec::as_slice) != Some(machine.next())
        {
            return Err(Bail(OTHER_STEPS));
        }
        self.successors += 1;
        self.generated += 1;
        self.successor.clear();
        self.successor.extend_from_slice(machine.next());
        let successor_epoch = machine.next_epoch();
        self.set_successor_current(machine, successor_epoch);
        // The state being expanded is in the model, so each constraint held of it.
        let is_state_in_model = holds_all_changed(
            machine,
            &context.constraints,
            &self.successor,
            &self.current,
        )?;
        let fingerprint = if is_state_in_model {
            Some(self.compute_key(machine, context)?)
        } else {
            None
        };
        self.set_expanded_current(machine);
        let is_in_model = is_state_in_model && holds_all(machine, &context.action_constraints)?;
        let found = match fingerprint {
            Some(fingerprint) if is_in_model => {
                let key = std::mem::take(&mut self.key);
                let found = self.states.find(&key, fingerprint);
                self.key = key;
                Some(found)
            }
            _ => None,
        };
        let is_new = matches!(found, Some(Err(_)));
        if is_new {
            self.set_distinct(machine, self.states.count() + 1)?;
        }
        if !is_in_model || is_new {
            self.set_successor_current(machine, successor_epoch);
            let holds =
                holds_all_changed(machine, &context.invariants, &self.successor, &self.current)?;
            self.set_expanded_current(machine);
            if !holds {
                return Err(Bail("an invariant violated"));
            }
        }
        if let Some(graph) = &mut self.graph
            && is_in_model
        {
            graph.edges.push(match found {
                Some(Ok(index)) => index,
                _ => self.states.count() as u32,
            });
            if let Some(labels) = &mut graph.labels {
                labels.push(self.action);
            }
        }
        for (action, unchanged) in &context.action_properties {
            if !crate::context::holds(machine, action)?
                && !crate::context::holds(machine, unchanged)?
            {
                return Err(Bail("an action property violated"));
            }
        }
        if let (Some(Err(slot)), Some(fingerprint)) = (found, fingerprint) {
            let key = std::mem::take(&mut self.key);
            let successor = std::mem::take(&mut self.successor);
            self.states
                .add(&successor, &key, fingerprint, slot, self.expanding as i32);
            self.key = key;
            self.successor = successor;
            self.new_states += 1;
            self.depth = self.level + 1;
        }
        Ok(())
    }
}

// Whether every constraint holds of an initial state, which has no parent to skip any by.
fn holds_all_changed_none(machine: &mut Machine<'_>, context: &EngineContext) -> Outcome<bool> {
    for constraint in &context.constraints {
        if !crate::context::holds(machine, &constraint.eval)? {
            return Ok(false);
        }
    }
    Ok(true)
}

fn describe(error: CompileError) -> String {
    match error {
        CompileError::Bail(reason) | CompileError::Decline(reason) => reason,
    }
}

/// Searches the model the IR describes. It runs compiled closures, which recurse with the
/// expressions and values, so its caller runs it on a thread with a deep stack.
pub fn search(ir: &Ir, settings: &Settings, reporter: &mut dyn Reporter) -> SearchOutcome {
    let model = &ir.model;
    let ranked: Vec<Vec<u16>> = ir.texts[..ir.ranked_count as usize]
        .iter()
        .map(|text| text.encode_utf16().collect())
        .collect();
    let mut store = Store::new();
    store.reset(ranked.iter().map(Vec::as_slice));
    let mut compiler = Compiler::new(ir, &mut store, settings.compile);
    let context = match EngineContext::build(&mut compiler, ir) {
        Ok(context) => context,
        Err(error) => return SearchOutcome::Declined(describe(error)),
    };
    let is_distinct_read = compiler.is_distinct_read;
    let program = compiler.finish();
    let mut machine = Machine::new(&program, store);
    let canonicalizer = model.symmetry.as_ref().map(|group| {
        let units = |text: u32| ir.texts[text as usize].encode_utf16().collect::<Vec<u16>>();
        let group: Vec<Vec<(Vec<u16>, Vec<u16>)>> = group
            .iter()
            .map(|pairs| {
                pairs
                    .iter()
                    .map(|&(name, image)| (units(name), units(image)))
                    .collect()
            })
            .collect();
        let order = ir.tlc_order.iter().map(|&index| index as usize).collect();
        Canonicalizer::new(&mut machine.store, &group, order)
    });
    let width = context.width;
    let order: Vec<usize> = if context.view.is_some() {
        vec![0]
    } else {
        ir.tlc_order.iter().map(|&index| index as usize).collect()
    };
    let mut search = Search {
        states: States {
            width,
            key_width: if context.view.is_some() {
                Some(1)
            } else {
                model.symmetry.as_ref().map(|_| width)
            },
            ids: Vec::new(),
            keys: Vec::new(),
            parents: Vec::new(),
            fingerprints: Vec::new(),
            set: FingerprintSet::new(),
            order,
            is_verified: settings.is_fingerprint_verified,
            collisions: 0,
        },
        reporter,
        is_distinct_read,
        generated: 0,
        initial_generated: 0,
        depth: 0,
        level: 1,
        successors: 0,
        new_states: 0,
        expanding: 0,
        current: vec![UNASSIGNED; width],
        successor: Vec::with_capacity(width),
        key: Vec::with_capacity(width),
        expansion_epoch: 0,
        level_id: 0,
        next_level_id: 0,
        fingerprints: Fingerprints::new(),
        canonicalizer,
        graph: model.is_recording_graph.then(|| Graph {
            edge_offsets: vec![0],
            labels: context.actions.as_ref().map(|_| Vec::new()),
            ..Graph::default()
        }),
        action: 0,
        checked: None,
    };
    // The actions take each state's steps when the search labels them for ENABLED.
    let actions = context
        .actions
        .as_ref()
        .filter(|_| model.is_recording_graph);
    let is_live_checked = settings.is_live_checked && actions.is_some();
    let mut out_degrees = [0u64; OUT_DEGREE_BUCKETS];
    let mut checkpoint_count = 0usize;
    let mut checkpoint_generated = 0u64;
    let mut initial_states = (0, 0);
    let mut is_past_initial = false;
    let result = (|| -> Outcome<()> {
        // --- initial states ---
        let unassigned = vec![UNASSIGNED; width];
        // The initial predicate assigns the current state in place, so nothing caches by its
        // epoch.
        machine.set_current(&unassigned, 0);
        machine.set_next(&unassigned);
        machine.reset_assigned();
        let zero = machine.store.int(0)?;
        machine.set_slot(LEVEL_SLOT, zero);
        search.set_distinct(&mut machine, 0)?;
        search.reporter.initial_states_started();
        (context.init)(&mut machine, &mut |machine: &mut Machine<'_>| {
            search.visit_initial(machine, &context)
        })?;
        initial_states = (search.initial_generated, search.states.count() as u64);
        search
            .reporter
            .initial_states(initial_states.0, initial_states.1);
        is_past_initial = true;

        // --- next states ---
        let mut level_end = search.states.count();
        let started_at = Instant::now();
        let mut progress_at = started_at + FIRST_PROGRESS;
        search.expanding = 0;
        while search.expanding < search.states.count() {
            let expanding = search.expanding;
            if expanding == level_end {
                search.level += 1;
                level_end = search.states.count();
            }
            checkpoint_count = search.states.count();
            checkpoint_generated = search.generated;
            if Some(expanding) == settings.stop_at {
                return Err(Bail("stopped where PROVE_IT_STOP_AT asked"));
            }
            if search.graph.is_some() && search.states.count() > MAXIMUM_GRAPH_STATES {
                return Err(Bail("a state graph too large to keep"));
            }
            search.current.clear();
            search
                .current
                .extend_from_slice(&search.states.ids[expanding * width..(expanding + 1) * width]);
            machine.set_next(&unassigned);
            machine.reset_assigned();
            search.new_states = 0;
            search.successors = 0;
            search.expansion_epoch = machine.next_epoch();
            search.level_id = machine.store.int(search.level as i64)?;
            search.next_level_id = machine.store.int(search.level as i64 + 1)?;
            search.set_expanded_current(&mut machine);
            machine.set_slot(NEXT_LEVEL_SLOT, search.next_level_id);
            match actions {
                None => (context.next)(&mut machine, &mut |machine: &mut Machine<'_>| {
                    search.visit_successor(machine, &context)
                })?,
                Some(actions) => {
                    if is_live_checked {
                        let mut checked = Vec::new();
                        (context.next)(&mut machine, &mut |machine: &mut Machine<'_>| {
                            checked.push(machine.next().to_vec());
                            Ok(())
                        })?;
                        search.checked = Some(checked);
                    }
                    for (position, action) in actions.iter().enumerate() {
                        search.action = position as u32;
                        action(&mut machine, &mut |machine: &mut Machine<'_>| {
                            search.visit_successor(machine, &context)
                        })?;
                    }
                    if let Some(checked) = search.checked.take()
                        && checked.len() as u64 != search.successors
                    {
                        return Err(Bail(OTHER_STEPS));
                    }
                }
            }
            if search.successors == 0 && model.check_deadlock {
                return Err(Bail("deadlock"));
            }
            if let Some(graph) = &mut search.graph {
                graph.successor_counts.push(search.successors as u32);
                graph.new_counts.push(search.new_states as u32);
                graph.edge_offsets.push(graph.edges.len() as u32);
            }
            out_degrees[(search.new_states as usize).min(OUT_DEGREE_BUCKETS - 1)] += 1;
            if expanding & 0xff == 0 && Instant::now() >= progress_at {
                progress_at = Instant::now() + PROGRESS_INTERVAL;
                let count = search.states.count() as u64;
                search.reporter.progress(
                    search.generated,
                    count,
                    count - expanding as u64 - 1,
                    search.depth.max(1),
                );
            }
            search.expanding += 1;
        }
        Ok(())
    })();
    let variables: Vec<&str> = ir
        .variables
        .iter()
        .map(|&text| &*ir.texts[text as usize])
        .collect();
    let collisions = search.states.collisions;
    let is_enabled_exact = !machine.is_past_walk;
    // The first `count` states and the steps of the first `expanded`, for the interpreter to
    // replay from the initial states on, with the answers to the liveness checker's atoms.
    let graph_checkpoint = |machine: &mut Machine<'_>,
                            search: &Search<'_>,
                            expanded: usize,
                            count: usize,
                            expanding: usize|
     -> Result<Checkpoint, &'static str> {
        let graph = search.graph.as_ref().expect("a graph");
        let states = &search.states;
        let edge_count = graph.edge_offsets[expanded] as usize;
        let live = LiveGraph {
            states: &states.ids[..count * width],
            width,
            count,
            expanded,
            edge_offsets: &graph.edge_offsets[..=expanded],
            edges: &graph.edges[..edge_count],
            labels: graph.labels.as_ref().map(|labels| &labels[..edge_count]),
            is_enabled_exact,
        };
        let tables = answer_atoms(machine, &live, &context.atoms, settings.is_live_checked)?;
        Ok(Checkpoint {
            expanding: expanding as u64,
            count: count as u64,
            generated: search.initial_generated,
            initial_generated: search.initial_generated,
            out_degrees: [0; OUT_DEGREE_BUCKETS],
            states: states.encode(&machine.store, &states.ids, width, count),
            parents: states.parents[..count].to_vec(),
            keys: None,
            graph: Some(GraphCheckpoint {
                expanded: expanded as u64,
                successor_counts: graph.successor_counts[..expanded].to_vec(),
                new_counts: graph.new_counts[..expanded].to_vec(),
                edge_offsets: graph.edge_offsets[..=expanded].to_vec(),
                edges: graph.edges[..edge_count].to_vec(),
                labels: graph
                    .labels
                    .as_ref()
                    .map(|labels| labels[..edge_count].to_vec()),
                initial_counts: graph.initial_counts.clone(),
                is_enabled_exact,
                tables,
            }),
        })
    };
    match result {
        Err(bail) if bail.0 == OTHER_STEPS => SearchOutcome::Invariant(OTHER_STEPS.into()),
        Ok(()) => {
            let count = search.states.count();
            if let Some(path) = &settings.state_log {
                write_state_log(
                    path,
                    &variables,
                    &search.states,
                    &machine.store,
                    &Logged {
                        count,
                        stopped: None,
                        expanding: count,
                        graph: search.graph.as_ref(),
                    },
                );
            }
            let checkpoint = match search.graph {
                Some(_) => match graph_checkpoint(&mut machine, &search, count, count, 0) {
                    Ok(checkpoint) => Some(Box::new(checkpoint)),
                    Err(reason) => return SearchOutcome::Invariant(reason.into()),
                },
                None => None,
            };
            let counts = Counts {
                generated: search.generated,
                distinct: count as u64,
                depth: if search.generated == 0 {
                    0
                } else {
                    search.depth.max(1)
                },
                initial_generated: initial_states.0,
                initial_distinct: initial_states.1,
                out_degrees,
            };
            SearchOutcome::Complete {
                counts: Box::new(counts),
                checkpoint,
                value_count: machine.store.value_count(),
                collisions,
                fingerprints: search.states.fingerprints,
            }
        }
        Err(bail) if !is_past_initial => SearchOutcome::Stopped {
            reason: bail.0.to_string(),
            checkpoint: None,
            collisions,
        },
        Err(bail) => {
            let count = checkpoint_count;
            let is_kept = search.graph.is_none() || count <= MAXIMUM_GRAPH_STATES;
            if let Some(path) = settings.state_log.as_ref().filter(|_| is_kept) {
                write_state_log(
                    path,
                    &variables,
                    &search.states,
                    &machine.store,
                    &Logged {
                        count,
                        stopped: Some(bail.0),
                        expanding: search.expanding,
                        graph: None,
                    },
                );
            }
            let checkpoint = if search.graph.is_none() {
                let states = &search.states;
                let store = &machine.store;
                Some(Box::new(Checkpoint {
                    expanding: search.expanding as u64,
                    count: count as u64,
                    generated: checkpoint_generated,
                    initial_generated: search.initial_generated,
                    out_degrees,
                    states: states.encode(store, &states.ids, width, count),
                    parents: states.parents[..count].to_vec(),
                    keys: states.key_width.map(|key_width| {
                        (
                            states.encode(store, &states.keys, key_width, count),
                            key_width as u32,
                        )
                    }),
                    graph: None,
                }))
            } else if !is_kept {
                // The interpreter searches a graph too large to keep from the start, since its
                // liveness checker may stop in the first states, before it has taken all of them
                // over.
                None
            } else {
                let expanding = search.expanding;
                match graph_checkpoint(&mut machine, &search, expanding, count, expanding) {
                    Ok(checkpoint) => Some(Box::new(checkpoint)),
                    Err(reason) => return SearchOutcome::Invariant(reason.into()),
                }
            };
            SearchOutcome::Stopped {
                reason: bail.0.to_string(),
                checkpoint,
                collisions,
            }
        }
    }
}

// A text as JSON writes it, a lone surrogate escaped as JSON.stringify escapes it.
fn write_json_text(out: &mut String, units: &[u16]) {
    out.push('"');
    for item in char::decode_utf16(units.iter().copied()) {
        match item {
            Ok('"') => out.push_str("\\\""),
            Ok('\\') => out.push_str("\\\\"),
            Ok('\n') => out.push_str("\\n"),
            Ok('\r') => out.push_str("\\r"),
            Ok('\t') => out.push_str("\\t"),
            Ok('\u{8}') => out.push_str("\\b"),
            Ok('\u{c}') => out.push_str("\\f"),
            Ok(character) if (character as u32) < 0x20 => {
                let _ = write!(out, "\\u{:04x}", character as u32);
            }
            Ok(character) => out.push(character),
            Err(error) => {
                let _ = write!(out, "\\u{:04x}", error.unpaired_surrogate());
            }
        }
    }
    out.push('"');
}

fn write_encoded(out: &mut String, encoded: &EncodedStates) {
    out.push('[');
    for (index, word) in encoded.words.iter().enumerate() {
        if index > 0 {
            out.push(',');
        }
        let _ = write!(out, "{word}");
    }
    out.push_str("],[");
    for (index, text) in encoded.strings.iter().enumerate() {
        if index > 0 {
            out.push(',');
        }
        write_json_text(out, text);
    }
    out.push(']');
}

// What a state log holds of a search: its first `count` states, why it stopped and where, and
// the steps that label each state with the action that first reached it.
struct Logged<'g> {
    count: usize,
    stopped: Option<&'g str>,
    expanding: usize,
    graph: Option<&'g Graph>,
}

// PROVE_IT_STATE_LOG: the states found, in TLC's order, as `state-log.ts` writes them.
fn write_state_log(
    path: &str,
    variables: &[&str],
    states: &States,
    store: &Store,
    logged: &Logged<'_>,
) {
    let (count, stopped, expanding, graph) =
        (logged.count, logged.stopped, logged.expanding, logged.graph);
    let Ok(file) = std::fs::File::create(path) else {
        return;
    };
    let mut writer = std::io::BufWriter::with_capacity(1 << 20, file);
    let mut line = String::new();
    line.push_str("{\"version\":1,\"variables\":[");
    for (index, variable) in variables.iter().enumerate() {
        if index > 0 {
            line.push(',');
        }
        write_json_text(&mut line, &variable.encode_utf16().collect::<Vec<u16>>());
    }
    let _ = write!(line, "],\"count\":{count},\"stopped\":");
    match stopped {
        Some(reason) => write_json_text(&mut line, &reason.encode_utf16().collect::<Vec<u16>>()),
        None => line.push_str("null"),
    }
    let _ = write!(line, ",\"expanding\":{expanding},\"order\":[");
    for (index, position) in states.order.iter().enumerate() {
        if index > 0 {
            line.push(',');
        }
        let _ = write!(line, "{position}");
    }
    line.push_str("],\"strings\":[");
    for (index, text) in store.get_string_order().iter().enumerate() {
        if index > 0 {
            line.push(',');
        }
        write_json_text(&mut line, text);
    }
    line.push(']');
    if let Some(key_width) = states.key_width {
        let _ = write!(line, ",\"keyWidth\":{key_width}");
    }
    line.push_str("}\n");
    // The action that first reached each state, when the search labels its steps.
    let mut actions = vec![-1i64; count];
    if let Some(Graph {
        edges,
        labels: Some(labels),
        ..
    }) = graph
    {
        let mut is_reached = vec![false; count];
        for (edge, &target) in edges.iter().enumerate() {
            let target = target as usize;
            if target >= count || is_reached[target] || states.parents[target] == -1 {
                continue;
            }
            is_reached[target] = true;
            actions[target] = i64::from(labels[edge]);
        }
    }
    let width = states.width;
    for (index, action) in actions.iter().enumerate() {
        let _ = write!(
            line,
            "[{index},{},{action},\"{:016x}\",",
            states.parents[index], states.fingerprints[index]
        );
        let encoded = states.encode(store, &states.ids[index * width..], width, 1);
        write_encoded(&mut line, &encoded);
        if let Some(key_width) = states.key_width {
            line.push(',');
            let encoded = states.encode(store, &states.keys[index * key_width..], key_width, 1);
            write_encoded(&mut line, &encoded);
        }
        line.push_str("]\n");
        if line.len() > 1 << 20 {
            let _ = writer.write_all(line.as_bytes());
            line.clear();
        }
    }
    let _ = writer.write_all(line.as_bytes());
    let _ = writer.flush();
}
