//! TLC's random simulation (`-simulate`), as `Simulator` and `SimulationWorker` run it on one
//! worker: from an initial state drawn at random, each step tries TLC's actions from one drawn at
//! random, striding by a prime drawn at random, until one has successors, and goes on to one of
//! them drawn at random, until the trace is as deep as `-depth` or deadlocks. Every successor is
//! checked against the invariants as it is generated. The draws follow TLC's `RandomGenerator`
//! call for call, so a run with the same seed takes the same traces.

use std::time::Duration;

use tla_ir::Ir;
use tla_values::print::is_printable;
use tla_values::random::{JavaRandom, next_prime};
use tla_values::store::Outcome;
use tla_values::{Bail, Id, Store};

use crate::clock::Instant;
use crate::compile::{Compiler, LEVEL_SLOT, NEXT_LEVEL_SLOT};
use crate::context::{EngineContext, first_failing_changed, holds, holds_all, holds_all_changed};
use crate::machine::{Machine, Registers, UNASSIGNED};
use crate::search::{
    Reporter, SearchOutcome, Settings, StopCounts, Violation, ViolationKind, chosen_values,
    describe, is_engine_limit, report_printed, start, startup_values,
};

// TLC reports its progress every minute (`TLCGlobals.progressInterval`).
const PROGRESS_INTERVAL: Duration = Duration::from_secs(60);

// What a walk stops at once a successor violates an invariant, which the simulation then reports.
const VIOLATED: &str = "a simulation's violation";

/// What a simulation runs besides the model, from TLC's command line.
#[derive(Clone, Copy, Debug)]
pub struct Simulation {
    /// How many traces to generate (`-simulate num=`), or none for no end.
    pub traces: Option<u64>,
    /// The most steps a trace takes (`-depth`), `i32::MAX` for `-depth -1`.
    pub depth: i32,
    /// The seed (`-seed`), and how many draws to skip after seeding (`-aril`).
    pub seed: i64,
    pub aril: i64,
}

pub enum SimulationOutcome {
    /// TLC stops before it computes the initial states, as the search reports it.
    Started(Box<SearchOutcome>),
    /// The engine doesn't follow TLC, for this reason.
    Declined(String),
    Simulated(Box<Simulated>),
}

/// What TLC reports of a simulation.
pub struct Simulated {
    /// How many initial states the initial predicate gave, and how many of them are in the model.
    pub initial_generated: u64,
    pub initial_states: u64,
    /// The states TLC counts as checked: every initial state and every successor.
    pub generated: u64,
    /// The traces TLC started.
    pub traces: u64,
    /// The mean (low 32 bits) and the sum of squared deviations (high 32 bits) of the lengths of
    /// the traces that ended without a violation, as TLC keeps them (Welford's algorithm).
    pub lengths: i64,
    /// The first violation, whose trace TLC prints: of an initial state, an invariant, or a
    /// deadlock.
    pub violation: Option<Box<Violation>>,
}

/// Folds the length of a trace into TLC's packed mean and squared deviations, the `traces`-th
/// (`SimulationWorkerStatistics.collectPostTrace`), wrapping as Java's ints and longs do.
pub fn add_length(lengths: i64, length: i64, traces: u64) -> i64 {
    let mean = (lengths & 0xFFFF_FFFF) as i32;
    let squares = ((lengths as u64) >> 32) as i64;
    let delta = length.wrapping_sub(i64::from(mean));
    let mean = mean.wrapping_add((delta / traces.max(1) as i64) as i32);
    let squares = squares.wrapping_add(delta.wrapping_mul(length.wrapping_sub(i64::from(mean))));
    squares.wrapping_shl(32) | (i64::from(mean) & 0xFFFF_FFFF)
}

// The states of a trace TLC's worker walks, end to end in one vector of `width` ids each, and
// the position among TLC's actions of the action that took each step: a long trace keeps eight
// bytes a step for a state of one variable.
struct Path {
    width: usize,
    length: usize,
    ids: Vec<Id>,
    actions: Vec<u32>,
}

impl Path {
    fn new(initial: &[Id]) -> Path {
        Path {
            width: initial.len(),
            length: 1,
            ids: initial.to_vec(),
            actions: Vec::new(),
        }
    }

    fn state(&self, position: usize) -> &[Id] {
        &self.ids[position * self.width..(position + 1) * self.width]
    }

    fn last(&self) -> &[Id] {
        self.state(self.length - 1)
    }

    fn push(&mut self, state: &[Id], action: u32) {
        self.ids.extend_from_slice(state);
        self.actions.push(action);
        self.length += 1;
    }
}

// The trace a violation stopped, with the registers as they were then.
struct Stopped {
    kind: ViolationKind,
    states: Vec<Vec<Id>>,
    labels: Vec<Option<u32>>,
    registers: Registers,
}

/// Simulates the model the IR describes as TLC does on one worker. It runs compiled closures,
/// which recurse with the expressions and values, so its caller runs it on a thread with a deep
/// stack.
pub fn simulate(
    ir: &Ir,
    settings: &Settings,
    simulation: &Simulation,
    reporter: &mut dyn Reporter,
) -> SimulationOutcome {
    let model = &ir.model;
    let ranked: Vec<Vec<u16>> = (0..ir.ranked_count)
        .map(|text| ir.get_text_units(text))
        .collect();
    let mut store = Store::new();
    store.reset(ranked.iter().map(Vec::as_slice));
    store.freeze_string_order();
    let mut compiler = Compiler::new(ir, &mut store, settings.compile);
    compiler.workers = settings.workers;
    compiler.is_native = true;
    compiler.simulation = Some(*simulation);
    let context = match EngineContext::build(&mut compiler, ir) {
        Ok(context) => context,
        Err(error) => return SimulationOutcome::Declined(describe(error)),
    };
    let Some(actions) = context.actions.as_ref() else {
        return SimulationOutcome::Declined("a next-state relation without TLC's actions".into());
    };
    let program = compiler.finish();
    let mut machine = Machine::new(&program, store);
    if let Err(outcome) = start(&mut machine, &context, settings, reporter) {
        return SimulationOutcome::Started(outcome);
    }
    machine.startup_random = machine.random.state();
    let mut run = Run {
        context: &context,
        reporter,
        simulation,
        order: ir.tlc_order.iter().map(|&index| index as usize).collect(),
        check_deadlock: model.check_deadlock,
        generated: 0,
        traces: 0,
        lengths: 0,
        next_states: Vec::new(),
        stopped: None,
        violated: (Vec::new(), 0),
        progressed: Instant::now(),
    };
    let result = run.run(&mut machine, actions);
    let initial = match result {
        Ok(initial) => initial,
        Err(Bail(reason)) => return SimulationOutcome::Declined(reason.into()),
    };
    let violation = match run.stopped.take() {
        Some(stopped) => {
            // The store goes with the violation, so whether the simulation ranked strings is
            // read here.
            if machine.store.has_unordered_strings() {
                return SimulationOutcome::Declined(
                    "unsupported: a violation's trace after ToString ranked strings".into(),
                );
            }
            let Ok(startup) = startup_values(&mut machine, &context) else {
                return SimulationOutcome::Declined(
                    "unsupported: the startup's values of a violation's trace".into(),
                );
            };
            let chosen = chosen_values(&mut machine, &context);
            Some(Box::new(Violation {
                chosen,
                kind: stopped.kind,
                states: stopped.states,
                labels: stopped.labels,
                counts: StopCounts::default(),
                store: std::mem::replace(&mut machine.store, Store::new()),
                startup,
                startup_random: machine.startup_random,
                random: None,
                symmetry: None,
                registers: stopped.registers,
                possible: Vec::new(),
                fingerprints: Vec::new(),
                added: None,
            }))
        }
        None => None,
    };
    SimulationOutcome::Simulated(Box::new(Simulated {
        initial_generated: initial.0,
        initial_states: initial.1,
        generated: run.generated,
        traces: run.traces,
        lengths: run.lengths,
        violation,
    }))
}

struct Run<'r, 'c> {
    context: &'c EngineContext,
    reporter: &'r mut dyn Reporter,
    simulation: &'c Simulation,
    // TLC's order of the variables.
    order: Vec<usize>,
    check_deadlock: bool,
    generated: u64,
    traces: u64,
    lengths: i64,
    // The successors of the current state the action taken has generated in the model.
    next_states: Vec<Vec<Id>>,
    // The violation, and the successor the walk stopped at with the invariant it violates.
    stopped: Option<Stopped>,
    violated: (Vec<Id>, usize),
    progressed: Instant,
}

impl Run<'_, '_> {
    // What the spec printed goes out as it runs.
    fn flush(&mut self, machine: &mut Machine<'_>) {
        for printed in &std::mem::take(&mut machine.output) {
            report_printed(self.reporter, &machine.store, printed);
        }
    }

    // TLC's main thread: the initial states, then the worker's traces. Returns how many initial
    // states the initial predicate gave and how many are in the model.
    fn run(&mut self, machine: &mut Machine<'_>, actions: &[crate::Step]) -> Outcome<(u64, u64)> {
        let context = self.context;
        let width = context.width;
        let unassigned = vec![UNASSIGNED; width];
        machine.set_current(&unassigned, 0);
        machine.set_next(&unassigned);
        machine.reset_assigned();
        let zero = machine.store.int(0)?;
        machine.set_slot(LEVEL_SLOT, zero);
        // `Tool.getInitStates`: every state the initial predicate gives, in its order.
        let mut initial = Vec::new();
        (context.init)(machine, &mut |machine: &mut Machine<'_>| {
            if machine.current().contains(&UNASSIGNED) {
                return Err(Bail("unsupported: an initial state that isn't complete"));
            }
            initial.push(machine.current().to_vec());
            Ok(())
        })
        .map_err(decline_failure)?;
        self.flush(machine);
        self.generated = initial.len() as u64;
        self.reporter.initial_states_progress(self.generated);
        // Each is checked against the invariants, then kept where it is in the model.
        let one = machine.store.int(1)?;
        let mut states = Vec::new();
        for state in &initial {
            let epoch = machine.next_epoch();
            machine.set_current(state, epoch);
            machine.set_slot(LEVEL_SLOT, one);
            for (position, invariant) in context.initial_invariants.iter().enumerate() {
                let holds = holds(machine, invariant).map_err(decline_failure)?;
                if !holds {
                    self.flush(machine);
                    self.stopped = Some(Stopped {
                        kind: ViolationKind::InitialInvariant(
                            context.initial_invariant_owners[position],
                        ),
                        states: vec![state.clone()],
                        labels: Vec::new(),
                        registers: machine.registers.clone(),
                    });
                    return Ok((self.generated, 0));
                }
            }
            let mut is_in_model = true;
            for constraint in &context.constraints {
                is_in_model = holds(machine, &constraint.eval).map_err(decline_failure)?;
                if !is_in_model {
                    break;
                }
            }
            self.flush(machine);
            if is_in_model {
                states.push(state.clone());
            }
        }
        if initial.is_empty() {
            return Err(Bail("unsupported: no initial state"));
        }
        if states.is_empty() {
            return Err(Bail("unsupported: no initial state in the model"));
        }
        machine.set_slot(LEVEL_SLOT, zero);
        let kept = states.len() as u64;
        self.reporter.initial_states(self.generated, kept);
        // `TLC.process` seeds the generator, skips -aril draws, and draws each worker's seed.
        let simulation = self.simulation;
        let mut seeding = JavaRandom::seeded(simulation.seed as u64);
        for _ in 0..simulation.aril {
            seeding.next_double();
        }
        let mut random = JavaRandom::seeded(seeding.next_long() as u64);
        // The worker's thread draws RandomElement from a generator of its own, seeded as the
        // main thread's was (`RandomEnumerableValues`).
        machine.seed_random(0);
        // The simulation stops at the first violation: TLC's worker goes on as its main thread
        // prints the trace, up to a trace of its own choosing, so only a violation in the last
        // trace leaves counts the caller can report.
        loop {
            self.traces += 1;
            let is_violated = self
                .simulate_trace(machine, actions, &states, &mut random)
                .map_err(decline_failure)?;
            if is_violated {
                break;
            }
            if simulation
                .traces
                .is_some_and(|traces| self.traces >= traces)
            {
                break;
            }
        }
        Ok((self.generated, kept))
    }

    // `SimulationWorker.simulateRandomTrace`.
    fn simulate_trace(
        &mut self,
        machine: &mut Machine<'_>,
        actions: &[crate::Step],
        initial: &[Vec<Id>],
        random: &mut JavaRandom,
    ) -> Outcome<bool> {
        let mut path = Path::new(&initial[random.next_index(initial.len())]);
        let count = actions.len();
        let mut step = 0;
        while step < self.simulation.depth {
            step += 1;
            if self.reporter.is_cancelled() {
                return Err(Bail("unsupported: the caller cancelled the simulation"));
            }
            if self.progressed.elapsed() >= PROGRESS_INTERVAL {
                self.progressed = Instant::now();
                self.reporter
                    .simulation_progress(self.generated, self.traces, self.lengths);
            }
            self.next_states.clear();
            let current = path.last().to_vec();
            let level = path.length as i64;
            let level_id = machine.store.int(level)?;
            let next_level_id = machine.store.int(level + 1)?;
            let mut index = random.next_index(count);
            let stride = next_prime(random) as usize;
            for _ in 0..count {
                let epoch = machine.next_epoch();
                machine.set_current(&current, epoch);
                machine.next.clear();
                machine.next.resize(current.len(), UNASSIGNED);
                machine.reset_assigned();
                machine.set_slot(LEVEL_SLOT, level_id);
                machine.set_slot(NEXT_LEVEL_SLOT, next_level_id);
                let walked = actions[index](machine, &mut |machine: &mut Machine<'_>| {
                    self.visit(machine, &current, epoch, (level_id, next_level_id))
                });
                self.flush(machine);
                match walked {
                    Ok(()) => {}
                    Err(Bail(VIOLATED)) => {
                        let (successor, owner) = std::mem::take(&mut self.violated);
                        path.push(&successor, index as u32);
                        let kind = ViolationKind::Invariant(owner);
                        self.stop(machine, &path, kind)?;
                        return Ok(true);
                    }
                    Err(bail) => return Err(bail),
                }
                if !self.next_states.is_empty() {
                    break;
                }
                index = (index + stride) % count;
            }
            if self.next_states.is_empty() {
                if self.check_deadlock {
                    let kind = ViolationKind::Deadlock {
                        accepted: None,
                        atom: None,
                    };
                    self.stop(machine, &path, kind)?;
                    return Ok(true);
                }
                break;
            }
            let chosen = random.next_index(self.next_states.len());
            path.push(&self.next_states[chosen], index as u32);
        }
        let length = i64::from(self.simulation.depth).min(path.length as i64);
        self.lengths = add_length(self.lengths, length, self.traces);
        Ok(false)
    }

    // A trace a violation stopped, without the steps that stutter, as TLC prints it
    // (`SimulationWorker.getTrace`).
    fn stop(&mut self, machine: &mut Machine<'_>, path: &Path, kind: ViolationKind) -> Outcome<()> {
        // From the last state back, a state equal to the one before it is dropped. TLC compares
        // the states' values in its order of the variables, up to the first that differs, which
        // fails where TLC can't compare them.
        let mut kept = Vec::new();
        for position in (0..path.length).rev() {
            let is_stuttering = position > 0
                && self.is_equal(machine, path.state(position), path.state(position - 1))?;
            if !is_stuttering {
                kept.push(position);
            }
        }
        kept.reverse();
        // With -depth -1 TLC prints the last state alone (`Simulator.printBehavior`): where the
        // store prints it as TLC does, that state is all the report takes.
        let last = path.state(*kept.last().expect("the initial state"));
        if self.simulation.depth == i32::MAX
            && last
                .iter()
                .all(|&value| is_printable(&machine.store, value))
        {
            kept.drain(..kept.len() - 1);
        }
        self.stopped = Some(Stopped {
            kind,
            states: kept
                .iter()
                .map(|&position| path.state(position).to_vec())
                .collect(),
            labels: kept
                .iter()
                .skip(1)
                .map(|&position| Some(path.actions[position - 1]))
                .collect(),
            registers: machine.registers.clone(),
        });
        Ok(())
    }

    // `TLCStateMut.equals`.
    fn is_equal(&self, machine: &mut Machine<'_>, left: &[Id], right: &[Id]) -> Outcome<bool> {
        for &variable in &self.order {
            let (left, right) = (left[variable], right[variable]);
            if left != right && !machine.store.equals_asked(left, right)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    // `SimulationWorker.addElement`: a successor the walk completed, checked against the
    // invariants and the action properties, then kept where it is in the model.
    fn visit(
        &mut self,
        machine: &mut Machine<'_>,
        current: &[Id],
        epoch: u64,
        (level_id, next_level_id): (Id, Id),
    ) -> Outcome<()> {
        let context = self.context;
        if machine.next().contains(&UNASSIGNED) {
            return Err(Bail("unsupported: a successor that isn't complete"));
        }
        self.generated += 1;
        let successor = machine.next().to_vec();
        let successor_epoch = machine.next_epoch();
        swap(machine, successor_epoch, next_level_id);
        let failing = first_failing_changed(machine, &context.invariants, &successor, current);
        swap(machine, epoch, level_id);
        match failing {
            Ok(None) => {}
            Ok(Some(failing)) => {
                self.violated = (successor, context.invariant_owners[failing]);
                return Err(Bail(VIOLATED));
            }
            Err((_, bail)) => return Err(bail),
        }
        for (action, unchanged) in &context.action_properties {
            if !holds(machine, action)? && !holds(machine, unchanged)? {
                return Err(Bail("unsupported: an action property violated"));
            }
        }
        swap(machine, successor_epoch, next_level_id);
        let is_state_in_model =
            holds_all_changed(machine, &context.constraints, &successor, current);
        swap(machine, epoch, level_id);
        if is_state_in_model? && holds_all(machine, &context.action_constraints)? {
            self.next_states.push(successor);
        }
        Ok(())
    }
}

// While a successor is checked as a state, it is current and the state the walk is expanding is
// the next one, which a state's predicates don't read: the two swap rather than copy.
fn swap(machine: &mut Machine<'_>, epoch: u64, level: Id) {
    std::mem::swap(&mut machine.cur, &mut machine.next);
    machine.epoch = epoch;
    machine.set_slot(LEVEL_SLOT, level);
}

// A failure TLC reports evaluating the model, which the simulation doesn't print yet, or the
// engine's own limit.
fn decline_failure(bail: Bail) -> Bail {
    if is_engine_limit(bail.0) {
        return bail;
    }
    Bail("unsupported: a failure evaluating the model in a simulation")
}
