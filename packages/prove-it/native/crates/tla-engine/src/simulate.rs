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
use crate::compile::{Compiler, DIAMETER_SLOT, LEVEL_SLOT, NEXT_LEVEL_SLOT};
use crate::context::{EngineContext, first_failing_changed, holds, holds_all, holds_all_changed};
use crate::machine::{Generate, Machine, Registers, UNASSIGNED};
use crate::search::{
    ErrorSite, Reporter, SearchOutcome, Settings, StopCounts, Violation, ViolationKind,
    chosen_values, describe, is_engine_limit, is_noted_failure, report_printed, start,
    startup_values,
};

// TLC reports its progress every minute (`TLCGlobals.progressInterval`).
const PROGRESS_INTERVAL: Duration = Duration::from_secs(60);

// What a walk stops at once a successor violates an invariant, which the simulation then reports.
const VIOLATED: &str = "a simulation's violation";

// What a walk stops at once a step violates an action property, which the simulation then
// reports.
const ACTION_VIOLATED: &str = "a simulation's action property violation";

// What the simulation stops at once it noted where it failed evaluating the model, which TLC
// reports.
const FAILED: &str = "a simulation's failure";
/// Why the run stops where the initial predicate gives no state in the model.
const UNSATISFIED: &str = "no initial state in the model";

// Why the run stops at an initial state the initial predicate left incomplete, which the
// simulation then reports.
const INCOMPLETE_INITIAL: &str = "a simulation's incomplete initial state";

// A successor the next-state relation leaves incomplete, which TLC's simulator reports otherwise
// than a failure evaluating the model.
const INCOMPLETE_SUCCESSOR: &str = "a successor that isn't complete";

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
    /// Whether TLC generates (`-generate`): its walk of an action stops at the first successor it
    /// keeps, trying the disjuncts and the bindings in an order it draws (`Tool.probabilistic`).
    pub is_generated: bool,
    /// The name of the initial predicate TLC records as an initial state's action, and where it
    /// is written, where the caller knows them.
    pub initial_action: Option<(tla_ir::TextId, tla_ir::SourceRange)>,
}

pub enum SimulationOutcome {
    /// TLC stops before it computes the initial states, as the search reports it.
    Started(Box<SearchOutcome>),
    /// The engine doesn't follow TLC, for this reason.
    Declined(String),
    Simulated(Box<Simulated>),
    /// The initial predicate gave this many states and the constraints kept none, which
    /// `Simulator.simulate` reports as an error once it has checked each (`TLC_NO_STATES_SATISFYING_INIT`,
    /// or `..._AND_CONSTRAINT` where it gave some).
    Unsatisfied {
        generated: u64,
    },
    /// An initial state the initial predicate left without a value for some variable, which
    /// `Simulator.simulate` reports once it has counted the initial states and checked those
    /// before it (`TLC_STATE_NOT_COMPLETELY_SPECIFIED_INITIAL`).
    InitialIncomplete {
        state: Vec<Id>,
        holds_collapsed: bool,
        store: Box<Store>,
    },
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
    /// deadlock; or where TLC failed evaluating the model (`ViolationKind::Error`).
    pub violation: Option<Box<Violation>>,
    /// The position in the model's actions of the action whose successors TLC failed to compute,
    /// where it failed in the next states.
    pub failed_action: Option<u32>,
    /// Whether the failure is a successor the action left a variable unassigned in, the
    /// violation's last state, which `SimulationWorker.addElement` reports
    /// (`EC.TLC_STATE_NOT_COMPLETELY_SPECIFIED_NEXT`) with the trace to it.
    pub is_incomplete: bool,
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
    let mut is_defer_legacy = false;
    let (context, program, store, is_diameter_read) = loop {
        let mut store = Store::new();
        store.reset(ranked.iter().map(Vec::as_slice));
        store.freeze_string_order();
        let mut compiler = Compiler::new(ir, &mut store, settings.compile);
        compiler.workers = settings.workers;
        compiler.is_native = true;
        compiler.simulation = Some(*simulation);
        compiler.is_defer_legacy = is_defer_legacy;
        let context = EngineContext::build(&mut compiler, ir);
        if compiler.has_unsupported_deferred {
            is_defer_legacy = true;
            continue;
        }
        let context = match context {
            Ok(context) => context,
            Err(error) => return SimulationOutcome::Declined(describe(error)),
        };
        let is_diameter_read = compiler.is_simulated_diameter_read;
        break (context, compiler.finish(), store, is_diameter_read);
    };
    let Some(actions) = context.actions.as_ref() else {
        return SimulationOutcome::Declined("a next-state relation without TLC's actions".into());
    };
    let mut machine = Machine::new(&program, store);
    // TLCGet("diameter") is 0 on TLC's main thread, which checks the assumptions and computes
    // the initial states.
    match machine.store.int(0) {
        Ok(zero) => machine.set_slot(DIAMETER_SLOT, zero),
        Err(Bail(reason)) => return SimulationOutcome::Declined(reason.into()),
    }
    machine.simulation.is_simulated = true;
    if let Err(outcome) = start(&mut machine, &context, settings, reporter, None) {
        return SimulationOutcome::Started(outcome);
    }
    machine.startup_random = machine.random.state();
    // What TLCGet reads of the run once TLC's simulator runs: the record of each action, by the
    // state it made.
    let records = match action_records(ir, &mut machine.store, simulation) {
        Ok(records) => records,
        Err(Bail(reason)) => return SimulationOutcome::Declined(reason.into()),
    };
    machine.simulation = crate::machine::SimulationRun {
        is_running: true,
        is_simulated: true,
        is_endless: simulation.traces.is_none(),
        action: Some(records.unknown),
        action_names: records.names.clone(),
        started: Some(Instant::now()),
        ..crate::machine::SimulationRun::default()
    };
    let mut run = Run {
        context: &context,
        reporter,
        simulation,
        is_diameter_read,
        order: ir.tlc_order.iter().map(|&index| index as usize).collect(),
        check_deadlock: model.check_deadlock,
        generated: 0,
        traces: 0,
        lengths: 0,
        next_states: Vec::new(),
        deferred: Vec::new(),
        stopped: None,
        violated: (Vec::new(), 0),
        failing: None,
        failed_action: None,
        incomplete: None,
        is_incomplete: false,
        kept: 0,
        progressed: Instant::now(),
        records,
        walking: 0,
        incomplete_initial: None,
        live: (!model.live_formula.is_empty()).then(|| {
            (
                crate::search::to_terms(&model.live_formula),
                model
                    .live_properties
                    .iter()
                    .map(|property| crate::search::to_terms(&property.formula))
                    .collect(),
            )
        }),
    };
    let result = run.run(&mut machine, actions);
    let initial = match result {
        Ok(initial) => initial,
        Err(Bail(FAILED)) => (run.generated, run.kept),
        Err(Bail(UNSATISFIED)) => {
            return SimulationOutcome::Unsatisfied {
                generated: run.generated,
            };
        }
        Err(Bail(INCOMPLETE_INITIAL)) => {
            let state = run
                .incomplete_initial
                .take()
                .expect("the incomplete initial state");
            return SimulationOutcome::InitialIncomplete {
                state,
                holds_collapsed: machine.program.holds_collapsed(),
                store: Box::new(std::mem::replace(&mut machine.store, Store::new())),
            };
        }
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
                holds_collapsed: machine.program.holds_collapsed(),
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
        failed_action: run.failed_action,
        is_incomplete: run.is_incomplete,
    }))
}

struct Run<'r, 'c> {
    context: &'c EngineContext,
    reporter: &'r mut dyn Reporter,
    simulation: &'c Simulation,
    // Whether the model reads TLCGet("diameter").
    is_diameter_read: bool,
    // TLC's order of the variables.
    order: Vec<usize>,
    check_deadlock: bool,
    generated: u64,
    traces: u64,
    lengths: i64,
    // The successors of the current state the action taken has generated in the model.
    next_states: Vec<Vec<Id>>,
    deferred: Vec<Option<crate::machine::DeferredCall>>,
    // The violation, and the successor the walk stopped at with the invariant it violates.
    stopped: Option<Stopped>,
    violated: (Vec<Id>, usize),
    // Where a check of a successor failed to evaluate, with the successor: `None` for a check
    // whose failure isn't reported here, as a constraint's.
    failing: Option<(Option<ErrorSite>, Vec<Id>)>,
    failed_action: Option<u32>,
    // The successor the walk left incomplete, which stops it, and whether the stop is it.
    incomplete: Option<Vec<Id>>,
    is_incomplete: bool,
    // How many initial states are in the model.
    kept: u64,
    progressed: Instant,
    records: ActionRecords,
    // The position in the model's actions of the action the walk takes.
    walking: u32,
    // The first initial state the initial predicate left incomplete, once the run reached it.
    incomplete_initial: Option<Vec<Id>>,
    // The temporal properties TLC checks each behavior against (`LiveCheck1`): the formula of
    // their negations and the fairness, and each property's.
    live: Option<(Vec<tla_live::Term>, Vec<Vec<tla_live::Term>>)>,
}

// TLC's record of each action (`RecordValue(Action)`), which TLCGet("action") gives of the state
// it made, as the store holds it: none where the engine doesn't know it.
struct ActionRecords {
    // The initial predicate's, of an initial state.
    initial: Option<Id>,
    // Each of the model's actions'.
    actions: Vec<Option<Id>>,
    // `Action.UNKNOWN`'s, of the state TLC builds as it computes the initial states and of none.
    unknown: Id,
    // The name of each of the model's actions.
    names: Vec<Id>,
}

// `RecordValue(Action)`: the action's name and where it is written (`RecordValue(Location)`); an
// action TLC split from an operator with parameters has its context too, which isn't followed.
fn action_records(ir: &Ir, store: &mut Store, simulation: &Simulation) -> Outcome<ActionRecords> {
    let text =
        |store: &mut Store, text: &str| store.str(&text.encode_utf16().collect::<Vec<u16>>());
    let record = |store: &mut Store, name: &str, range: [i32; 4], module: &str| -> Outcome<Id> {
        let location_keys = ["beginLine", "beginColumn", "endLine", "endColumn", "module"]
            .map(|key| text(store, key));
        let mut location_values = Vec::with_capacity(5);
        for bound in range {
            location_values.push(store.int(i64::from(bound))?);
        }
        location_values.push(text(store, module));
        let location = store.function_of(&location_keys, &location_values)?;
        let keys = [text(store, "name"), text(store, "location")];
        let values = [text(store, name), location];
        store.function_of(&keys, &values)
    };
    let unknown = record(store, "UnnamedAction", [0; 4], "--TLA+ BUILTINS--")?;
    let initial = match simulation.initial_action {
        Some((name, range)) => Some(record(
            store,
            &ir.texts[name as usize],
            [
                range.start_line,
                range.start_column,
                range.end_line,
                range.end_column,
            ],
            &ir.texts[range.module as usize],
        )?),
        None => None,
    };
    let mut actions = Vec::with_capacity(ir.model.actions.len());
    let mut names = Vec::with_capacity(ir.model.actions.len());
    for action in &ir.model.actions {
        let name = &ir.texts[action.name as usize];
        names.push(text(store, name));
        // An action of no operator has no parameters; one of an operator a LET defines names
        // the values of its parameters in its label.
        let has_parameters = match action.definition {
            None => ir.texts[action.label as usize].contains('('),
            Some(definition) => !matches!(
                &ir.nodes.arena[ir.definitions[definition as usize] as usize].kind,
                tla_ir::NodeKind::Definition(definition)
                    if matches!(&definition.form, tla_ir::DefinitionForm::Operator(params) if params.is_empty())
            ),
        };
        actions.push(match action.location {
            Some(range) if !has_parameters => Some(record(
                store,
                name,
                [
                    range.start_line,
                    range.start_column,
                    range.end_line,
                    range.end_column,
                ],
                &ir.texts[range.module as usize],
            )?),
            _ => None,
        });
    }
    Ok(ActionRecords {
        initial,
        actions,
        unknown,
        names,
    })
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
        // `Tool.getInitStates`: every state the initial predicate gives, in its order, whether
        // or not it assigns every variable; the simulator checks that only as it goes through
        // them below.
        let mut initial = Vec::new();
        let walked = (context.init)(machine, &mut |machine: &mut Machine<'_>| {
            machine.deferred = None;
            initial.push(machine.current().to_vec());
            Ok(())
        });
        if let Err(bail) = walked {
            return Err(self.note_failure(machine, bail, ErrorSite::Init, Vec::new(), Vec::new()));
        }
        self.flush(machine);
        self.generated = initial.len() as u64;
        machine.simulation.generated = self.generated;
        // TLC checks each initial state, which its action made.
        machine.simulation.action = self.records.initial;
        self.reporter.initial_states_progress(self.generated);
        // Each is checked against the invariants, then kept where it is in the model.
        let one = machine.store.int(1)?;
        let mut states = Vec::new();
        for state in &initial {
            // `Tool.isGoodState`: the first state without a value for some variable stops the
            // run, after the states before it are checked against the invariants and the
            // constraints.
            if state.contains(&UNASSIGNED) {
                self.incomplete_initial = Some(state.clone());
                return Err(Bail(INCOMPLETE_INITIAL));
            }
            let epoch = machine.next_epoch();
            machine.set_current(state, epoch);
            machine.set_slot(LEVEL_SLOT, one);
            for (position, invariant) in context.initial_invariants.iter().enumerate() {
                let owner = context.initial_invariant_owners[position];
                let holds = match holds(machine, invariant) {
                    Ok(holds) => holds,
                    Err(bail) => {
                        let site = ErrorSite::InitialInvariant(owner as u32);
                        return Err(self.note_failure(
                            machine,
                            bail,
                            site,
                            vec![state.clone()],
                            Vec::new(),
                        ));
                    }
                };
                if !holds {
                    self.flush(machine);
                    self.stopped = Some(Stopped {
                        kind: ViolationKind::InitialInvariant(owner),
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
        if states.is_empty() {
            return Err(Bail(UNSATISFIED));
        }
        machine.set_slot(LEVEL_SLOT, zero);
        let kept = states.len() as u64;
        self.kept = kept;
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
            machine.simulation.traces = self.traces;
            // TLCGet("diameter") on the worker is the number of the trace it generates
            // (`SimulationWorker.getTraceCnt`), up to Java's largest int. The store keeps every
            // integer it makes, so the slot, which keys what the engine caches of the expressions
            // that read it, is set only where the model reads it and the simulation ends: one
            // without end holds no value per trace, and declines a read of the diameter.
            if self.is_diameter_read && simulation.traces.is_some() {
                let diameter = machine.store.int(self.traces.min(i32::MAX as u64) as i64)?;
                machine.set_slot(DIAMETER_SLOT, diameter);
            }
            let is_violated = self
                .simulate_trace(machine, actions, &states, &mut random)
                .map_err(|bail| {
                    if bail.0 == FAILED {
                        bail
                    } else {
                        decline_failure(bail)
                    }
                })?;
            if is_violated || machine.registers.is_exit {
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
        machine.simulation.steps.clear();
        let count = actions.len();
        let mut step = 0;
        while step < self.simulation.depth && !machine.registers.is_exit {
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
            self.deferred.clear();
            machine.deferred = None;
            let current = path.last().to_vec();
            machine.simulation.action = match path.actions.last() {
                Some(&action) => self.records.actions[action as usize],
                None => self.records.initial,
            };
            let level = path.length as i64;
            let level_id = machine.store.int(level)?;
            let next_level_id = machine.store.int(level + 1)?;
            let mut index = random.next_index(count);
            let stride = next_prime(random) as usize;
            for _ in 0..count {
                machine.deferred = None;
                let epoch = machine.next_epoch();
                machine.set_current(&current, epoch);
                machine.next.clear();
                machine.next.resize(current.len(), UNASSIGNED);
                machine.reset_assigned();
                machine.set_slot(LEVEL_SLOT, level_id);
                machine.set_slot(NEXT_LEVEL_SLOT, next_level_id);
                self.walking = index as u32;
                // The worker's generator draws the disjuncts the walk tries, as it draws the
                // actions (`TLCGlobals.simulator.getRNG`).
                if self.simulation.is_generated {
                    machine.generate = Some(Generate {
                        random: *random,
                        has_states: false,
                    });
                }
                let walked = actions[index](machine, &mut |machine: &mut Machine<'_>| {
                    self.visit(machine, &current, epoch, (level_id, next_level_id))
                });
                if let Some(generate) = machine.generate.take() {
                    *random = generate.random;
                }
                self.flush(machine);
                match walked {
                    Ok(()) => {}
                    Err(Bail(reason @ (VIOLATED | ACTION_VIOLATED))) => {
                        let (successor, owner) = std::mem::take(&mut self.violated);
                        path.push(&successor, index as u32);
                        let kind = if reason == VIOLATED {
                            ViolationKind::Invariant(owner)
                        } else {
                            ViolationKind::ActionProperty(owner)
                        };
                        self.stop(machine, &path, kind).map_err(decline_failure)?;
                        return Ok(true);
                    }
                    // `SimulationWorker.addElement` reports a check of a successor that fails
                    // with the trace to the successor, and the worker's `simulateAndReport` any
                    // other error with the trace to the state it was expanding.
                    Err(bail) => {
                        let site = match self.failing.take() {
                            Some((Some(site), successor)) => {
                                path.push(&successor, index as u32);
                                site
                            }
                            Some((None, _)) => return Err(decline_failure(bail)),
                            None => {
                                self.failed_action = Some(index as u32);
                                ErrorSite::Next
                            }
                        };
                        // `SimulationWorker.addElement` throws an incomplete successor with the
                        // trace to it, which TLC prints with the variables it lacks.
                        if bail.0 == INCOMPLETE_SUCCESSOR
                            && site == ErrorSite::Next
                            && machine.output.is_empty()
                            && let Some(successor) = self.incomplete.take()
                        {
                            path.push(&successor, index as u32);
                            self.is_incomplete = true;
                            let kind = ViolationKind::Error { site };
                            self.stop(machine, &path, kind).map_err(decline_failure)?;
                            return Err(Bail(FAILED));
                        }
                        if bail.0 == INCOMPLETE_SUCCESSOR
                            || !is_noted_failure(bail.0)
                            || !machine.output.is_empty()
                        {
                            return Err(decline_failure(bail));
                        }
                        let kind = ViolationKind::Error { site };
                        self.stop(machine, &path, kind).map_err(decline_failure)?;
                        return Err(Bail(FAILED));
                    }
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
                    self.stop(machine, &path, kind).map_err(decline_failure)?;
                    return Ok(true);
                }
                break;
            }
            let chosen = random.next_index(self.next_states.len());
            if let Some(deferred) = self.deferred[chosen].take() {
                // What TLCGet reads of the state the deferred expression runs in isn't followed.
                machine.simulation.action = None;
                let locals = std::mem::replace(&mut machine.locals, deferred.locals);
                let epoch = machine.next_epoch();
                machine.set_current(&deferred.current, epoch);
                machine.set_next(&deferred.next);
                let executed = (deferred.evaluate)(machine);
                machine.locals = locals;
                self.flush(machine);
                executed.map_err(decline_failure)?;
            }
            path.push(&self.next_states[chosen], index as u32);
            machine.simulation.steps.push(index as u32);
        }
        if machine.registers.is_exit {
            return Ok(false);
        }
        // `SimulationWorker.simulateRandomTrace` checks the behavior against the temporal
        // properties before it counts its length, at the level its last state has then.
        let level = match self.live {
            Some(_) => match self.check_liveness(machine, &path)? {
                Some(level) => level,
                None => return Ok(true),
            },
            None => path.length,
        };
        let length = i64::from(self.simulation.depth).min(level as i64);
        self.lengths = add_length(self.lengths, length, self.traces);
        machine.simulation.lengths = self.lengths;
        Ok(false)
    }

    // Notes where TLC's main thread failed evaluating the model, with the states it was working
    // on, which TLC reports: a failure the evaluator of failures words, where the spec printed
    // nothing in the evaluation that failed. Any other stop declines.
    fn note_failure(
        &mut self,
        machine: &Machine<'_>,
        bail: Bail,
        site: ErrorSite,
        states: Vec<Vec<Id>>,
        labels: Vec<Option<u32>>,
    ) -> Bail {
        if !is_noted_failure(bail.0) || !machine.output.is_empty() {
            return decline_failure(bail);
        }
        self.stopped = Some(Stopped {
            kind: ViolationKind::Error { site },
            states,
            labels,
            registers: machine.registers.clone(),
        });
        Bail(FAILED)
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
            && !matches!(kind, ViolationKind::Error { .. })
            && !machine.program.holds_collapsed()
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

    // `LiveCheck1.checkTrace` of the behavior, without the steps that stutter
    // (`SimulationWorker.getTrace`): none where it found a counterexample, which stops the
    // simulation, or else the level of the behavior's last state as the trace leaves it. The
    // checker evaluates the atoms as TLC asks for them, on the machine.
    //
    // `getTrace` drops each state equal to the one before it and gives every state it keeps its
    // position in what remains as its level (`setPredecessor`), so the behavior's last state is
    // as deep as the states kept, unless the last step stutters: a state it drops keeps the
    // level it was generated at.
    fn check_liveness(&mut self, machine: &mut Machine<'_>, path: &Path) -> Outcome<Option<usize>> {
        let context = self.context;
        if context.is_live_printing || context.diameter_atoms.contains(&true) {
            return Err(Bail(
                "unsupported: a simulated behavior's temporal properties whose atoms print or read the diameter",
            ));
        }
        let mut kept = Vec::new();
        for position in 0..path.length {
            if position > 0
                && self.is_equal(machine, path.state(position), path.state(position - 1))?
            {
                continue;
            }
            kept.push(position);
        }
        let level = if kept.last() == Some(&(path.length - 1)) {
            kept.len()
        } else {
            path.length
        };
        // The graph of the behavior: its distinct states, and the steps from each, in the order
        // the behavior takes them first.
        let width = path.width;
        let mut states: Vec<Id> = Vec::new();
        let mut indices: std::collections::HashMap<&[Id], u32> = std::collections::HashMap::new();
        let mut trace = Vec::with_capacity(kept.len());
        for &position in &kept {
            let state = path.state(position);
            let next = indices.len() as u32;
            let index = *indices.entry(state).or_insert_with(|| {
                states.extend_from_slice(state);
                next
            });
            trace.push(index);
        }
        let count = indices.len();
        let mut successors: Vec<Vec<u32>> = vec![Vec::new(); count];
        for pair in trace.windows(2) {
            let steps = &mut successors[pair[0] as usize];
            if !steps.contains(&pair[1]) {
                steps.push(pair[1]);
            }
        }
        let mut edge_offsets = vec![0u32];
        let mut edges = Vec::new();
        for steps in &successors {
            edges.extend_from_slice(steps);
            edge_offsets.push(edges.len() as u32);
        }
        let parents = vec![-1; count];
        let fingerprints = vec![0; count];
        let graph = tla_live::Graph {
            parents: &parents,
            edge_offsets: &edge_offsets,
            edges: &edges,
            fingerprints: &fingerprints,
            reals: None,
            diameters: None,
            levels: None,
        };
        let (formula, properties) = self.live.as_ref().expect("the temporal properties");
        let properties: Vec<&[tla_live::Term]> = properties.iter().map(Vec::as_slice).collect();
        let found = {
            let answers = crate::live::LiveAnswers {
                machine: std::cell::RefCell::new(&mut *machine),
                atoms: &context.atoms,
                states: &states,
                width,
                edges: &edges,
            };
            tla_live::check_trace(
                formula,
                &properties,
                &tla_live::Source {
                    graph: &graph,
                    answers: &answers,
                },
                &trace,
            )
        };
        if !machine.output.is_empty() {
            return Err(Bail(
                "unsupported: a simulated behavior's temporal properties whose atoms print",
            ));
        }
        let (counterexample, violated) = match found {
            Ok(Some(found)) => found,
            Ok(None) => return Ok(Some(level)),
            Err(_) => {
                return Err(Bail(
                    "unsupported: a simulated behavior's temporal properties the checker declines",
                ));
            }
        };
        let printed = &kept[..counterexample.length];
        let back =
            (!counterexample.is_stuttering).then(|| path.actions[kept[counterexample.length] - 1]);
        self.stopped = Some(Stopped {
            kind: ViolationKind::SimulatedLasso {
                loop_start: counterexample.loop_start,
                back,
                violated,
            },
            states: printed
                .iter()
                .map(|&position| path.state(position).to_vec())
                .collect(),
            labels: printed
                .iter()
                .skip(1)
                .map(|&position| Some(path.actions[position - 1]))
                .collect(),
            registers: machine.registers.clone(),
        });
        Ok(None)
    }

    // `TLCStateMut.equals`.
    fn is_equal(&self, machine: &mut Machine<'_>, left: &[Id], right: &[Id]) -> Outcome<bool> {
        for &variable in &self.order {
            let (left, right) = (left[variable], right[variable]);
            // A variable an incomplete successor lacks equals only another that lacks it.
            if left != right
                && (left == UNASSIGNED
                    || right == UNASSIGNED
                    || !machine.store.equals_asked(left, right)?)
            {
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
            // Where the walk generates (`-generate`), its draws aren't followed past it.
            if machine.generate.is_some() {
                return Err(Bail("unsupported: a successor that isn't complete"));
            }
            self.incomplete = Some(machine.next().to_vec());
            return Err(Bail(INCOMPLETE_SUCCESSOR));
        }
        self.generated += 1;
        machine.simulation.generated = self.generated;
        let successor = machine.next().to_vec();
        let deferred = machine.deferred.take().map(|mut deferred| {
            for (value, assigned) in deferred.current.iter_mut().zip(machine.current()) {
                if *value == UNASSIGNED {
                    *value = *assigned;
                }
            }
            for (value, assigned) in deferred.next.iter_mut().zip(&successor) {
                if *value == UNASSIGNED {
                    *value = *assigned;
                }
            }
            deferred
        });
        let successor_epoch = machine.next_epoch();
        let walking = (self.walking, self.records.actions[self.walking as usize]);
        to_successor(machine, successor_epoch, next_level_id, walking);
        let failing = first_failing_changed(machine, &context.invariants, &successor, current);
        to_current(machine, epoch, level_id);
        match failing {
            Ok(None) => {}
            Ok(Some(failing)) => {
                self.violated = (successor, context.invariant_owners[failing]);
                return Err(Bail(VIOLATED));
            }
            Err((failing, bail)) => {
                let owner = context.invariant_owners[failing] as u32;
                self.failing = Some((Some(ErrorSite::Invariant(owner)), successor));
                return Err(bail);
            }
        }
        for (position, (action, unchanged)) in context.action_properties.iter().enumerate() {
            let holds = holds(machine, action)
                .and_then(|is_held| Ok(is_held || holds(machine, unchanged)?));
            match holds {
                Ok(true) => {}
                Ok(false) => {
                    self.violated = (successor, position);
                    return Err(Bail(ACTION_VIOLATED));
                }
                Err(bail) => {
                    let site = ErrorSite::ActionProperty(position as u32);
                    self.failing = Some((Some(site), successor));
                    return Err(bail);
                }
            }
        }
        to_successor(machine, successor_epoch, next_level_id, walking);
        let is_state_in_model =
            holds_all_changed(machine, &context.constraints, &successor, current);
        to_current(machine, epoch, level_id);
        // A constraint that fails to evaluate isn't reported here.
        let is_in_model = is_state_in_model
            .and_then(|is_in| Ok(is_in && holds_all(machine, &context.action_constraints)?));
        let is_in_model = match is_in_model {
            Ok(is_in_model) => is_in_model,
            Err(bail) => {
                self.failing = Some((None, successor));
                return Err(bail);
            }
        };
        if is_in_model {
            if let Some(generate) = machine.generate.as_mut() {
                generate.has_states = true;
            }
            self.next_states.push(successor);
            self.deferred.push(machine.deferred.take().or(deferred));
        }
        Ok(())
    }
}

// The successor as the state TLC checks, made by the action the walk takes: the action and the
// steps TLCGet reads are its.
fn to_successor(
    machine: &mut Machine<'_>,
    epoch: u64,
    level: Id,
    (walking, record): (u32, Option<Id>),
) {
    swap(machine, epoch, level);
    let run = &mut machine.simulation;
    run.steps.push(walking);
    std::mem::swap(&mut run.action, &mut run.expanding_action);
    run.action = record;
}

// Back to the state the walk expands, after `to_successor`.
fn to_current(machine: &mut Machine<'_>, epoch: u64, level: Id) {
    swap(machine, epoch, level);
    let run = &mut machine.simulation;
    run.steps.pop();
    run.action = run.expanding_action.take();
}

// While a successor is checked as a state, it is current and the state the walk is expanding is
// the next one, which a state's predicates don't read: the two swap rather than copy.
fn swap(machine: &mut Machine<'_>, epoch: u64, level: Id) {
    std::mem::swap(&mut machine.cur, &mut machine.next);
    machine.epoch = epoch;
    machine.set_slot(LEVEL_SLOT, level);
}

// A failure TLC reports evaluating the model where the simulation doesn't note it, or the engine's
// own limit.
fn decline_failure(bail: Bail) -> Bail {
    if is_engine_limit(bail.0) {
        return bail;
    }
    Bail("unsupported: a failure evaluating the model in a simulation")
}
