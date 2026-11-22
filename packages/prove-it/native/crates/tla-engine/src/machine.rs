//! The registers compiled code reads, as `compile.ts`'s `CUR`, `NXT`, `LOC`, `STACK` and `EPOCH`,
//! and the caches a compiled program fills as it runs. A [`Program`] is what compiling leaves
//! besides the closures: the bodies of recursive definitions, which the closures that call them
//! find by number, and how many caches of each kind to make. A [`Machine`] runs closures of one
//! program on one store.

use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Arc, OnceLock};

use tla_ir::NodeId;
pub use tla_ir::RuntimeWarning;
use tla_values::fingerprint::{Fingerprints, Polynomial};
use tla_values::store::{Outcome, ShapeJoin};
use tla_values::{Bail, Id, Store};

use crate::compile::Lambda;
use crate::compile::lazy::Lazy;
use crate::memo::{EMPTY, EPOCH_KEYS, EpochCache, MemoTable};
use tla_values::random::JavaRandom;

/// A compiled expression: its value, or where TLC would fail, or the engine hands over.
pub type Eval = Arc<dyn Fn(&mut Machine<'_>) -> Outcome<Id> + Send + Sync>;
/// A membership test that builds its set only when it must.
pub type Member = Arc<dyn Fn(&mut Machine<'_>, Id) -> Outcome<bool> + Send + Sync>;
/// What TLC evaluates to make a set's value, evaluated without building the set.
pub type Parts = Arc<dyn Fn(&mut Machine<'_>) -> Outcome<()> + Send + Sync>;
/// What a walk of an action does with each state it completes.
pub type Continue<'c> = dyn FnMut(&mut Machine<'_>) -> Outcome<()> + 'c;
/// A walk of the initial predicate or of an action, in TLC's order, calling its continuation once
/// for each state it completes (`Step` in `action.ts`).
pub type Step = Arc<dyn Fn(&mut Machine<'_>, &mut Continue<'_>) -> Outcome<()> + Send + Sync>;

/// What the search hands the interpreter's printer, in order: what Print or PrintT printed, or a
/// count of initial states, which waits with what was printed before it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Printed {
    Values(Prints),
    InitialStates(u64),
    /// The base expression of an EXCEPT whose selected path does not exist.
    Warning(RuntimeWarning),
}

/// What TLC's workers printed, with several of them: where one printed as another may have
/// (`Machine::is_print_raced`), the order of what they print changes from run to run, unless
/// they all print the same.
#[derive(Clone, Debug, Default)]
pub struct WorkerPrints {
    /// The first thing a worker printed.
    pub first: Option<Prints>,
    /// Whether a worker printed something else since.
    pub is_mixed: bool,
    /// Whether a worker printed as another may have.
    pub is_raced: bool,
}

/// Why the engine stops at TLCExt's Trace where the search doesn't keep the behavior.
pub(crate) const TRACE_UNKEPT: &str = "TLCExt's Trace, the behavior the engine doesn't keep";
/// TLCExt's Trace of a state the initial predicate hasn't assigned every variable of, which TLC
/// fails at (`TLCExt.getTrace`).
pub(crate) const TRACE_OF_INCOMPLETE_STATE: &str = "Trace of a state not completely specified";
/// TLCExt's Trace where TLC's rebuild of the trace evaluates again an initial predicate or a
/// next-state relation that may print, draw or set a register, which the engine doesn't, or read
/// what changes as the search goes, as TLCGet's counts, where TLC may rebuild other states or
/// fail to find them.
const TRACE_REBUILT_WITH_EFFECTS: &str =
    "TLCExt's Trace, whose rebuild evaluates again what may have an effect or change";
/// What a search stops with once its machines evaluated as many bodies of recursive definitions
/// as PROVE_IT_TEST_EVALUATIONS allows.
pub const EVALUATIONS_SPENT: &str = "stopped where PROVE_IT_TEST_EVALUATIONS asked";

/// What TLCGet reads of TLC's simulation (`Simulator.getStatistics`, `TLCGetSet`'s ACTION), as the
/// simulation sets it: TLC's main thread once it has started, and its one worker.
#[derive(Clone, Debug, Default)]
pub struct SimulationRun {
    /// Whether TLC's simulator runs: as TLC starts, before it makes its simulator, TLCGet of the
    /// run fails, and the engine leaves it.
    pub is_running: bool,
    /// Whether the machine simulates (`-simulate`), from TLC's start: TLC's main thread then has
    /// no model checker, whose empty trace TLCGet("diameter") reads as 1 in the assumptions.
    pub is_simulated: bool,
    /// Whether the simulation has no end (`-simulate` without `num=`). Each trace's count, which
    /// TLCGet("diameter") and TLCGet("stats") read, would then make a new integer the store keeps
    /// for good, where TLC's simulator runs in constant memory: the engine declines a read of
    /// either as the worker runs.
    pub is_endless: bool,
    /// The record of the action that made the state TLC evaluates in (`TLCState.getAction`), or
    /// none where the engine doesn't know it.
    pub action: Option<Id>,
    /// The action of the state the walk expands, kept while TLC checks a successor of it.
    pub expanding_action: Option<Id>,
    /// The positions in the model's actions of the steps that lead to that state.
    pub steps: Vec<u32>,
    /// The traces TLC started, and the states it generated.
    pub traces: u64,
    pub generated: u64,
    /// TLC's packed mean and squared deviations of the lengths of the traces it finished.
    pub lengths: i64,
    /// The name of each of the model's actions, as the store holds it.
    pub action_names: Vec<Id>,
    /// When TLC's simulator started, which TLCGet("stats").duration counts the seconds from.
    pub started: Option<crate::clock::Instant>,
}

/// What one Print or PrintT printed: the values, and in the native checker TLC's text of each,
/// which the compiler knows where the store forgets how TLC built a value the spec writes there.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Prints {
    pub values: Vec<Id>,
    /// TLC's text of each value, before TLC's pretty-printer breaks its lines; `None` where the
    /// engine doesn't know one, or isn't the native checker.
    pub texts: Option<Vec<Vec<u16>>>,
    /// Whether this is the prompt TLCSet("pause", TRUE) prints, after which TLC reads a byte of
    /// its standard input (`System.in.read`) before it goes on.
    pub is_pause_prompt: bool,
}

impl Prints {
    /// A startup PrintT whose argument the engine can't compute, but the trace evaluator can,
    /// which words it as TLC prints it: it holds no value (a Print or PrintT holds at least one).
    pub fn unworded() -> Prints {
        Prints {
            values: Vec::new(),
            texts: None,
            is_pause_prompt: false,
        }
    }

    /// Whether this is the print `Prints::unworded` makes, which only the trace evaluator words.
    pub fn is_unworded(&self) -> bool {
        self.values.is_empty() && self.texts.is_none()
    }
}

/// A variable that has no value yet, -1 in the TypeScript registers.
pub const UNASSIGNED: Id = u32::MAX;

/// What a constant definition's once slot holds where the definition failed as TLC started, which
/// TLC keeps no value of and evaluates again at each use (`Machine::constant_once`).
pub(crate) const RETRIED_ONCE: Id = u32::MAX - 1;

// How far past its place in the set that last passed `Machine::holds_all` looks for an element.
const PASSED_WINDOW: u32 = 4;

/// How deep recursive operators and functions may call themselves before the engine hands over,
/// so that deep TLA+ recursion stops cleanly rather than overflow the native stack. WebAssembly's
/// frames are on the host's stack, which holds about 1,500 calls of a simple recursive operator
/// under Bun and 1,800 under Node's default stack (fallback.md), so it stops sooner there. TLC's
/// own JVM stack holds a few hundred to a few thousand, by the frames each level takes: under a
/// 2 MB thread stack the cheapest recursion, `G(n) == IF n = 0 THEN 0 ELSE G(n - 1)`, evaluated
/// 2,000 calls and overflowed past 2,900 in every probe, so a recursion that ends deeper than
/// that is one TLC overflows on, which the engine leaves to TLC rather than answer. A value the
/// engine kept counts the calls nested below its evaluation where it is read again
/// (`reach_cached`), since TLC evaluates it again there.
const MAXIMUM_RECURSION: u32 = if cfg!(target_arch = "wasm32") {
    1_000
} else {
    3_000
};

/// Why the engine as WebAssembly stops at that bound, for which the library throws
/// `WebAssemblyStackError` (`src/library-check.ts`).
pub const WEBASSEMBLY_TOO_DEEP: &str = "recursion deeper than WebAssembly's stack holds";

/// Why the engine stops at that bound, which the evaluator of failures evaluates again: TLC
/// overflows its stack where the recursion never ends.
pub(crate) const TOO_DEEP: &str = if cfg!(target_arch = "wasm32") {
    WEBASSEMBLY_TOO_DEEP
} else {
    "recursion too deep"
};

/// Where a memo table reads one of its keys.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Key {
    Current(u32),
    Next(u32),
    Slot(u32),
}

/// The most keys a name bound once is found by, as many as a memo table's.
pub(crate) const BINDING_KEYS: usize = 6;

/// A name bound once: a LET definition or an operator's argument its body may read more than
/// once, where its keys are read and its expression.
pub(crate) struct BoundName {
    pub keys: Box<[Key]>,
    pub inner: Eval,
}

/// Where a memo table of an expression that reads names bound once reads one of its keys: a
/// place, or such a name's value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ThroughKey {
    Read(Key),
    Binding(u32),
}

/// In place of the value of a name bound once: its expression gave no value to key a memo table
/// by for what it read (`Machine::binding_key`), which a read of the name evaluates again.
const UNKEYED: Id = EMPTY - 1;

/// The value a name bound once last had, by what its expression read then, with how deep the
/// evaluation nested recursive calls.
#[derive(Clone)]
pub(crate) struct BoundValue {
    read: [Id; BINDING_KEYS],
    value: Id,
    height: u32,
}

impl Default for BoundValue {
    fn default() -> BoundValue {
        BoundValue {
            read: [EMPTY; BINDING_KEYS],
            value: EMPTY,
            height: 0,
        }
    }
}

/// A recursive operator or function once its body has settled.
pub(crate) struct Recursive {
    pub body: Eval,
    pub table: Option<usize>,
    pub keys: Vec<Key>,
    /// The slots the body binds, which a call inside it would overwrite.
    pub slot_start: u32,
    pub slot_end: u32,
    /// For a function: whether an argument is in its domain.
    pub domain: Option<Member>,
}

/// How the engine makes TLCExt's Trace: the shape of a state's record and the variable of each
/// of its fields, and whether TLC's rebuild of the trace, which evaluates the initial predicate
/// and the next-state relation again (`getTraceInfo`), may find other states or have an effect in
/// each (`Compiler::may_change_again`).
pub(crate) struct TraceRecord {
    pub(crate) shape: tla_values::store::RecordShape,
    pub(crate) order: Vec<usize>,
    pub(crate) is_init_effectful: bool,
    pub(crate) is_next_effectful: bool,
}

/// What a compiled program needs besides its closures.
#[derive(Default)]
pub struct Program {
    pub(crate) width: usize,
    /// Where the spec reads TLCExt's Trace, how the engine makes it (`Machine::trace`).
    pub(crate) trace_record: Option<TraceRecord>,
    pub(crate) slot_count: usize,
    /// Each memo table's width, and whether it is kept: a recursive definition's, which doesn't
    /// turn off once full (`MemoTable::kept`).
    pub(crate) memo_tables: Vec<(usize, bool)>,
    pub(crate) epoch_count: usize,
    pub(crate) once_count: usize,
    pub(crate) round_count: usize,
    pub(crate) recursives: Vec<Option<Recursive>>,
    /// The names bound once, which a memo table keyed by one's value reads by its number.
    pub(crate) bindings: Vec<BoundName>,
    /// The bodies of the function constructors that may be the function of an application,
    /// each list by the number `Machine::applying_construction` holds.
    pub(crate) constructions: Vec<Box<[NodeId]>>,
    pub(crate) is_epoch_checked: bool,
    /// What TLC seeds the generator its startup and initial states draw from with, and what a
    /// state's fingerprint is xored with to seed the draws of its expansion.
    pub(crate) random_seed: u64,
    /// The index in FP64.Polys of the polynomial TLC fingerprints with.
    pub(crate) fingerprint_index: usize,
    /// PROVE_IT_TEST_EVALUATIONS: how many bodies of recursive definitions the machines of a
    /// search may evaluate between them, and how many they have.
    pub(crate) evaluation_budget: Option<u64>,
    pub(crate) evaluations: AtomicU64,
    /// Whether a machine enumerated a set of functions, records or tuples TLC keeps lazy and
    /// prints by its parts (`Lazy::check_printed`), whose enumeration the store holds and would
    /// print instead.
    pub(crate) is_collapsed: AtomicBool,
    /// The AssertError applications the engine leaves to its caller to compute once as it
    /// starts, each with the value the caller computed: their message is a string, and their
    /// expression reads neither the state nor a name bound around it and has no effect, so TLC
    /// computes the same value wherever it evaluates them.
    pub(crate) delegated: Vec<(NodeId, Arc<OnceLock<bool>>)>,
    /// How many workers TLC runs, whose threads share the system properties TLCSet sets in
    /// whatever order they race to them.
    pub(crate) workers: usize,
    /// Whether the model may read TLCGet("config"), whose install the engine writes "unknown"
    /// where TLC writes where its jar is (`TLCGlobals.Version.installLocation`).
    pub(crate) reads_config: bool,
    /// How many tests of every element of a set keep the set that last passed
    /// (`Machine::holds_all`).
    pub(crate) pass_count: usize,
}

impl Program {
    /// Whether the machines evaluated more bodies of recursive definitions than
    /// PROVE_IT_TEST_EVALUATIONS allows.
    pub(crate) fn is_evaluation_budget_spent(&self) -> bool {
        self.evaluation_budget
            .is_some_and(|budget| self.evaluations.load(Ordering::Relaxed) > budget)
    }

    /// Whether a value the store holds may print otherwise than TLC prints it: an enumeration of
    /// a set TLC prints by its parts (`Program::is_collapsed`).
    pub(crate) fn holds_collapsed(&self) -> bool {
        self.is_collapsed.load(Ordering::Relaxed)
    }

    pub(crate) fn polynomial(&self) -> &'static Polynomial {
        Polynomial::get(self.fingerprint_index)
    }
}

/// The statistics of one memo table, as `getMemoStatistics` gives them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MemoStatistics {
    pub width: usize,
    pub size: usize,
    pub lookups: u64,
    pub hits: u64,
    pub is_enabled: bool,
}

#[derive(Clone)]
pub(crate) struct DeferredCall {
    pub evaluate: Eval,
    pub locals: Vec<Id>,
    pub current: Vec<Id>,
    pub next: Vec<Id>,
}

pub struct Machine<'p> {
    pub store: Store,
    pub(crate) cur: Vec<Id>,
    pub(crate) next: Vec<Id>,
    pub(crate) locals: Vec<Id>,
    pub(crate) stack: Vec<Id>,
    pub(crate) epoch: u64,
    epoch_count: u64,
    pub(crate) program: &'p Program,
    pub(crate) tables: Vec<MemoTable>,
    pub(crate) epochs: Vec<EpochCache>,
    /// The last value of each name bound once (`Program::bindings`).
    bindings: Vec<BoundValue>,
    pub(crate) onces: Vec<Id>,
    /// The values computed once whose evaluation nested recursive calls, with how deep they
    /// went, which a machine that adopts them counts where it reads them too.
    pub(crate) deep_onces: Vec<(Id, u32)>,
    // The round of membership tests in which each set's parts last ran (`onceARound`).
    pub(crate) rounds: Vec<u64>,
    /// For each round of parts whose sets read nothing, whether a run of it settled it
    /// (`run_settled`).
    settled_rounds: Vec<bool>,
    /// How many times a run of parts passed a round that ran before in it and didn't settle.
    unsettled_passes: u64,
    pub(crate) parts_round: u64,
    parts_rounds: u64,
    pub(crate) depth: u32,
    /// The depth at which a recursive call stops with TOO_DEEP: MAXIMUM_RECURSION, or less while
    /// the engine looks for a substitute TLC's stack may not hold (`within_recursion`).
    recursion_limit: u32,
    /// The deepest `depth` the evaluation reached since the innermost cache that measures it
    /// started (`reach_from_here`), counting what a cached value's evaluation nested below it.
    reach: u32,
    /// How many variables the walk has assigned (`registers.assigned`).
    pub(crate) assigned: u32,
    /// Whether a step took TLC's shortcut past a conjunct it would otherwise walk
    /// (`shortcuts.isPastWalk`).
    pub is_past_walk: bool,
    /// The join of the shapes of the values each walk assigned to each variable, kept only where
    /// an action atom is answered from the steps (`live.rs`): no comparison of TLC's predicate
    /// evaluation of the next-state relation fails where every variable's join is comparable.
    pub assigned_shapes: Option<Vec<ShapeJoin>>,
    /// Whether a walk, where the machine keeps the shapes, enumerated for `x' \in S` a set whose
    /// membership TLC may test against values the walk never assigned: an empty one, as
    /// `[a : {}]`, which still tests the value's kind, or one that drops elements, as a filter
    /// does. Then the shapes the walks joined don't cover TLC's predicate evaluation.
    pub is_membership_unsafe: bool,
    /// The bits of the action atoms whose pieces of Next the walk is in (`pieces.rs`).
    pub(crate) piece_bits: u64,
    // The next states ENABLED runs its actions into, kept for the next test.
    pub(crate) spare_states: Vec<Vec<Id>>,
    /// What was printed since the search last handed it on (`tlc.output`).
    pub output: Vec<Printed>,
    pub(crate) deferred: Option<DeferredCall>,
    /// The generator RandomElement and RandomSubset draw from: the interpreter's for the initial
    /// states, then one seeded for each state the search expands (`runtime.getRandom`).
    pub(crate) random: JavaRandom,
    /// The state of the generator the startup left, which a violation's trace draws from.
    pub(crate) startup_random: u64,
    pub(crate) startup_values: Option<Vec<Id>>,
    pub(crate) keeping_lazy_function_value: bool,
    /// The functions an application read with KeepLazy from an argument or a LET definition
    /// whose constructor holds records TLC may print as written (`names_argument_with_written_records`).
    /// The last value put in `kept_lazy_records`, which an application reading it again skips.
    pub(crate) last_kept_lazy_record: Id,
    pub(crate) kept_lazy_records: std::collections::HashSet<
        Id,
        std::hash::BuildHasherDefault<crate::symmetry::IntegerHasher>,
    >,
    /// Where the function of an application may be the value of a function constructor, the
    /// bodies of those constructors, by their number in `Program::constructions`, until one of
    /// them takes it (`Tool`'s OPCODE_fa evaluates it with KeepLazy).
    pub(crate) applying_construction: Option<u32>,
    /// The function a constructor kept lazy where building it failed, which no cache keeps:
    /// TLC builds it again, at once, where it isn't applied.
    pub(crate) kept_lazy_function: Id,
    /// How many times a startup definition that failed as TLC started has been evaluated again
    /// at a use (`constant_once`), which a read of a name TLC binds to a `LazyValue` counts.
    pub(crate) retried_reads: u32,
    pub(crate) guarding_function_body_warnings: bool,
    /// Whether the liveness checker's atom being answered is evaluating: TLC prints a warning
    /// such as an EXCEPT's missing path (2144) or an UNCHANGED that doesn't hold (2143) as its
    /// liveness checker evaluates the atom, between what it reports there, which the engine
    /// doesn't place.
    pub(crate) guarding_atom_warnings: bool,
    /// TLC's registers, which TLCSet sets and TLCGet reads.
    pub registers: Registers,
    /// What TLCGet reads of TLC's simulation as it runs, where the machine simulates.
    pub simulation: SimulationRun,
    /// Whether TLC has seen the successor whose action constraints the search checks, which
    /// PickSuccessor reads; None elsewhere.
    pub(crate) is_successor_seen: Option<bool>,
    /// Whether, with several workers, another of TLC's workers may print as this one does: TLC's
    /// queue holds a state other than the one being expanded, which another worker takes and
    /// expands as this one goes on (`StateQueue.sDequeue`), so the order of what they print
    /// changes from run to run.
    pub(crate) is_print_raced: bool,
    /// Whether, with several workers, the machine evaluates as one of TLC's workers does.
    pub(crate) is_worker_evaluating: bool,
    /// What TLC's workers printed so far, with several workers.
    pub(crate) worker_prints: WorkerPrints,
    /// TLCCache's value of each expression it caches, by the expression's node and the key's
    /// fingerprint (`tlcEval2`).
    pub(crate) tlc_caches: HashMap<(NodeId, u64), Id>,
    /// The fingerprints of the values TLCFP and TLCCache's keys fingerprint.
    pub(crate) fingerprints: Fingerprints,
    /// The functions TLC keeps lazy that the machine built, which the store's ids of them number.
    pub(crate) lazy_functions: Vec<Lambda>,
    /// For each variable the walk assigned a set TLC may stream an element of twice: the value
    /// assigned, and the set as TLC built it, or None where the engine has no reference of it.
    /// TLC binds the set as built until it fingerprints the state the walk completes, which
    /// caches it as its normalized set (`Tool.getInitStates`, `Tool.getNextStates`).
    pub(crate) held: Vec<Option<(Id, Option<Lazy>)>>,
    /// Whether the search walks the initial predicate and it has completed no state yet, before
    /// which TLC fingerprints no state, so it has cached no value a state holds as its
    /// normalized set (`DoInitFunctor.addElement`).
    pub(crate) is_before_initial_state: bool,
    /// Where the search keeps TLCExt's Trace, the epoch of the state it expands, whose behavior
    /// is at `TRACE_SLOT`, as a list of pairs (`Search::keep_trace`): `u64::MAX` before it
    /// expands one, where the slot holds the empty list.
    pub(crate) trace_epoch: Option<u64>,
    /// The last behavior made a tuple of, and the tuple (`Machine::trace`).
    trace_tuple: (Id, Id),
    /// Whether the machine computes the substitutes and the constant definitions as TLC does
    /// as it processes the spec (`SpecProcessor.processConstantDefns`), before it has made its
    /// checker or simulator (`TLCGlobals.mainChecker`), whose registers TLCExt reads.
    pub(crate) is_processing_constants: bool,
    /// Whether the machine computes a definition as TLC does as it starts only to find whether
    /// TLC fails or completes there before any effect, stopping at its TLCSet
    /// (`tla_ir::Startup::register_probes`).
    pub(crate) is_probing_registers: bool,
    /// Whether such a computation reached TLCSet of a key that sets nothing as TLC starts.
    pub(crate) has_probed_unset_register: bool,
    /// Whether TLCSet("pause", TRUE) prompts, as TLC's breadth-first model checker does from its
    /// one worker and its main thread once it computes the initial states; elsewhere the engine
    /// declines it, but in a simulation, which has no model checker and ignores it.
    pub(crate) is_pause_prompted: bool,
    /// Whether the machine runs TLC's startup, the constant definitions and then the
    /// assumptions, on the one thread TLC runs them on, before any state: a recursive function
    /// TLC keeps lazy may print as it is applied or converted only there
    /// (`Compiler::kept_lazy_conversion`).
    pub(crate) is_starting: bool,
    /// Where the simulation generates (`-generate`), the walk of an action: the worker's
    /// generator, and whether the walk kept a successor, past which TLC's walk stops.
    pub(crate) generate: Option<Generate>,
    /// For each test of every element of a set in a set that reads nothing, the set that last
    /// passed (`holds_all`), or EMPTY.
    passed: Vec<Id>,
}

/// What a walk of an action TLC generates draws from and has found (`Tool.probabilistic`).
pub(crate) struct Generate {
    pub(crate) random: JavaRandom,
    /// Whether the walk kept a successor (`SimulationWorker.hasStates`).
    pub(crate) has_states: bool,
}

/// TLC's registers (`IdThread`'s local values and named registers): the value TLCSet stored under
/// each natural number, and under each name that starts with "s:", ids of the machine's store.
#[derive(Clone, Debug, Default)]
pub struct Registers {
    pub numbered: Vec<Option<Id>>,
    pub named: Vec<(Id, Id)>,
    /// Whether TLCSet("exit", TRUE) ran, which stops TLC's search once the worker finishes the
    /// state it is expanding (`ModelChecker.stop`).
    pub is_exit: bool,
    /// How many times TLCSet has set a register.
    pub writes: u64,
    /// The system properties TLCSet("-D<name>", v) set, by name, each the string of the value's
    /// text (`System.setProperty`), which every worker reads alike.
    pub properties: Vec<(Vec<u16>, Id)>,
}

impl Registers {
    pub fn is_empty(&self) -> bool {
        self.numbered.iter().all(Option::is_none)
            && self.named.is_empty()
            && self.properties.is_empty()
    }
}

impl<'p> Machine<'p> {
    pub fn new(program: &'p Program, store: Store) -> Machine<'p> {
        Machine {
            store,
            cur: vec![UNASSIGNED; program.width],
            next: vec![UNASSIGNED; program.width],
            locals: vec![0; program.slot_count],
            stack: Vec::with_capacity(1024),
            epoch: 0,
            epoch_count: 0,
            program,
            tables: program
                .memo_tables
                .iter()
                .map(|&(width, is_kept)| {
                    if is_kept {
                        MemoTable::kept(width)
                    } else {
                        MemoTable::new(width)
                    }
                })
                .collect(),
            epochs: (0..program.epoch_count)
                .map(|_| EpochCache::default())
                .collect(),
            bindings: vec![BoundValue::default(); program.bindings.len()],
            onces: vec![EMPTY; program.once_count],
            deep_onces: vec![(EMPTY, 0); program.once_count],
            rounds: vec![u64::MAX; program.round_count],
            settled_rounds: vec![false; program.round_count],
            unsettled_passes: 0,
            parts_round: 0,
            parts_rounds: 0,
            depth: 0,
            recursion_limit: MAXIMUM_RECURSION,
            reach: 0,
            assigned: 0,
            is_past_walk: false,
            assigned_shapes: None,
            is_membership_unsafe: false,
            piece_bits: 0,
            spare_states: Vec::new(),
            output: Vec::new(),
            deferred: None,
            random: JavaRandom::seeded(program.random_seed),
            startup_random: 0,
            startup_values: None,
            keeping_lazy_function_value: false,
            last_kept_lazy_record: crate::memo::EMPTY,
            kept_lazy_records: std::collections::HashSet::default(),
            applying_construction: None,
            kept_lazy_function: EMPTY,
            retried_reads: 0,
            guarding_function_body_warnings: false,
            guarding_atom_warnings: false,
            registers: Registers::default(),
            simulation: SimulationRun::default(),
            is_successor_seen: None,
            is_print_raced: false,
            is_worker_evaluating: false,
            worker_prints: WorkerPrints::default(),
            tlc_caches: HashMap::new(),
            fingerprints: Fingerprints::new(program.polynomial()),
            lazy_functions: Vec::new(),
            held: vec![None; program.width],
            is_before_initial_state: false,
            trace_epoch: None,
            trace_tuple: (UNASSIGNED, UNASSIGNED),
            generate: None,
            is_processing_constants: false,
            is_probing_registers: false,
            has_probed_unset_register: false,
            is_pause_prompted: false,
            is_starting: false,
            passed: vec![EMPTY; program.pass_count],
        }
    }

    /// Notes a value a walk assigned to a variable, where the machine keeps their shapes. A walk
    /// through an instance's action, as ENABLED takes, can assign slots past the spec's variables,
    /// which no step the search keeps holds. A value the state being expanded holds, as most of a
    /// successor's are, was noted when a walk assigned it to that state.
    #[inline(always)]
    pub(crate) fn note_assigned(&mut self, variable: usize, value: Id, is_initial: bool) {
        if let Some(join) = self
            .assigned_shapes
            .as_mut()
            .and_then(|joins| joins.get_mut(variable))
            && (is_initial || self.cur[variable] != value)
        {
            self.store.join_shape(join, value);
        }
    }

    /// Notes that a walk enumerated such a set for an assignment, where the machine keeps the
    /// shapes.
    pub(crate) fn note_unsafe_membership(&mut self) {
        self.is_membership_unsafe |= self.assigned_shapes.is_some();
    }

    /// Seeds the draws of a state's expansion with its fingerprint, as TLC's workers do.
    pub(crate) fn seed_random(&mut self, fingerprint: u64) {
        self.random = JavaRandom::seeded(fingerprint ^ self.program.random_seed);
    }

    /// Lets each memo table take no more than `entries` entries, such as its share of the room of
    /// the machines of a search on threads, so that the tables of all of them take about what one
    /// machine's do.
    pub fn limit_memo(&mut self, entries: usize) {
        for table in &mut self.tables {
            table.limit(entries);
        }
    }

    /// Takes the values another machine on the same store computed once where this one has none.
    pub(crate) fn adopt_onces(&mut self, onces: &[Id], deep_onces: &[(Id, u32)]) {
        for (own, &other) in self.onces.iter_mut().zip(onces) {
            if *own == EMPTY {
                *own = other;
            }
        }
        for (own, &other) in self.deep_onces.iter_mut().zip(deep_onces) {
            if own.0 == EMPTY {
                *own = other;
            }
        }
    }

    /// Forgets what the caches hold of ids from `bound` on, which the store has let go of.
    pub fn forget_from(&mut self, bound: Id) {
        for table in &mut self.tables {
            table.forget_from(bound);
        }
        for cache in &mut self.epochs {
            *cache = EpochCache::default();
        }
        self.bindings.fill(BoundValue::default());
        for once in self
            .onces
            .iter_mut()
            .filter(|once| **once >= bound && **once != RETRIED_ONCE)
        {
            *once = EMPTY;
        }
        for once in self.deep_onces.iter_mut().filter(|once| once.0 >= bound) {
            *once = (EMPTY, 0);
        }
        for passed in self.passed.iter_mut().filter(|passed| **passed >= bound) {
            *passed = EMPTY;
        }
        self.spare_states.clear();
    }

    /// A number no current state has had, for the caches of expressions that read many
    /// variables: a state keeps its epoch while it is current and unchanged, and 0 marks one
    /// nothing may cache by.
    pub fn next_epoch(&mut self) -> u64 {
        self.epoch_count += 1;
        self.epoch_count
    }

    /// Makes a state current, under an epoch from [`Machine::next_epoch`], or 0.
    pub fn set_current(&mut self, state: &[Id], epoch: u64) {
        self.cur.clear();
        self.cur.extend_from_slice(state);
        self.epoch = epoch;
    }

    /// Makes a state the next one, which primed variables read; [`UNASSIGNED`] marks a variable
    /// without a value.
    pub fn set_next(&mut self, state: &[Id]) {
        self.next.clear();
        self.next.extend_from_slice(state);
    }

    /// TLCExt's Trace, the records of the states from an initial state to the current one
    /// (`TLCExt.getTrace`): the behavior at `TRACE_SLOT` where the current state is the one the
    /// search expands, and otherwise, as the search checks a successor or an initial state, that
    /// behavior and the current state's record, which TLC gives only of a state whose variables
    /// are all assigned.
    pub(crate) fn trace(&mut self) -> Outcome<Id> {
        let Some(epoch) = self.trace_epoch else {
            return Err(Bail(TRACE_UNKEPT));
        };
        let behavior = self.behavior_tuple();
        let is_expanded = self.epoch == epoch;
        if !is_expanded && self.cur.contains(&UNASSIGNED) {
            return Err(Bail(TRACE_OF_INCOMPLETE_STATE));
        }
        // TLC rebuilds the states before the one it gives the trace of, from the initial
        // predicate on, as it found them: past the state expanded, a successor's trace is
        // rebuilt through the state expanded, which a state constraint's needn't be, as TLC
        // writes a successor to its trace only once the constraints hold.
        let length = self.store.tuple_elements(behavior).len();
        let rebuilt = if is_expanded {
            length.saturating_sub(1)
        } else {
            length
        };
        let trace = self
            .program
            .trace_record
            .as_ref()
            .expect("a spec that reads Trace");
        if rebuilt >= 1 && trace.is_init_effectful || rebuilt >= 2 && trace.is_next_effectful {
            return Err(Bail(TRACE_REBUILT_WITH_EFFECTS));
        }
        if is_expanded {
            return Ok(behavior);
        }
        let record = self.state_record(&self.cur.clone());
        Ok(self.store.append_tuple(behavior, record))
    }

    // The behavior at `TRACE_SLOT` as the tuple of its records, made once for each behavior.
    fn behavior_tuple(&mut self) -> Id {
        let list = self.locals[crate::compile::TRACE_SLOT as usize];
        if self.trace_tuple.0 == list {
            return self.trace_tuple.1;
        }
        let mut records = Vec::new();
        let mut rest = list;
        while rest != tla_values::store::EMPTY_TUPLE {
            let &[prefix, record] = self.store.tuple_elements(rest) else {
                unreachable!("a behavior is a list of pairs");
            };
            records.push(record);
            rest = prefix;
        }
        records.reverse();
        let tuple = self.store.tuple_of(&records);
        self.trace_tuple = (list, tuple);
        tuple
    }

    /// A state as the record TLC makes of it for TLCExt's Trace (`RecordValue(TLCState)`).
    pub(crate) fn state_record(&mut self, state: &[Id]) -> Id {
        let trace = self
            .program
            .trace_record
            .as_ref()
            .expect("a spec that reads Trace");
        let values: Vec<Id> = trace
            .order
            .iter()
            .map(|&variable| state[variable])
            .collect();
        self.store.record_of(&trace.shape, &values)
    }

    /// The epoch of the current state.
    pub fn epoch(&self) -> u64 {
        self.epoch
    }

    /// The current state.
    pub fn current(&self) -> &[Id] {
        &self.cur
    }

    /// The next state, [`UNASSIGNED`] where a variable has no value.
    pub fn next(&self) -> &[Id] {
        &self.next
    }

    /// Forgets the walk's assignments, as `resetAssigned` does before a state is expanded.
    pub fn reset_assigned(&mut self) {
        self.assigned = 0;
    }

    /// Sets a slot that no bound name takes, such as the level TLCGet reads.
    pub fn set_slot(&mut self, slot: u32, value: Id) {
        self.locals[slot as usize] = value;
    }

    pub fn evaluate(&mut self, eval: &Eval) -> Outcome<Id> {
        eval(self)
    }

    pub fn memo_statistics(&self) -> Vec<MemoStatistics> {
        self.tables
            .iter()
            .map(|table| MemoStatistics {
                width: table.width(),
                size: table.size(),
                lookups: table.lookups(),
                hits: table.hits(),
                is_enabled: table.is_enabled(),
            })
            .collect()
    }

    #[inline(always)]
    pub(crate) fn read_current(&self, variable: u32) -> Outcome<Id> {
        match self.cur[variable as usize] {
            UNASSIGNED => Err(Bail("variable not assigned")),
            value => Ok(value),
        }
    }

    #[inline(always)]
    pub(crate) fn read_next(&self, variable: u32) -> Outcome<Id> {
        match self.next[variable as usize] {
            UNASSIGNED => Err(Bail("primed variable not assigned")),
            value => Ok(value),
        }
    }

    #[inline(always)]
    pub(crate) fn read_key(&self, key: Key) -> Id {
        match key {
            Key::Current(variable) => self.cur[variable as usize],
            Key::Next(variable) => self.next[variable as usize],
            Key::Slot(slot) => self.locals[slot as usize],
        }
    }

    // Evaluates through a memo table, the keys read before the inner evaluation and the value
    // stored after it, so a bailout stores nothing.
    // The number of keys is the closure's own, so their reads unroll.
    #[inline(always)]
    pub(crate) fn lookup<const WIDTH: usize>(
        &mut self,
        table: usize,
        keys: &[Key; WIDTH],
        inner: &Eval,
    ) -> Outcome<Id> {
        if !self.tables[table].is_enabled() {
            return inner(self);
        }
        let read = keys.map(|key| self.read_key(key));
        let (known, height) = self.tables[table].find(&read);
        if known != EMPTY && height == 0 {
            return Ok(known);
        }
        self.lookup_further(table, &read, known, height, inner)
    }

    // A lookup that missed, or hit a value whose evaluation nested recursive calls, kept out of
    // line so that a plain hit stays short.
    #[inline(never)]
    fn lookup_further(
        &mut self,
        table: usize,
        read: &[Id],
        known: Id,
        height: u32,
        inner: &Eval,
    ) -> Outcome<Id> {
        if known != EMPTY {
            self.reach_cached(height)?;
            return Ok(known);
        }
        let output_at = self.output.len();
        let outer = self.reach_from_here();
        let value = inner(self);
        let height = self.reached_below(outer);
        let value = value?;
        if self.output.len() == output_at && value != self.kept_lazy_function {
            self.tables[table].set_with_height(read, value, height);
        }
        Ok(value)
    }

    /// Reads a name bound once: TLC binds a LET definition or an operator's argument to a
    /// `LazyValue`, which computes it where the body first reads it and keeps the value for its
    /// other reads of the same states. The value is kept by what the expression read, so a read
    /// finds it wherever those are the same, and it is computed, with its failure, only where
    /// one reads it. Nothing is kept of an evaluation that printed a warning or kept a function
    /// lazy, as a memo table keeps nothing of one (`lookup_further`).
    #[inline(always)]
    pub(crate) fn binding<const WIDTH: usize>(
        &mut self,
        index: usize,
        keys: &[Key; WIDTH],
        inner: &Eval,
    ) -> Outcome<Id> {
        let read = keys.map(|key| self.read_key(key));
        let known = &self.bindings[index];
        // Compared key by key, which beats a call to memcmp for six keys or fewer.
        let mut is_known = known.value < UNKEYED && known.height == 0;
        for (place, &key) in read.iter().enumerate() {
            is_known &= known.read[place] == key;
        }
        if is_known {
            return Ok(known.value);
        }
        self.bind(index, &read, inner)
    }

    #[inline(never)]
    fn bind(&mut self, index: usize, read: &[Id], inner: &Eval) -> Outcome<Id> {
        let known = &self.bindings[index];
        if known.value < UNKEYED && known.read.iter().zip(read).all(|(kept, key)| kept == key) {
            let (value, height) = (known.value, known.height);
            self.reach_cached(height)?;
            return Ok(value);
        }
        let output_at = self.output.len();
        let outer = self.reach_from_here();
        let value = inner(self);
        let height = self.reached_below(outer);
        let value = value?;
        if self.output.len() == output_at && value != self.kept_lazy_function {
            self.keep_binding(index, read, value, height);
        }
        Ok(value)
    }

    fn keep_binding(&mut self, index: usize, read: &[Id], value: Id, height: u32) {
        let kept = &mut self.bindings[index];
        kept.read[..read.len()].copy_from_slice(read);
        kept.value = value;
        kept.height = height;
    }

    /// The value of a name bound once, for a memo table to key what reads the name by, or None
    /// where the table can't: the expression fails or warns, which only a read of the name may
    /// do, or its evaluation nests recursive calls, which each read counts from where it is. Nor
    /// does a value of a thread's own key one: the thread lets go of it at the level's end, where
    /// what the expression read may still find the entry in a later level. It is evaluated apart
    /// from what TLC is evaluating: as no application's function, and reaching no deeper than
    /// before.
    #[inline(always)]
    fn binding_key(&mut self, index: u32) -> Option<Id> {
        let program = self.program;
        let bound = &program.bindings[index as usize];
        let known = &self.bindings[index as usize];
        let mut is_known = known.value != EMPTY;
        for (place, &key) in bound.keys.iter().enumerate() {
            is_known &= known.read[place] == self.read_key(key);
        }
        if is_known {
            let (value, height) = (known.value, known.height);
            return (value != UNKEYED && height == 0 && !self.store.is_own(value)).then_some(value);
        }
        self.bind_key(index)
    }

    // `binding_key` of a name whose value isn't known for what its expression reads now.
    #[inline(never)]
    fn bind_key(&mut self, index: u32) -> Option<Id> {
        let program = self.program;
        let bound = &program.bindings[index as usize];
        let width = bound.keys.len();
        let mut read = [EMPTY; BINDING_KEYS];
        for (place, &key) in read.iter_mut().zip(bound.keys.iter()) {
            *place = self.read_key(key);
        }
        let output_at = self.output.len();
        let stack_at = self.stack.len();
        let reach = std::mem::replace(&mut self.reach, self.depth);
        let keeping = std::mem::replace(&mut self.keeping_lazy_function_value, false);
        let applying = self.applying_construction.take();
        let kept = self.kept_lazy_function;
        let value = (bound.inner)(self);
        let height = self.reach.saturating_sub(self.depth);
        let is_kept_lazy =
            self.kept_lazy_function != kept || matches!(value, Ok(value) if value == kept);
        self.reach = reach;
        self.keeping_lazy_function_value = keeping;
        self.applying_construction = applying;
        self.kept_lazy_function = kept;
        self.stack.truncate(stack_at);
        match value {
            Ok(value) if self.output.len() == output_at && !is_kept_lazy => {
                self.keep_binding(index as usize, &read[..width], value, height);
                (height == 0 && !self.store.is_own(value)).then_some(value)
            }
            _ => {
                self.output.truncate(output_at);
                self.keep_binding(index as usize, &read[..width], UNKEYED, 0);
                None
            }
        }
    }

    /// `lookup` of an expression that reads names bound once, keyed by their values in place of
    /// what their expressions read. Where one has no value to key by, `plain` evaluates it as it
    /// would be without the names: through its table keyed by everything it reads, if it has one.
    #[inline(always)]
    pub(crate) fn lookup_through<const WIDTH: usize>(
        &mut self,
        table: usize,
        keys: &[ThroughKey; WIDTH],
        inner: &Eval,
        plain: &Eval,
    ) -> Outcome<Id> {
        if !self.tables[table].is_enabled() {
            return plain(self);
        }
        let mut read = [EMPTY; WIDTH];
        for (place, &key) in read.iter_mut().zip(keys) {
            *place = match key {
                ThroughKey::Read(key) => self.read_key(key),
                ThroughKey::Binding(index) => match self.binding_key(index) {
                    Some(value) => value,
                    None => return plain(self),
                },
            };
        }
        let (known, height) = self.tables[table].find(&read);
        if known != EMPTY && height == 0 {
            if self.program.is_epoch_checked && inner(self)? != known {
                panic!("a memo table keyed by names bound once hit a stale value");
            }
            return Ok(known);
        }
        self.lookup_further(table, &read, known, height, inner)
    }

    pub(crate) fn epoch_lookup(
        &mut self,
        cache: usize,
        slots: &[u32],
        inner: &Eval,
    ) -> Outcome<Id> {
        if self.epoch == 0 || !self.epochs[cache].is_enabled() {
            return inner(self);
        }
        let epoch = self.epoch;
        let mut keys = [0; EPOCH_KEYS];
        for (index, &slot) in slots.iter().enumerate() {
            keys[index] = self.locals[slot as usize];
        }
        let entry = EpochCache::entry(&keys);
        let known = self.epochs[cache].get(epoch, entry, &keys);
        if known != EMPTY {
            if self.program.is_epoch_checked && inner(self)? != known {
                panic!("an epoch cache hit a stale value");
            }
            self.reach_cached(self.epochs[cache].height(entry))?;
            return Ok(known);
        }
        let output_at = self.output.len();
        let outer = self.reach_from_here();
        let value = inner(self);
        let height = self.reached_below(outer);
        let value = value?;
        if self.output.len() == output_at && value != self.kept_lazy_function {
            self.epochs[cache].set(epoch, entry, &keys, value, height);
        }
        Ok(value)
    }

    /// Evaluates an expression that reads nothing once. One whose evaluation nests recursive
    /// calls is kept with how deep they went, which reading it counts (`reach_cached`), as TLC
    /// evaluates it again where it reads it.
    pub(crate) fn once(&mut self, once: usize, inner: &Eval) -> Outcome<Id> {
        if let Some(known) = self.known_once(once)? {
            return Ok(known);
        }
        let outer = self.reach_from_here();
        let value = inner(self);
        let height = self.reached_below(outer);
        let value = value?;
        if value != self.kept_lazy_function {
            self.keep_once(once, value, height);
        }
        Ok(value)
    }

    /// The value kept once, counting the recursive calls its evaluation nested.
    #[inline(always)]
    fn known_once(&mut self, once: usize) -> Outcome<Option<Id>> {
        let known = self.onces[once];
        if known != EMPTY {
            return Ok(Some(known));
        }
        let (deep, height) = self.deep_onces[once];
        if deep != EMPTY {
            self.reach_cached(height)?;
            return Ok(Some(deep));
        }
        Ok(None)
    }

    // Keeps a value computed once. One whose evaluation nested recursive calls is kept apart, with
    // its height, which the machines that share it (`adopt_onces`) count too.
    fn keep_once(&mut self, once: usize, value: Id, height: u32) {
        if height == 0 {
            self.onces[once] = value;
        } else {
            self.deep_onces[once] = (value, height);
        }
    }

    /// Evaluates a definition TLC computes once at startup (`processConstantDefns`), whose value
    /// it then reads wherever it is used, however deep its evaluation went.
    pub(crate) fn constant_once(&mut self, once: usize, inner: &Eval) -> Outcome<Id> {
        let known = self.onces[once];
        // One that failed as TLC started TLC keeps no value of (`processConstantDefns` swallows
        // the failure before `setToolObject`), and evaluates again at every use, with its prints
        // and draws, though it computed at a use before.
        if known == RETRIED_ONCE {
            self.retried_reads = self.retried_reads.wrapping_add(1);
            return inner(self);
        }
        if known != EMPTY {
            return Ok(known);
        }
        let value = inner(self)?;
        if value != self.kept_lazy_function {
            self.onces[once] = value;
        }
        Ok(value)
    }

    /// Starts measuring how deep recursive calls nest below here, for a cache to keep with the
    /// value; returns the outer measure, which `reached_below` restores.
    #[inline(always)]
    fn reach_from_here(&mut self) -> u32 {
        std::mem::replace(&mut self.reach, self.depth)
    }

    /// Ends the measure `reach_from_here` started: how many recursive calls nested below here.
    /// The outer measure reaches at least as deep.
    #[inline(always)]
    fn reached_below(&mut self, outer: u32) -> u32 {
        let height = self.reach.saturating_sub(self.depth);
        self.reach = self.reach.max(outer);
        height
    }

    /// Reads a cached value whose evaluation nested `height` recursive calls below where it ran:
    /// TLC keeps no cache and evaluates it again here, so its stack goes that much deeper than
    /// this call's, and past the bound the engine stops as it does for a call it makes
    /// (`MAXIMUM_RECURSION`).
    #[inline(always)]
    fn reach_cached(&mut self, height: u32) -> Outcome<()> {
        if height == 0 {
            return Ok(());
        }
        let reached = self.depth.saturating_add(height);
        if reached > self.recursion_limit {
            return Err(Bail(TOO_DEEP));
        }
        self.reach = self.reach.max(reached);
        Ok(())
    }

    pub(crate) fn once_quiet(&mut self, once: usize, inner: &Eval) -> Outcome<Id> {
        if let Some(known) = self.known_once(once)? {
            return Ok(known);
        }
        let output_at = self.output.len();
        let outer = self.reach_from_here();
        let value = inner(self);
        let height = self.reached_below(outer);
        let value = value?;
        if self.output.len() == output_at && value != self.kept_lazy_function {
            self.keep_once(once, value, height);
        }
        Ok(value)
    }

    /// Evaluates the function of an application, with KeepLazy, and marks the constructors that
    /// may be its value. Where its arguments are values, the mark of an application whose
    /// function this one is holds again once its function is evaluated, as TLC applies it with
    /// that application's control (`FcnLambdaValue.apply`); otherwise it is dropped.
    pub(crate) fn function_value(
        &mut self,
        evaluate: &Eval,
        construction: Option<u32>,
        is_applied_to_values: bool,
    ) -> Outcome<Id> {
        let outer = self.keeping_lazy_function_value;
        let applying = self.applying_construction.take();
        let kept = self.kept_lazy_function;
        self.keeping_lazy_function_value = true;
        self.applying_construction = construction;
        let result = evaluate(self);
        self.keeping_lazy_function_value = outer;
        self.applying_construction = if is_applied_to_values { applying } else { None };
        self.kept_lazy_function = kept;
        result
    }

    /// Whether the constructor of this body is the function an application evaluates.
    pub(crate) fn take_applied_construction(&mut self, body: NodeId) -> bool {
        let program = self.program;
        let is_applied = self
            .applying_construction
            .is_some_and(|bodies| program.constructions[bodies as usize].contains(&body));
        if is_applied {
            self.applying_construction = None;
        }
        is_applied
    }

    pub(crate) fn constructed_function_body(&mut self, evaluate: &Eval) -> Outcome<Id> {
        let outer = self.guarding_function_body_warnings;
        self.guarding_function_body_warnings |= self.keeping_lazy_function_value;
        let result = evaluate(self);
        self.guarding_function_body_warnings = outer;
        result
    }

    /// What the effects so far have left: what was printed, the random draws, and the writes of
    /// TLC's registers, which differ after an evaluation that printed, drew or set a register.
    pub(crate) fn effects(&self) -> (usize, u64, u64) {
        (
            self.output
                .iter()
                .filter(|output| !matches!(output, Printed::Warning(_)))
                .count(),
            self.random.state(),
            self.registers.writes,
        )
    }

    /// Runs the parts of a round whose sets read nothing, as `Compiler::once_a_round` runs a
    /// round: once in each run of parts. Such parts do the same each time, so once a run of them
    /// has neither failed nor nested a recursive call, a cached one's height included, nor passed
    /// a round that did, they run no more on this machine: TLC's stack feels nothing of them.
    pub(crate) fn run_settled(
        &mut self,
        round: usize,
        run: impl FnOnce(&mut Self) -> Outcome<()>,
    ) -> Outcome<()> {
        if self.settled_rounds[round] {
            return Ok(());
        }
        if self.rounds[round] == self.parts_round {
            // It ran in this run of parts and didn't settle, so it recursed.
            self.unsettled_passes += 1;
            return Ok(());
        }
        let passes = self.unsettled_passes;
        let outer = self.reach_from_here();
        let result = run(self);
        let height = self.reached_below(outer);
        result?;
        self.settled_rounds[round] = height == 0 && self.unsettled_passes == passes;
        self.rounds[round] = self.parts_round;
        Ok(())
    }

    /// Whether `test` holds of every element of `set`, in the set's order, up to the first it
    /// fails at or doesn't hold of, as TLC tests them (`SubsetValue.member`). `test` is
    /// membership in a set that reads nothing, so it does the same of an element each time. The
    /// elements of the set that last passed here, in a run that printed nothing and nested no
    /// recursive call, a cached one's height included, pass again and leave nothing behind, so
    /// only the others are tested: the first that fails, or doesn't hold, is the same. A set that
    /// holds a function TLC keeps lazy, or ANY, isn't kept: equal ids say nothing of those.
    pub(crate) fn holds_all(&mut self, pass: usize, set: Id, test: &Member) -> Outcome<bool> {
        let passed = self.passed[pass];
        if passed == set {
            return Ok(true);
        }
        let known = if passed == EMPTY {
            0
        } else {
            self.store.size_of(passed)
        };
        let output_at = self.output.len();
        let outer = self.reach_from_here();
        let mut result = Ok(true);
        let mut at = 0;
        for index in 0..self.store.size_of(set) {
            let element = self.store.element_at(set, index);
            // Both sets are in TLC's order, so the element is at or just after `at` if the one
            // that passed holds it; one further on is tested again, which changes nothing.
            let found = (at..known.min(at + PASSED_WINDOW))
                .find(|&position| self.store.element_at(passed, position) == element);
            if let Some(position) = found {
                if self.program.is_epoch_checked
                    && (test(self, element) != Ok(true) || self.output.len() != output_at)
                {
                    panic!("an element of a set that passed doesn't pass again");
                }
                at = position + 1;
                continue;
            }
            match test(self, element) {
                Ok(true) => {}
                other => {
                    result = other;
                    break;
                }
            }
        }
        let height = self.reached_below(outer);
        if result == Ok(true)
            && height == 0
            && self.output.len() == output_at
            && !self.store.comparison_can_fail(set)
        {
            self.passed[pass] = set;
        }
        result
    }

    /// Runs a set's parts in a round of their own, in which each lazy set's parts run once.
    pub(crate) fn run_parts(&mut self, parts: &Parts) -> Outcome<()> {
        let outer = self.parts_round;
        self.parts_rounds += 1;
        self.parts_round = self.parts_rounds;
        let result = parts(self);
        self.parts_round = outer;
        result
    }

    /// Evaluates with the slots from `start` to `end` kept as they were, since a recursive
    /// definition's body binds its names at slots fixed when it compiled.
    pub(crate) fn keeping_slots(&mut self, eval: &Eval, start: u32, end: u32) -> Outcome<Id> {
        match end.saturating_sub(start) {
            0 => return eval(self),
            1 => return self.keeping::<1>(eval, start as usize),
            2 => return self.keeping::<2>(eval, start as usize),
            3 => return self.keeping::<3>(eval, start as usize),
            4 => return self.keeping::<4>(eval, start as usize),
            _ => {}
        }
        let at = self.stack.len();
        self.stack
            .extend_from_slice(&self.locals[start as usize..end as usize]);
        let result = eval(self);
        self.locals[start as usize..end as usize].copy_from_slice(&self.stack[at..]);
        self.stack.truncate(at);
        result
    }

    #[inline(always)]
    fn keeping<const N: usize>(&mut self, eval: &Eval, start: usize) -> Outcome<Id> {
        let kept: [Id; N] = std::array::from_fn(|index| self.locals[start + index]);
        let result = eval(self);
        for (index, value) in kept.into_iter().enumerate() {
            self.locals[start + index] = value;
        }
        result
    }

    /// Calls a recursive operator or function whose arguments are bound already.
    pub(crate) fn call_recursive(&mut self, index: usize) -> Outcome<Id> {
        let program = self.program;
        let recursive = program.recursives[index]
            .as_ref()
            .expect("a recursive definition called before its body settled");
        if self.depth >= self.recursion_limit {
            return Err(Bail(TOO_DEEP));
        }
        self.depth += 1;
        self.reach = self.reach.max(self.depth);
        let result = match recursive.table {
            Some(table) if self.tables[table].is_enabled() => self.call_kept(recursive, table),
            _ => self.evaluate_recursive(recursive),
        };
        self.depth -= 1;
        result
    }

    // A call of an operator whose table keeps what its calls returned.
    #[inline(never)]
    fn call_kept(&mut self, recursive: &Recursive, table: usize) -> Outcome<Id> {
        let mut read = [0; 6];
        for (index, &key) in recursive.keys.iter().enumerate() {
            read[index] = self.read_key(key);
        }
        let keys = &read[..recursive.keys.len()];
        let (known, height) = self.tables[table].find(keys);
        if known != EMPTY {
            // TLC calls the operator again, as deep as it went where it was kept.
            return self.reach_cached(height).map(|()| known);
        }
        let output_at = self.output.len();
        let outer = self.reach_from_here();
        let value = self.evaluate_recursive(recursive);
        let height = self.reached_below(outer);
        if let Ok(value) = value
            && self.output.len() == output_at
            && value != self.kept_lazy_function
        {
            self.tables[table].set_with_height(keys, value, height);
        }
        value
    }

    #[inline(always)]
    fn evaluate_recursive(&mut self, recursive: &Recursive) -> Outcome<Id> {
        if let Some(budget) = self.program.evaluation_budget
            && self.program.evaluations.fetch_add(1, Ordering::Relaxed) >= budget
        {
            return Err(Bail(EVALUATIONS_SPENT));
        }
        self.keeping_slots(&recursive.body, recursive.slot_start, recursive.slot_end)
    }

    /// Runs `run` with recursive calls stopped with TOO_DEEP once they nest `calls` deeper than
    /// where it starts (or at MAXIMUM_RECURSION, whichever comes first).
    pub(crate) fn within_recursion<T>(
        &mut self,
        calls: u32,
        run: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let limit = self.recursion_limit;
        self.recursion_limit = limit.min(self.depth.saturating_add(calls));
        let result = run(self);
        self.recursion_limit = limit;
        result
    }

    /// Runs a walk of a recursive function's body one call deeper, as `call_recursive` runs a
    /// call.
    pub(crate) fn nested(&mut self, run: impl FnOnce(&mut Self) -> Outcome<()>) -> Outcome<()> {
        if self.depth >= self.recursion_limit {
            return Err(Bail(TOO_DEEP));
        }
        self.depth += 1;
        self.reach = self.reach.max(self.depth);
        let result = run(self);
        self.depth -= 1;
        result
    }

    pub(crate) fn recursive_domain(&self, index: usize) -> Member {
        self.program.recursives[index]
            .as_ref()
            .and_then(|recursive| recursive.domain.clone())
            .expect("a recursive function without its domain")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_machine_starts_with_only_its_programs_empty_tables() {
        let program = Program {
            memo_tables: vec![(1, false), (3, true)],
            ..Program::default()
        };
        let mut store = Store::new();
        store.reset(std::iter::empty::<&[u16]>());
        let mut machine = Machine::new(&program, store);
        let table = machine.tables[0].width();
        machine.tables[0].set(&[7], 9);
        assert_eq!(table, 1);
        let mut store = Store::new();
        store.reset(std::iter::empty::<&[u16]>());
        let fresh = Machine::new(&program, store);
        let statistics = fresh.memo_statistics();
        assert_eq!(
            statistics
                .iter()
                .map(|table| (table.width, table.size, table.lookups))
                .collect::<Vec<_>>(),
            [(1, 0, 0), (3, 0, 0)]
        );
    }
}
