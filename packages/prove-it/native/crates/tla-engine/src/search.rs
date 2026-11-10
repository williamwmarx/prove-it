//! The engine's breadth-first search, `runEngine` in `search.ts` step for step on one thread. It
//! explores states in TLC's order, counts them as TLC does, and tells states apart by TLC's
//! fingerprint of their key: the state, or its VIEW. Anything else it meets (a violation, an
//! error, a feature it doesn't implement) ends the run with a checkpoint, from which the reference
//! interpreter goes on.

use std::cell::Cell;
use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;
use std::io::Write as _;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Duration;

use crate::clock::Instant;

use tla_ir::{Ir, LiveTerm, Model, PredicateForm};
use tla_live::{Event, Liveness, Term, Verdict};
use tla_values::fingerprint::{Dense, Entries, Fingerprints, Overlaid, Parent, SharedFingerprints};
use tla_values::random::JavaRandom;
use tla_values::store::{KIND_SET, Outcome, ShapeJoin, TRUE};
use tla_values::transfer::{EncodedStates, SharedEncoder, SharedStates, StateEncoder};
use tla_values::{Bail, Id, NESTING_STACK_BYTES, Store};

use crate::compile::{CompileError, Compiler, DISTINCT_SLOT, LEVEL_SLOT, NEXT_LEVEL_SLOT, Options};
use crate::context::{
    Atom, EngineContext, Startup, StartupSymmetry, count_possible, first_failing_changed,
    holds_all, holds_all_changed,
};
use crate::live::{Diameters, LiveAnswers, LiveGraph, Table, UNKNOWN, answer_atoms};
use crate::machine::{Eval, Machine, Printed, Registers, Step, UNASSIGNED};
use crate::symmetry::{
    Canonicalizer, Group, NamedGroup, close_group, get_permutations, name_group,
};

pub const OUT_DEGREE_BUCKETS: usize = 32;
const PROGRESS_INTERVAL: Duration = Duration::from_secs(60);
const FIRST_PROGRESS: Duration = Duration::from_secs(3);
// TLC checks the temporal properties part way through the search once the graph grew by more than
// a tenth since the last check (TLCGlobals.livenessThreshold), unless the checks took a fifth of
// the time so far (livenessRatio).
const LIVENESS_GROWTH: f64 = 0.1;
const LIVENESS_RATIO: f64 = 0.2;
// The search stops where a check part way through it finds a counterexample.
const PERIODIC_LASSO: &str = "a counterexample part way through the search";

/// What the caller asks of a search besides the model.
#[derive(Clone, Debug)]
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
    /// Whether the caller reports a violation the search stops at itself: the search passes on
    /// what the spec printed before it, and finds the action of each step of its trace.
    pub is_violation_reported: bool,
    /// PROVE_IT_WORKERS: how many threads expand a level of states, at most as many as the
    /// machine runs at once.
    pub threads: usize,
    /// How many workers TLC runs with (`-workers`), which TLCGet("config") reports.
    pub workers: usize,
    /// PROVE_IT_SHARED_LEVEL: the fewest states a level shares between the threads, below which
    /// one thread expands it, since a short level isn't worth the threads' start.
    pub minimum_shared_level: usize,
    /// Whether the temporal properties are checked as the search goes, as TLC does unless
    /// `-lncheck final`.
    pub is_liveness_periodic: bool,
    /// PROVE_IT_TEST_LIVE_CHECK_AT, for tests: the number of expanded states after which the
    /// search checks the temporal properties the first time, rather than after FIRST_PROGRESS.
    pub test_live_check_at: Option<usize>,
}

// How many candidates ahead the merge reads the state table.
const MERGE_PREFETCH: usize = 16;

/// A level of fewer states runs on one thread, as `MINIMUM_SHARED_LEVEL` in `search.ts`, unless
/// its states are costly enough that sharing it pays (`SHARED_WORK`).
pub const MINIMUM_SHARED_LEVEL: usize = 2048;

/// A shorter level is shared too where the previous level's time per state says its work, on one
/// thread, would take this long; each thread then takes at least `THREAD_WORK` of it. Starting a
/// level's threads costs tens of microseconds, and sharing changes none of what the search finds.
const SHARED_WORK: Duration = Duration::from_millis(8);
const THREAD_WORK: Duration = Duration::from_millis(2);

impl Default for Settings {
    fn default() -> Settings {
        Settings {
            compile: Options::default(),
            stop_at: None,
            is_fingerprint_verified: false,
            state_log: None,
            is_live_checked: false,
            is_violation_reported: false,
            threads: 1,
            workers: 1,
            minimum_shared_level: MINIMUM_SHARED_LEVEL,
            is_liveness_periodic: false,
            test_live_check_at: None,
        }
    }
}

/// What a search tells its caller as it runs, as `runEngine`'s callbacks.
pub trait Reporter {
    fn initial_states_started(&mut self);
    fn initial_states_progress(&mut self, count: u64);
    fn initial_states(&mut self, generated: u64, distinct: u64);
    fn progress(&mut self, generated: u64, distinct: u64, queued: u64, depth: u64);
    /// TLC starts to check the temporal properties of its `branches` on the graph of the first
    /// `expanded` states, part way through the search: `counts` are the states generated, the
    /// states found and the depth so far.
    fn liveness_started(&mut self, _branches: u64, _expanded: u64, _counts: [u64; 3]) {}
    /// The check part way through the search found the properties hold so far.
    fn liveness_finished(&mut self) {}
    /// What Print or PrintT printed: the values, as ids of the search's store.
    fn print(&mut self, store: &Store, values: &[Id]);
    /// What Print or PrintT printed while TLC started: as the substitutes and constant
    /// definitions were evaluated, before [`Reporter::startup_done`], then as the assumptions
    /// were. The interpreter printed it already where it handed the search over.
    fn startup_print(&mut self, _store: &Store, _values: &[Id]) {}
    /// The sets the symmetry permutes that hold fewer than two elements, by name, which TLC warns
    /// about once it has evaluated the symmetry (2300, `TLC_SYMMETRY_SET_TOO_SMALL`). The
    /// interpreter warned already where it handed the search over.
    fn symmetry_sets_too_small(&mut self, _names: &[String]) {}
    /// TLC has evaluated the substitutes, the constant definitions and the symmetry, and prints
    /// what it prints itself before it checks the assumptions.
    fn startup_done(&mut self) {}
    /// Checks the assumption at this position of the IR's assumptions, which the engine can't
    /// evaluate (AssertError, which compares TLC's message for a failure), after those before it
    /// held, and reports what it prints. `Err` declines the model.
    fn check_assumption(&mut self, _position: u32) -> Result<Delegated, String> {
        Err(DELEGATED_ASSUMPTION.into())
    }
}

/// Why the engine leaves an assumption to its caller.
pub const DELEGATED_ASSUMPTION: &str = "unsupported: AssertError";

/// What the caller found of an assumption the engine left to it.
pub struct Delegated {
    pub holds: bool,
    /// The state it leaves TLC's generator in.
    pub random: u64,
}

/// The counts TLC reports of a search, so far or in all.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Counts {
    pub generated: u64,
    pub distinct: u64,
    /// The states found and not yet expanded: none for a search that completed, and those left
    /// where a check part way through it found a counterexample.
    pub queued: u64,
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
    pub states: SharedStates,
    pub parents: Vec<i32>,
    /// What TLC fingerprints in place of each state when that isn't the state, its view, with
    /// the width of each.
    pub keys: Option<(SharedStates, u32)>,
    /// The steps of the states expanded, for the interpreter to replay and check temporal
    /// properties on, when the search records them.
    pub graph: Option<GraphCheckpoint>,
    /// What each `_POSSIBLE` predicate counted before the expansion the interpreter goes on
    /// from, or -1 where it wasn't evaluated.
    pub possible: Vec<i64>,
    /// The value TLC computed at startup of each of the model's startup definitions, as one row,
    /// unless one is a value the encoding has no tag for, such as a function TLC keeps lazy.
    pub startup: Option<SharedStates>,
    /// The state of the generator the startup left (`JavaRandom::state`).
    pub startup_random: u64,
    /// The symmetry group the search reduced by, if any.
    pub symmetry: Option<NamedGroup>,
}

/// TLC's registers once the search completes, which a postcondition reads, with the store their
/// ids are of.
pub struct FinalRegisters {
    pub registers: Registers,
    pub store: Store,
}

// TLC's registers once the search is over, where TLCSet set any, which takes the store: only
// what follows the search reads them.
fn take_registers(machine: &mut Machine<'_>) -> Option<Box<FinalRegisters>> {
    (!machine.registers.is_empty()).then(|| {
        Box::new(FinalRegisters {
            registers: std::mem::take(&mut machine.registers),
            store: std::mem::replace(&mut machine.store, Store::new()),
        })
    })
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
    /// The engine doesn't take the model, for this reason, before producing any state or
    /// reporting anything.
    Declined(String),
    /// The assumption TLC reports by this name is false (2104).
    AssumptionViolated { name: String },
    /// A constant definition the configuration names has a value TLC rejects, with TLC's
    /// configuration error, after the startup reported what the constant definitions printed.
    ConfigError { message: String },
    /// The assumption at this position of the IR's assumptions failed to evaluate (2105), after
    /// the startup reported what it printed, the assumptions before it included. Only where
    /// `Settings::is_violation_reported`; elsewhere the engine declines.
    AssumptionFailed { position: u32 },
    Complete {
        counts: Box<Counts>,
        /// With temporal properties, the whole search for the interpreter to print a
        /// counterexample from or to check them on, unless they hold.
        checkpoint: Option<Box<Checkpoint>>,
        /// With temporal properties, what checking them found.
        liveness: Option<Liveness>,
        /// For each state of a lasso the check found, the position of the first of TLC's actions
        /// that takes it to the next state of the lasso (from the last, the cycle's first), or
        /// `None` where none does or it stutters; empty without a lasso or a walk of the actions.
        lasso_actions: Vec<Option<u32>>,
        /// The lasso's states and the actions of its steps, where the caller reports the
        /// violation itself and the search labelled every step TLC labels.
        violation: Option<Box<Violation>>,
        /// TLC's fingerprint of each state's key, in the order found.
        fingerprints: Vec<u64>,
        value_count: usize,
        /// The most threads a level was shared between, 1 where none was.
        threads: usize,
        /// Under PROVE_IT_FP_VERIFY, how many fingerprints two different keys shared.
        collisions: u64,
        /// What each `_POSSIBLE` predicate counted, or -1 where it wasn't evaluated.
        possible: Vec<i64>,
        /// TLC's registers once the search completes, where TLCSet set any.
        registers: Option<Box<FinalRegisters>>,
    },
    /// The search stopped, with a checkpoint unless it stopped computing the initial states, as
    /// the TypeScript engine computes them before the part of its search that hands over a
    /// checkpoint: the interpreter then starts from scratch.
    Stopped {
        reason: String,
        checkpoint: Option<Box<Checkpoint>>,
        collisions: u64,
        /// What TLC reports for the stop, when the engine knows it.
        violation: Option<Box<Violation>>,
    },
    /// The engine broke one of its own invariants, or a self-check failed
    /// (`EngineInvariantError`).
    Invariant(String),
}

/// A violation the search stopped at, with the states TLC prints for it.
pub struct Violation {
    pub kind: ViolationKind,
    /// The states of the trace, each as its variables' values in the engine's order, ids of
    /// `store`.
    pub states: Vec<Vec<Id>>,
    /// For each step of the trace, the position in the model's actions of the first of TLC's
    /// actions that takes it, or `None` where the search didn't find it, as under SYMMETRY or a
    /// VIEW, whose stored states aren't the ones TLC prints.
    pub labels: Vec<Option<u32>>,
    /// The counts TLC reports after the trace.
    pub counts: StopCounts,
    pub store: Store,
    /// The value TLC computed at startup of each of the model's startup definitions, ids of
    /// `store`.
    pub startup: Vec<Id>,
    /// The state of the generator the startup left (`JavaRandom::state`).
    pub startup_random: u64,
    /// The state of the generator where an invariant of the last state stopped the search, which
    /// TLC's worker goes on drawing from as it finds that state again.
    pub random: Option<u64>,
    /// The symmetry group the search reduced by, if any.
    pub symmetry: Option<NamedGroup>,
    /// TLC's registers as the search left them, ids of `store`.
    pub registers: Registers,
    /// Each `_POSSIBLE` predicate's count as the search left it, which TLC checks with the
    /// postconditions after it reports the violation.
    pub possible: Vec<i64>,
    /// After an invariant that fails to evaluate past the initial states, TLC's set of
    /// fingerprints when it stopped, sorted, the failing state's among them where TLC added it:
    /// TLC replays the expansion and skips each successor in the set. Empty for any other stop.
    pub fingerprints: Vec<u64>,
}

/// A path to a tableau node that accepts every behavior: its states, as a `Violation`'s, whose
/// actions the caller finds, and the positions of the properties TLC names.
pub struct AcceptedTrace {
    pub states: Vec<Vec<Id>>,
    pub violated: Vec<usize>,
}

pub enum ViolationKind {
    /// An initial state violates an invariant: its position in the model's invariants, then
    /// past them in its properties checked as invariants.
    InitialInvariant(usize),
    /// An initial state violates the state predicate of a property at this position in the
    /// model's initial predicates.
    InitialPredicate(usize),
    /// The last state of the trace violates an invariant, as an `InitialInvariant` names it.
    Invariant(usize),
    /// The last state of the trace has no successors. TLC adds it to the behavior graphs after it
    /// reports the deadlock, where it may reach a tableau node that accepts every behavior, which
    /// it reports next, as on its Github710d.
    Deadlock {
        accepted: Option<Box<AcceptedTrace>>,
    },
    /// The trace is a lasso whose cycle starts at the state at `loop_start` and goes back to it,
    /// by the action at `loop_label` in the model's actions; `None` where the cycle is the last
    /// state alone, which stutters.
    Lasso {
        loop_start: usize,
        loop_label: Option<u32>,
        /// What the atoms printed as TLC found the properties the lasso violates, once it had
        /// rebuilt the lasso: each print's values, ids of the violation's store.
        printed: Vec<Vec<Id>>,
    },
    /// The last state of the trace reaches a tableau node that accepts every behavior, which TLC
    /// stops at as it adds the state: the positions of the properties it names.
    Accepted { violated: Vec<usize> },
    /// The model has initial states and no next-state relation to take their steps by; the
    /// violation has no states.
    NoNextState,
    /// Evaluating the model failed where TLC fails (an assertion, a value of the wrong kind, a
    /// function applied outside its domain): the states lead to where, as `ErrorSite` says.
    Error { site: ErrorSite },
}

/// Where a search failed evaluating the model, as `tla_trace::Site` names it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ErrorSite {
    /// Computing the initial states; the violation's states are empty.
    Init,
    /// Computing the successors of the trace's last state.
    Next,
    /// Evaluating the invariant at this position of the model's invariants on the trace's last
    /// state, a successor of the state before it.
    Invariant(u32),
    /// Evaluating the constraint at this position of the model's constraints on an initial state,
    /// the violation's one state.
    InitialConstraint(u32),
    /// Evaluating the invariant at this position of the model's invariants on an initial state,
    /// the violation's one state.
    InitialInvariant(u32),
    /// Evaluating the predicate at this position of the IR's `model.initial_predicates`, which
    /// TLC checks of an initial state after the invariants (its implied inits), on the
    /// violation's one state.
    InitialPredicate(u32),
    /// Evaluating the atom at this position of the IR's `model.atoms` as TLC adds the trace's
    /// last state to the behavior graphs: on that state, or, `is_extra`, on the state after it in
    /// the violation's states, which isn't the trace's: a state predicate's state, or an action's
    /// step's next state.
    Atom { atom: u32, is_extra: bool },
    /// Evaluating the atom at this position of the IR's `model.atoms` as TLC adds an initial
    /// state, the violation's one state, to the behavior graphs, before it checks the state.
    InitialAtom(u32),
}

// The stops that are the engine's own limits, not a failure TLC reports: what it doesn't
// support, what it won't build, what its search and printing can't reproduce, and the violations
// the search reports otherwise.
const SUCCESSOR_CHECK_FAILED: &str =
    "a constraint, a VIEW or an action property that fails on a successor";
const INITIAL_VIEW_FAILED: &str = "a VIEW that fails on an initial state";

fn is_engine_limit(reason: &str) -> bool {
    !TLC_FAILURES.contains(&reason)
}

// The reasons a search stops for that are failures TLC reports evaluating the model. Every other
// reason is the engine's own limit, for the interpreter to take over from, so a model the engine
// can't follow never reports a failure TLC doesn't. Enumerating an infinite set is among the
// limits: the engine enumerates some sets TLC keeps lazy. So is comparing a record with a
// function, which fails in TLC only where it built the value as a record.
const TLC_FAILURES: &[&str] = &[
    "@@ of non-functions",
    "BagCardinality of a non-bag",
    "CHOOSE found no element",
    "CHOOSE from a non-set",
    "DOMAIN of a non-function",
    "EXCEPT on a non-function",
    "Head of an empty sequence",
    "IsFiniteSet of a non-set",
    "RandomElement of the empty set",
    "SortSeq of a non-sequence",
    "SubBag of a non-bag",
    "SubSeq of a non-sequence",
    "SubSeq outside the sequence's domain",
    "TLCModelValue of a value that isn't a string",
    "Tail of an empty sequence",
    "a CASE condition that isn't a boolean",
    "a SelectSeq test that isn't a boolean",
    "a SelectSeq test that isn't an operator",
    "a conjunct that isn't a boolean",
    "a count that isn't a number",
    "a function over a non-set",
    "a function set of non-sets",
    crate::compile::lazy::INFINITE_DOMAIN,
    "a function set over a non-set domain",
    "a guard that isn't a boolean",
    "a membership in SUBSET of a non-set",
    "a mistyped membership in Int",
    "a mistyped membership in Nat",
    "a mistyped membership in STRING",
    "a mistyped membership in Seq",
    "a mistyped membership in a set of functions",
    "a mistyped membership in a set of records",
    "a mistyped membership in a set of tuples",
    "a mistyped membership in an infinite set",
    "a predicate that isn't a boolean",
    "a product of a non-set",
    "a record set of a non-set",
    "a set with too many elements for TLC 1.7.4",
    "a successor that isn't complete",
    "a symmetry function of values that aren't model values",
    "a symmetry that isn't a set of functions",
    "a symmetry value that isn't a function",
    "a tuple pattern that doesn't match",
    "action composition",
    "an IF condition that isn't a boolean",
    "an action quantified over a non-set",
    "an assertion failed",
    "an initial state that isn't complete",
    "an operator's table applied outside its rows",
    "an unbounded CHOOSE",
    "applied a function outside its domain",
    "applied a non-function",
    "applied a recursive function outside its domain",
    "concatenation of a string and a sequence",
    "differently typed model values",
    "division by zero",
    "drew from a value that isn't a set",
    "enumerated a filter of an infinite set",
    "enumerated a non-set",
    crate::compile::INFINITE_BOUND,
    "equality of values TLC can't compare",
    "expected a bag",
    "expected a boolean",
    "expected a function",
    "expected a sequence",
    "expected a set",
    "expected an integer",
    "filtered a non-set",
    "integer overflow",
    "mapped a non-set",
    "membership in a non-set",
    "membership of a value TLC can't compare",
    "modulus by a non-positive number",
    "negative exponent",
    "no CASE arm holds",
    "primed variable not assigned",
    "quantified over a non-set",
    "the left side of => isn't a boolean",
    "values TLC can't compare",
    "variable not assigned",
    "zero to the power of zero",
    crate::compile::lazy::SUBSET_OVERFLOW,
];

/// The counts of a search that stopped, as TLC reports them.
#[derive(Clone, Copy, Default)]
pub struct StopCounts {
    pub generated: u64,
    pub distinct: u64,
    pub queued: u64,
    pub depth: u64,
    /// After an invariant that fails to evaluate, the expansions' out-degrees, the one TLC was
    /// running among them with the new states it had found, as TLC prints them.
    pub out_degrees: [u64; OUT_DEGREE_BUCKETS],
}

// What a search found stopping it, before it hands over the store: the state found that is the
// trace's last state or its parent, then that state when the search didn't keep it.
struct Found {
    kind: ViolationKind,
    parent: Option<usize>,
    last: Option<Vec<Id>>,
    // TLC's fingerprint of the last state, where TLC added it to its set before the stop.
    fingerprint: Option<u64>,
    // The state of the generator where a successor's invariant stopped the search.
    random: Option<u64>,
    counts: StopCounts,
}

const EXIT_UNFOLLOWED: &str = "unsupported: TLCSet(\"exit\", TRUE) outside an invariant";
const LAZY_FUNCTION_HELD: Bail = Bail("unsupported: a state holding a function TLC keeps lazy");
/// Where an atom sets or reads TLC's registers, the search answers the atoms as TLC evaluates
/// them, which it follows only so far.
const ONLINE_DECLINED: &str = "the liveness checker declined as the search went";
const ONLINE_INITIAL: &str = "TLC's registers in atoms of the initial states";
const ONLINE_LATE: &str = "a late node where the atoms use TLC's registers";
const ONLINE_ACCEPTED: &str = "an accepting node where the atoms use TLC's registers";
const NO_NEXT_STATE: &str = "initial states and no next-state relation";
const GRAPH_TOO_LARGE: &str = "a state graph too large to keep";

/// Where TLC may fail evaluating an atom of the temporal properties as it adds a state.
const ATOM_FAILED: &str = "an atom of the temporal properties that may fail to evaluate";

/// What PROVE_IT_LIVE_CHECK finds when TLC's actions take other steps than the next-state relation.
const OTHER_STEPS: &str = "the actions took other steps than the next-state relation";

// Past this many states a search that doesn't check the temporal properties as it goes, where TLC
// would, hands its graph over and the interpreter goes on, since the interpreter checks them on the
// graph as it grows and may find a violation early in a state space the engine would search
// without end; and a hand-over past it starts the interpreter from scratch.
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
    /// Under SYMMETRY or a VIEW, the state each step reached, `width` ids each, which the liveness
    /// checker checks rather than the state stored for it.
    reals: Option<Vec<Id>>,
    /// The search's depth once it expanded each state, TLC's diameter as it adds the state to the
    /// behavior graphs.
    diameters: Vec<u32>,
}

/// The fingerprints found, each with the index of its state: open addressing with linear probing,
/// keyed by TLC's FP64 of the key (DESIGN.md 2.3). A probe reads only the fingerprints, eight to a
/// cache line; the indices, in an array of their own, are read only for an edge of the graph or
/// to verify a fingerprint. 0 marks an empty slot, so a state whose fingerprint is 0 is kept apart.
struct FingerprintSet {
    fingerprints: Vec<u64>,
    // The index of the state in each slot, kept only where the search reads it back: for a graph's
    // edges, or to tell a collision.
    indices: Option<Vec<u32>>,
    // A fingerprint's home slot is the top bits of its hash, so that growing the table moves each
    // fingerprint to about twice its slot, and the table is rewritten in order.
    shift: u32,
    mask: usize,
    len: usize,
    zero: Option<u32>,
}

// The slot that stands for the fingerprint 0, past the table's.
const ZERO_SLOT: usize = usize::MAX;

impl FingerprintSet {
    const INITIAL_CAPACITY: usize = 1 << 12;

    fn new(is_indexed: bool) -> FingerprintSet {
        let capacity = Self::INITIAL_CAPACITY;
        FingerprintSet {
            fingerprints: vec![0; capacity],
            indices: is_indexed.then(|| vec![0; capacity]),
            shift: u64::BITS - capacity.trailing_zeros(),
            mask: capacity - 1,
            len: 0,
            zero: None,
        }
    }

    /// Reads the slot a fingerprint's probe starts at, so that the probe finds it in the cache:
    /// the read goes on while the search does other work.
    #[inline(always)]
    fn touch(&self, fingerprint: u64) {
        let slot: *const u64 = &self.fingerprints[self.home(fingerprint)];
        #[cfg(target_arch = "x86_64")]
        // SAFETY: a prefetch is a hint to the cache. It reads nothing the program sees and never
        // faults, and the address is an element of a live slice.
        unsafe {
            std::arch::x86_64::_mm_prefetch::<{ std::arch::x86_64::_MM_HINT_T0 }>(slot.cast());
        }
        #[cfg(not(target_arch = "x86_64"))]
        let _ = slot;
    }

    #[inline(always)]
    fn home(&self, fingerprint: u64) -> usize {
        (fingerprint.wrapping_mul(0x9e37_79b9_7f4a_7c15) >> self.shift) as usize
    }

    /// The slot that holds this fingerprint, or the slot to put it in.
    #[inline(always)]
    fn find(&self, fingerprint: u64) -> Result<usize, usize> {
        if fingerprint == 0 {
            return self.zero.map_or(Err(ZERO_SLOT), |_| Ok(ZERO_SLOT));
        }
        let mut slot = self.home(fingerprint);
        loop {
            match self.fingerprints[slot] {
                0 => return Err(slot),
                stored if stored == fingerprint => return Ok(slot),
                _ => slot = (slot + 1) & self.mask,
            }
        }
    }

    /// The index of the state whose fingerprint is in a slot.
    fn index(&self, slot: usize) -> u32 {
        match (self.zero, &self.indices) {
            (Some(index), _) if slot == ZERO_SLOT => index,
            (_, Some(indices)) => indices[slot],
            (_, None) => unreachable!("a search that reads its states' indices keeps them"),
        }
    }

    fn insert(&mut self, slot: usize, fingerprint: u64, index: u32) {
        if slot == ZERO_SLOT {
            self.zero = Some(index);
            return;
        }
        self.fingerprints[slot] = fingerprint;
        if let Some(indices) = &mut self.indices {
            indices[slot] = index;
        }
        self.len += 1;
        // At most half full: a third full measured slower, the larger table missing the cache
        // more often than a probe leaves its cache line, and 70% no faster.
        if self.len * 2 > self.fingerprints.len() {
            let capacity = self.fingerprints.len() * 2;
            let fingerprints = std::mem::replace(&mut self.fingerprints, vec![0; capacity]);
            let indices = self
                .indices
                .as_mut()
                .map(|indices| std::mem::replace(indices, vec![0; capacity]));
            self.shift -= 1;
            self.mask = capacity - 1;
            for (old, stored) in fingerprints.into_iter().enumerate() {
                if stored != 0 {
                    let mut slot = self.home(stored);
                    while self.fingerprints[slot] != 0 {
                        slot = (slot + 1) & self.mask;
                    }
                    self.fingerprints[slot] = stored;
                    if let (Some(indices), Some(old_indices)) = (&mut self.indices, &indices) {
                        indices[slot] = old_indices[old];
                    }
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

    // The states from an initial state to this one, each the parent of the next.
    fn path_to(&self, index: usize) -> Vec<u32> {
        let mut path = vec![index as u32];
        while let parent @ 0.. = self.parents[*path.last().expect("a state") as usize] {
            path.push(parent as u32);
        }
        path.reverse();
        path
    }

    fn state(&self, index: u32) -> &[Id] {
        let index = index as usize;
        &self.ids[index * self.width..(index + 1) * self.width]
    }

    fn key_of(&self, index: usize) -> &[Id] {
        match self.key_width {
            Some(width) => &self.keys[index * width..(index + 1) * width],
            None => &self.ids[index * self.width..(index + 1) * self.width],
        }
    }

    // The slot of the state with this key's fingerprint, or the slot to add it at.
    fn find(&mut self, key: &[Id], fingerprint: u64) -> Result<usize, usize> {
        let found = self.set.find(fingerprint);
        if self.is_verified
            && let Ok(slot) = found
            && self.key_of(self.set.index(slot) as usize) != key
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
            encoder
                .encode(store, &ids[index * width..(index + 1) * width])
                .expect(
                    "a state compute_key let the search keep, which holds only values that encode",
                );
        }
        encoder.finish()
    }

    fn share(&self, store: &Store, ids: &[Id], width: usize, count: usize) -> SharedStates {
        let mut encoder = SharedEncoder::new(store);
        for index in 0..count {
            encoder
                .encode(store, &ids[index * width..(index + 1) * width])
                .expect(
                    "a state compute_key let the search keep, which holds only values that encode",
                );
        }
        encoder.finish()
    }
}

// Where the search finds and adds the states its walks reach: the states found, or, for a thread
// expanding a level, the states found before the level and what the thread found in it.
trait Reached {
    fn key_width(&self) -> Option<usize>;
    fn order(&self) -> &[usize];
    fn count(&self) -> usize;
    // Reads ahead the slot a fingerprint's probe starts at.
    fn touch(&self, fingerprint: u64);
    // The slot of the state with this key's fingerprint, or the slot to add it at.
    fn find(&mut self, key: &[Id], fingerprint: u64) -> Result<usize, usize>;
    fn add(&mut self, state: &[Id], key: &[Id], fingerprint: u64, slot: usize, parent: i32);
    // The index of the state in a slot, for an edge of the graph.
    fn index(&self, slot: usize) -> u32;
    // Whether an invariant that fails of a new state, false or failing to evaluate, waits to stop
    // the search until it is known that no other thread found another state with its key first.
    fn defers_violation(&mut self, _parent: usize, _fingerprint: u64) -> bool {
        false
    }
}

impl Reached for States {
    fn key_width(&self) -> Option<usize> {
        self.key_width
    }

    fn order(&self) -> &[usize] {
        &self.order
    }

    fn count(&self) -> usize {
        States::count(self)
    }

    #[inline(always)]
    fn touch(&self, fingerprint: u64) {
        self.set.touch(fingerprint);
    }

    #[inline(always)]
    fn find(&mut self, key: &[Id], fingerprint: u64) -> Result<usize, usize> {
        States::find(self, key, fingerprint)
    }

    fn add(&mut self, state: &[Id], key: &[Id], fingerprint: u64, slot: usize, parent: i32) {
        States::add(self, state, key, fingerprint, slot, parent);
    }

    fn index(&self, slot: usize) -> u32 {
        self.set.index(slot)
    }
}

// The search's state besides the machine, which the walks' continuations update.
struct Search<'r, T, E = Dense> {
    states: T,
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
    // The key, when it isn't the state.
    key: Vec<Id>,
    expansion_epoch: u64,
    level_id: Id,
    next_level_id: Id,
    fingerprints: Fingerprints<E>,
    // The state being expanded, whose successors' fingerprints follow from its own when the key is
    // the state.
    parent: Parent,
    canonicalizer: Option<Canonicalizer>,
    graph: Option<Graph>,
    // The position of the action whose steps the search is taking.
    action: u32,
    // Under PROVE_IT_LIVE_CHECK, the steps the next-state relation took from the state.
    checked: Option<Vec<Vec<Id>>>,
    // Whether a successor is checked once the walk reaches the next, when nothing the search
    // evaluates can tell: then the probe of its fingerprint, read ahead, doesn't wait on memory.
    is_pipelined: bool,
    // Whether the spec may build a function TLC keeps lazy, which no state may hold: TLC can't
    // fingerprint one.
    is_lambda_built: bool,
    // The violation the search stops at, when it knows what TLC reports for it.
    violation: Option<Found>,
    // The successor waiting to be checked, and its fingerprint.
    pending: Vec<Id>,
    pending_fingerprint: Option<u64>,
    // For each _POSSIBLE predicate, how many states or steps it has held of, or -1 before TLC has
    // evaluated it.
    possible: Vec<i64>,
    // With temporal properties, what the search printed computing the initial states and then
    // expanding each state, held until the liveness checker's atoms have printed between them.
    held: Option<Vec<Vec<Printed>>>,
    // Whether TLCSet("exit", TRUE) ran in an invariant, where the search follows it.
    is_exit_followed: bool,
}

impl<'r, T: Reached, E: Entries> Search<'r, T, E> {
    fn new(
        states: T,
        reporter: &'r mut dyn Reporter,
        is_distinct_read: bool,
        is_pipelined: bool,
    ) -> Search<'r, T, E> {
        let width = states.order().len().max(1);
        Search {
            states,
            reporter,
            is_distinct_read,
            generated: 0,
            initial_generated: 0,
            depth: 0,
            level: 1,
            successors: 0,
            new_states: 0,
            expanding: 0,
            current: Vec::with_capacity(width),
            successor: Vec::with_capacity(width),
            key: Vec::with_capacity(width),
            expansion_epoch: 0,
            level_id: 0,
            next_level_id: 0,
            fingerprints: Fingerprints::default(),
            parent: Parent::default(),
            canonicalizer: None,
            graph: None,
            action: 0,
            checked: None,
            is_pipelined,
            is_lambda_built: false,
            pending: Vec::with_capacity(width),
            violation: None,
            pending_fingerprint: None,
            possible: Vec::new(),
            held: None,
            is_exit_followed: false,
        }
    }

    // What the spec printed while the engine computed the initial states or expanded a state goes
    // out once that's done: if the engine hands over, the interpreter does it again.
    fn flush(&mut self, machine: &mut Machine<'_>) {
        let output = std::mem::take(&mut machine.output);
        if let Some(held) = &mut self.held {
            held.push(output);
            return;
        }
        for printed in &output {
            report_printed(self.reporter, &machine.store, printed);
        }
    }

    // TLCGet("distinct") counts the states found so far, and a new state before its checks.
    fn set_distinct(&self, machine: &mut Machine<'_>, count: usize) -> Outcome<()> {
        if self.is_distinct_read {
            let id = machine.store.int(count as i64)?;
            machine.set_slot(DISTINCT_SLOT, id);
        }
        Ok(())
    }

    // The fingerprint of the key of the state that is current, which is the successor when the
    // search visits one: from the fingerprint of the state being expanded when the key is the
    // state. TLC fingerprints the view of the representative when it has both.
    fn compute_key(
        &mut self,
        machine: &mut Machine<'_>,
        context: &EngineContext,
        is_successor: bool,
    ) -> Outcome<u64> {
        // Where the key is a VIEW, the state itself isn't fingerprinted, which would refuse it;
        // every state the search keeps is one the transfer encoding can write.
        if (self.is_lambda_built || context.view.is_some())
            && machine
                .current()
                .iter()
                .any(|&value| machine.store.holds_lazy_function(value))
        {
            return Err(LAZY_FUNCTION_HELD);
        }
        if self.states.key_width().is_none() {
            let (store, order) = (&machine.store, self.states.order());
            return Ok(if is_successor {
                self.fingerprints.get_child(
                    store,
                    &mut self.parent,
                    &self.current,
                    &self.successor,
                    order,
                )?
            } else {
                self.fingerprints
                    .get_state(store, machine.current(), order)?
            });
        }
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
        self.fingerprints
            .get_state(&machine.store, &self.key, self.states.order())
    }

    fn visit_initial(&mut self, machine: &mut Machine<'_>, context: &EngineContext) -> Outcome<()> {
        if machine.current().contains(&UNASSIGNED) {
            return Err(Bail("an initial state that isn't complete"));
        }
        let one = machine.store.int(1)?;
        machine.set_slot(LEVEL_SLOT, one);
        let count = self.initial_generated;
        if count > 1 && count.is_power_of_two() {
            // A count after what the initial predicate printed waits with it.
            if machine.output.is_empty() {
                self.reporter.initial_states_progress(count);
            } else {
                machine.output.push(Printed::InitialStates(count));
            }
        }
        self.generated += 1;
        self.initial_generated += 1;
        let mut is_in_model = true;
        for (position, constraint) in context.constraints.iter().enumerate() {
            match crate::context::holds(machine, &constraint.eval) {
                Ok(true) => {}
                Ok(false) => {
                    is_in_model = false;
                    break;
                }
                Err(bail) => {
                    let site = ErrorSite::InitialConstraint(context.constraint_owners[position]);
                    let distinct = self.states.count() as u64;
                    return Err(self.note_initial_error(machine, site, distinct, bail));
                }
            }
        }
        if is_in_model {
            count_possible(machine, &context.possible, false, &mut self.possible)?;
        }
        let found = if is_in_model {
            // TLC reports a VIEW that fails on an initial state as it fingerprints the state
            // (DoInitFunctor.addElement), which no site here stands for.
            let fingerprint = self.compute_key(machine, context, false).map_err(|bail| {
                if is_engine_limit(bail.0) {
                    bail
                } else {
                    Bail(INITIAL_VIEW_FAILED)
                }
            })?;
            let key = self
                .states
                .key_width()
                .map_or(machine.current(), |_| &self.key);
            Some((fingerprint, self.states.find(key, fingerprint)))
        } else {
            None
        };
        if !matches!(found, Some((_, Ok(_)))) {
            if is_in_model {
                self.set_distinct(machine, self.states.count() + 1)?;
            }
            let mut failing = None;
            for (position, invariant) in context.initial_invariants.iter().enumerate() {
                match crate::context::holds(machine, invariant) {
                    Ok(true) => {}
                    Ok(false) => {
                        failing = Some(position);
                        break;
                    }
                    Err(bail) => {
                        let owner = context.initial_invariant_owners[position] as u32;
                        let distinct = (self.states.count() + usize::from(is_in_model)) as u64;
                        let site = ErrorSite::InitialInvariant(owner);
                        return Err(self.note_initial_error(machine, site, distinct, bail));
                    }
                }
            }
            if let Some(failing) = failing {
                self.violation = Some(Found {
                    kind: ViolationKind::InitialInvariant(
                        context.initial_invariant_owners[failing],
                    ),
                    parent: None,
                    last: Some(machine.current().to_vec()),
                    fingerprint: None,
                    random: None,
                    counts: StopCounts::default(),
                });
                return Err(Bail("an invariant violated in an initial state"));
            }
            for (position, predicate) in context.initial_predicates.iter().enumerate() {
                match crate::context::holds(machine, predicate) {
                    Ok(true) => {}
                    Ok(false) => {
                        self.violation = Some(Found {
                            kind: ViolationKind::InitialPredicate(position),
                            parent: None,
                            last: Some(machine.current().to_vec()),
                            fingerprint: None,
                            random: None,
                            counts: StopCounts::default(),
                        });
                        return Err(Bail("a property violated in an initial state"));
                    }
                    Err(bail) => {
                        let distinct = (self.states.count() + usize::from(is_in_model)) as u64;
                        let site = ErrorSite::InitialPredicate(position as u32);
                        return Err(self.note_initial_error(machine, site, distinct, bail));
                    }
                }
            }
            if let Some((fingerprint, Err(slot))) = found {
                self.states
                    .add(machine.current(), &self.key, fingerprint, slot, -1);
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

    fn set_expanded_current(&self, machine: &mut Machine<'_>) {
        machine.set_current(&self.current, self.expansion_epoch);
        machine.set_slot(LEVEL_SLOT, self.level_id);
    }

    // While the search checks a successor as a state, it is current and the state being expanded
    // is the next one, which a state's predicates don't read: the two swap rather than copy.
    fn swap_successor(&self, machine: &mut Machine<'_>, epoch: u64, level: Id) {
        std::mem::swap(&mut machine.cur, &mut machine.next);
        machine.epoch = epoch;
        machine.set_slot(LEVEL_SLOT, level);
    }

    // A successor the walk completed: checked now, or, pipelined, once the walk reaches the next
    // successor or ends, with its fingerprint computed and its slot read now.
    fn visit_successor(
        &mut self,
        machine: &mut Machine<'_>,
        context: &EngineContext,
    ) -> Outcome<()> {
        if !self.is_pipelined {
            return self.check_successor(machine, context, None);
        }
        // The search checks the successor waiting to be checked before it stops.
        if machine.next().contains(&UNASSIGNED) {
            return Err(Bail("a successor that isn't complete"));
        }
        let fingerprint = self.fingerprints.get_child(
            &machine.store,
            &mut self.parent,
            &self.current,
            machine.next(),
            self.states.order(),
        )?;
        self.states.touch(fingerprint);
        self.check_pending(machine, context)?;
        self.pending.clear();
        self.pending.extend_from_slice(machine.next());
        self.pending_fingerprint = Some(fingerprint);
        Ok(())
    }

    // Checks the successor waiting to be checked, as the walk would have when it completed it. The
    // search calls it once a walk returns, before it stops for anything the walk did since, so a
    // stop has the reason it would have had.
    fn check_pending(&mut self, machine: &mut Machine<'_>, context: &EngineContext) -> Outcome<()> {
        let Some(fingerprint) = self.pending_fingerprint.take() else {
            return Ok(());
        };
        std::mem::swap(&mut machine.next, &mut self.pending);
        let result = self.check_successor(machine, context, Some(fingerprint));
        std::mem::swap(&mut machine.next, &mut self.pending);
        result
    }

    // Where TLCSet("exit", TRUE) ran outside an invariant, TLC's progress then isn't followed.
    fn check_exit_followed(&self, machine: &Machine<'_>) -> Outcome<()> {
        if machine.registers.is_exit && !self.is_exit_followed {
            return Err(Bail(EXIT_UNFOLLOWED));
        }
        Ok(())
    }

    // Checks the successor that is the machine's next state; its fingerprint is `known` when the
    // pipeline computed it already.
    fn check_successor(
        &mut self,
        machine: &mut Machine<'_>,
        context: &EngineContext,
        known: Option<u64>,
    ) -> Outcome<()> {
        if machine.next().contains(&UNASSIGNED) {
            return Err(Bail("a successor that isn't complete"));
        }
        // TLC reports a constraint, a VIEW or an action property that fails to evaluate with the
        // successor in its trace (Worker.addElement), which no site here stands for: the failure
        // of an invariant is noted where it is found.
        self.check_complete_successor(machine, context, known)
            .map_err(|bail| {
                if self.violation.is_none() && !is_engine_limit(bail.0) {
                    Bail(SUCCESSOR_CHECK_FAILED)
                } else {
                    bail
                }
            })
    }

    fn check_complete_successor(
        &mut self,
        machine: &mut Machine<'_>,
        context: &EngineContext,
        known: Option<u64>,
    ) -> Outcome<()> {
        self.check_exit_followed(machine)?;
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
        self.swap_successor(machine, successor_epoch, self.next_level_id);
        // The state being expanded is in the model, so each constraint held of it.
        let is_state_in_model = holds_all_changed(
            machine,
            &context.constraints,
            &self.successor,
            &self.current,
        )
        .and_then(|is_state_in_model| {
            if is_state_in_model {
                count_possible(machine, &context.possible, false, &mut self.possible)?;
            }
            Ok(is_state_in_model)
        });
        self.swap_successor(machine, self.expansion_epoch, self.level_id);
        let is_in_model = is_state_in_model? && holds_all(machine, &context.action_constraints)?;
        // TLC fingerprints a successor, which evaluates the VIEW, only where it is in the model
        // (Worker.addElement).
        let fingerprint = match known {
            Some(fingerprint) => Some(fingerprint),
            None if is_in_model => {
                self.swap_successor(machine, successor_epoch, self.next_level_id);
                let fingerprint = self.compute_key(machine, context, true);
                self.swap_successor(machine, self.expansion_epoch, self.level_id);
                Some(fingerprint?)
            }
            None => None,
        };
        if is_in_model {
            count_possible(machine, &context.possible, true, &mut self.possible)?;
        }
        let found = match fingerprint {
            Some(fingerprint) if is_in_model => {
                let key = self
                    .states
                    .key_width()
                    .map_or(&self.successor, |_| &self.key);
                Some(self.states.find(key, fingerprint))
            }
            _ => None,
        };
        let is_new = matches!(found, Some(Err(_)));
        if is_new {
            self.set_distinct(machine, self.states.count() + 1)?;
        }
        self.check_exit_followed(machine)?;
        if !is_in_model || is_new {
            self.swap_successor(machine, successor_epoch, self.next_level_id);
            let failing =
                first_failing_changed(machine, &context.invariants, &self.successor, &self.current);
            self.swap_successor(machine, self.expansion_epoch, self.level_id);
            // TLC's main thread, woken by the stop, may print its progress as the worker goes
            // on, or not, as the threads race: the binary prints none.
            if machine.registers.is_exit {
                self.is_exit_followed = true;
            }
            let failed = match failing {
                Ok(None) => None,
                Ok(Some(failing)) => {
                    let count = self.states.count() as u64;
                    self.violation = Some(Found {
                        kind: ViolationKind::Invariant(context.invariant_owners[failing]),
                        parent: Some(self.expanding),
                        last: Some(self.successor.clone()),
                        fingerprint: None,
                        random: Some(machine.random.state()),
                        counts: StopCounts {
                            generated: self.generated,
                            distinct: count + u64::from(is_new),
                            queued: count - self.expanding as u64 - 1,
                            depth: if is_new {
                                self.depth.max(self.level + 1)
                            } else {
                                self.depth
                            },
                            ..StopCounts::default()
                        },
                    });
                    Some(Bail("an invariant violated"))
                }
                Err((failing, bail)) => {
                    if !is_engine_limit(bail.0) {
                        let count = self.states.count() as u64;
                        self.violation = Some(Found {
                            kind: ViolationKind::Error {
                                site: ErrorSite::Invariant(
                                    context.invariant_owners[failing] as u32,
                                ),
                            },
                            parent: Some(self.expanding),
                            last: Some(self.successor.clone()),
                            fingerprint: fingerprint.filter(|_| is_new),
                            random: None,
                            counts: StopCounts {
                                generated: self.generated,
                                distinct: count + u64::from(is_new),
                                queued: count - self.expanding as u64 - 1,
                                depth: if is_new {
                                    self.depth.max(self.level + 1)
                                } else {
                                    self.depth
                                },
                                // TLC counts the new state before it checks the invariants. The
                                // search loop adds the expansions it completed.
                                out_degrees: std::array::from_fn(|bucket| {
                                    let new_states = self.new_states + u64::from(is_new);
                                    let failing = (new_states as usize).min(OUT_DEGREE_BUCKETS - 1);
                                    u64::from(bucket == failing)
                                }),
                            },
                        });
                    }
                    Some(bail)
                }
            };
            if let Some(bail) = failed {
                let is_deferred = is_new
                    && fingerprint.is_some_and(|fingerprint| {
                        self.states.defers_violation(self.expanding, fingerprint)
                    });
                if !is_deferred {
                    return Err(bail);
                }
            }
        }
        if let Some(graph) = &mut self.graph
            && is_in_model
        {
            graph.edges.push(match found {
                Some(Ok(slot)) => self.states.index(slot),
                _ => self.states.count() as u32,
            });
            if let Some(labels) = &mut graph.labels {
                labels.push(self.action);
            }
            if let Some(reals) = &mut graph.reals {
                reals.extend_from_slice(&self.successor);
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
            self.states.add(
                &self.successor,
                &self.key,
                fingerprint,
                slot,
                self.expanding as i32,
            );
            self.new_states += 1;
            self.depth = self.level + 1;
        }
        Ok(())
    }
}

impl<T: Reached, E: Entries> Search<'_, T, E> {
    // Takes the steps of the state `current` holds, the state `expanding` names, whose
    // fingerprint is given: through the next-state relation, or through each of TLC's actions.
    fn expand(
        &mut self,
        machine: &mut Machine<'_>,
        context: &EngineContext,
        fingerprint: u64,
        actions: Option<&[Step]>,
        is_live_checked: bool,
        check_deadlock: bool,
    ) -> Outcome<()> {
        machine.next.clear();
        machine.next.resize(self.current.len(), UNASSIGNED);
        machine.reset_assigned();
        self.new_states = 0;
        self.successors = 0;
        self.expansion_epoch = machine.next_epoch();
        self.level_id = machine.store.int(self.level as i64)?;
        self.next_level_id = machine.store.int(self.level as i64 + 1)?;
        self.set_expanded_current(machine);
        machine.seed_random(fingerprint);
        machine.set_slot(NEXT_LEVEL_SLOT, self.next_level_id);
        if self.states.key_width().is_none() {
            self.fingerprints.set_parent(
                &machine.store,
                &self.current,
                self.states.order(),
                fingerprint,
                &mut self.parent,
            )?;
        }
        match actions {
            None => {
                let next = context.next.as_ref().expect("a next-state relation");
                let walked = next(machine, &mut |machine: &mut Machine<'_>| {
                    self.visit_successor(machine, context)
                });
                self.check_pending(machine, context)?;
                walked.map_err(|bail| self.note_next_error(bail))?;
            }
            Some(actions) => {
                if is_live_checked {
                    let mut checked = Vec::new();
                    let next = context.next.as_ref().expect("a next-state relation");
                    next(machine, &mut |machine: &mut Machine<'_>| {
                        checked.push(machine.next().to_vec());
                        Ok(())
                    })?;
                    self.checked = Some(checked);
                }
                for (position, action) in actions.iter().enumerate() {
                    self.action = position as u32;
                    let walked = action(machine, &mut |machine: &mut Machine<'_>| {
                        self.visit_successor(machine, context)
                    });
                    self.check_pending(machine, context)?;
                    walked.map_err(|bail| self.note_next_error(bail))?;
                }
                if let Some(checked) = self.checked.take()
                    && checked.len() as u64 != self.successors
                {
                    return Err(Bail(OTHER_STEPS));
                }
            }
        }
        if self.successors == 0 && check_deadlock {
            let count = self.states.count() as u64;
            self.violation = Some(Found {
                kind: ViolationKind::Deadlock { accepted: None },
                parent: Some(self.expanding),
                last: None,
                fingerprint: None,
                random: None,
                counts: StopCounts {
                    generated: self.generated,
                    distinct: count,
                    queued: count - self.expanding as u64 - 1,
                    depth: self.depth.max(1),
                    ..StopCounts::default()
                },
            });
            return Err(Bail("deadlock"));
        }
        Ok(())
    }
}

impl<T: Reached, E: Entries> Search<'_, T, E> {
    // A failure computing the successors of the state being expanded, which TLC reports with the
    // path to that state, unless the search already found what stopped it.
    // A failure evaluating a constraint or an invariant on an initial state, which TLC reports
    // with the state and the counts so far, the state counted as generated.
    fn note_initial_error(
        &mut self,
        machine: &Machine<'_>,
        site: ErrorSite,
        distinct: u64,
        bail: Bail,
    ) -> Bail {
        if self.violation.is_none() && !is_engine_limit(bail.0) {
            self.violation = Some(Found {
                kind: ViolationKind::Error { site },
                parent: None,
                last: Some(machine.current().to_vec()),
                fingerprint: None,
                random: None,
                counts: StopCounts {
                    generated: self.generated,
                    distinct,
                    queued: distinct,
                    depth: 1,
                    ..StopCounts::default()
                },
            });
        }
        bail
    }

    fn note_next_error(&mut self, bail: Bail) -> Bail {
        if self.violation.is_none() && !is_engine_limit(bail.0) {
            let count = self.states.count() as u64;
            self.violation = Some(Found {
                kind: ViolationKind::Error {
                    site: ErrorSite::Next,
                },
                parent: Some(self.expanding),
                last: None,
                fingerprint: None,
                random: None,
                counts: StopCounts {
                    generated: self.generated,
                    distinct: count,
                    queued: count - self.expanding as u64 - 1,
                    depth: self.depth.max(1),
                    ..StopCounts::default()
                },
            });
        }
        bail
    }
}

// The most states of a level a thread claims at once (`CHUNK` in `parallel.ts`).
const CHUNK: usize = 32;

// Marks a slot of a thread's own states, which `Candidates::find` returns apart from the slots of
// the states found before the level.
const SEEN: usize = 1 << (usize::BITS - 1);

// A thread expanding part of a level reports nothing: what it would report, Print's output, makes
// the search run on one thread.
struct Quiet;

impl Reporter for Quiet {
    fn initial_states_started(&mut self) {}
    fn initial_states_progress(&mut self, _count: u64) {}
    fn initial_states(&mut self, _generated: u64, _distinct: u64) {}
    fn progress(&mut self, _generated: u64, _distinct: u64, _queued: u64, _depth: u64) {}
    fn print(&mut self, _store: &Store, _values: &[Id]) {}
}

// The states a thread found in a level that weren't found before it, in the order it found them:
// each once, from the first of its own steps that reached it (DESIGN.md 4.1).
struct Candidates<'b> {
    before: &'b States,
    seen: FingerprintSet,
    ids: Vec<Id>,
    keys: Vec<Id>,
    fingerprints: Vec<u64>,
    parents: Vec<u32>,
    deferred: Vec<(u32, u64)>,
    collisions: u64,
}

impl Candidates<'_> {
    fn key_of(&self, index: usize) -> &[Id] {
        match self.before.key_width {
            Some(width) => &self.keys[index * width..(index + 1) * width],
            None => &self.ids[index * self.before.width..(index + 1) * self.before.width],
        }
    }
}

impl Reached for Candidates<'_> {
    fn key_width(&self) -> Option<usize> {
        self.before.key_width
    }

    fn order(&self) -> &[usize] {
        &self.before.order
    }

    fn count(&self) -> usize {
        self.before.count() + self.parents.len()
    }

    #[inline(always)]
    fn touch(&self, fingerprint: u64) {
        self.before.set.touch(fingerprint);
    }

    // A key's values that the store held before the level have the same ids in the thread's
    // overlay, and the others have ids the store doesn't, so the keys compare by id.
    fn find(&mut self, key: &[Id], fingerprint: u64) -> Result<usize, usize> {
        let before = self.before;
        if let Ok(slot) = before.set.find(fingerprint) {
            if before.is_verified && before.key_of(before.set.index(slot) as usize) != key {
                self.collisions += 1;
            }
            return Ok(slot);
        }
        let found = self.seen.find(fingerprint);
        if before.is_verified
            && let Ok(slot) = found
            && self.key_of(self.seen.index(slot) as usize) != key
        {
            self.collisions += 1;
        }
        found.map(|slot| slot | SEEN)
    }

    fn add(&mut self, state: &[Id], key: &[Id], fingerprint: u64, slot: usize, parent: i32) {
        let index = self.parents.len() as u32;
        self.ids.extend_from_slice(state);
        if self.before.key_width.is_some() {
            self.keys.extend_from_slice(key);
        }
        self.fingerprints.push(fingerprint);
        self.parents.push(parent as u32);
        self.seen.insert(slot, fingerprint, index);
    }

    // A state found before the level by its index, and one the thread found by the index it would
    // have if the thread's states all joined the store after the level's first: the merge gives
    // each the index it does take.
    fn index(&self, slot: usize) -> u32 {
        if slot & SEEN == 0 {
            return self.before.set.index(slot);
        }
        (self.before.count() + self.seen.index(slot & !SEEN) as usize) as u32
    }

    // Where the key isn't the state, a thread that takes a state for new may have missed another
    // with the same key that another thread found first, whose invariant TLC checks instead.
    fn defers_violation(&mut self, parent: usize, fingerprint: u64) -> bool {
        if self.before.key_width.is_none() {
            return false;
        }
        self.deferred.push((parent as u32, fingerprint));
        true
    }
}

// A thread of the search: its machine, on an overlay of the store, and its caches, which it keeps
// from level to level but for what they hold of the overlay's own values. Each takes cache lines
// of its own, since its machine's registers are written on every step.
#[repr(align(128))]
struct Worker<'p> {
    machine: Machine<'p>,
    fingerprints: Fingerprints<Overlaid>,
    canonicalizer: Option<Canonicalizer>,
    // The store's count of values when the overlay was last laid on it: its own ids start there.
    bound: Id,
    // The id in the store of each of the overlay's values imported.
    imported: Vec<Id>,
}

impl Worker<'_> {
    fn attach(&mut self, store: &Arc<Store>, fingerprints: &SharedFingerprints) {
        self.machine.forget_from(self.bound);
        self.fingerprints
            .attach(fingerprints, store.value_count() as Id);
        if let Some(canonicalizer) = &mut self.canonicalizer {
            canonicalizer.forget_from(self.bound);
        }
        self.machine.store.attach(store.clone());
        self.bound = store.value_count() as Id;
        self.imported.clear();
    }
}

// A run of a level's states a thread claimed: the first, and where its successor counts and
// candidates start among the thread's.
struct Claimed {
    start: usize,
    successors: usize,
    candidates: usize,
}

// What a thread did in a level: the runs it claimed, how many successors it generated from each
// state it expanded, and the states it found.
struct Expanded {
    claimed: Vec<Claimed>,
    successors: Vec<u32>,
    // The steps of each state it expanded, where the search records its graph, each to a state
    // by the index `Candidates::index` gives it.
    graph: Option<Graph>,
    ids: Vec<Id>,
    keys: Vec<Id>,
    fingerprints: Vec<u64>,
    parents: Vec<u32>,
    // Each state, by its parent, whose invariant failed but which another thread may have found
    // first under a VIEW or symmetry, as another state with the same key.
    deferred: Vec<(u32, u64)>,
    collisions: u64,
    is_past_walk: bool,
}

// A level the threads share: the states `[start, end)`, the next run to claim, and the first
// state not to expand, lowered to the state being expanded wherever a thread stops.
struct Level {
    start: usize,
    end: usize,
    chunk: usize,
    number: u64,
    cursor: Padded<AtomicUsize>,
    stop: Padded<AtomicUsize>,
    is_pipelined: bool,
    check_deadlock: bool,
    // Whether the search hands its graph over past MAXIMUM_GRAPH_STATES.
    is_graph_bounded: bool,
    // PROVE_IT_STOP_AT: where the search stops, as if it failed there.
    stop_at: Option<usize>,
}

// A value on cache lines of its own, so that writing it doesn't move what threads read beside it.
#[repr(align(128))]
struct Padded<T>(T);

impl<T> std::ops::Deref for Padded<T> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.0
    }
}

// What every thread of a level reads.
struct Shared<'s> {
    context: &'s EngineContext,
    before: &'s States,
    level: &'s Level,
    // The actions that label the steps, where the search records a graph that labels them.
    actions: Option<&'s [Step]>,
    // Where the search records its graph, what each thread records of its steps.
    recording: Option<Recording>,
}

// What a graph keeps of each step besides its target: the action that took it, and the state it
// reached under SYMMETRY or a VIEW.
#[derive(Clone, Copy)]
struct Recording {
    is_labelled: bool,
    is_real: bool,
}

// Expands runs of a level's states on a thread, until none are left before the first state not to
// expand, recording where it stops if it stops.
fn expand_claimed(worker: &mut Worker<'_>, shared: &Shared<'_>) -> Expanded {
    let (before, level) = (shared.before, shared.level);
    let candidates = Candidates {
        before,
        seen: FingerprintSet::new(before.set.indices.is_some()),
        ids: Vec::new(),
        keys: Vec::new(),
        fingerprints: Vec::new(),
        parents: Vec::new(),
        deferred: Vec::new(),
        collisions: 0,
    };
    let mut quiet = Quiet;
    let mut search = Search::new(candidates, &mut quiet, false, level.is_pipelined);
    search.level = level.number;
    search.graph = shared.recording.map(|recording| Graph {
        edge_offsets: vec![0],
        labels: recording.is_labelled.then(Vec::new),
        reals: recording.is_real.then(Vec::new),
        ..Graph::default()
    });
    search.fingerprints = std::mem::take(&mut worker.fingerprints);
    search.canonicalizer = worker.canonicalizer.take();
    let (mut claimed, mut successors) = (Vec::new(), Vec::new());
    let width = before.width;
    'claiming: loop {
        let start = level.cursor.fetch_add(level.chunk, Ordering::Relaxed);
        if start >= level.end || start >= level.stop.load(Ordering::Relaxed) {
            break;
        }
        claimed.push(Claimed {
            start,
            successors: successors.len(),
            candidates: search.states.parents.len(),
        });
        for expanding in start..(start + level.chunk).min(level.end) {
            if expanding >= level.stop.load(Ordering::Relaxed) {
                break 'claiming;
            }
            search.expanding = expanding;
            search.current.clear();
            search
                .current
                .extend_from_slice(&before.ids[expanding * width..(expanding + 1) * width]);
            let fingerprint = before.fingerprints[expanding];
            let machine = &mut worker.machine;
            let context = shared.context;
            match search.expand(
                machine,
                context,
                fingerprint,
                shared.actions,
                false,
                level.check_deadlock,
            ) {
                Ok(()) => {
                    successors.push(search.successors as u32);
                    if let Some(graph) = &mut search.graph {
                        graph.edge_offsets.push(graph.edges.len() as u32);
                    }
                }
                Err(_) => {
                    level.stop.fetch_min(expanding, Ordering::Relaxed);
                    break 'claiming;
                }
            }
        }
    }
    worker.fingerprints = std::mem::take(&mut search.fingerprints);
    worker.canonicalizer = search.canonicalizer.take();
    let found = search.states;
    Expanded {
        claimed,
        successors,
        graph: search.graph,
        ids: found.ids,
        keys: found.keys,
        fingerprints: found.fingerprints,
        parents: found.parents,
        deferred: found.deferred,
        collisions: found.collisions,
        is_past_walk: worker.machine.is_past_walk,
    }
}

impl Search<'_, States> {
    // Expands the level from the state `expanding` to `end` on the threads (DESIGN.md 4.1, 4.2):
    // each expands runs of it in an overlay of the store, and the states they found join the
    // store's in the order of the step that first reached each, by parent and then by step, which
    // is the order TLC's one worker finds them in. Where a thread stops, the search stops at the
    // first state whose expansion stopped, with the states and counts found before it.
    fn expand_level(
        &mut self,
        machine: &mut Machine<'_>,
        workers: &mut [Worker<'_>],
        context: &EngineContext,
        level: &Level,
        actions: Option<&[Step]>,
        out_degrees: &mut [u64; OUT_DEGREE_BUCKETS],
    ) -> Outcome<()> {
        let shared = Shared {
            context,
            before: &self.states,
            level,
            actions,
            recording: self.graph.as_ref().map(|graph| Recording {
                is_labelled: graph.labels.is_some(),
                is_real: graph.reals.is_some(),
            }),
        };
        let store = Arc::new(std::mem::take(&mut machine.store));
        let fingerprints = self.fingerprints.share();
        let expanded: Vec<Expanded> = std::thread::scope(|scope| {
            let threads: Vec<_> = workers
                .iter_mut()
                .map(|worker| {
                    let (shared, store, fingerprints) = (&shared, &store, &fingerprints);
                    std::thread::Builder::new()
                        .stack_size(NESTING_STACK_BYTES)
                        .spawn_scoped(scope, move || {
                            worker.attach(store, fingerprints);
                            expand_claimed(worker, shared)
                        })
                        .expect("a thread for the search")
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
        for worker in workers.iter_mut() {
            worker.machine.store.detach();
            worker.fingerprints.detach();
        }
        machine.store = Arc::into_inner(store).expect("the store, once the threads let go of it");
        self.fingerprints.take_back(fingerprints);
        let mut stop = level.stop.load(Ordering::Relaxed);
        let mut owners = vec![None; (level.end - level.start).div_ceil(level.chunk)];
        for (thread, found) in expanded.iter().enumerate() {
            for (run, claimed) in found.claimed.iter().enumerate() {
                owners[(claimed.start - level.start) / level.chunk] = Some((thread, run));
            }
        }
        let width = self.states.width;
        let key_width = self.states.key_width;
        let is_verified = self.states.is_verified;
        let mut new_counts = vec![0u32; level.end - level.start];
        let (mut state, mut key) = (Vec::with_capacity(width), Vec::with_capacity(width));
        // Where the search records its graph, the index each thread's states took, by the order
        // it found them in: their own where they joined the states, or that of the state with
        // their key found first.
        let before_count = self.states.count();
        let mut resolved: Vec<Vec<u32>> = expanded
            .iter()
            .map(|found| match self.graph {
                Some(_) => vec![u32::MAX; found.parents.len()],
                None => Vec::new(),
            })
            .collect();
        // The states in order, each run by the thread that claimed it: what each state's expansion
        // found joins the states found, unless an invariant it deferred fails of a state that is
        // new, which stops the search there.
        'states: for &(thread, run) in owners.iter().map_while(Option::as_ref) {
            let found = &expanded[thread];
            let claimed = &found.claimed[run];
            let next = found.claimed.get(run + 1);
            let worker = &mut workers[thread];
            let overlay = &worker.machine.store;
            let mut import = |ids: &[Id], into: &mut Vec<Id>| {
                into.clear();
                into.extend(
                    ids.iter()
                        .map(|&id| machine.store.import(overlay, id, &mut worker.imported)),
                );
            };
            let mut candidate = claimed.candidates;
            let mut deferred = found
                .deferred
                .partition_point(|&(parent, _)| (parent as usize) < claimed.start);
            for (offset, parent) in
                (claimed.start..(claimed.start + level.chunk).min(level.end)).enumerate()
            {
                if parent > stop {
                    break 'states;
                }
                while let Some(&(at, fingerprint)) = found.deferred.get(deferred)
                    && at as usize == parent
                {
                    if self.states.set.find(fingerprint).is_err() {
                        stop = parent;
                        break 'states;
                    }
                    deferred += 1;
                }
                if parent == stop {
                    break 'states;
                }
                // The bounds the one-thread search checks before it expands a state of a graph it
                // records stop it there, on the one-thread path.
                if self.graph.as_ref().is_some_and(|graph| {
                    level.is_graph_bounded && self.states.count() > MAXIMUM_GRAPH_STATES
                        || self.states.count() >= i32::MAX as usize
                        || graph.edges.len() >= i32::MAX as usize
                }) {
                    stop = parent;
                    break 'states;
                }
                self.generated += u64::from(found.successors[claimed.successors + offset]);
                let candidates =
                    candidate..next.map_or(found.parents.len(), |next| next.candidates);
                for index in candidates {
                    if found.parents[index] as usize != parent {
                        break;
                    }
                    candidate += 1;
                    // The probe for a candidate further on, so that its slot is in the cache by its
                    // turn: the table is far larger than the cache, and the merge runs alone.
                    if let Some(&ahead) = found.fingerprints.get(index + MERGE_PREFETCH) {
                        self.states.set.touch(ahead);
                    }
                    let fingerprint = found.fingerprints[index];
                    let ids = &found.ids[index * width..(index + 1) * width];
                    let keys = key_width
                        .map(|key_width| &found.keys[index * key_width..(index + 1) * key_width]);
                    if is_verified {
                        import(keys.unwrap_or(ids), &mut key);
                    }
                    let slot = match self.states.find(&key, fingerprint) {
                        Ok(slot) => {
                            if let Some(index) = resolved[thread].get_mut(index) {
                                *index = self.states.index(slot);
                            }
                            continue;
                        }
                        Err(slot) => slot,
                    };
                    if let Some(index) = resolved[thread].get_mut(index) {
                        *index = self.states.count() as u32;
                    }
                    import(ids, &mut state);
                    if let Some(keys) = keys {
                        import(keys, &mut key);
                    }
                    self.states
                        .add(&state, &key, fingerprint, slot, parent as i32);
                    new_counts[parent - level.start] += 1;
                    self.depth = self.depth.max(level.number + 1);
                }
                if let Some(graph) = &mut self.graph {
                    let steps_of = found.graph.as_ref().expect("a thread's steps");
                    let at = claimed.successors + offset;
                    let steps =
                        steps_of.edge_offsets[at] as usize..steps_of.edge_offsets[at + 1] as usize;
                    let resolved = &resolved[thread];
                    graph
                        .edges
                        .extend(steps_of.edges[steps.clone()].iter().map(|&target| {
                            let target = target as usize;
                            if target < before_count {
                                target as u32
                            } else {
                                resolved[target - before_count]
                            }
                        }));
                    if let (Some(labels), Some(labels_of)) = (&mut graph.labels, &steps_of.labels) {
                        labels.extend_from_slice(&labels_of[steps.clone()]);
                    }
                    if let (Some(reals), Some(reals_of)) = (&mut graph.reals, &steps_of.reals) {
                        import(
                            &reals_of[steps.start * width..steps.end * width],
                            &mut state,
                        );
                        reals.extend_from_slice(&state);
                    }
                    graph.successor_counts.push(found.successors[at]);
                    graph.new_counts.push(new_counts[parent - level.start]);
                    graph.edge_offsets.push(graph.edges.len() as u32);
                    graph.diameters.push(self.depth.max(1) as u32);
                }
            }
        }
        new_counts.truncate(stop - level.start);
        for &count in &new_counts {
            out_degrees[(count as usize).min(OUT_DEGREE_BUCKETS - 1)] += 1;
        }
        for found in &expanded {
            self.states.collisions += found.collisions;
            machine.is_past_walk |= found.is_past_walk;
        }
        // The shapes each thread's walks assigned, joined into the store's from the values that
        // widened them, which the thread's overlay forgets at the next level.
        if let Some(joins) = &mut machine.assigned_shapes {
            for worker in workers.iter_mut() {
                let overlay = &worker.machine.store;
                for (join, found) in joins
                    .iter_mut()
                    .zip(worker.machine.assigned_shapes.iter_mut().flatten())
                {
                    for &id in found.widening() {
                        let id = machine.store.import(overlay, id, &mut worker.imported);
                        machine.store.join_shape(join, id);
                    }
                    *found = ShapeJoin::default();
                }
            }
        }
        self.expanding = stop;
        // The fingerprints each thread computed, of the store's values and of the values it made
        // that are now the store's, for every thread to read at the next level.
        for worker in workers.iter() {
            self.fingerprints
                .absorb(&worker.fingerprints, &worker.imported);
        }
        if stop < level.end && level.stop_at == Some(stop) {
            return Err(Bail("stopped where PROVE_IT_STOP_AT asked"));
        }
        // A level stopped part way, by a violation, an error or a limit at the state `stop`, ends
        // on one thread: it expands `stop` again, and stops there as the one-thread search does,
        // with everything TLC reports of the stop, which a thread keeps none of.
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

// What TLC's startup printed as it evaluated the substitutes, the constant definitions and the
// symmetry, the symmetry's group and the sets it warns about, then what it printed as it evaluated
// the assumptions, and the assumption it found false.
struct Started {
    printed: Vec<Vec<Id>>,
    /// The sets the symmetry permutes that TLC warns hold fewer than two elements, by name.
    small_sets: Vec<String>,
    group: Option<Group>,
    assumed: Vec<Vec<Id>>,
    violated: Option<String>,
    /// The assumption that failed to evaluate, by its position, and why.
    failed: Option<(u32, Bail)>,
    /// The configuration error a constant definition's value gave, which ends the startup.
    config_error: Option<String>,
    /// The assumption the engine left to its caller, by its position.
    // The assumption left to the caller, and why the engine didn't evaluate it.
    delegated: Option<(u32, Bail)>,
}

// TLC's startup: it evaluates the substitutes and the constant definitions, then the assumptions
// until one is false. What they print is kept until all of it is evaluated, so a model the engine
// can't take prints nothing.
// `is_native`: the native checker reports an assumption the engine fails to evaluate however it
// fails, since its evaluator of failures words TLC's error or finds none, which keeps the run
// from being native; otherwise one the engine can't follow is the interpreter's, as is a
// substitute that fails.
fn run_startup(machine: &mut Machine<'_>, startup: &Startup, is_native: bool) -> Outcome<Started> {
    let take = |machine: &mut Machine<'_>| {
        std::mem::take(&mut machine.output)
            .into_iter()
            .filter_map(|printed| match printed {
                Printed::Values(values) => Some(values),
                Printed::InitialStates(_) => None,
            })
            .collect::<Vec<_>>()
    };
    // The front end rejects a substitute TLC checks and finds failing (`processConstantDefns`), so
    // one that fails here is one the native checker leaves to fail where it is used, as TLC does.
    for evaluate in &startup.substitutes {
        let result = evaluate(machine);
        if !is_native {
            result?;
        }
    }
    // `processConstantDefns`: TLC swallows whatever a constant definition throws and keeps it as
    // an operator, which evaluates it again, with its effects, at every use, where the engine
    // would keep the first value it computes.
    for evaluate in &startup.definitions {
        if evaluate(machine).is_err() {
            return Err(Bail(
                "unsupported: a definition TLC computes at startup that fails there",
            ));
        }
    }
    // `getConstantValue`: TLC keeps a definition that fails to evaluate as an operator.
    for (evaluate, form, kind, name) in &startup.predicates {
        let value = match evaluate(machine) {
            Ok(value) => value,
            Err(bail) if is_engine_limit(bail.0) => return Err(bail),
            Err(_) => continue,
        };
        // The store forgets how TLC built some values, whose text then depends on it.
        let format = |machine: &Machine<'_>| {
            if tla_values::print::is_printable(&machine.store, value) {
                tla_values::print::format_value(&machine.store, value)
            } else {
                Err(Bail(
                    "unsupported: printing a value whose text depends on how TLC built it",
                ))
            }
        };
        let message = match form {
            PredicateForm::Predicate if value == TRUE => continue,
            PredicateForm::Predicate => {
                format!("The {kind} of {name} is equal to {}", format(machine)?)
            }
            PredicateForm::Definition => format!("The {kind} {name} cannot be a constant."),
            PredicateForm::Specification => {
                format!("The value of {name} is equal to {}", format(machine)?)
            }
        };
        return Ok(Started {
            printed: take(machine),
            small_sets: Vec::new(),
            group: None,
            assumed: Vec::new(),
            violated: None,
            failed: None,
            config_error: Some(message),
            delegated: None,
        });
    }
    let (group, small_sets) = match &startup.symmetry {
        Some(symmetry) => symmetry_group(machine, symmetry)?,
        None => (None, Vec::new()),
    };
    let printed = take(machine);
    let assumed = check_assumptions(machine, startup, 0, is_native)?;
    Ok(Started {
        printed,
        small_sets,
        group,
        assumed: take(machine),
        violated: assumed.violated,
        failed: assumed.failed,
        config_error: None,
        delegated: assumed.delegated,
    })
}

struct Assumed {
    violated: Option<String>,
    failed: Option<(u32, Bail)>,
    // The assumption left to the caller, and why the engine didn't evaluate it.
    delegated: Option<(u32, Bail)>,
}

// The assumptions from `from` on, until one is false, fails, or is left to the caller.
fn check_assumptions(
    machine: &mut Machine<'_>,
    startup: &Startup,
    from: usize,
    is_native: bool,
) -> Outcome<Assumed> {
    let mut assumed = Assumed {
        violated: None,
        failed: None,
        delegated: None,
    };
    for (position, (evaluate, name)) in startup.assumptions.iter().enumerate().skip(from) {
        match crate::context::holds(machine, evaluate) {
            Ok(true) => {}
            Ok(false) => {
                assumed.violated = Some(name.clone());
                break;
            }
            // One the engine stops at a limit of is the caller's too, whose evaluator follows
            // TLC further, as where TLC compares two sets it can't enumerate part by part. So
            // is one that enumerates a set the engine takes for one TLC can't enumerate, which
            // TLC fails at only where it enumerates such a set itself: it compares two sets of
            // functions over Nat by their parts, and enumerates `Nat \cap S` by S.
            Err(bail)
                if is_native
                    && (is_engine_limit(bail.0)
                        || [
                            crate::compile::lazy::INFINITE_DOMAIN,
                            crate::compile::INFINITE_BOUND,
                        ]
                        .contains(&bail.0)) =>
            {
                assumed.delegated = Some((position as u32, bail));
                break;
            }
            Err(bail) if is_engine_limit(bail.0) && !is_native => return Err(bail),
            Err(bail) => {
                assumed.failed = Some((position as u32, bail));
                break;
            }
        }
    }
    Ok(assumed)
}

// The group of the SYMMETRY definition's value as `Tool.getSymmetryPerms` builds it, none where
// it has no permutation but the identity, and the sets it permutes that TLC warns hold fewer than
// two elements: all of them where there are as many as permutations, or else each set TLC checks
// that holds no model value the group moves.
fn symmetry_group(
    machine: &mut Machine<'_>,
    symmetry: &StartupSymmetry,
) -> Outcome<(Option<Group>, Vec<String>)> {
    let value = (symmetry.definition)(machine)?;
    let permutations = get_permutations(&mut machine.store, value)?;
    let names = |sets: Vec<&(String, Option<Eval>)>| {
        sets.into_iter().map(|(name, _)| name.clone()).collect()
    };
    if symmetry.permuted_sets.len() >= permutations.len() {
        return Ok((None, names(symmetry.permuted_sets.iter().collect())));
    }
    let group = close_group(permutations);
    let moved: HashSet<Id> = group
        .iter()
        .flat_map(|permutation| permutation.values().copied())
        .collect();
    let mut small = Vec::new();
    for set in &symmetry.permuted_sets {
        let Some(operand) = &set.1 else { continue };
        let value = operand(machine)?;
        let store = &machine.store;
        if store.kind_of(value) == KIND_SET
            && !(0..store.size_of(value))
                .any(|index| moved.contains(&store.element_at(value, index)))
        {
            small.push(set);
        }
    }
    Ok(((!group.is_empty()).then_some(group), names(small)))
}

// The values the startup definitions computed, which reading them again gives without effects.
fn startup_values(machine: &mut Machine<'_>, context: &EngineContext) -> Outcome<Vec<Id>> {
    context
        .startup
        .definitions
        .iter()
        .map(|evaluate| evaluate(machine))
        .collect()
}

// The startup definitions' values as one row of shared states.
fn share_startup(machine: &mut Machine<'_>, context: &EngineContext) -> Outcome<SharedStates> {
    let values = startup_values(machine, context)?;
    let mut encoder = SharedEncoder::new(&machine.store);
    encoder.encode(&machine.store, &values)?;
    Ok(encoder.finish())
}

/// Searches the model the IR describes. It runs compiled closures, which recurse with the
/// expressions and values, so its caller runs it on a thread with a deep stack.
pub fn search(ir: &Ir, settings: &Settings, reporter: &mut dyn Reporter) -> SearchOutcome {
    let model = &ir.model;
    let ranked: Vec<Vec<u16>> = (0..ir.ranked_count)
        .map(|text| ir.get_text_units(text))
        .collect();
    let mut store = Store::new();
    store.reset(ranked.iter().map(Vec::as_slice));
    store.freeze_string_order();
    let mut compiler = Compiler::new(ir, &mut store, settings.compile);
    compiler.workers = settings.workers;
    compiler.is_native = settings.is_violation_reported;
    let context = match EngineContext::build(&mut compiler, ir) {
        Ok(context) => context,
        Err(error) => return SearchOutcome::Declined(describe(error)),
    };
    // A search that ranked strings may start over in the interpreter, which would print again
    // what the search printed; the native checker never starts over.
    if compiler.is_printing && compiler.is_ranking && !settings.is_violation_reported {
        return SearchOutcome::Declined("unsupported: Print with ToString".into());
    }
    // The liveness checker evaluates its atoms in an order of its own.
    if compiler.is_cached && settings.is_live_checked {
        return SearchOutcome::Declined("unsupported: TLCCache with a liveness check".into());
    }
    let is_distinct_read = compiler.is_distinct_read;
    let is_printing = compiler.is_printing;
    // Checking a successor once the walk reaches the next reorders nothing anyone can see where
    // nothing prints, reads the count of distinct states, caches what TLC first evaluates, or
    // fingerprints a VIEW or symmetry's representative, which the walk would then interleave with.
    let is_lambda_built = compiler.is_lambda_built;
    let is_pipelined = !is_printing
        && !is_lambda_built
        && !compiler.is_cached
        && !is_distinct_read
        && context.view.is_none()
        && model.startup.symmetry.is_none()
        && !settings.is_live_checked;
    // A level's states are shared between threads where the order of the steps across states
    // shows nowhere but in the states found and the graph the merge records in that order: nothing
    // prints or reads the count of distinct states, and no test asks for a check of the graph at
    // a state inside a level.
    // More threads than the machine runs at once would only take turns.
    let thread_count = settings
        .threads
        .min(std::thread::available_parallelism().map_or(1, std::num::NonZero::get));
    // ToString ranks the strings it makes as it evaluates, which threads would do in no order.
    let is_shared = thread_count > 1
        && !compiler.is_ranking
        && !compiler.is_printing
        && !is_lambda_built
        && !compiler.is_cached
        && !is_distinct_read
        && !(model.is_recording_graph && settings.test_live_check_at.is_some())
        // The online checker adds each state as it is expanded, between the expansions, and the
        // held prints come out between them: neither may meet a level the threads share.
        && !(model.is_recording_graph && (context.is_live_registered || compiler.is_printing))
        && !settings.is_live_checked
        && context.possible.is_empty();
    // The liveness checker's atoms are answered on the threads too, unless ToString ranks strings,
    // TLCCache caches (TLC keeps one cache for the run, which the search's machine holds, and fills
    // it in the order it first evaluates each expression), or anything prints, draws or reads or
    // sets TLC's registers: a helper machine has none of the search's registers or generator.
    let atom_threads = if compiler.is_ranking
        || compiler.is_printing
        || is_lambda_built
        || compiler.is_tlc_cache_used
    {
        1
    } else {
        thread_count
    };
    let program = compiler.finish();
    let mut machine = Machine::new(&program, store);
    // TLCGet("level") is 0 while TLC starts.
    let startup = machine.store.int(0).and_then(|zero| {
        machine.set_slot(LEVEL_SLOT, zero);
        run_startup(
            &mut machine,
            &context.startup,
            settings.is_violation_reported,
        )
    });
    let group = match startup {
        Err(Bail(reason)) => return SearchOutcome::Declined(reason.into()),
        Ok(Started {
            failed: Some((_, Bail(reason))),
            ..
        }) if !settings.is_violation_reported => return SearchOutcome::Declined(reason.into()),
        Ok(started) => {
            let report = |reporter: &mut dyn Reporter, printed: &[Vec<Id>]| {
                printed
                    .iter()
                    .for_each(|values| reporter.startup_print(&machine.store, values));
            };
            report(reporter, &started.printed);
            if let Some(message) = started.config_error {
                return SearchOutcome::ConfigError { message };
            }
            if !started.small_sets.is_empty() {
                reporter.symmetry_sets_too_small(&started.small_sets);
            }
            reporter.startup_done();
            report(reporter, &started.assumed);
            let mut assumed = Assumed {
                violated: started.violated,
                failed: started.failed,
                delegated: started.delegated,
            };
            // The caller checks each assumption the engine leaves to it, and the engine goes on
            // from the generator's state it leaves.
            while let Some((position, bail)) = assumed.delegated {
                let delegated = match reporter.check_assumption(position) {
                    Ok(delegated) => delegated,
                    Err(reason) if bail.0 == DELEGATED_ASSUMPTION => {
                        return SearchOutcome::Declined(reason);
                    }
                    // Where the caller can't check one the engine stopped at a limit of, TLC may
                    // fail there, which the caller reports as it does any that fails.
                    Err(_) => {
                        assumed = Assumed {
                            violated: None,
                            failed: Some((position, bail)),
                            delegated: None,
                        };
                        break;
                    }
                };
                if !delegated.holds {
                    let name = context.startup.assumptions[position as usize].1.clone();
                    return SearchOutcome::AssumptionViolated { name };
                }
                machine.random = JavaRandom::from_state(delegated.random);
                assumed = match check_assumptions(
                    &mut machine,
                    &context.startup,
                    position as usize + 1,
                    settings.is_violation_reported,
                ) {
                    Ok(assumed) => assumed,
                    Err(Bail(reason)) => return SearchOutcome::Declined(reason.into()),
                };
                let printed = std::mem::take(&mut machine.output)
                    .into_iter()
                    .filter_map(|printed| match printed {
                        Printed::Values(values) => Some(values),
                        Printed::InitialStates(_) => None,
                    })
                    .collect::<Vec<_>>();
                printed
                    .iter()
                    .for_each(|values| reporter.startup_print(&machine.store, values));
            }
            if let Some(name) = assumed.violated {
                return SearchOutcome::AssumptionViolated { name };
            }
            if let Some((position, _)) = assumed.failed {
                return SearchOutcome::AssumptionFailed { position };
            }
            if context.is_diameter_searched || context.is_view_search_read {
                return SearchOutcome::Stopped {
                    reason: if context.is_diameter_searched {
                        crate::context::DIAMETER_SEARCHED
                    } else {
                        crate::context::VIEW_SEARCH_READ
                    }
                    .into(),
                    checkpoint: None,
                    collisions: 0,
                    violation: None,
                };
            }
            started.group
        }
    };
    // The initial states draw on from where the startup left the generator.
    let startup_random = machine.random.state();
    machine.startup_random = startup_random;
    // The group by the names of the model values each permutation moves, for the interpreter and
    // the trace, which read the search's states by another store.
    let named_group = group
        .as_ref()
        .map(|group| name_group(&machine.store, group));
    let is_symmetric = group.is_some();
    let canonicalizer = group.map(|group| {
        let order = ir.tlc_order.iter().map(|&index| index as usize).collect();
        Canonicalizer::new(&machine.store, group, order)
    });
    let width = context.width;
    let order: Vec<usize> = if context.view.is_some() {
        vec![0]
    } else {
        ir.tlc_order.iter().map(|&index| index as usize).collect()
    };
    let states = States {
        width,
        key_width: if context.view.is_some() {
            Some(1)
        } else {
            is_symmetric.then_some(width)
        },
        ids: Vec::new(),
        keys: Vec::new(),
        parents: Vec::new(),
        fingerprints: Vec::new(),
        set: FingerprintSet::new(settings.is_fingerprint_verified || model.is_recording_graph),
        order,
        is_verified: settings.is_fingerprint_verified,
        collisions: 0,
    };
    let mut search = Search::new(states, reporter, is_distinct_read, is_pipelined);
    search.possible = vec![-1; context.possible.len()];
    search.canonicalizer = canonicalizer;
    search.is_lambda_built = is_lambda_built;
    search.held = (model.is_recording_graph && is_printing).then(Vec::new);
    search.graph = model.is_recording_graph.then(|| Graph {
        edge_offsets: vec![0],
        labels: context
            .actions
            .as_ref()
            .filter(|_| model.is_labelled)
            .map(|_| Vec::new()),
        reals: search.states.key_width.map(|_| Vec::new()),
        ..Graph::default()
    });
    // Where an atom sets or reads TLC's registers, the checker adds each state as the search
    // expands it and asks the atoms then, as TLC evaluates them.
    let mut online = None;
    // Why the checker declined as the search went, if it did.
    let mut online_declined: Option<String> = None;
    if settings.is_violation_reported && search.graph.is_some() && context.is_live_registered {
        let properties: Vec<Vec<Term>> = model
            .live_properties
            .iter()
            .map(|property| to_terms(&property.formula))
            .collect();
        let property_terms: Vec<&[Term]> = properties.iter().map(Vec::as_slice).collect();
        let checker = tla_live::Online::new(&to_terms(&model.live_formula), &property_terms);
        let declined = match &checker {
            Err(declined) => Some(declined.0.as_str()),
            Ok(_) if search.states.key_width.is_some() || is_symmetric => {
                Some("TLC's registers in the atoms under SYMMETRY or a VIEW")
            }
            Ok(_) if context.diameter_atoms.contains(&true) => {
                Some("TLC's registers and TLCGet(\"diameter\") in the atoms")
            }
            Ok(_) => None,
        };
        if let Some(reason) = declined {
            return SearchOutcome::Declined(reason.into());
        }
        // What the search and the atoms print comes out in TLC's order as it is.
        search.held = None;
        online = checker.ok();
    }
    // The actions take each state's steps when the search labels them for ENABLED.
    let actions = context
        .actions
        .as_ref()
        .filter(|_| model.is_recording_graph && model.is_labelled);
    let is_live_checked = settings.is_live_checked && actions.is_some();
    let mut out_degrees = [0u64; OUT_DEGREE_BUCKETS];
    let mut checkpoint_count = 0usize;
    let mut checkpoint_generated = 0u64;
    let mut checkpoint_possible = search.possible.clone();
    let mut initial_states = (0, 0);
    let mut is_past_initial = false;
    let mut workers: Vec<Worker<'_>> = Vec::new();
    // The answers to the liveness checker's atoms about the first `count` states and the steps of
    // the first `expanded`.
    let graph_tables = |machine: &mut Machine<'_>,
                        search: &Search<'_, States>,
                        expanded: usize,
                        count: usize,
                        reals: Option<&Reals>,
                        last_diameter: Option<u32>|
     -> Result<Vec<Table>, &'static str> {
        let graph = search.graph.as_ref().expect("a graph");
        let edge_count = graph.edge_offsets[expanded] as usize;
        // Read as the tables are answered, since taking the steps from the states the search
        // didn't store may take a shortcut past a walk too.
        let is_enabled_exact = !machine.is_past_walk;
        // Where no walk took the shortcut, no comparison of an assigned value can fail, and no
        // string was ranked since (which may take a string out of its class), TLC's predicate
        // evaluation of the next-state relation holds of every step the walks took.
        let is_next_taken = is_enabled_exact
            && !machine.store.has_unordered_strings()
            && machine
                .assigned_shapes
                .as_ref()
                .is_some_and(|joins| joins.iter().all(ShapeJoin::is_comparable));
        let live = match reals {
            Some(reals) => LiveGraph {
                states: &reals.states,
                width,
                count: reals.states.len() / width,
                expanded: reals.expanded(),
                edge_offsets: &reals.offsets,
                edges: &reals.edges,
                labels: reals.labels.as_deref(),
                is_enabled_exact,
                is_next_taken,
            },
            None => LiveGraph {
                states: &search.states.ids[..count * width],
                width,
                count,
                expanded,
                edge_offsets: &graph.edge_offsets[..=expanded],
                edges: &graph.edges[..edge_count],
                labels: graph.labels.as_ref().map(|labels| &labels[..edge_count]),
                is_enabled_exact,
                is_next_taken,
            },
        };
        answer_atoms(
            machine,
            &live,
            &context.atoms,
            settings.is_live_checked,
            context.is_live_printing,
            &Diameters {
                atoms: &context.diameter_atoms,
                last: last_diameter,
            },
            &mut (0..atom_threads)
                .filter(|_| atom_threads > 1)
                .map(|_| Machine::new(&program, Store::new()))
                .collect::<Vec<_>>(),
        )
    };
    // The most threads a level was shared between.
    let mut threads_used = 1;
    // TLC checks the temporal properties part way through the search as well (ModelChecker's
    // doPeriodicWork), which the engine does where the checker takes the graph so far as TLC does:
    // without the states the search reached but didn't store, prints or TLC's diameter.
    let is_periodic = settings.is_liveness_periodic
        && model.is_recording_graph
        && online.is_none()
        && search.states.key_width.is_none()
        && search.held.is_none()
        && !context.is_live_printing
        && !settings.is_live_checked
        && !context.diameter_atoms.contains(&true);
    // The graph's size at the last check, from 1 as TLC's, and the time the checks took.
    let mut periodic_size = 1usize;
    let mut periodic_time = Duration::ZERO;
    let mut test_live_check_at = settings.test_live_check_at.filter(|_| is_periodic);
    // Where the engine doesn't check as the graph grows, or a check couldn't decide, it hands a
    // large graph to the interpreter, which checks as it grows and, even under `-lncheck final`,
    // stops at a state whose tableau node accepts every behavior.
    let is_graph_bounded = Cell::new(model.is_recording_graph && !is_periodic);
    // What the check that found a counterexample answered and found, and the states it took.
    let mut periodic_lasso: Option<(Vec<Table>, Liveness, usize)> = None;
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
        // An action atom answered from the steps needs the shapes of what the walks assign.
        if context
            .atoms
            .iter()
            .any(|atom| matches!(atom, Atom::Action { is_next: true, .. }))
        {
            machine.assigned_shapes = Some((0..width).map(|_| ShapeJoin::default()).collect());
        }
        (context.init)(&mut machine, &mut |machine: &mut Machine<'_>| {
            search.visit_initial(machine, &context)
        })?;
        search.flush(&mut machine);
        initial_states = (search.initial_generated, search.states.count() as u64);
        // TLC stops before it expands a state, at a time of its threads' choosing.
        if machine.registers.is_exit {
            return Err(Bail(
                "unsupported: TLCSet(\"exit\", TRUE) as TLC starts or computes the initial states",
            ));
        }
        // TLC adds each initial state to the behavior graphs as it finds it, and stops where an
        // atom fails to evaluate. It then replays the initial states, checking each again and
        // adding those after the one it failed at, which the engine follows where there is but
        // the one.
        if settings.is_violation_reported
            && search.graph.is_some()
            && online.is_none()
            && search.states.key_width.is_none()
            && search.held.is_none()
            && !context.is_live_printing
            && !context.diameter_atoms.contains(&true)
        {
            let count = search.states.count();
            let tables = graph_tables(&mut machine, &search, 0, count, None, None).map_err(Bail)?;
            if let Some(unanswered) = unanswered_at(model, &search, &tables, 0, count) {
                search.violation = (initial_states == (1, 1)).then(|| Found {
                    kind: ViolationKind::Error {
                        site: ErrorSite::InitialAtom(unanswered.atom),
                    },
                    parent: None,
                    last: Some(search.states.state(unanswered.state).to_vec()),
                    fingerprint: None,
                    random: None,
                    counts: StopCounts {
                        generated: 1,
                        distinct: 1,
                        queued: 1,
                        depth: 1,
                        ..StopCounts::default()
                    },
                });
                return Err(Bail(ATOM_FAILED));
            }
        }
        if search.held.is_none() {
            search
                .reporter
                .initial_states(initial_states.0, initial_states.1);
        }
        is_past_initial = true;
        if let Some(online) = &mut online {
            // TLC evaluates an atom of an initial state as it finds the state, among the initial
            // predicate's own evaluations, which the search doesn't follow.
            if online.asks_initial_states() && search.states.count() > 0 {
                return Err(Bail(ONLINE_INITIAL));
            }
            for state in 0..search.states.count() as u32 {
                add_online(
                    &mut machine,
                    &context,
                    &search,
                    online,
                    (state, true),
                    &mut online_declined,
                )?;
            }
        }
        if context.next.is_none() && search.states.count() > 0 {
            search.violation = Some(Found {
                kind: ViolationKind::NoNextState,
                parent: None,
                last: None,
                fingerprint: None,
                random: None,
                counts: StopCounts::default(),
            });
            return Err(Bail(NO_NEXT_STATE));
        }

        // --- next states ---
        // The initial states are the first level, which starts as the loop does, so that it too
        // can be shared between threads.
        let mut level_end = 0;
        search.level = 0;
        // The previous level's first state, when it started and on how many threads, for its time
        // per state on one thread.
        let mut level_start = (0, Instant::now(), 1);
        let started_at = Instant::now();
        let mut progress_at = started_at + FIRST_PROGRESS;
        // TLC's check of the temporal properties on the graph of the states expanded so far, where
        // it grew enough and the checks took little enough of the time: it skips the nodes of the
        // states not yet expanded, and the search stops where it finds a counterexample.
        let mut check_periodically =
            |machine: &mut Machine<'_>, search: &mut Search<'_, States>| -> Outcome<()> {
                let expanded = search
                    .graph
                    .as_ref()
                    .map_or(0, |graph| graph.edge_offsets.len() - 1);
                let count = search.states.count();
                let at = Instant::now();
                let growth = expanded.saturating_sub(periodic_size) as f64 / periodic_size as f64;
                let budget = (at - started_at).as_secs_f64() * LIVENESS_RATIO;
                if expanded == count
                    || growth <= LIVENESS_GROWTH
                    || periodic_time.as_secs_f64() > budget
                {
                    return Ok(());
                }
                periodic_size = expanded;
                let tables =
                    graph_tables(machine, search, expanded, count, None, None).map_err(Bail)?;
                let liveness = check_liveness(
                    model,
                    search,
                    &tables,
                    None,
                    false,
                    &context.diameter_atoms,
                    thread_count,
                );
                periodic_time += at.elapsed();
                // Whatever the checker leaves undecided, the check of the complete graph decides,
                // and the graph is bounded again for the interpreter, which checks as it grows.
                let (Some(branches), Verdict::Holds | Verdict::Lasso { .. }) =
                    (liveness.branches, &liveness.verdict)
                else {
                    is_graph_bounded.set(true);
                    return Ok(());
                };
                search.reporter.liveness_started(
                    branches as u64,
                    expanded as u64,
                    [search.generated, count as u64, search.depth.max(1)],
                );
                if liveness.verdict == Verdict::Holds {
                    search.reporter.liveness_finished();
                    return Ok(());
                }
                periodic_lasso = Some((tables, liveness, expanded));
                Err(Bail(PERIODIC_LASSO))
            };
        search.expanding = 0;
        while search.expanding < search.states.count() {
            let expanding = search.expanding;
            if expanding == level_end {
                search.level += 1;
                level_end = search.states.count();
                let states = level_end - expanding;
                let (previous_start, previous_at, previous_threads) = level_start;
                let per_state = (expanding > previous_start).then(|| {
                    previous_at.elapsed() * previous_threads / (expanding - previous_start) as u32
                });
                let work = per_state.map_or(Duration::ZERO, |per_state| per_state * states as u32);
                // A thread takes at least half the fewest states a level shares, or at least
                // THREAD_WORK of its predicted work, whichever gives more threads, and at least
                // one state.
                let by_count = if states >= settings.minimum_shared_level {
                    states / settings.minimum_shared_level.div_ceil(2).max(1)
                } else {
                    1
                };
                let by_work = if work >= SHARED_WORK {
                    (work.as_nanos() / THREAD_WORK.as_nanos()) as usize
                } else {
                    1
                };
                // A thread claims whole states, so no more threads than states.
                let threads = thread_count.min(by_count.max(by_work)).min(states);
                level_start = (
                    expanding,
                    Instant::now(),
                    if is_shared { threads.max(1) as u32 } else { 1 },
                );
                if is_shared && threads > 1 {
                    debug_assert!(online.is_none() && search.held.is_none());
                    threads_used = threads_used.max(threads);
                    if workers.is_empty() {
                        // The memo tables of the search's machine and its workers' share one
                        // machine's room, so that memory doesn't grow with the threads.
                        machine.share_memo(thread_count);
                        workers = (0..thread_count)
                            .map(|_| Worker {
                                machine: {
                                    let mut worker = Machine::new(&program, Store::new());
                                    worker.share_memo(thread_count);
                                    worker.assigned_shapes =
                                        machine.assigned_shapes.as_ref().map(|joins| {
                                            joins.iter().map(|_| ShapeJoin::default()).collect()
                                        });
                                    worker
                                },
                                fingerprints: Fingerprints::default(),
                                canonicalizer: search
                                    .canonicalizer
                                    .as_ref()
                                    .map(Canonicalizer::fresh),
                                bound: machine.store.value_count() as Id,
                                imported: Vec::new(),
                            })
                            .collect();
                    }
                    let level = Level {
                        start: expanding,
                        end: level_end,
                        chunk: ((level_end - expanding) / (4 * threads)).clamp(1, CHUNK),
                        number: search.level,
                        cursor: Padded(AtomicUsize::new(expanding)),
                        stop: Padded(AtomicUsize::new(
                            settings
                                .stop_at
                                .filter(|&at| at >= expanding)
                                .map_or(level_end, |at| at.min(level_end)),
                        )),
                        is_pipelined,
                        check_deadlock: model.check_deadlock,
                        is_graph_bounded: is_graph_bounded.get(),
                        stop_at: settings.stop_at,
                    };
                    let expanded = search.expand_level(
                        &mut machine,
                        &mut workers[..threads],
                        &context,
                        &level,
                        actions.map(Vec::as_slice),
                        &mut out_degrees,
                    );
                    checkpoint_count = search.states.count();
                    checkpoint_generated = search.generated;
                    expanded?;
                    if test_live_check_at.is_some_and(|at| search.expanding >= at) {
                        test_live_check_at = None;
                        check_periodically(&mut machine, &mut search)?;
                    }
                    if Instant::now() >= progress_at {
                        progress_at = Instant::now() + PROGRESS_INTERVAL;
                        if is_periodic {
                            check_periodically(&mut machine, &mut search)?;
                        }
                        let count = search.states.count() as u64;
                        search.reporter.progress(
                            search.generated,
                            count,
                            count - search.expanding as u64,
                            search.depth.max(1),
                        );
                    }
                    continue;
                }
            }
            checkpoint_count = search.states.count();
            checkpoint_generated = search.generated;
            checkpoint_possible.clone_from(&search.possible);
            if Some(expanding) == settings.stop_at {
                return Err(Bail("stopped where PROVE_IT_STOP_AT asked"));
            }
            if is_graph_bounded.get() && search.states.count() > MAXIMUM_GRAPH_STATES {
                return Err(Bail(GRAPH_TOO_LARGE));
            }
            // The search numbers its states and its graph's steps in 32 bits.
            if search.states.count() >= i32::MAX as usize
                || search
                    .graph
                    .as_ref()
                    .is_some_and(|graph| graph.edges.len() >= i32::MAX as usize)
            {
                return Err(Bail(GRAPH_TOO_LARGE));
            }
            search.current.clear();
            search
                .current
                .extend_from_slice(&search.states.ids[expanding * width..(expanding + 1) * width]);
            let fingerprint = search.states.fingerprints[expanding];
            let expanded = search.expand(
                &mut machine,
                &context,
                fingerprint,
                actions.map(Vec::as_slice),
                is_live_checked,
                model.check_deadlock,
            );
            if let Err(bail) = expanded {
                if let Some(Found {
                    kind:
                        ViolationKind::Error {
                            site: ErrorSite::Invariant(_),
                        },
                    counts,
                    ..
                }) = &mut search.violation
                {
                    for (count, completed) in counts.out_degrees.iter_mut().zip(out_degrees) {
                        *count += completed;
                    }
                }
                return Err(bail);
            }
            if let Some(graph) = &mut search.graph {
                graph.successor_counts.push(search.successors as u32);
                graph.new_counts.push(search.new_states as u32);
                graph.edge_offsets.push(graph.edges.len() as u32);
                graph.diameters.push(search.depth.max(1) as u32);
            }
            out_degrees[(search.new_states as usize).min(OUT_DEGREE_BUCKETS - 1)] += 1;
            search.flush(&mut machine);
            search.check_exit_followed(&machine)?;
            if let Some(online) = &mut online {
                add_online(
                    &mut machine,
                    &context,
                    &search,
                    online,
                    (expanding as u32, false),
                    &mut online_declined,
                )?;
                search.flush(&mut machine);
            }
            if test_live_check_at.is_some_and(|at| expanding + 1 >= at) {
                test_live_check_at = None;
                check_periodically(&mut machine, &mut search)?;
            }
            if expanding & 0xff == 0 && Instant::now() >= progress_at {
                progress_at = Instant::now() + PROGRESS_INTERVAL;
                if is_periodic {
                    check_periodically(&mut machine, &mut search)?;
                }
                let count = search.states.count() as u64;
                search.reporter.progress(
                    search.generated,
                    count,
                    count - expanding as u64 - 1,
                    search.depth.max(1),
                );
            }
            search.expanding += 1;
            // TLC's worker finishes the state, then finds the queue finished (`stop`).
            if search.is_exit_followed {
                if search.graph.is_some() || online.is_some() {
                    return Err(Bail(
                        "unsupported: TLCSet(\"exit\", TRUE) with temporal properties",
                    ));
                }
                break;
            }
        }
        Ok(())
    })();
    let variables: Vec<&str> = ir
        .variables
        .iter()
        .map(|&text| &*ir.texts[text as usize])
        .collect();
    let collisions = search.states.collisions;
    // The first `count` states and the steps of the first `expanded`, for the interpreter to
    // replay from the initial states on, with the answers to the liveness checker's atoms.
    let graph_checkpoint = |machine: &mut Machine<'_>,
                            search: &Search<'_, States>,
                            expanded: usize,
                            count: usize,
                            expanding: usize,
                            tables: Vec<Table>,
                            possible: Vec<i64>|
     -> Checkpoint {
        let graph = search.graph.as_ref().expect("a graph");
        let states = &search.states;
        let edge_count = graph.edge_offsets[expanded] as usize;
        Checkpoint {
            expanding: expanding as u64,
            count: count as u64,
            generated: search.initial_generated,
            initial_generated: search.initial_generated,
            out_degrees: [0; OUT_DEGREE_BUCKETS],
            states: states.share(&machine.store, &states.ids, width, count),
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
                is_enabled_exact: !machine.is_past_walk,
                tables,
            }),
            possible,
            startup: share_startup(machine, &context).ok(),
            startup_random,
            symmetry: named_group.clone(),
        }
    };
    let outcome = match result {
        Err(bail) if bail.0 == OTHER_STEPS => SearchOutcome::Invariant(OTHER_STEPS.into()),
        // The interpreter prints the counterexample with the counts so far, as TLC does.
        Err(bail) if bail.0 == PERIODIC_LASSO => {
            let (tables, liveness, expanded) = periodic_lasso
                .take()
                .expect("the counterexample a check found");
            let count = search.states.count();
            if let Some(path) = &settings.state_log {
                write_state_log(
                    path,
                    &variables,
                    &search.states,
                    &machine.store,
                    &Logged {
                        count,
                        stopped: Some(PERIODIC_LASSO),
                        expanding: expanded,
                        graph: search.graph.as_ref(),
                    },
                );
            }
            let lasso_actions = match &liveness.verdict {
                Verdict::Lasso {
                    path, loop_start, ..
                } => label_lasso(&mut machine, &context, &mut search, path, *loop_start)
                    .unwrap_or_default(),
                _ => Vec::new(),
            };
            let checkpoint = graph_checkpoint(
                &mut machine,
                &search,
                expanded,
                count,
                0,
                tables,
                search.possible.clone(),
            );
            let counts = Counts {
                generated: search.generated,
                distinct: count as u64,
                queued: (count - expanded) as u64,
                depth: search.depth.max(1),
                initial_generated: initial_states.0,
                initial_distinct: initial_states.1,
                out_degrees,
            };
            let violation = match &liveness.verdict {
                Verdict::Lasso {
                    path, loop_start, ..
                } if settings.is_violation_reported => to_lasso(
                    &mut machine,
                    &context,
                    &search,
                    (path, *loop_start),
                    &lasso_actions,
                    Vec::new(),
                    &counts,
                ),
                _ => None,
            };
            SearchOutcome::Complete {
                counts: Box::new(counts),
                checkpoint: Some(Box::new(checkpoint)),
                liveness: Some(liveness),
                lasso_actions,
                violation,
                value_count: machine.store.value_count(),
                threads: threads_used,
                collisions,
                possible: search.possible.clone(),
                registers: None,
                fingerprints: search.states.fingerprints,
            }
        }
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
            // The temporal properties are checked here, and the interpreter takes the graph over
            // only to print a counterexample, to check them itself, or under PROVE_IT_LIVE_CHECK
            // to check them again.
            // TLC rebuilds a counterexample's states before it evaluates the properties on it, each
            // with what it sets, which the engine doesn't follow.
            let online_liveness = match &mut online {
                None => None,
                Some(online) => {
                    let verdict = with_online(&mut machine, &context, &search, |source| {
                        online.finish(source)
                    });
                    if verdict != Ok(Verdict::Holds) {
                        return SearchOutcome::Stopped {
                            reason: "a counterexample where the atoms use TLC's registers".into(),
                            checkpoint: None,
                            collisions,
                            violation: None,
                        };
                    }
                    Some(Liveness {
                        branches: Some(online.branches()),
                        verdict: Verdict::Holds,
                        events: Vec::new(),
                        unanswered: None,
                    })
                }
            };
            let (checkpoint, liveness, lasso_actions, lasso_printed) = match search.graph {
                Some(_) if online_liveness.is_some() => {
                    (None, online_liveness, Vec::new(), Vec::new())
                }
                Some(_) => {
                    // Under SYMMETRY or a VIEW, the checker may ask about the steps from states the
                    // search reached but didn't store, which the engine takes and checks again.
                    let mut reals = real_states(&search, width);
                    // The checker logs the states it adds and the atoms it evaluates where the
                    // atoms print or the search printed, whose prints it then places.
                    let is_effectful = context.is_live_printing
                        || search
                            .held
                            .as_ref()
                            .is_some_and(|held| held.iter().any(|printed| !printed.is_empty()));
                    // Whatever the steps from the states the search didn't store printed, TLC prints
                    // where the engine doesn't follow.
                    let mut is_late_printed = false;
                    let (tables, liveness) = loop {
                        let tables = match graph_tables(
                            &mut machine,
                            &search,
                            count,
                            count,
                            reals.as_ref(),
                            Some(search.depth.max(1) as u32),
                        ) {
                            Ok(tables) => tables,
                            Err(reason) => return SearchOutcome::Invariant(reason.into()),
                        };
                        let mut liveness = check_liveness(
                            model,
                            &search,
                            &tables,
                            reals.as_ref(),
                            is_effectful,
                            &context.diameter_atoms,
                            thread_count,
                        );
                        if liveness.verdict != Verdict::Unexpanded {
                            break (tables, liveness);
                        }
                        let expanded = match &mut reals {
                            Some(reals) => expand_reals(&mut machine, &context, &mut search, reals),
                            None => Ok(false),
                        };
                        is_late_printed |= !machine.output.is_empty();
                        machine.output.clear();
                        match expanded {
                            Ok(true) => {}
                            Ok(false) => {
                                liveness.verdict = Verdict::Declined(tla_live::UNEXPANDED.into());
                                break (tables, liveness);
                            }
                            Err(Bail(reason)) => {
                                liveness.verdict = Verdict::Declined(reason.into());
                                break (tables, liveness);
                            }
                        }
                    };
                    // An atom TLC evaluates as it adds a state, which the engine didn't answer:
                    // where TLC fails evaluating it, it stops there.
                    if let Some(unanswered) = liveness.unanswered.filter(|_| {
                        settings.is_violation_reported
                            && reals.is_none()
                            && !is_late_printed
                            && !context.diameter_atoms.contains(&true)
                            && search
                                .held
                                .as_ref()
                                .is_none_or(|held| held.iter().all(|printed| printed.is_empty()))
                            && tables.iter().all(|table| table.prints.is_empty())
                    }) && let Some(found) =
                        to_atom_failure(&context, &search, initial_states, unanswered)
                    {
                        return SearchOutcome::Stopped {
                            reason: ATOM_FAILED.into(),
                            checkpoint: None,
                            collisions,
                            violation: to_violation(
                                found,
                                &mut machine,
                                &context,
                                &mut search,
                                false,
                            ),
                        };
                    }
                    if let Some(held) = search.held.take() {
                        let order = (!is_late_printed && !settings.is_live_checked)
                            .then(|| {
                                order_printed(
                                    &held,
                                    &tables,
                                    &liveness,
                                    context.is_invariant_printing
                                        || is_distinct_read
                                        || model.actions.len() > 1,
                                )
                            })
                            .flatten();
                        let Some(order) = order else {
                            // The interpreter checks the properties from the start, printing all
                            // of it in its order.
                            let why = match &liveness.verdict {
                                Verdict::Declined(declined) => declined.0.as_str(),
                                Verdict::Accepted { .. } => "a node that accepts every behavior",
                                _ if is_late_printed => "steps from states it didn't store",
                                _ if settings.is_live_checked => "PROVE_IT_LIVE_CHECK",
                                _ => "prints it doesn't place in TLC's order",
                            };
                            return SearchOutcome::Stopped {
                                reason: format!(
                                    "printing where the native checker doesn't check the \
                                     temporal properties: {why}"
                                ),
                                checkpoint: None,
                                collisions,
                                violation: None,
                            };
                        };
                        for out in order {
                            match out {
                                Out::Printed(printed) => {
                                    report_printed(search.reporter, &machine.store, printed);
                                }
                                Out::InitialStates => search
                                    .reporter
                                    .initial_states(initial_states.0, initial_states.1),
                            }
                        }
                    }
                    let lasso_printed: Vec<Vec<Id>> = liveness
                        .events
                        .iter()
                        .skip_while(|&&event| event != Event::Lasso)
                        .flat_map(|event| match *event {
                            Event::Atom { atom, slot } => tables[atom as usize].printed(slot),
                            _ => &[],
                        })
                        .filter_map(|printed| match printed {
                            Printed::Values(values) => Some(values.clone()),
                            Printed::InitialStates(_) => None,
                        })
                        .collect();
                    let checkpoint = (liveness.verdict != Verdict::Holds
                        || settings.is_live_checked)
                        .then(|| {
                            Box::new(graph_checkpoint(
                                &mut machine,
                                &search,
                                count,
                                count,
                                0,
                                // The interpreter answers TLCGet("diameter") as the search goes.
                                tables
                                    .into_iter()
                                    .zip(&context.diameter_atoms)
                                    .map(|(table, &is_diameter_read)| {
                                        if !is_diameter_read {
                                            return table;
                                        }
                                        Table {
                                            answers: Vec::new(),
                                            is_from_steps: false,
                                            unknown: Some("TLCGet(\"diameter\")".into()),
                                            prints: Vec::new(),
                                        }
                                    })
                                    .collect(),
                                search.possible.clone(),
                            ))
                        });
                    let lasso_actions = match &liveness.verdict {
                        Verdict::Lasso {
                            path, loop_start, ..
                        } => label_lasso(&mut machine, &context, &mut search, path, *loop_start)
                            .unwrap_or_default(),
                        _ => Vec::new(),
                    };
                    (checkpoint, Some(liveness), lasso_actions, lasso_printed)
                }
                None => (None, None, Vec::new(), Vec::new()),
            };
            let counts = Counts {
                generated: search.generated,
                distinct: count as u64,
                // None but where TLCSet("exit", TRUE) stopped the search.
                queued: (count - search.expanding) as u64,
                depth: if search.generated == 0 {
                    0
                } else {
                    search.depth.max(1)
                },
                initial_generated: initial_states.0,
                initial_distinct: initial_states.1,
                out_degrees,
            };
            let value_count = machine.store.value_count();
            // Under SYMMETRY or a VIEW the lasso's states are the stored ones, from which the
            // caller rebuilds those TLC prints.
            let violation = match liveness.as_ref().map(|liveness| &liveness.verdict) {
                Some(Verdict::Lasso {
                    path, loop_start, ..
                }) if settings.is_violation_reported => to_lasso(
                    &mut machine,
                    &context,
                    &search,
                    (path, *loop_start),
                    &lasso_actions,
                    lasso_printed,
                    &counts,
                ),
                Some(Verdict::Accepted {
                    state,
                    path,
                    violated,
                }) if settings.is_violation_reported
                    && search.states.key_width.is_none()
                    && !is_symmetric =>
                {
                    to_accepted(
                        &mut machine,
                        &context,
                        &mut search,
                        initial_states,
                        *state,
                        path,
                        violated.clone(),
                    )
                }
                _ => None,
            };
            SearchOutcome::Complete {
                counts: Box::new(counts),
                checkpoint,
                liveness,
                lasso_actions,
                violation,
                value_count,
                threads: threads_used,
                collisions,
                possible: search.possible.clone(),
                registers: None,
                fingerprints: search.states.fingerprints,
            }
        }
        Err(bail) if !is_past_initial => {
            if search.violation.is_none() && !is_engine_limit(bail.0) {
                let count = search.states.count() as u64;
                search.violation = Some(Found {
                    kind: ViolationKind::Error {
                        site: ErrorSite::Init,
                    },
                    parent: None,
                    last: None,
                    fingerprint: None,
                    random: None,
                    counts: StopCounts {
                        generated: search.generated,
                        distinct: count,
                        queued: count,
                        // TLC's depth is 1 once it has written a state.
                        depth: u64::from(count > 0),
                        ..StopCounts::default()
                    },
                });
            }
            // TLC adds each initial state to the behavior graphs before it checks it, and fails
            // where an atom fails to evaluate, which the engine leaves to the interpreter.
            let violation = search
                .violation
                .take()
                .filter(|_| settings.is_violation_reported)
                .filter(|found| {
                    // Where TLC evaluates atoms that use the registers as it adds an initial
                    // state, the search follows it only up to the first state it would add.
                    let is_before_states = search.states.count() == 0
                        && (found.last.is_none()
                            || matches!(
                                found.kind,
                                ViolationKind::Error {
                                    site: ErrorSite::InitialConstraint(_)
                                }
                            ));
                    match &online {
                        Some(online) => !online.asks_initial_states() || is_before_states,
                        None => {
                            search.graph.is_none()
                                || matches!(
                                    found.kind,
                                    ViolationKind::Error {
                                        site: ErrorSite::InitialAtom(_)
                                    }
                                )
                                || answers_initial_atoms(&mut machine, &context, &search, found)
                        }
                    }
                });
            // Otherwise the interpreter starts from scratch and prints it all again.
            if violation.is_some() {
                for printed in search.held.take().iter().flatten().flatten() {
                    report_printed(search.reporter, &machine.store, printed);
                }
                search.flush(&mut machine);
            }
            SearchOutcome::Stopped {
                reason: bail.0.to_string(),
                checkpoint: None,
                collisions,
                violation: violation.and_then(|found| {
                    to_violation(found, &mut machine, &context, &mut search, is_printing)
                }),
            }
        }
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
                    states: states.share(store, &states.ids, width, count),
                    parents: states.parents[..count].to_vec(),
                    keys: states.key_width.map(|key_width| {
                        (
                            states.share(store, &states.keys, key_width, count),
                            key_width as u32,
                        )
                    }),
                    graph: None,
                    possible: checkpoint_possible.clone(),
                    startup: share_startup(&mut machine, &context).ok(),
                    startup_random,
                    symmetry: named_group.clone(),
                }))
            } else if !is_kept
                || search.states.key_width.is_some()
                || search.held.is_some()
                || online.is_some()
            {
                // The interpreter searches a graph too large to keep from the start, since its
                // liveness checker may stop in the first states, before it has taken all of them
                // over; under SYMMETRY or a VIEW, since its replay of the graph would give its
                // liveness checker the states stored rather than the states each step reached; and
                // where the search held what it printed, which the interpreter prints in its order.
                None
            } else {
                let expanding = search.expanding;
                match graph_tables(&mut machine, &search, expanding, count, None, None) {
                    Ok(tables) => Some(Box::new(graph_checkpoint(
                        &mut machine,
                        &search,
                        expanding,
                        count,
                        expanding,
                        tables,
                        checkpoint_possible.clone(),
                    ))),
                    Err(reason) => return SearchOutcome::Invariant(reason.into()),
                }
            };
            let is_traced = settings.is_violation_reported;
            let found = search.violation.take().filter(|_| is_traced);
            // TLC adds each state it expands to the behavior graphs, even under -lncheck final, the
            // deadlocked state too after it reports the deadlock, and stops at the first whose
            // tableau node accepts every behavior (`LiveCheck#addNextState`): the search reports
            // its violation where TLC wouldn't, and a deadlock with the path to the node the
            // deadlocked state reaches, as on TLC's Github710d.
            let found = match found {
                // TLC adds a deadlocked state to the behavior graphs once it has reported the
                // deadlock, with what its atoms set, which the engine doesn't follow.
                Some(found) if online.is_some() => {
                    (!matches!(found.kind, ViolationKind::Deadlock { .. })).then_some(found)
                }
                // TLC runs Next again from a state it adds a tableau node of late, printing
                // again what Next prints, which the search doesn't place before its stop.
                Some(_)
                    if search.graph.is_some()
                        && search.held.as_ref().is_some_and(|held| {
                            held.iter().skip(1).any(|printed| !printed.is_empty())
                        }) =>
                {
                    None
                }
                Some(mut found) if search.graph.is_some() => {
                    let mut expanded = search.expanding;
                    let is_deadlock = matches!(found.kind, ViolationKind::Deadlock { .. });
                    if is_deadlock {
                        let graph = search.graph.as_mut().expect("a graph");
                        graph.edge_offsets.push(graph.edges.len() as u32);
                        expanded += 1;
                    }
                    let tables =
                        graph_tables(&mut machine, &search, expanded, count, None, None).ok();
                    // TLC had added the initial states and each state before the one it was
                    // expanding, and stopped at the first whose atom failed to evaluate.
                    let unanswered = tables
                        .as_ref()
                        .filter(|tables| {
                            search.states.key_width.is_none()
                                && !is_symmetric
                                && !context.diameter_atoms.contains(&true)
                                && search.held.as_ref().is_none_or(|held| {
                                    held.iter().all(|printed| printed.is_empty())
                                })
                                && tables.iter().all(|table| table.prints.is_empty())
                        })
                        .and_then(|tables| unanswered_at(model, &search, tables, expanded, count))
                        .filter(|unanswered| {
                            unanswered.is_initial || (unanswered.state as usize) < search.expanding
                        });
                    // The tables leave unanswered what the checker asks of no finished search,
                    // such as ENABLED of a state not yet expanded, as well as what fails: TLC
                    // stopped at the atom only where evaluating it fails as TLC fails.
                    let unanswered = unanswered.and_then(|unanswered| {
                        let failure = atom_failure(&mut machine, &context, &search, unanswered);
                        machine.output.clear();
                        match failure {
                            Some(Ok(_)) => None,
                            Some(Err(bail)) if !is_engine_limit(bail.0) => Some(Some(unanswered)),
                            _ => Some(None),
                        }
                    });
                    let verdict = tables.and_then(|tables| {
                        accepted_at(model, &context, &search, &tables, expanded, count)
                    });
                    match verdict {
                        _ if unanswered.is_some() => unanswered.flatten().and_then(|unanswered| {
                            to_atom_failure(&context, &search, initial_states, unanswered)
                        }),
                        Some(None) => Some(found),
                        // TLC stops at the first state whose tableau node accepts every
                        // behavior, which is the deadlocked one only where that is the last it
                        // added.
                        Some(Some(Verdict::Accepted {
                            state,
                            path,
                            violated,
                        })) if is_deadlock && state as usize == search.expanding => {
                            found.kind = ViolationKind::Deadlock {
                                accepted: Some(Box::new(AcceptedTrace {
                                    states: path
                                        .iter()
                                        .map(|&index| search.states.state(index).to_vec())
                                        .collect(),
                                    violated,
                                })),
                            };
                            Some(found)
                        }
                        _ => None,
                    }
                }
                found => found,
            };
            // What the search printed comes before the violation, as TLC prints as it checks each
            // successor once it has it (`Worker.addElement`): that of the expansion it stopped in
            // too, and what it held back for the liveness checker's atoms to print between, unless
            // an atom printed.
            if found.is_some() && !(search.held.is_some() && context.is_live_printing) {
                if let Some(held) = search.held.take()
                    && let Some((initial, expansions)) = held.split_first()
                {
                    for printed in initial {
                        report_printed(search.reporter, &machine.store, printed);
                    }
                    search
                        .reporter
                        .initial_states(initial_states.0, initial_states.1);
                    for printed in expansions.iter().flatten() {
                        report_printed(search.reporter, &machine.store, printed);
                    }
                }
                search.flush(&mut machine);
            }
            let mut violation = found.and_then(|found| {
                to_violation(found, &mut machine, &context, &mut search, is_printing)
            });
            // Past the states the search keeps, TLC's may have stopped at a tableau node that
            // accepts every behavior, as on its Github710b, whose x grows without bound. The
            // path is of the states the search keeps, which are those TLC prints where nothing
            // printed and no SYMMETRY or VIEW reduced them.
            if is_traced
                && bail.0 == GRAPH_TOO_LARGE
                && online.is_none()
                && !is_printing
                && search.states.key_width.is_none()
                && !is_symmetric
            {
                let expanded = search.expanding;
                let accepted = graph_tables(&mut machine, &search, expanded, count, None, None)
                    .ok()
                    .and_then(|tables| {
                        accepted_at(model, &context, &search, &tables, expanded, count)
                    })
                    .flatten();
                if let Some(Verdict::Accepted {
                    state,
                    path,
                    violated,
                }) = accepted
                {
                    violation = to_accepted(
                        &mut machine,
                        &context,
                        &mut search,
                        initial_states,
                        state,
                        &path,
                        violated,
                    );
                }
            }
            SearchOutcome::Stopped {
                reason: online_declined
                    .take()
                    .map_or_else(|| bail.0.to_string(), |why| format!("{}: {why}", bail.0)),
                checkpoint,
                collisions,
                violation,
            }
        }
    };
    // The strings the search ranked, such as ToString's, the temporal atoms' included, may rank
    // otherwise in TLC, so the interpreter makes them again from the start rather than taking
    // over the search.
    let is_unordered = machine.store.has_unordered_strings();
    match outcome {
        // TLC orders a violation's sets of strings by its own ranking, which the search's may not
        // be, so the interpreter reports it.
        SearchOutcome::Stopped {
            reason, collisions, ..
        } if is_unordered => SearchOutcome::Stopped {
            reason,
            checkpoint: None,
            collisions,
            violation: None,
        },
        SearchOutcome::Complete {
            checkpoint: Some(_),
            collisions,
            ..
        } if is_unordered => SearchOutcome::Stopped {
            reason: "a graph with strings the search ranked".into(),
            checkpoint: None,
            collisions,
            violation: None,
        },
        SearchOutcome::Complete {
            counts,
            checkpoint,
            liveness,
            lasso_actions,
            violation,
            fingerprints,
            value_count,
            threads,
            collisions,
            possible,
            registers: _,
        } => SearchOutcome::Complete {
            counts,
            checkpoint,
            liveness,
            lasso_actions,
            violation,
            fingerprints,
            value_count,
            threads,
            collisions,
            possible,
            registers: take_registers(&mut machine),
        },
        outcome => outcome,
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
    let Some(mut writer) = crate::log_file::create(path) else {
        return;
    };
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

// The action of each step of a path of the search's states, then of the step from its last state
// to `last` when given, as TLC's `Tool#getState` finds it: for the step from one state to the
// next, the first of TLC's actions with a step from the one to the other, or `None` for the first
// state or where none does. Empty when the engine has no walk of TLC's actions.
fn label_path(
    machine: &mut Machine<'_>,
    context: &EngineContext,
    search: &mut Search<'_, States>,
    path: &[u32],
    last: Option<&[Id]>,
    is_rebuilt: bool,
) -> Outcome<Vec<Option<u32>>> {
    let Some(actions) = &context.actions else {
        return Ok(Vec::new());
    };
    let unassigned = vec![UNASSIGNED; context.width];
    let states = &search.states;
    let depths = get_depths(&states.parents);
    let depths: Vec<i64> = path.iter().map(|&state| depths[state as usize]).collect();
    let fingerprints: Vec<u64> = path
        .iter()
        .map(|&state| states.fingerprints[state as usize])
        .collect();
    let mut targets: Vec<Vec<Id>> = path
        .iter()
        .skip(1)
        .map(|&state| states.state(state).to_vec())
        .collect();
    targets.extend(last.map(<[Id]>::to_vec));
    // Under SYMMETRY or a VIEW, TLC rebuilds the trace as `Tool#getState` does: each state is the
    // first successor of the one before with the fingerprint of the next state of the path.
    let mut from = states.state(path[0]).to_vec();
    let mut labels = vec![None];
    for (position, target) in targets.iter().enumerate() {
        let level = machine.store.int(depths[position])?;
        let next_level = machine.store.int(depths[position] + 1)?;
        let mut found = None;
        for (index, action) in actions.iter().enumerate() {
            let epoch = machine.next_epoch();
            machine.set_current(&from, epoch);
            machine.set_slot(LEVEL_SLOT, level);
            machine.set_slot(NEXT_LEVEL_SLOT, next_level);
            machine.set_next(&unassigned);
            machine.reset_assigned();
            let mut successors = Vec::new();
            action(machine, &mut |machine: &mut Machine<'_>| {
                if is_rebuilt {
                    successors.push(machine.next().to_vec());
                } else if successors.is_empty() && machine.next() == &target[..] {
                    successors.push(target.clone());
                }
                Ok(())
            })?;
            for successor in successors {
                let is_found = !is_rebuilt || {
                    let epoch = machine.next_epoch();
                    machine.set_current(&successor, epoch);
                    search.compute_key(machine, context, false)? == fingerprints[position + 1]
                };
                if is_found {
                    found = Some((index as u32, successor));
                    break;
                }
            }
            if found.is_some() {
                break;
            }
        }
        labels.push(found.as_ref().map(|found| found.0));
        from = found.map_or_else(|| target.clone(), |found| found.1);
    }
    Ok(labels)
}

// The violation a search found, with the store its states are in, or nothing where the search
// ranked strings.
fn to_violation(
    found: Found,
    machine: &mut Machine<'_>,
    context: &EngineContext,
    search: &mut Search<'_, States>,
    is_printing: bool,
) -> Option<Box<Violation>> {
    let path = found
        .parent
        .map_or_else(Vec::new, |parent| search.states.path_to(parent));
    let mut states: Vec<Vec<Id>> = path
        .iter()
        .map(|&index| search.states.state(index).to_vec())
        .collect();
    states.extend(found.last.iter().cloned());
    // The search finds the steps' actions where it keeps the states TLC prints and nothing it
    // evaluates for them prints. Elsewhere, or where it can't, the caller's rebuild of the trace
    // finds them, as TLC does.
    let is_reduced = search.states.key_width.is_some() || search.canonicalizer.is_some();
    let unlabelled = vec![None; states.len().saturating_sub(1)];
    let labels = if path.is_empty() || is_reduced || is_printing {
        unlabelled
    } else {
        label_path(
            machine,
            context,
            search,
            &path,
            found.last.as_deref(),
            false,
        )
        .ok()
        .filter(|labels| !labels.is_empty())
        .map_or(unlabelled, |labels| labels.into_iter().skip(1).collect())
    };
    let startup = startup_values(machine, context).ok()?;
    let symmetry = search
        .canonicalizer
        .as_ref()
        .map(|canonicalizer| name_group(&machine.store, canonicalizer.group()));
    // The store goes with the violation, so whether the search, or finding the actions, ranked
    // strings is read here, as for the search's outcome.
    let is_shaped = labels.len() + 1 == states.len()
        || matches!(
            found.kind,
            ViolationKind::NoNextState
                | ViolationKind::Error {
                    site: ErrorSite::Init
                }
        ) && states.is_empty();
    let fingerprints = match found.kind {
        ViolationKind::Error {
            site: ErrorSite::Invariant(_),
        } => {
            let mut fingerprints = search.states.fingerprints.clone();
            fingerprints.extend(found.fingerprint);
            fingerprints.sort_unstable();
            fingerprints
        }
        _ => Vec::new(),
    };
    (is_shaped && !machine.store.has_unordered_strings()).then(|| {
        Box::new(Violation {
            kind: found.kind,
            states,
            labels,
            counts: found.counts,
            store: std::mem::replace(&mut machine.store, Store::new()),
            startup,
            startup_random: machine.startup_random,
            random: found.random,
            symmetry,
            registers: std::mem::take(&mut machine.registers),
            possible: search.possible.clone(),
            fingerprints,
        })
    })
}

// Where TLC's search, adding the states the search expanded to the behavior graphs, stops at a
// tableau node that accepts every behavior: `Verdict::Accepted`, none, or `None` where the engine
// can't tell.
fn accepted_at(
    model: &Model,
    context: &EngineContext,
    search: &Search<'_, States>,
    tables: &[Table],
    expanded: usize,
    count: usize,
) -> Option<Option<Verdict>> {
    // TLC evaluates the atoms as it adds each state, and fails where the engine couldn't answer
    // one: a state predicate on any state, an ENABLED on an expanded one, as on TLC's
    // InitialLivenessEvaluationError, whose ENABLED reads an x' it never assigns. An action the
    // checker asks of no step it leaves unanswered.
    let is_answered = context.atoms.iter().zip(tables).all(|(atom, table)| {
        table.unknown.is_none()
            && match atom {
                Atom::State(_) => !table.answers[..count].contains(&UNKNOWN),
                Atom::Enabled { .. } => !table.answers[..expanded].contains(&UNKNOWN),
                Atom::Action { .. } | Atom::Unknown(_) => true,
            }
    });
    if !is_answered || context.is_live_printing || context.diameter_atoms.contains(&true) {
        return None;
    }
    let graph = search.graph.as_ref().expect("a graph");
    let answers: Vec<Option<&[u8]>> = tables
        .iter()
        .map(|table| table.unknown.is_none().then_some(&table.answers[..]))
        .collect();
    let properties: Vec<Vec<Term>> = model
        .live_properties
        .iter()
        .map(|property| to_terms(&property.formula))
        .collect();
    let property_terms: Vec<&[Term]> = properties.iter().map(Vec::as_slice).collect();
    tla_live::find_accepted(
        &to_terms(&model.live_formula),
        &property_terms,
        &tla_live::Graph {
            parents: &search.states.parents[..count],
            edge_offsets: &graph.edge_offsets[..=expanded],
            edges: &graph.edges,
            fingerprints: &search.states.fingerprints[..count],
            reals: None,
            diameters: None,
        },
        &answers,
    )
    .ok()
}

// Runs the checker of a search that answers the atoms as it goes on the search's graph so far,
// with the atoms' answers as the machine gives them now.
fn with_online<T>(
    machine: &mut Machine<'_>,
    context: &EngineContext,
    search: &Search<'_, States>,
    run: impl FnOnce(&tla_live::Source<'_>) -> T,
) -> T {
    let graph = search.graph.as_ref().expect("a graph");
    let count = search.states.count();
    let live = tla_live::Graph {
        parents: &search.states.parents[..count],
        edge_offsets: &graph.edge_offsets,
        edges: &graph.edges,
        fingerprints: &search.states.fingerprints[..count],
        reals: None,
        diameters: None,
    };
    let answers = LiveAnswers {
        machine: std::cell::RefCell::new(machine),
        atoms: &context.atoms,
        states: &search.states.ids,
        width: context.width,
        edges: &graph.edges,
    };
    run(&tla_live::Source {
        graph: &live,
        answers: &answers,
    })
}

// Adds a state to TLC's behavior graphs as TLC does once it has found an initial state or
// expanded a state: the atoms it evaluates then are evaluated on the machine as it is. Where the
// checker declines, into `declined` goes why.
fn add_online(
    machine: &mut Machine<'_>,
    context: &EngineContext,
    search: &Search<'_, States>,
    online: &mut tla_live::Online,
    (state, is_initial): (u32, bool),
    declined: &mut Option<String>,
) -> Outcome<()> {
    let added = with_online(machine, context, search, |source| {
        if is_initial {
            online.add_initial_state(source, state).map(|()| None)
        } else {
            online.add_state(source, state)
        }
    });
    // TLC runs Next again from a state it adds a node of late, with what Next sets.
    let is_late = online
        .take_events()
        .iter()
        .any(|event| matches!(event, Event::Late(_)));
    match added {
        Err(reason) => {
            *declined = Some(reason.0);
            Err(Bail(ONLINE_DECLINED))
        }
        Ok(Some(_)) => Err(Bail(ONLINE_ACCEPTED)),
        Ok(None) if is_late => Err(Bail(ONLINE_LATE)),
        Ok(None) => Ok(()),
    }
}

// Whether every atom of a state evaluates on each initial state the search found before it
// stopped among them, the one it stopped at included, and prints nothing.
fn answers_initial_atoms(
    machine: &mut Machine<'_>,
    context: &EngineContext,
    search: &Search<'_, States>,
    found: &Found,
) -> bool {
    let unassigned = vec![UNASSIGNED; context.width];
    let states: Vec<Vec<Id>> = (0..search.states.count() as u32)
        .map(|index| search.states.state(index).to_vec())
        .chain(found.last.clone())
        .collect();
    !context.is_live_printing
        && states.iter().all(|state| {
            let epoch = machine.next_epoch();
            machine.set_current(state, epoch);
            machine.set_next(&unassigned);
            context.atoms.iter().all(|atom| match atom {
                Atom::State(eval) | Atom::Enabled { run: Ok(eval), .. } => eval(machine).is_ok(),
                Atom::Action { .. } => true,
                Atom::Enabled { run: Err(_), .. } | Atom::Unknown(_) => false,
            })
        })
}

// What evaluating an atom the tables left unanswered gives, or `None` where the engine has no
// evaluation of it.
fn atom_failure(
    machine: &mut Machine<'_>,
    context: &EngineContext,
    search: &Search<'_, States>,
    unanswered: tla_live::Unanswered,
) -> Option<Outcome<Id>> {
    let edges = search.graph.as_ref()?.edges.len() as u32;
    let slot = match context.atoms.get(unanswered.atom as usize)? {
        Atom::Action { .. } if unanswered.slot >= edges => {
            tla_live::Slot::Stutter(unanswered.slot - edges)
        }
        Atom::Action { .. } => tla_live::Slot::Step {
            state: unanswered.state,
            edge: unanswered.slot,
        },
        _ => tla_live::Slot::State(unanswered.slot),
    };
    let atoms = &context.atoms;
    let graph = search.graph.as_ref()?;
    LiveAnswers {
        machine: std::cell::RefCell::new(machine),
        atoms,
        states: &search.states.ids,
        width: context.width,
        edges: &graph.edges,
    }
    .evaluate(unanswered.atom, slot)
    .ok()
}

// The first atom the engine didn't answer that TLC evaluates as it adds the states the search
// expanded to the behavior graphs.
fn unanswered_at(
    model: &Model,
    search: &Search<'_, States>,
    tables: &[Table],
    expanded: usize,
    count: usize,
) -> Option<tla_live::Unanswered> {
    let graph = search.graph.as_ref()?;
    let answers: Vec<Option<&[u8]>> = tables
        .iter()
        .map(|table| table.unknown.is_none().then_some(&table.answers[..]))
        .collect();
    tla_live::find_unanswered(
        &to_terms(&model.live_formula),
        &tla_live::Graph {
            parents: &search.states.parents[..count],
            edge_offsets: &graph.edge_offsets[..=expanded],
            edges: &graph.edges,
            fingerprints: &search.states.fingerprints[..count],
            reals: None,
            diameters: None,
        },
        &answers,
    )
}

// Where TLC evaluates an atom the engine didn't answer as it adds a state to the behavior graphs,
// the failure the caller evaluates again, with the counts of TLC's search then: what it generated
// and found up to that state, and the out-degrees of the states it expanded.
fn to_atom_failure(
    context: &EngineContext,
    search: &Search<'_, States>,
    initial_states: (u64, u64),
    unanswered: tla_live::Unanswered,
) -> Option<Found> {
    let graph = search.graph.as_ref()?;
    let state = unanswered.state as usize;
    let slot = unanswered.slot as usize;
    // TLC fails adding an initial state before it reports the initial states, where the search
    // looks for it.
    if unanswered.is_initial {
        return None;
    }
    // The state the atom reads besides the one TLC adds: a successor's state predicate, or the
    // next state of one of the added state's steps.
    let extra = match context.atoms.get(unanswered.atom as usize)? {
        Atom::State(_) => (slot != state).then_some(slot),
        Atom::Enabled { .. } => {
            if slot != state {
                return None;
            }
            None
        }
        Atom::Action { .. } => {
            let edges = graph.edges.len();
            let next = if slot < edges {
                let range =
                    graph.edge_offsets[state] as usize..graph.edge_offsets[state + 1] as usize;
                if !range.contains(&slot) {
                    return None;
                }
                graph.edges[slot] as usize
            } else if slot - edges == state {
                state
            } else {
                return None;
            };
            Some(next)
        }
        Atom::Unknown(_) => return None,
    };
    let sum = |counts: &[u32]| {
        counts[..=state]
            .iter()
            .map(|&count| u64::from(count))
            .sum::<u64>()
    };
    let distinct = initial_states.1 + sum(&graph.new_counts);
    let mut out_degrees = [0u64; OUT_DEGREE_BUCKETS];
    for &count in &graph.new_counts[..=state] {
        out_degrees[(count as usize).min(OUT_DEGREE_BUCKETS - 1)] += 1;
    }
    Some(Found {
        kind: ViolationKind::Error {
            site: ErrorSite::Atom {
                atom: unanswered.atom,
                is_extra: extra.is_some(),
            },
        },
        parent: Some(state),
        last: extra.map(|extra| search.states.state(extra as u32).to_vec()),
        fingerprint: None,
        random: None,
        counts: StopCounts {
            generated: initial_states.0 + sum(&graph.successor_counts),
            distinct,
            queued: distinct - state as u64 - 1,
            depth: u64::from(graph.diameters[state]),
            out_degrees,
        },
    })
}

// A path to a node that accepts every behavior as a violation the caller prints, with the counts of
// TLC's search when it stops as it adds `state`: what it generated and found by then, as the graph
// records them.
fn to_accepted(
    machine: &mut Machine<'_>,
    context: &EngineContext,
    search: &mut Search<'_, States>,
    initial_states: (u64, u64),
    state: u32,
    path: &[u32],
    violated: Vec<usize>,
) -> Option<Box<Violation>> {
    let mut labels = label_path(machine, context, search, path, None, false).ok()?;
    if labels.len() != path.len() || machine.store.has_unordered_strings() {
        return None;
    }
    labels.remove(0);
    let startup = startup_values(machine, context).ok()?;
    let graph = search.graph.as_ref()?;
    let state = state as usize;
    let sum = |counts: &[u32]| {
        counts[..=state]
            .iter()
            .map(|&count| u64::from(count))
            .sum::<u64>()
    };
    let distinct = initial_states.1 + sum(&graph.new_counts);
    let counts = StopCounts {
        generated: initial_states.0 + sum(&graph.successor_counts),
        distinct,
        queued: distinct - state as u64 - 1,
        depth: u64::from(graph.diameters[state]),
        ..StopCounts::default()
    };
    Some(Box::new(Violation {
        kind: ViolationKind::Accepted { violated },
        states: path
            .iter()
            .map(|&index| search.states.state(index).to_vec())
            .collect(),
        labels,
        counts,
        store: std::mem::replace(&mut machine.store, Store::new()),
        startup,
        startup_random: machine.startup_random,
        random: None,
        symmetry: None,
        registers: std::mem::take(&mut machine.registers),
        possible: search.possible.clone(),
        fingerprints: Vec::new(),
    }))
}

// A lasso as a violation the caller prints: its states, and the action of each step, which every
// step but a stuttering last one has.
fn to_lasso(
    machine: &mut Machine<'_>,
    context: &EngineContext,
    search: &Search<'_, States>,
    (path, loop_start): (&[u32], usize),
    actions: &[Option<u32>],
    printed: Vec<Vec<Id>>,
    counts: &Counts,
) -> Option<Box<Violation>> {
    // Under SYMMETRY or a VIEW the stored states aren't those TLC prints, and the caller's rebuild
    // finds the steps' actions, the step back into the cycle's too, as TLC does.
    let is_reduced = search.states.key_width.is_some() || search.canonicalizer.is_some();
    let (labels, loop_label) = if is_reduced {
        (vec![None; path.len().saturating_sub(1)], None)
    } else {
        let (&loop_label, steps) = actions.split_last()?;
        let is_stuttering = loop_start + 1 == path.len();
        let is_labelled = actions.len() == path.len() && (is_stuttering || loop_label.is_some());
        if !is_labelled {
            return None;
        }
        (steps.to_vec(), loop_label)
    };
    let startup = startup_values(machine, context).ok()?;
    let symmetry = search
        .canonicalizer
        .as_ref()
        .map(|canonicalizer| name_group(&machine.store, canonicalizer.group()));
    (!machine.store.has_unordered_strings()).then(|| {
        Box::new(Violation {
            kind: ViolationKind::Lasso {
                loop_start,
                loop_label,
                printed,
            },
            states: path
                .iter()
                .map(|&index| search.states.state(index).to_vec())
                .collect(),
            labels,
            counts: StopCounts {
                generated: counts.generated,
                distinct: counts.distinct,
                queued: counts.queued,
                depth: counts.depth,
                ..StopCounts::default()
            },
            store: std::mem::replace(&mut machine.store, Store::new()),
            startup,
            startup_random: machine.startup_random,
            random: None,
            symmetry,
            registers: std::mem::take(&mut machine.registers),
            possible: search.possible.clone(),
            fingerprints: Vec::new(),
        })
    })
}

// The actions of a lasso's steps: from each state to the next, and from the last to the cycle's
// first, `None` for that step when the cycle is the last state alone, which stutters.
fn label_lasso(
    machine: &mut Machine<'_>,
    context: &EngineContext,
    search: &mut Search<'_, States>,
    path: &[u32],
    loop_start: usize,
) -> Outcome<Vec<Option<u32>>> {
    let is_stuttering = loop_start + 1 == path.len();
    let mut closed = path.to_vec();
    if !is_stuttering {
        closed.push(path[loop_start]);
    }
    let is_rebuilt = search.states.key_width.is_some();
    let mut labels = label_path(machine, context, search, &closed, None, is_rebuilt)?;
    if labels.is_empty() {
        return Ok(labels);
    }
    labels.remove(0);
    if is_stuttering {
        labels.push(None);
    }
    Ok(labels)
}

fn report_printed(reporter: &mut dyn Reporter, store: &Store, printed: &Printed) {
    match printed {
        Printed::Values(values) => reporter.print(store, values),
        Printed::InitialStates(count) => reporter.initial_states_progress(*count),
    }
}

/// What the search reports, held until the liveness checker has checked the properties.
enum Out<'p> {
    Printed(&'p Printed),
    /// The count of initial states.
    InitialStates,
}

// What the search and the atoms printed, in TLC's order: the initial states' prints, then each
// expanded state's, followed by those of the atoms TLC evaluates as it adds the state to the
// behavior graphs, and again where TLC runs Next from a state it adds a node of late. Nothing where
// anything printed and the native checker leaves the properties to the interpreter or finds a node
// that accepts every behavior, or where an atom printed as TLC adds an initial state, which the
// engine doesn't follow.
fn order_printed<'p>(
    held: &'p [Vec<Printed>],
    tables: &'p [Table],
    liveness: &Liveness,
    is_replay_inexact: bool,
) -> Option<Vec<Out<'p>>> {
    let is_printed = held.iter().any(|printed| !printed.is_empty())
        || tables.iter().any(|table| !table.prints.is_empty());
    // The interpreter replays the search to a state whose node accepts every behavior, printing
    // as it goes, so there it checks from the start.
    let is_decided = !matches!(
        liveness.verdict,
        Verdict::Declined(_) | Verdict::Unexpanded | Verdict::Accepted { .. }
    );
    if is_printed && !is_decided {
        return None;
    }
    let (initial, expansions) = held.split_first()?;
    let mut order: Vec<Out<'p>> = initial.iter().map(Out::Printed).collect();
    order.push(Out::InitialStates);
    let mut next = 0;
    let mut is_initial = false;
    for event in &liveness.events {
        match *event {
            // What TLC prints from here on follows the check's start.
            Event::Lasso => break,
            Event::Initial(_) => is_initial = true,
            Event::Expanded(state) => {
                is_initial = false;
                let end = (state as usize + 1).min(expansions.len());
                for printed in &expansions[next.min(end)..end] {
                    order.extend(printed.iter().map(Out::Printed));
                }
                next = next.max(end);
            }
            // TLC runs Next again from a stored state it adds a node of late, and prints what
            // the search printed expanding it.
            // TLC checks no invariant then, the count of distinct states has grown since, and
            // it runs Next action by action with the atoms of each action's successors between,
            // so where an invariant may print among Next's prints, anything reads that count or
            // Next has several actions, the interpreter checks from the start.
            Event::Late(state) => {
                if let Some(printed) = expansions.get(state as usize) {
                    if is_replay_inexact && !printed.is_empty() {
                        return None;
                    }
                    order.extend(printed.iter().map(Out::Printed));
                }
            }
            Event::Atom { atom, slot } => {
                let printed = tables[atom as usize].printed(slot);
                if is_initial && !printed.is_empty() {
                    return None;
                }
                order.extend(printed.iter().map(Out::Printed));
            }
        }
    }
    for printed in &expansions[next.min(expansions.len())..] {
        order.extend(printed.iter().map(Out::Printed));
    }
    Some(order)
}

/// Under SYMMETRY or a VIEW, the states the steps reached: the states stored, then each other state
/// a step reached, once, with its level. The steps are the search's, then those from the states
/// past the stored ones that the liveness checker asked about, each with the stored state with its
/// fingerprint and the position of the state it reached.
struct Reals {
    width: usize,
    states: Vec<Id>,
    levels: Vec<i64>,
    positions: HashMap<Vec<Id>, u32>,
    offsets: Vec<u32>,
    targets: Vec<u32>,
    edges: Vec<u32>,
    labels: Option<Vec<u32>>,
}

impl Reals {
    fn expanded(&self) -> usize {
        self.offsets.len() - 1
    }

    // The position of the state a step to the stored state `target` reached.
    fn position(&mut self, stored: &[Id], target: u32, real: &[Id], level: i64) -> u32 {
        if stored == real {
            return target;
        }
        if let Some(&position) = self.positions.get(real) {
            return position;
        }
        self.states.extend_from_slice(real);
        self.levels.push(level);
        let position = (self.states.len() / self.width - 1) as u32;
        self.positions.insert(real.to_vec(), position);
        position
    }
}

// Each state's depth, from its parent's: the search stores a parent before its children.
fn get_depths(parents: &[i32]) -> Vec<i64> {
    let mut depths: Vec<i64> = Vec::with_capacity(parents.len());
    for &parent in parents {
        depths.push(if parent == -1 {
            1
        } else {
            depths[parent as usize] + 1
        });
    }
    depths
}

fn real_states(search: &Search<'_, States>, width: usize) -> Option<Reals> {
    let graph = search.graph.as_ref()?;
    let reached = graph.reals.as_ref()?;
    let states = &search.states;
    let count = states.count();
    let depths = get_depths(&states.parents);
    let mut reals = Reals {
        width,
        states: states.ids[..count * width].to_vec(),
        levels: Vec::new(),
        positions: HashMap::new(),
        offsets: graph.edge_offsets.clone(),
        targets: graph.edges.clone(),
        edges: Vec::with_capacity(graph.edges.len()),
        labels: graph.labels.clone(),
    };
    for (state, &depth) in depths.iter().enumerate() {
        let start = graph.edge_offsets[state] as usize;
        let end = graph.edge_offsets[state + 1] as usize;
        for edge in start..end {
            let target = graph.edges[edge];
            let real = &reached[edge * width..(edge + 1) * width];
            let position = reals.position(states.state(target), target, real, depth + 1);
            reals.edges.push(position);
        }
    }
    Some(reals)
}

// Takes the steps from the states past the stored ones that no step was taken from yet, as TLC's
// late `addNextState` takes them: each successor in the model, through each of TLC's actions when
// the search labels its steps. Whether there were any.
fn expand_reals(
    machine: &mut Machine<'_>,
    context: &EngineContext,
    search: &mut Search<'_, States>,
    reals: &mut Reals,
) -> Outcome<bool> {
    let width = reals.width;
    let count = search.states.count();
    let first = reals.expanded();
    let total = reals.states.len() / width;
    let walks: Vec<&Step> = match (&reals.labels, &context.actions) {
        (Some(_), Some(actions)) => actions.iter().collect(),
        _ => context.next.iter().collect(),
    };
    let unassigned = vec![UNASSIGNED; width];
    for state in first..total {
        let current = reals.states[state * width..(state + 1) * width].to_vec();
        let depth = reals.levels[state - count];
        let level = machine.store.int(depth)?;
        let next_level = machine.store.int(depth + 1)?;
        let set_current = |machine: &mut Machine<'_>| {
            let epoch = machine.next_epoch();
            machine.set_current(&current, epoch);
            machine.set_slot(LEVEL_SLOT, level);
            machine.set_slot(NEXT_LEVEL_SLOT, next_level);
        };
        let mut successors: Vec<(Vec<Id>, u32)> = Vec::new();
        for (label, walk) in walks.iter().enumerate() {
            set_current(machine);
            machine.set_next(&unassigned);
            machine.reset_assigned();
            walk(machine, &mut |machine: &mut Machine<'_>| {
                if machine.next().contains(&UNASSIGNED) {
                    return Err(Bail("a successor that isn't complete"));
                }
                successors.push((machine.next().to_vec(), label as u32));
                Ok(())
            })?;
        }
        for (successor, label) in successors {
            let epoch = machine.next_epoch();
            machine.set_current(&successor, epoch);
            machine.set_slot(LEVEL_SLOT, next_level);
            if !holds_all_changed_none(machine, context)? {
                continue;
            }
            let fingerprint = search.compute_key(machine, context, false)?;
            set_current(machine);
            machine.set_next(&successor);
            if !holds_all(machine, &context.action_constraints)? {
                continue;
            }
            let slot = search
                .states
                .find(&search.key, fingerprint)
                .map_err(|_| Bail("a step to a state the search didn't find"))?;
            let target = search.states.index(slot);
            let position =
                reals.position(search.states.state(target), target, &successor, depth + 1);
            reals.targets.push(target);
            reals.edges.push(position);
            if let Some(labels) = &mut reals.labels {
                labels.push(label);
            }
        }
        reals.offsets.push(reals.targets.len() as u32);
    }
    Ok(first < total)
}

// Checks the temporal properties on a complete search's graph from the answers to the atoms.
fn to_terms(terms: &[LiveTerm]) -> Vec<Term> {
    terms
        .iter()
        .map(|&term| match term {
            LiveTerm::Boolean(value) => Term::Boolean(value),
            LiveTerm::State(atom) => Term::State(atom),
            LiveTerm::Enabled(atom) => Term::Enabled(atom),
            LiveTerm::Action { atom, enabled } => Term::Action { atom, enabled },
            LiveTerm::Not => Term::Not,
            LiveTerm::Always => Term::Always,
            LiveTerm::Eventually => Term::Eventually,
            LiveTerm::Next => Term::Next,
            LiveTerm::And(count) => Term::And(count),
            LiveTerm::Or(count) => Term::Or(count),
        })
        .collect()
}

fn check_liveness(
    model: &Model,
    search: &Search<'_, States>,
    tables: &[Table],
    reals: Option<&Reals>,
    is_effectful: bool,
    diameter_atoms: &[bool],
    threads: usize,
) -> Liveness {
    let graph = search.graph.as_ref().expect("a graph");
    // Under SYMMETRY or a VIEW, TLC names the violated properties from the trace it rebuilds, of
    // states the graph doesn't hold, so the checker names none.
    let properties: Vec<Vec<Term>> = model
        .live_properties
        .iter()
        .filter(|_| reals.is_none())
        .map(|property| to_terms(&property.formula))
        .collect();
    let property_terms: Vec<&[Term]> = properties.iter().map(Vec::as_slice).collect();
    let answers: Vec<Option<&[u8]>> = tables
        .iter()
        .map(|table| table.unknown.is_none().then_some(&table.answers[..]))
        .collect();
    tla_live::check(
        &to_terms(&model.live_formula),
        &property_terms,
        &tla_live::Graph {
            parents: &search.states.parents,
            edge_offsets: reals.map_or(&graph.edge_offsets, |reals| &reals.offsets),
            edges: reals.map_or(&graph.edges, |reals| &reals.targets),
            fingerprints: &search.states.fingerprints,
            reals: reals.map(|reals| &reals.edges[..]),
            diameters: diameter_atoms.contains(&true).then(|| tla_live::Diameters {
                states: &graph.diameters,
                last: search.depth.max(1) as u32,
                atoms: diameter_atoms,
            }),
        },
        &answers,
        is_effectful,
        threads,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn takes_only_tlc_failures_for_failures_tlc_reports() {
        // A run-time decline, such as a Print of a value the engine can't print as TLC does, is
        // the engine's own limit; a failed Assert is TLC's.
        assert!(is_engine_limit(
            "printing a value whose text depends on how TLC built it"
        ));
        assert!(is_engine_limit("unsupported: Print"));
        assert!(is_engine_limit("a power set too large to build"));
        assert!(!is_engine_limit("an assertion failed"));
        assert!(!is_engine_limit("a mistyped membership in Nat"));
        // suite/test202's assumption, which TLC evaluates without enumerating Nat.
        assert!(is_engine_limit("enumerated Nat"));
        // TLC fails only where a value it built as a record meets a function, which the store,
        // knowing a value by its domain, can't tell from a function over strings.
        assert!(is_engine_limit("record compared with a function"));
    }

    fn verified_states() -> States {
        States {
            width: 1,
            key_width: None,
            ids: Vec::new(),
            keys: Vec::new(),
            parents: Vec::new(),
            fingerprints: Vec::new(),
            set: FingerprintSet::new(true),
            order: vec![0],
            is_verified: true,
            collisions: 0,
        }
    }

    // PROVE_IT_FP_VERIFY: a fingerprint two different keys share is a collision, which merges the
    // two as TLC does, and counts it.
    #[test]
    fn counts_a_fingerprint_two_keys_share() {
        let mut states = verified_states();
        let Err(slot) = states.find(&[7], 42) else {
            panic!("an empty set found a state");
        };
        states.add(&[7], &[], 42, slot, -1);
        let found = states.find(&[7], 42).expect("a state found");
        assert_eq!(states.set.index(found), 0);
        assert_eq!(states.collisions, 0);
        assert_eq!(states.find(&[8], 42), Ok(found));
        assert_eq!(states.collisions, 1);
        assert!(states.find(&[8], 43).is_err());
        assert_eq!(states.collisions, 1);
    }

    // Every fingerprint finds its state after the table has grown many times.
    #[test]
    fn finds_every_fingerprint_after_growing() {
        let mut states = verified_states();
        let fingerprint_of = |index: u32| u64::from(index).wrapping_mul(0x2545_f491_4f6c_dd1d);
        for index in 0..10_000u32 {
            let Err(slot) = states.find(&[index], fingerprint_of(index)) else {
                panic!("a fingerprint found before it was added");
            };
            states.add(&[index], &[], fingerprint_of(index), slot, -1);
        }
        for index in 0..10_000u32 {
            let slot = states
                .find(&[index], fingerprint_of(index))
                .expect("a fingerprint added");
            assert_eq!(states.set.index(slot), index);
        }
        assert_eq!(states.collisions, 0);
        assert_eq!(states.ids.len(), 10_000);
    }

    // The fingerprint 0 marks an empty slot, so a state whose fingerprint is 0 is kept apart.
    #[test]
    fn keeps_a_state_whose_fingerprint_is_zero() {
        let mut states = verified_states();
        let Err(slot) = states.find(&[5], 0) else {
            panic!("an empty set found a state");
        };
        states.add(&[5], &[], 0, slot, -1);
        let Err(slot) = states.find(&[6], 1) else {
            panic!("a fingerprint found before it was added");
        };
        states.add(&[6], &[], 1, slot, -1);
        let found = states
            .find(&[5], 0)
            .expect("the state whose fingerprint is 0");
        assert_eq!(states.set.index(found), 0);
        assert_eq!(states.collisions, 0);
        assert_eq!(states.set.len, 1);
    }

    // Under a VIEW or symmetry the key is kept beside the state, and compared for a collision.
    #[test]
    fn compares_the_key_when_it_isnt_the_state() {
        let mut states = verified_states();
        states.key_width = Some(1);
        let Err(slot) = states.find(&[70], 42) else {
            panic!("an empty set found a state");
        };
        states.add(&[7], &[70], 42, slot, -1);
        assert!(states.find(&[70], 42).is_ok());
        assert_eq!(states.collisions, 0);
        assert!(states.find(&[80], 42).is_ok());
        assert_eq!(states.collisions, 1);
        assert_eq!(
            (states.ids.as_slice(), states.keys.as_slice()),
            (&[7][..], &[70][..])
        );
    }
}
