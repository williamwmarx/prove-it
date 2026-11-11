//! The registers compiled code reads, as `compile.ts`'s `CUR`, `NXT`, `LOC`, `STACK` and `EPOCH`,
//! and the caches a compiled program fills as it runs. A [`Program`] is what compiling leaves
//! besides the closures: the bodies of recursive definitions, which the closures that call them
//! find by number, and how many caches of each kind to make. A [`Machine`] runs closures of one
//! program on one store.

use std::collections::HashMap;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

use tla_ir::NodeId;
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
}

/// What a search stops with once its machines evaluated as many bodies of recursive definitions
/// as PROVE_IT_TEST_EVALUATIONS allows.
pub const EVALUATIONS_SPENT: &str = "stopped where PROVE_IT_TEST_EVALUATIONS asked";

/// What one Print or PrintT printed: the values, and in the native checker TLC's text of each,
/// which the compiler knows where the store forgets how TLC built a value the spec writes there.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Prints {
    pub values: Vec<Id>,
    /// TLC's text of each value, before TLC's pretty-printer breaks its lines; `None` where the
    /// engine doesn't know one, or isn't the native checker.
    pub texts: Option<Vec<Vec<u16>>>,
}

/// A variable that has no value yet, -1 in the TypeScript registers.
pub const UNASSIGNED: Id = u32::MAX;

/// How deep recursive operators and functions may call themselves before the engine hands over,
/// so that deep TLA+ recursion stops cleanly rather than overflow the native stack. WebAssembly's
/// frames are on the host's stack, which holds about 1,500 calls of a simple recursive operator
/// under Bun and 1,800 under Node's default stack (fallback.md), so it stops sooner there. TLC's
/// own JVM stack holds a few hundred.
const MAXIMUM_RECURSION: u32 = if cfg!(target_arch = "wasm32") {
    1_000
} else {
    20_000
};

/// Where a memo table reads one of its keys.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Key {
    Current(u32),
    Next(u32),
    Slot(u32),
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

/// What a compiled program needs besides its closures.
#[derive(Default)]
pub struct Program {
    pub(crate) width: usize,
    pub(crate) slot_count: usize,
    /// Each memo table's width, and whether it is kept: a recursive definition's, which doesn't
    /// turn off once full (`MemoTable::kept`).
    pub(crate) memo_tables: Vec<(usize, bool)>,
    pub(crate) epoch_count: usize,
    pub(crate) once_count: usize,
    pub(crate) round_count: usize,
    pub(crate) recursives: Vec<Option<Recursive>>,
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
}

impl Program {
    /// Whether the machines evaluated more bodies of recursive definitions than
    /// PROVE_IT_TEST_EVALUATIONS allows.
    pub(crate) fn is_evaluation_budget_spent(&self) -> bool {
        self.evaluation_budget
            .is_some_and(|budget| self.evaluations.load(Ordering::Relaxed) > budget)
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
    pub(crate) onces: Vec<Id>,
    // The round of membership tests in which each set's parts last ran (`onceARound`).
    pub(crate) rounds: Vec<u64>,
    pub(crate) parts_round: u64,
    parts_rounds: u64,
    depth: u32,
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
    /// The generator RandomElement and RandomSubset draw from: the interpreter's for the initial
    /// states, then one seeded for each state the search expands (`runtime.getRandom`).
    pub(crate) random: JavaRandom,
    /// The state of the generator the startup left, which a violation's trace draws from.
    pub(crate) startup_random: u64,
    /// TLC's registers, which TLCSet sets and TLCGet reads.
    pub registers: Registers,
    /// Whether TLC has seen the successor whose action constraints the search checks, which
    /// PickSuccessor reads; None elsewhere.
    pub(crate) is_successor_seen: Option<bool>,
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
}

impl Registers {
    pub fn is_empty(&self) -> bool {
        self.numbered.iter().all(Option::is_none) && self.named.is_empty()
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
            onces: vec![EMPTY; program.once_count],
            rounds: vec![u64::MAX; program.round_count],
            parts_round: 0,
            parts_rounds: 0,
            depth: 0,
            assigned: 0,
            is_past_walk: false,
            assigned_shapes: None,
            is_membership_unsafe: false,
            piece_bits: 0,
            spare_states: Vec::new(),
            output: Vec::new(),
            random: JavaRandom::seeded(program.random_seed),
            startup_random: 0,
            registers: Registers::default(),
            is_successor_seen: None,
            tlc_caches: HashMap::new(),
            fingerprints: Fingerprints::new(program.polynomial()),
            lazy_functions: Vec::new(),
            held: vec![None; program.width],
            is_before_initial_state: false,
        }
    }

    /// Notes a value a walk assigned to a variable, where the machine keeps their shapes. A walk
    /// through an instance's action, as ENABLED takes, can assign slots past the spec's variables,
    /// which no step the search keeps holds.
    #[inline(always)]
    pub(crate) fn note_assigned(&mut self, variable: usize, value: Id) {
        if let Some(join) = self
            .assigned_shapes
            .as_mut()
            .and_then(|joins| joins.get_mut(variable))
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
    pub(crate) fn adopt_onces(&mut self, onces: &[Id]) {
        for (own, &other) in self.onces.iter_mut().zip(onces) {
            if *own == EMPTY {
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
        for once in self.onces.iter_mut().filter(|once| **once >= bound) {
            *once = EMPTY;
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
        let known = self.tables[table].get(&read);
        if known != EMPTY {
            return Ok(known);
        }
        let value = inner(self)?;
        self.tables[table].set(&read, value);
        Ok(value)
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
            return Ok(known);
        }
        let value = inner(self)?;
        self.epochs[cache].set(epoch, entry, &keys, value);
        Ok(value)
    }

    pub(crate) fn once(&mut self, once: usize, inner: &Eval) -> Outcome<Id> {
        let known = self.onces[once];
        if known != EMPTY {
            return Ok(known);
        }
        let value = inner(self)?;
        self.onces[once] = value;
        Ok(value)
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
        if end <= start {
            return eval(self);
        }
        let at = self.stack.len();
        self.stack
            .extend_from_slice(&self.locals[start as usize..end as usize]);
        let result = eval(self);
        self.locals[start as usize..end as usize].copy_from_slice(&self.stack[at..]);
        self.stack.truncate(at);
        result
    }

    /// Calls a recursive operator or function whose arguments are bound already.
    pub(crate) fn call_recursive(&mut self, index: usize) -> Outcome<Id> {
        let program = self.program;
        let recursive = program.recursives[index]
            .as_ref()
            .expect("a recursive definition called before its body settled");
        if self.depth >= MAXIMUM_RECURSION {
            return Err(Bail("recursion too deep"));
        }
        self.depth += 1;
        let result = match recursive.table {
            Some(table) if self.tables[table].is_enabled() => {
                let mut read = [0; 6];
                for (index, &key) in recursive.keys.iter().enumerate() {
                    read[index] = self.read_key(key);
                }
                let keys = &read[..recursive.keys.len()];
                let known = self.tables[table].get(keys);
                if known != EMPTY {
                    Ok(known)
                } else {
                    let value = self.evaluate_recursive(recursive);
                    if let Ok(value) = value {
                        self.tables[table].set(keys, value);
                    }
                    value
                }
            }
            _ => self.evaluate_recursive(recursive),
        };
        self.depth -= 1;
        result
    }

    fn evaluate_recursive(&mut self, recursive: &Recursive) -> Outcome<Id> {
        if let Some(budget) = self.program.evaluation_budget
            && self.program.evaluations.fetch_add(1, Ordering::Relaxed) >= budget
        {
            return Err(Bail(EVALUATIONS_SPENT));
        }
        self.keeping_slots(&recursive.body, recursive.slot_start, recursive.slot_end)
    }

    /// Runs a walk of a recursive function's body one call deeper, as `call_recursive` runs a
    /// call.
    pub(crate) fn nested(&mut self, run: impl FnOnce(&mut Self) -> Outcome<()>) -> Outcome<()> {
        if self.depth >= MAXIMUM_RECURSION {
            return Err(Bail("recursion too deep"));
        }
        self.depth += 1;
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
