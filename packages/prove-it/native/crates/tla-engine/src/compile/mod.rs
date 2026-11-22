//! Compiles the expressions of an engine IR into closures over the ids of a tla-values store, as
//! `src/engine/compile.ts` compiles the TypeScript AST: kind by kind, with the same footprints,
//! caches and places to stop. Each compiled expression knows its footprint: the state variables,
//! primed variables and bound names it reads. An expression worth caching is wrapped in a memo
//! table keyed by the ids in its footprint, one that reads nothing is evaluated once, and one that
//! reads too many variables for a table is cached while one state is current.
//!
//! Operators are expanded where they are applied, with their parameters bound to the argument
//! expressions, as TLA+ defines them. A recursive operator or function is compiled once and called
//! by value instead, its body compiled again until what it reads settles.
//!
//! What the TypeScript engine refuses, this compiler refuses with the same reason
//! ([`CompileError::Bail`]). What the TypeScript engine runs and this one doesn't yet, such as the
//! builtins it bridges to the interpreter and ENABLED, which needs the walker, this one declines
//! ([`CompileError::Decline`]).

mod bridged;
pub(crate) use bridged::IS_A_BAG_OF_LAZY_FUNCTION;
pub(crate) mod builtins;
mod fused;
pub(crate) mod lazy;
pub(crate) mod lazy_function;

pub(crate) use lazy_function::Lambda;
mod nodes;
pub(crate) use nodes::EXCEPT_INCOMPATIBLE_KEY;
mod pieces;
mod predicate;
mod pruned;
pub(crate) mod random;
mod sets;
mod walker;

pub(crate) use builtins::{
    ENUMERATED_INT, ENUMERATED_NAT, ENUMERATED_SEQ, ENUMERATED_STRING, NON_SET_OPERAND,
};
pub use walker::ActionOptions;
pub(crate) use walker::INFINITE_BOUND;

use std::cell::{Cell, OnceCell, RefCell};
use std::collections::{HashMap, HashSet};
use std::fmt::Display;
use std::rc::{Rc, Weak};
use std::sync::Arc;
use std::sync::atomic::AtomicBool;

use tla_ir::{
    Bound, Builtin, Definition, DefinitionForm, Index, Ir, Name, NodeId, NodeKind, Param, Pattern,
    Resolution, TextId, Value,
};
use tla_values::store::{FALSE, KIND_BOOL, KIND_INT, KIND_SET, KIND_STRING, Outcome, TRUE};
use tla_values::{Bail, Id, Store};

use crate::footprint::Footprint;
use crate::machine::{Eval, Key, Machine, Member, Parts, Program, Recursive, Step};
use crate::memo::EPOCH_KEYS;

/// What TLCGet reads of TLC's search, at slots of their own so that an expression that reads one
/// is cached by its value: the level of the current state and of the next, and the number of
/// distinct states, which the search sets. An expression that prints has the print slot, which
/// nothing sets, in its footprint, and nothing caches it.
pub const LEVEL_SLOT: u32 = 0;
pub const NEXT_LEVEL_SLOT: u32 = 1;
pub const DISTINCT_SLOT: u32 = 2;
const PRINT_SLOT: u32 = 3;

/// A bound past `TLCGlobals.setBound` elements whose value TLC may keep lazy or hold built.
pub(crate) const UNKNOWN_BOUND_PAST_SET_BOUND: &str =
    "unsupported: a bound of more than TLCGlobals.setBound elements TLC may hold lazy";
/// Why the engine stops where a recursive function TLC keeps lazy as it starts would print after
/// the startup, as it is applied or converted on a worker's thread.
pub(crate) const KEPT_LAZY_AFTER_STARTUP: &str =
    "unsupported: a recursive function that prints, applied after TLC starts";
/// Why the engine stops where such a function is a value TLC may not convert, or may convert
/// after evaluating other parts (`Compiler::converting_operands`).
const KEPT_LAZY_USED_AS_VALUE: &str =
    "a recursive function that prints, used as a value TLC may not convert";

/// Why the engine stops at a constant definition it holds as a set TLC keeps lazy, built of a part
/// with effects, which TLC has only as it first converts the set (`Compiler::kept_definition`).
const KEPT_WITH_EFFECTS: &str =
    "a constant definition TLC keeps as a lazy set whose effects it has as it first converts it";

/// The builtins whose evaluation has an effect: it prints, draws, sets a register, asserts or
/// touches a file.
// Builtins TLC evaluates every argument of with the control it evaluates the application with,
// as an opcode of `Tool.evalAppl` or a Java method (`OpValue.eval`), never `KeepLazy` of its own.
const EAGER_ARGUMENT_BUILTINS: &[&str] = &[
    "Print",
    "PrintT",
    "ToString",
    "=",
    "#",
    "\\in",
    "\\notin",
    "\\subseteq",
    "\\cup",
    "\\cap",
    "\\",
    "UNION",
    "SUBSET",
    "DOMAIN",
    "Cardinality",
];

const EFFECT_BUILTINS: &[&str] = &[
    "Print",
    "PrintT",
    "AssertEq",
    "RandomElement",
    "RandomSubset",
    "RandomSubsetSet",
    "RandomSetOfSubsets",
    "TestRandomSetOfSubsets",
    "TLCSet",
    "TLCGetAndSet",
    "_Track",
    "JsonSerialize",
    "ndJsonSerialize",
    "JsonDeserialize",
    "ndJsonDeserialize",
];

/// Where IOUtils's Serialize writes NDJSON or fails, which `Json.textSerialize` does.
pub(crate) const TEXT_SERIALIZED: &str = "IOUtils's Serialize, which TLC writes or fails at";
/// TLCGet("diameter"), which only the liveness checker's atoms read.
pub const DIAMETER_SLOT: u32 = 4;
/// What reads a TLC register, which nothing sets either, so nothing caches it.
const REGISTER_SLOT: u32 = 5;
const WARNING_SLOT: u32 = 6;
pub(crate) const LAZY_FUNCTION_WARNING: &str =
    "unsupported: a warning in a finite function TLC keeps lazy";
pub(crate) const ATOM_WARNING: &str =
    "unsupported: a warning as the liveness checker evaluates an atom of the temporal properties";
/// TLCGet("generated"), TLCGet("queue") and the "initial" field of TLCGet("stats"), the counts of
/// TLC's model checker the search sets where the spec reads them (`ModelChecker.getStatesGenerated`,
/// `getStateQueueSize`, `getInitialStatesGenerated`).
pub const GENERATED_SLOT: u32 = 7;
pub const QUEUE_SLOT: u32 = 8;
pub const INITIAL_SLOT: u32 = 9;
/// TLCExt's Trace: the tuple of the records of the states from an initial state to the one the
/// search expands (`Machine::trace`).
pub const TRACE_SLOT: u32 = 10;
const SEARCH_SLOTS: [u32; 10] = [
    LEVEL_SLOT,
    NEXT_LEVEL_SLOT,
    DISTINCT_SLOT,
    PRINT_SLOT,
    DIAMETER_SLOT,
    REGISTER_SLOT,
    GENERATED_SLOT,
    QUEUE_SLOT,
    INITIAL_SLOT,
    TRACE_SLOT,
];

const MAXIMUM_MEMO_WIDTH: usize = 6;
const MAXIMUM_EXPANSION: u32 = 2000;
/// The builtins that write a value's text, or keep a value another may write.
const TEXT_BUILTINS: [&str; 7] = [
    "Print",
    "PrintT",
    "AssertEq",
    "ToString",
    "JsonSerialize",
    "ndJsonSerialize",
    "TLCSet",
];

/// The builtins whose value is a boolean, a number or a string, whatever their arguments hold.
const SCALAR_BUILTINS: [&str; 34] = [
    "Cardinality",
    "IsFiniteSet",
    "Len",
    "\\in",
    "\\notin",
    "=",
    "#",
    "/=",
    "\\subseteq",
    "\\subset",
    "\\supseteq",
    "\\supset",
    "<",
    ">",
    "<=",
    ">=",
    "=<",
    "\\leq",
    "\\geq",
    "+",
    "-",
    "-.",
    "*",
    "\\div",
    "%",
    "^",
    "~",
    "\\lnot",
    "\\neg",
    "=>",
    "<=>",
    "\\equiv",
    "/\\",
    "\\/",
];

/// Why an expression didn't compile.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CompileError {
    /// The TypeScript engine refuses it too, for this reason, word for word.
    Bail(String),
    /// The TypeScript engine compiles it and this one doesn't yet.
    Decline(String),
}

impl From<Bail> for CompileError {
    fn from(bail: Bail) -> CompileError {
        CompileError::Bail(bail.0.to_string())
    }
}

type Compiling<T> = Result<T, CompileError>;

/// An argument of a call of a RECURSIVE operator whose body may print, which fails where the
/// engine evaluates it before the body, and TLC where the body first reads it.
const RECURSIVE_ARGUMENT_FAILED: &str =
    "unsupported: a failing argument of a recursive operator that prints";

/// How deep the engine follows a RECURSIVE operator whose body may print. TLC's stack overflows
/// at a depth that depends on its thread's stack and on the frames each level takes, past which
/// it reports the overflow after printing what it printed so far: `R(n) == IF n = 0 THEN 0 ELSE
/// P(n, n) + R(n - 1)`, which prints at each level, overflowed at about 640 levels as TLC
/// computed its constants, and with the call before the print at under 1,500 everywhere.
const PRINTING_RECURSION_LIMIT: u32 = 50;
const PRINTING_RECURSION_TOO_DEEP: &str =
    "unsupported: a recursion that prints, deeper than TLC's stack surely holds";

fn unsupported<T>(what: impl Display) -> Compiling<T> {
    Err(CompileError::Bail(format!("unsupported: {what}")))
}

fn decline<T>(what: impl Display) -> Compiling<T> {
    Err(CompileError::Decline(what.to_string()))
}

/// Settings that change how compiled code caches, never what it computes.
#[derive(Clone, Copy, Debug, Default)]
pub struct Options {
    /// PROVE_IT_MEMO=off: no memo table, epoch cache or value computed once.
    pub is_memo_off: bool,
    /// PROVE_IT_EPOCH_CHECK=1: evaluate again on each hit of an epoch cache, and panic if the
    /// value differs.
    pub is_epoch_checked: bool,
}

pub(crate) fn eval(
    evaluate: impl Fn(&mut Machine<'_>) -> Outcome<Id> + Send + Sync + 'static,
) -> Eval {
    Arc::new(evaluate)
}

pub(crate) fn member(
    test: impl Fn(&mut Machine<'_>, Id) -> Outcome<bool> + Send + Sync + 'static,
) -> Member {
    Arc::new(test)
}

pub(crate) fn parts(
    run: impl Fn(&mut Machine<'_>) -> Outcome<()> + Send + Sync + 'static,
) -> Parts {
    Arc::new(run)
}

pub(crate) fn bool_id(value: bool) -> Id {
    Id::from(value)
}

pub(crate) fn check_boolean(value: Id) -> Outcome<Id> {
    if value == TRUE || value == FALSE {
        Ok(value)
    } else {
        Err(Bail("expected a boolean"))
    }
}

/// What a fused node may read of a compiled expression without calling it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Shape {
    Other,
    Constant(Id),
    /// An unprimed variable, which fails while unassigned.
    Current(u32),
    Slot(u32),
    /// A bound name whose values are integers, as a name bound over an interval's are.
    IntSlot(u32),
    /// `f[i]`, with `f` an unprimed variable and `i` a bound name.
    ApplyVar {
        variable: u32,
        slot: u32,
        is_int: bool,
    },
    /// `f[i][j]`, with `f` an unprimed variable and `i` and `j` bound names.
    ApplyVar2 {
        variable: u32,
        slot: u32,
        second: u32,
    },
    /// `r.f`, with `r` a bound name.
    Field {
        slot: u32,
        key: Id,
    },
    /// TLCGet of a simulation's run, which evaluates only where its parts read
    /// (`builtins::SimulationRun`).
    SimulationRun(builtins::SimulationRun),
}

impl Shape {
    pub(crate) fn slot(self) -> Option<(u32, bool)> {
        match self {
            Shape::Slot(slot) => Some((slot, false)),
            Shape::IntSlot(slot) => Some((slot, true)),
            _ => None,
        }
    }
}

/// A set filter's parts, for a Cardinality of it that counts without building it.
pub(crate) struct Filter {
    pub set: Eval,
    pub stream: Option<lazy::Reference>,
    pub slots: Vec<u32>,
    pub tuple: bool,
    pub predicate: predicate::Test,
    pub reject: Option<predicate::Reject>,
}

impl Filter {
    // SetPredValue enumerates its lazy input without converting that input to a SetEnumValue.
    pub(crate) fn elements(&self, machine: &mut Machine<'_>) -> Outcome<(Option<Id>, Vec<Id>)> {
        if let Some(reference) = &self.stream {
            return Ok((None, reference(machine)?.stream(machine)?));
        }
        let set = nodes::evaluate_set(machine, &self.set, "filtered a non-set")?;
        Ok((Some(set), machine.store.set_elements(set).to_vec()))
    }
}

/// A compiled expression, with what `compile.ts`'s `Compiled` and `LazySet` say of it.
#[derive(Clone)]
pub struct Compiled {
    pub(crate) eval: Eval,
    pub footprint: Footprint,
    /// Whether evaluating it costs more than looking it up, so that caching it pays.
    pub(crate) is_costly: bool,
    /// For a set: whether TLC's value is a normalized set, enumerated in its order.
    pub(crate) is_normalized: bool,
    /// For a set: whether TLC's value is a set enumeration, and whether each element's is.
    pub(crate) is_enumerated: bool,
    pub(crate) are_elements_enumerated: bool,
    /// For a set: whether TLC's value is known to stream its elements as its normalized set does,
    /// which a UNION or `\cup` TLC keeps lazy doesn't (`isStreamedApart`), and a value of unknown
    /// provenance, such as a bound name's, may not; whether each of its elements is; and whether
    /// each element of those is, which a UNION's elements are.
    pub(crate) is_in_order: bool,
    pub(crate) are_elements_in_order: bool,
    pub(crate) are_elements_of_elements_in_order: bool,
    /// Whether the value is always TRUE or FALSE.
    pub(crate) is_boolean: bool,
    pub(crate) is_constant: bool,
    /// Nat, Int, STRING, Seq(S), or a union with one of them, which the engine only tests.
    pub(crate) infinite: Option<&'static str>,
    /// For Nat, Int or STRING itself: the store's name of it, which a set that holds it as an
    /// element takes as its value (`tla_values::store::NAT`).
    pub(crate) infinite_value: Option<i32>,
    /// For a set built from others, such as `SUBSET S` or `S \X T`: whether one of them may be
    /// one the engine only tests, which would make it one TLC can't enumerate either.
    pub(crate) has_infinite_part: bool,
    /// Membership, when the engine can test it without building the set.
    pub(crate) member: Option<Member>,
    /// What TLC evaluates to make the set's value, its parts in TLC's order.
    pub(crate) parts: Option<Parts>,
    pub(crate) shape: Shape,
    /// For `a..b`: its bounds, which a quantifier over it counts through without the set.
    pub(crate) interval: Option<(Eval, Eval)>,
    pub(crate) filter: Option<Arc<Filter>>,
    /// For a boolean: the fused predicate a parent can walk in place of calling it.
    pub(crate) predicate: Option<Arc<predicate::Predicate>>,
    /// For a set TLC keeps lazy: the interpreter's value of it, which says the order TLC
    /// enumerates it in.
    pub(crate) reference: Option<lazy::Reference>,
    /// Whether TLC keeps the value it evaluates for later uses (`LazyValue`), as it keeps an
    /// argument or a LET definition named more than once, where a use before may have cached a
    /// set it holds as its normalized set (`Lazy::Kept`).
    pub(crate) is_kept: bool,
    /// For a set enumeration whose first element is a set TLC keeps lazy: that element's value
    /// and reference. TLC's sort compares each element after the first as the receiver, which
    /// caches it as its normalized set, and leaves the first as built (`ValueVec.sort`), which a
    /// name bound to it streams.
    pub(crate) unsorted_first: Option<(Eval, Option<lazy::Reference>)>,
    /// For a set enumeration some of whose elements TLC keeps lazy: each element's reference, in
    /// the order written, which a UNION of the set streams (`Lazy::Enumeration`).
    pub(crate) element_references: Option<Vec<lazy::Reference>>,
    /// For a set TLC keeps lazy that may stream apart: whether its reference is TLC's value as
    /// built, each set it is built of streaming in order or so referenced, where the reference of
    /// a set the engine holds as an id, such as a variable's the initial predicate assigned, is
    /// its normalized set, as is a variable's that `x' \in S` binds to an element S holds as
    /// built, which only `Machine::held` follows.
    pub(crate) is_reference_exact: bool,
    /// For `SUBSET S`: S, which `\subseteq` of two power sets compares in their place.
    pub(crate) subset_base: Option<Box<Compiled>>,
    /// For a set: whether TLC keeps it lazy, not as a set enumeration or an interval
    /// (`Reducible`), such as SUBSET S, [S -> T], [a : S], S \X T, or the union of one with
    /// another.
    pub(crate) is_irreducible: bool,
    /// For a set: whether TLC is known to hold it as a set enumeration (`Reducible`) though the
    /// compiled set isn't one, as a model's constant, or a union, intersection or difference TLC
    /// reduces.
    pub(crate) is_reducible: bool,
}

impl Compiled {
    /// Whether the set may be one TLC can't enumerate.
    pub(crate) fn may_be_infinite(&self) -> bool {
        self.infinite.is_some() || self.has_infinite_part
    }

    pub fn eval(&self) -> &Eval {
        &self.eval
    }

    /// Whether the expression reads what TLCGet reads or prints, which only the search keeps.
    pub fn reads_search(&self) -> bool {
        self.footprint
            .slots
            .iter()
            .any(|slot| SEARCH_SLOTS.contains(slot))
    }

    /// Whether the expression reads TLCGet("level"), of the state or, primed, of the next.
    pub fn reads_level(&self) -> bool {
        self.footprint
            .slots
            .iter()
            .any(|&slot| slot == LEVEL_SLOT || slot == NEXT_LEVEL_SLOT)
    }

    /// Whether the expression reads TLCGet("distinct"), which only the search keeps.
    pub fn reads_distinct(&self) -> bool {
        self.footprint.slots.contains(&DISTINCT_SLOT)
    }

    /// Whether the expression sets or reads TLC's registers.
    pub fn uses_registers(&self) -> bool {
        self.footprint.slots.contains(&REGISTER_SLOT)
    }

    /// Whether the expression reads TLCGet("diameter").
    pub fn reads_diameter(&self) -> bool {
        self.footprint.slots.contains(&DIAMETER_SLOT)
    }

    pub(crate) fn is_printing(&self) -> bool {
        self.footprint.slots.contains(&PRINT_SLOT)
    }

    /// Whether TLC keeps the set lazy, as a class that builds itself into a set enumeration
    /// element by element where it must (`toSetEnum`): not an interval, a power set, a set it
    /// can't enumerate or one it reduces.
    pub(crate) fn is_kept_lazy(&self) -> bool {
        self.interval.is_none()
            && self.subset_base.is_none()
            && self.infinite.is_none()
            && !self.is_reducible
            && !self.is_enumerated
            && (self.is_irreducible || self.reference.is_some())
    }

    /// The set as an element of a tuple, a record or a set enumeration, which TLC compares,
    /// fingerprints and prints as its normalized set where it keeps it lazy (`convertAndCache`),
    /// built in a ValueVec that fails past `TLCGlobals.setBound` elements: the engine, which
    /// holds the value built, doesn't follow such a set past that many.
    pub(crate) fn held(self) -> Compiled {
        if !self.is_kept_lazy() || self.may_be_infinite() {
            return self;
        }
        let built = self.eval.clone();
        self.with_eval(eval(move |machine| {
            let id = built(machine)?;
            if machine.store.kind_of(id) == KIND_SET
                && machine.store.size_of(id) as usize > tla_values::SET_BOUND
            {
                return Err(Bail(
                    "unsupported: a set TLC keeps lazy past TLCGlobals.setBound elements, held in a value",
                ));
            }
            Ok(id)
        }))
    }

    /// Fails where TLC fails to enumerate the set, of `size` elements, as a bound of a quantifier,
    /// a CHOOSE or a set map (`Tool.contexts`, OPCODE_bc): it takes them in normalized order
    /// (`EnumerableValue.elements(Ordering.NORMALIZED)`), which builds a set it keeps lazy, such as
    /// `S \X T`, `[S -> T]`, `[a : S]`, or a `\cup` or UNION it doesn't reduce, into a set
    /// enumeration (`toSetEnum`), whose ValueVec fails once it holds `TLCGlobals.setBound`
    /// elements and is given another, duplicates and all (`ValueVec.ensureCapacity`). An interval
    /// builds its array at once (`IntervalValue.toSetEnum`), a power set enumerates itself in
    /// that order (`SubsetValue.elements(Ordering)`), and a set enumeration is built already.
    // Whether a set's first and last elements, in normalized order, are sets.
    fn holds_only_sets(&self, machine: &Machine<'_>, id: Id) -> bool {
        let size = machine.store.size_of(id);
        machine.store.kind_of(id) == KIND_SET
            && size > 0
            && machine.store.kind_of(machine.store.element_at(id, 0)) == KIND_SET
            && machine
                .store
                .kind_of(machine.store.element_at(id, size - 1))
                == KIND_SET
    }

    pub(crate) fn check_enumerated(
        &self,
        machine: &mut Machine<'_>,
        id: Id,
        size: u32,
    ) -> Outcome<()> {
        if self.interval.is_some()
            || self.subset_base.is_some()
            || self.infinite.is_some()
            || self.is_reducible
            || self.is_enumerated
        {
            return Ok(());
        }
        let is_past = size as usize > tla_values::SET_BOUND;
        if !self.is_kept_lazy() {
            // A set of unknown provenance, such as a bound name's or a function's value, may be
            // one TLC keeps lazy. A variable's is one TLC fingerprinted, which built it. One of
            // sets is taken for a power set, which enumerates itself in normalized order.
            return if !is_past
                || matches!(self.shape, Shape::Current(_))
                || self.holds_only_sets(machine, id)
            {
                Ok(())
            } else {
                Err(Bail(UNKNOWN_BOUND_PAST_SET_BOUND))
            };
        }
        if is_past {
            return Err(tla_values::SET_BOUND_EXCEEDED);
        }
        if self.is_in_order {
            return Ok(());
        }
        // A set that may stream an element twice adds it to the ValueVec twice.
        let Some(reference) = &self.reference else {
            return Ok(());
        };
        let lazy = reference(machine)?;
        if lazy.streamed_at_most(machine)? <= tla_values::SET_BOUND as u128 {
            return Ok(());
        }
        if lazy.stream(machine)?.len() > tla_values::SET_BOUND {
            return Err(tla_values::SET_BOUND_EXCEEDED);
        }
        Ok(())
    }

    /// The value as TLC keeps it for later uses, and so each element of a set enumeration of it,
    /// which its sort leaves as built only where it is the first (`ValueVec.sort`).
    pub(crate) fn kept(compiled: Compiled) -> Compiled {
        Compiled::kept_from(compiled, false)
    }

    /// The value as TLC keeps it for later uses, or, with `is_assigned`, as TLC builds it until
    /// the initial predicate completes a state, as a constant definition the initial predicate
    /// only assigns to variables (`Compiler::initial_assignments`).
    fn kept_from(compiled: Compiled, is_assigned: bool) -> Compiled {
        if compiled.is_kept {
            return compiled;
        }
        let kept = |reference: lazy::Reference| {
            Arc::new(move |machine: &mut Machine<'_>| {
                let built = reference(machine)?;
                Ok(if is_assigned && machine.is_before_initial_state {
                    built
                } else {
                    built.kept()
                })
            }) as lazy::Reference
        };
        Compiled {
            reference: compiled.reference.clone().map(kept),
            element_references: compiled
                .element_references
                .clone()
                .map(|references| references.into_iter().map(kept).collect()),
            is_kept: true,
            ..compiled
        }
    }

    fn with_predicate(self, predicate: predicate::Predicate) -> Compiled {
        Compiled {
            predicate: Some(Arc::new(predicate)),
            ..self
        }
    }

    fn with_eval(&self, eval: Eval) -> Compiled {
        Compiled {
            eval,
            shape: Shape::Other,
            predicate: None,
            ..self.clone()
        }
    }
}

pub(crate) fn leaf(eval: Eval, footprint: Footprint) -> Compiled {
    Compiled {
        eval,
        footprint,
        is_costly: false,
        is_normalized: true,
        is_enumerated: false,
        are_elements_enumerated: false,
        is_in_order: false,
        are_elements_in_order: false,
        are_elements_of_elements_in_order: false,
        is_boolean: false,
        is_constant: false,
        infinite: None,
        infinite_value: None,
        has_infinite_part: false,
        member: None,
        parts: None,
        shape: Shape::Other,
        interval: None,
        filter: None,
        predicate: None,
        reference: None,
        is_kept: false,
        unsorted_first: None,
        element_references: None,
        is_reference_exact: false,
        subset_base: None,
        is_irreducible: false,
        is_reducible: false,
    }
}

// Where the definition cache keeps a definition compiled in a context.
fn definition_index(context: &Context) -> usize {
    usize::from(context.is_primed) + 2 * usize::from(context.is_init)
}

// A set's reference, or None for a set TLC keeps lazy that the engine has no reference for, such
// as a UNION that streams duplicates.
pub(crate) fn reference_of(set: &Compiled) -> Option<lazy::Reference> {
    if set.reference.is_some() || !set.is_normalized {
        return set.reference.clone();
    }
    let evaluate = set.eval.clone();
    Some(Arc::new(move |machine| {
        Ok(lazy::Lazy::Set(evaluate(machine)?))
    }))
}

// A reference built from components, when every component has one.
pub(crate) fn combine_references(
    components: &[&Compiled],
    build: impl Fn(&mut Machine<'_>, Vec<lazy::Lazy>) -> Outcome<lazy::Lazy> + Send + Sync + 'static,
) -> Option<lazy::Reference> {
    let references: Vec<lazy::Reference> = components
        .iter()
        .map(|component| reference_of(component))
        .collect::<Option<_>>()?;
    Some(Arc::new(move |machine| {
        let mut values = Vec::with_capacity(references.len());
        for reference in &references {
            values.push(reference(machine)?);
        }
        build(machine, values)
    }))
}

// A memo table's lookup, with its keys in an array of their own length.
fn memo_lookup(table: usize, keys: &[Key], inner: Eval) -> Eval {
    fn with<const WIDTH: usize>(table: usize, keys: &[Key], inner: Eval) -> Eval {
        let keys: [Key; WIDTH] = keys.try_into().expect("as many keys as the width");
        eval(move |machine| machine.lookup(table, &keys, &inner))
    }
    match keys.len() {
        1 => with::<1>(table, keys, inner),
        2 => with::<2>(table, keys, inner),
        3 => with::<3>(table, keys, inner),
        4 => with::<4>(table, keys, inner),
        5 => with::<5>(table, keys, inner),
        _ => with::<MAXIMUM_MEMO_WIDTH>(table, keys, inner),
    }
}

// A boolean whose value is a fused predicate.
pub(crate) fn predicate_node(predicate: predicate::Predicate, footprint: Footprint) -> Compiled {
    Compiled {
        is_boolean: true,
        ..leaf(predicate::evaluate(&predicate), footprint)
    }
    .with_predicate(predicate)
}

pub(crate) fn constant(id: Id) -> Compiled {
    Compiled {
        is_constant: true,
        is_boolean: id == TRUE || id == FALSE,
        shape: Shape::Constant(id),
        ..leaf(eval(move |_| Ok(id)), Footprint::default())
    }
}

// --- scopes ---

#[derive(Clone)]
pub(crate) struct Context {
    scope: Option<Rc<Scope>>,
    is_primed: bool,
    /// Whether the expression is part of the initial predicate, where unprimed variables are
    /// assigned.
    is_init: bool,
    /// Whether the engine evaluates the expression exactly when TLC does, so that it may print.
    can_print: bool,
    /// Whether the expression is part of the initial predicate or an action the walk compiles,
    /// which TLC reads through `getInitStates` and `getNextStates` (`guard_retried_effects`).
    is_walked: bool,
    /// The definitions whose bodies the expression is written in, innermost first. An argument
    /// keeps its caller's, so a definition reached again through an argument isn't taken for
    /// recursion.
    expanding: Option<Rc<Expansion>>,
}

// What `may_be_lazy_or_print_within` learned in one walk: the answer for each node it looked
// through without meeting a node on its path again, and how many times it met one again.
#[derive(Default)]
struct LazyWalk {
    answers: HashMap<NodeId, bool>,
    met_again: usize,
}

struct Expansion {
    node: NodeId,
    outer: Option<Rc<Expansion>>,
}

impl Context {
    pub(crate) const ROOT: Context = Context {
        scope: None,
        is_primed: false,
        is_init: false,
        can_print: false,
        is_walked: false,
        expanding: None,
    };

    fn is_expanding(&self, node: NodeId) -> bool {
        let mut expansion = &self.expanding;
        while let Some(current) = expansion {
            if current.node == node {
                return true;
            }
            expansion = &current.outer;
        }
        false
    }

    // The definitions the body of `node` is written in: the caller's and `node`.
    fn expanding_with(&self, node: NodeId) -> Option<Rc<Expansion>> {
        Some(Rc::new(Expansion {
            node,
            outer: self.expanding.clone(),
        }))
    }

    fn primed(&self, is_primed: bool) -> Context {
        Context {
            is_primed,
            ..self.clone()
        }
    }

    fn with_scope(&self, scope: Option<Rc<Scope>>) -> Context {
        Context {
            scope,
            ..self.clone()
        }
    }

    fn without_print(&self) -> Context {
        Context {
            can_print: false,
            ..self.clone()
        }
    }

    // The context a definition's body compiles in: no scope, and the caller's levels.
    fn global(&self, can_print: bool) -> Context {
        Context {
            scope: None,
            can_print,
            ..self.clone()
        }
    }
}

pub(crate) struct Scope {
    name: TextId,
    binding: Binding,
    parent: Option<Rc<Scope>>,
}

enum Binding {
    Slot(u32),
    /// An operator's argument, which TLA+ substitutes for the parameter.
    Argument(Rc<Argument>),
    Operator(Rc<Operator>),
    /// A value, or a function a LET defines, which TLC keeps lazy, with the context it is defined
    /// in and, once a prime reaches it, the function compiled again to read the next state.
    Value {
        compiled: Box<Compiled>,
        lazy: Option<Rc<LazyFunction>>,
    },
    /// A recursive function defined in a LET, whose body sees the LET's scope, itself included:
    /// the scope that binds it.
    Recursive {
        definition: NodeId,
    },
}

struct Argument {
    expression: NodeId,
    context: Context,
    /// Whether evaluating it at each use gives the value TLC keeps: TLC evaluates a LET
    /// definition or an argument once, at its first use, and keeps the value (`LazyValue`),
    /// where the engine evaluates it at each use. That differs only for one that reads a
    /// register something writes between its uses, so this holds where it is used once or
    /// nothing where it is used may write one.
    is_each_use_alike: bool,
    /// Whether it is named at most once, outside any binder, where it is used, so that the engine
    /// evaluates it at most once where TLC's `LazyValue` computes it once.
    is_read_once: bool,
    /// Whether, read more than once, it may reach a startup definition with effects, which may
    /// have failed as TLC started (`may_reach_startup_definition`), known once it is compiled.
    reaches_startup: Cell<bool>,
    /// Whether TLC keeps its value for later uses that may cache it as its normalized set: an
    /// argument or a LET definition of an expression named more than once
    /// (`Compiled::is_kept`). TLC evaluates a LET of an action or the initial predicate anew at
    /// each use (`Tool.getInitStates`, `Tool.getNextStates`).
    is_kept: bool,
    compiled: RefCell<[Option<Compiled>; 2]>,
    /// For a binding of an instance's scope whose expression closes over that scope: the scope
    /// that binds it, which its context reaches.
    own_scope: RefCell<Weak<Scope>>,
    /// For a LET definition, or an argument of a call, in a constant definition TLC computes as
    /// it starts: the slot that keeps its value from its first use to the LET's or the call's
    /// end. TLC binds it to a `LazyValue`, which `getValue` computes at the first use and keeps
    /// for the others, since `evalConstantDefn` evaluates with a next state (`TLCState.Empty`),
    /// so that a draw or a print in it runs once, where it is first used, and not at all where
    /// it isn't used.
    once_slot: Option<u32>,
    /// For a LET definition of a constructor whose body may print, draw or set a register, which
    /// the LET names only as the function of applications: TLC evaluates each such use with
    /// KeepLazy, so whether it keeps the `FcnLambdaValue` or builds it anew, it evaluates the body
    /// only at each key applied (`is_applied_lazily`).
    is_applied_function: bool,
    /// For a LET definition its LET names once, where it is evaluated at most once: TLC's
    /// `LazyValue` then computes it only at that use, with the use's `EvalControl`, so it is built
    /// as the expression written there would be (`printed_construction_of`).
    is_named_once: bool,
    /// For a LET definition without parameters none of whose uses TLC may evaluate with
    /// `EvalControl.KeepLazy` (`is_used_eagerly_in_let`): whichever use computes its
    /// `LazyValue`, and whether a later use reads the value kept or computes it again, the value
    /// is built as the expression written there would be, and prints so (`deepCopy` and
    /// `deepNormalize` of what Print and PrintT print leave the kept value as it was, and what
    /// normalizes it in place doesn't change its normalized text).
    is_built_alike: bool,
}

// The context an argument's expression compiles in.
fn argument_context(argument: &Argument) -> Context {
    match argument.own_scope.borrow().upgrade() {
        Some(scope) => argument.context.with_scope(Some(scope)),
        None => argument.context.clone(),
    }
}

struct LazyFunction {
    definition: NodeId,
    context: Context,
    primed: RefCell<Option<Compiled>>,
}

#[derive(Clone, Copy)]
enum OperatorBody {
    Node(NodeId),
    /// A builtin passed as an operator, applied to its parameters `$0`, `$1`, ...
    Builtin(Index),
}

struct Operator {
    params: Vec<Param>,
    body: OperatorBody,
    context: Context,
    /// A RECURSIVE operator defined in a LET, whose context binds it: the scope that binds it,
    /// which whoever reaches the operator holds.
    is_recursive: bool,
    own_scope: RefCell<Weak<Scope>>,
}

impl Operator {
    fn new(params: Vec<Param>, body: OperatorBody, context: Context) -> Rc<Operator> {
        Rc::new(Operator {
            params,
            body,
            context,
            is_recursive: false,
            own_scope: RefCell::new(Weak::new()),
        })
    }
}

fn lookup(scope: &Option<Rc<Scope>>, name: TextId) -> Option<Rc<Scope>> {
    let mut current = scope.as_ref();
    while let Some(node) = current {
        if node.name == name {
            return Some(Rc::clone(node));
        }
        current = node.parent.as_ref();
    }
    None
}

fn bind(scope: &Option<Rc<Scope>>, name: TextId, binding: Binding) -> Option<Rc<Scope>> {
    Some(Rc::new(Scope {
        name,
        binding,
        parent: scope.clone(),
    }))
}

// The context an operator binding's body sees: a RECURSIVE one's, or one of an instance's scope
// that closes over that scope, binds the operator itself.
fn operator_context(operator: &Operator) -> Context {
    if operator.is_recursive {
        return operator
            .context
            .with_scope(operator.own_scope.borrow().upgrade());
    }
    match operator.own_scope.borrow().upgrade() {
        Some(scope) => operator.context.with_scope(Some(scope)),
        None => operator.context.clone(),
    }
}

/// An operand of a builtin: an argument as written, or a parameter `$i` of a builtin passed as
/// an operator, which looks like an identifier to what inspects the argument.
#[derive(Clone)]
pub(crate) struct Operand {
    node: NodeId,
    context: Context,
    is_param: bool,
    /// For a builtin applied as an operator argument's body: the slot its parameter is bound to.
    slot: Option<u32>,
}

// --- fixed points ---

// A recursive operator's or function's body compiles again until what it reads settles, and
// meanwhile a call of it reads what it assumes so far. What else is cached as it compiles against
// that assumption holds only while the assumption does: it's dropped when the assumption grows.
struct FixedPoint {
    is_settled: Cell<bool>,
    dependents: RefCell<Vec<Dependent>>,
}

/// A recursive operator: a global one by its definition's node, or one a LET defines by the
/// address of its binding, which the operator's entries keep alive so the address isn't reused.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum OperatorKey {
    Global(NodeId),
    Local(usize),
    /// A global operator with operator parameters, by its position among the specializations
    /// the compiler made of it for the operators its calls pass (`Compiler::specialized`).
    Specialized(usize),
}

impl OperatorKey {
    fn local(operator: &Rc<Operator>) -> Self {
        Self::Local(Rc::as_ptr(operator) as usize)
    }
}

#[derive(Clone, Copy)]
enum Dependent {
    Definition {
        definition: NodeId,
        index: usize,
        entry: u64,
    },
    Operator {
        key: OperatorKey,
        index: usize,
        entry: u64,
    },
    Function {
        key: (NodeId, usize),
        index: usize,
        entry: u64,
    },
}

struct RecursiveOperator {
    entry: u64,
    runtime: usize,
    slots: Vec<u32>,
    is_normalized: Cell<bool>,
    is_enumerated: Cell<bool>,
    assumed: RefCell<Footprint>,
    body_footprint: RefCell<Option<Footprint>>,
    fixed_point: Rc<FixedPoint>,
}

pub(crate) struct RecursiveFunction {
    entry: u64,
    runtime: usize,
    /// The slot of its argument: a tuple where it has several bounds.
    slot: u32,
    /// How many bounds it has: TLC's domain is their product.
    arity: usize,
    domain: Compiled,
    /// Where its body is a function construction, which TLC keeps lazy (`FcnLambdaValue`), the
    /// runtime that applies f[a] to b without building f[a], and the slot of b.
    element: Option<(usize, u32)>,
    /// Where TLC keeps it lazy as it starts and its body prints, the machine's slot of the
    /// function it converts to (`Compiler::kept_lazy_conversion`).
    converted: Option<usize>,
    assumed: RefCell<Footprint>,
    body_footprint: RefCell<Option<Footprint>>,
    fixed_point: Rc<FixedPoint>,
}

impl RecursiveFunction {
    fn footprint(&self) -> Footprint {
        let read = match &*self.body_footprint.borrow() {
            Some(body) => body.without_slots(&[self.slot]),
            None => self.assumed.borrow().clone(),
        };
        self.domain.footprint.merge(&read)
    }
}

type Entries<T> = [Option<T>; 2];
// A recursive operator's entries, with the LET operator its key names, kept alive.
type OperatorEntries = (Option<Rc<Operator>>, Entries<Rc<RecursiveOperator>>);
// A recursive function's entries, keyed by its definition and the scope that binds it.
type FunctionEntries = (Option<Rc<Scope>>, Entries<Rc<RecursiveFunction>>);

/// The compiler of one IR, interning its constants in a store.
pub struct Compiler<'a> {
    ir: &'a Ir,
    pub store: &'a mut Store,
    options: Options,
    program: Program,
    texts: Vec<Option<Vec<u16>>>,
    // A definition compiled unprimed or primed, outside the initial predicate or in it, where a
    // variable's value isn't yet known to stream in order (`is_in_order`).
    definition_cache: HashMap<NodeId, [Option<(u64, Compiled)>; 4]>,
    // The definitions TLC evaluates once at startup, each compiled to read the value it computed
    // then, once compiled.
    startup_definitions: HashMap<NodeId, Option<Compiled>>,
    // The machine's slot each compiled startup definition keeps its value in.
    startup_onces: HashMap<NodeId, usize>,
    recursive_operators: HashMap<OperatorKey, OperatorEntries>,
    /// Each recursive operator with operator parameters compiled for the operators a call
    /// passes it, by its definition's node, which keeps them alive.
    specialized: Vec<(NodeId, Vec<Rc<Operator>>)>,
    recursive_functions: HashMap<(NodeId, usize), FunctionEntries>,
    /// Whether each recursive function definition asked about is one TLC keeps lazy as it starts
    /// and applies printing (`is_kept_lazy_at_startup`).
    kept_lazy: RefCell<HashMap<NodeId, bool>>,
    /// For each definition asked about, whether each definition met names it
    /// (`names_cached`): those on the way to where a walk found it do, and every one a
    /// walk met that ended without finding it doesn't, so a long chain of dependents takes the
    /// chain once in all.
    names_startup: RefCell<HashMap<NodeId, HashMap<NodeId, bool>>>,
    /// The definitions whose bodies may evaluate a startup definition with effects, through the
    /// definitions they name (`definition_reaches_startup`), found once for the whole program.
    reaching_startup: RefCell<Option<HashSet<NodeId>>>,
    /// What `holds_written_records` found of each expression an argument binds.
    written_records: RefCell<HashMap<NodeId, bool>>,
    /// The machine's slot each such function keeps the function it converted to in, which every
    /// application reads from then on (`FcnLambdaValue.fcnRcd`).
    conversion_onces: HashMap<NodeId, usize>,
    /// The references to such a function TLC converts as it evaluates the expression around them
    /// (`converting_operands`), and whether the node being compiled is one.
    converting_references: HashSet<NodeId>,
    is_converting: bool,
    /// For each global recursive function, the scope that binds its name to it, so that a body
    /// naming it locally, as an instance's copy of it does, reaches the same function.
    global_function_scopes: HashMap<NodeId, Rc<Scope>>,
    /// The slots of names bound over intervals, whose values are integers.
    int_slots: HashSet<u32>,
    /// How many ENABLED actions the compiler is inside, whose private next state also holds the
    /// variables ENABLED's rewrite of an instance names (`x@ENABLED`), at slots past the state's.
    enabled_depth: u32,
    /// How many of them are where the engine doesn't evaluate as TLC does, so don't print.
    silent_enabled_depth: u32,
    /// The fields of a record or tuple constructor that hold an INSTANCE fact literal TLC did
    /// not initialize, where what reads the constructor reads none of them: each compiles to a
    /// value nothing reads (`with_null_substituted`).
    null_substituted: Vec<NodeId>,
    /// The variables an ENABLED's next state holds: the state's and those past it.
    variable_extent: usize,
    /// The name EXCEPT binds `@` to: its text, or one no text has if the IR holds none.
    at: TextId,
    depth: u32,
    // The unsettled fixed points the compiles under way have read, innermost first.
    reads: Option<Vec<Rc<FixedPoint>>>,
    /// The walks whose first step is a guard `f[k] = c`, by the address of their step, each kept
    /// alive so no other step takes its address (`walker::Leading`).
    leading_guards: HashMap<usize, (Step, walker::Leading)>,
    /// The nodes of Next's walk that make up an action atom, each with the bit a walk through it
    /// sets on the step it takes and the values it fixes (`pieces.rs`).
    pub(crate) pieces: Vec<pieces::Piece>,
    /// The `\E`s of Next the walk being compiled is inside: each one's node, the position of a
    /// bound and the slot its name takes.
    pub(crate) binders: Vec<(NodeId, usize, u32)>,
    // The fused predicate of each walk whose first step is a guard, by the walk's address.
    first_guards: HashMap<usize, (Step, predicate::Predicate)>,
    /// The bodies of recursive functions an action applies, each walked once for what the walk
    /// knows where it applies it (`walker::WalkedFunction`).
    walked_functions: Vec<walker::WalkedFunction>,
    /// The bodies of RECURSIVE operators an action applies, each walked once likewise
    /// (`walker::WalkedOperator`).
    walked_operators: Vec<walker::WalkedOperator>,
    // What cached compiles read of fixed points that hadn't settled when they compiled.
    provisional: HashMap<u64, Vec<Rc<FixedPoint>>>,
    entry_count: u64,
    /// How many continuations the walk being compiled has compiled for what its paths know.
    specialisations: usize,
    /// Whether an expression reads TLCGet("distinct"), whose slot the search must then set.
    pub is_distinct_read: bool,
    /// Whether an expression reads TLCGet("diameter"), which only the liveness checker sets.
    pub is_diameter_read: bool,
    /// Whether an expression of a simulation reads TLCGet("diameter"), the number of the trace
    /// the simulation then sets for each trace.
    pub is_simulated_diameter_read: bool,
    /// Whether the spec reads the counts of TLC's search the search keeps as it goes
    /// (`Search::set_counts`): the states generated, the initial ones, those left on the queue,
    /// and the diameter where the search checks no temporal property.
    pub is_count_read: bool,
    /// Whether the spec reads TLCExt's Trace, which the search then keeps (`Machine::trace`).
    pub is_trace_read: bool,
    /// Whether anything compiled may print, and whether it uses ToString, which ranks strings.
    pub is_printing: bool,
    /// Whether anything compiled may print, draw or write once TLC has started: any such effect
    /// but one written in the body of a definition TLC computes once as it starts, or of an
    /// assumption, and compiled as part of it (`Compiler::note_effect`).
    pub is_printing_past_startup: bool,
    /// The values computed once at startup whose bodies have such an effect: with each of them
    /// computed, no read of one has it again (`Machine::constant_once`).
    pub startup_effect_onces: Vec<usize>,
    /// The body TLC evaluates at startup alone that is being compiled, if one is.
    startup_descent: Option<StartupDescent>,
    /// Ordered warning events may be produced during evaluation.
    pub is_warning: bool,
    /// Whether a walk compiled may warn that an UNCHANGED variable changed (2143), which TLC's
    /// ENABLED warns of (`enabledUnchangedImpl`) where its search may not.
    pub(crate) is_unchanged_warning: bool,
    /// How many startup definitions' bodies are being compiled, where a print the engine can't
    /// tell TLC prints declines rather than prints as the engine holds its value.
    startup_bodies: u32,
    pub is_ranking: bool,
    /// Whether a variable is assigned a set TLC keeps lazy, and whether a set read out of the
    /// state is enumerated in TLC's order: under a VIEW TLC never normalizes the first, so the
    /// second would come in an order the store doesn't keep.
    pub is_lazy_set_held: bool,
    pub is_held_set_enumerated: bool,
    /// For each variable, whether a walk streams a set that reads its value in the step that
    /// assigns it, which only then needs the set it is assigned as TLC built it
    /// (`Machine::held`).
    held_streams: Vec<Arc<AtomicBool>>,
    /// The pruning of the enumeration of `x' \in [D -> T]` for the walk of the membership at a
    /// node, which its conjunction sets as it walks it (`pruned`).
    pruning: Option<(NodeId, pruned::Pruning)>,
    /// The slots of names a walk binds over a set enumeration whose first element TLC keeps lazy,
    /// with that element's value and reference (`Compiled::unsorted_first`).
    unsorted_slots: HashMap<u32, (Eval, Option<lazy::Reference>)>,
    /// Whether the caller reports what the search finds itself (`Settings::is_violation_reported`),
    /// as the native checker does: only then does the engine follow what the interpreter wouldn't
    /// take a search over with, such as TLC's registers, and otherwise declines it as the
    /// TypeScript engine does.
    pub is_native: bool,
    /// Where the Json module's operators read and write their files (`Settings::json_files`).
    pub json_files: crate::search::JsonFiles,
    /// How many workers TLC runs with (`-workers`), which TLCGet("config") reports.
    pub workers: usize,
    /// The caller's computation of a constant definition TLC computes as it starts, where the
    /// engine fails on it (`Settings::adopter`).
    pub adopter: Option<crate::search::Adopter>,
    /// The constant definitions each use of which reads the value TLC keeps
    /// (`Compiler::adopted_definition`), which a walk evaluates rather than walks.
    pub(crate) adopted: HashSet<NodeId>,
    /// The simulation TLC runs (`-simulate`) rather than a search: its actions then print as they
    /// run, TLCGet("config") reads its settings, and TLCGet reads no other key of the search.
    pub simulation: Option<crate::simulate::Simulation>,
    pub(crate) is_defer_legacy: bool,
    pub(crate) has_unsupported_deferred: bool,
    /// Whether anything compiled may build a function TLC keeps lazy, which only the machine that
    /// built it can apply.
    pub is_lambda_built: bool,
    /// The function constructor an application being compiled applies directly, which TLC
    /// evaluates there with KeepLazy and so keeps a `FcnLambdaValue` (`Tool`'s OPCODE_fa and
    /// OPCODE_fc): its domain once, then its body only at the key applied.
    pub(crate) applied_construction: Option<NodeId>,
    /// The nodes of the initial predicate TLC may compute the initial states from rather than
    /// evaluate (`Tool.getInitStates`), and the functions of the applications among them, which
    /// it evaluates with `EvalControl.Init` rather than KeepLazy (OPCODE_fa): a constructor over a
    /// set it reduces it builds at once (OPCODE_fc's `toFcnRcd`), evaluating its body at each key.
    /// The engine applies none of them at the key only (`is_applied_lazily`).
    pub(crate) init_predicates: HashSet<NodeId>,
    /// The filter an equality being compiled compares, which TLC enumerates whole as it compares
    /// it (`compile_filter_compared`).
    pub(crate) converted_filter: Option<NodeId>,
    /// Whether TLCCache caches anything compiled whose value depends on what TLC evaluates first.
    pub is_cached: bool,
    /// Whether anything compiled applies PickSuccessor, which reads the states TLC has seen.
    pub is_picking: bool,
    /// Whether anything compiled applies TLCCache, whose cache is the machine's own, where TLC
    /// keeps one for every worker.
    pub is_tlc_cache_used: bool,
    // The contexts of the instance scopes translated so far.
    scope_contexts: HashMap<Index, Option<Context>>,
    // The definitions the spec names where TLC may cache the value it keeps for a constant
    // definition as its normalized set (`Compiler::normalized_definitions`).
    normalized_definitions: OnceCell<HashMap<NodeId, bool>>,
    /// The variables a Print or PrintT reads as its argument, or within it, whose assignments the
    /// walk notes how they built the value (`walker::Assigned`).
    printed_variables: OnceCell<HashSet<u32>>,
    /// The conjunct the walk is compiling as a guard, with what the walk knows on its path, for a
    /// Print or PrintT that is the conjunct itself to print a variable as its assignment built it.
    print_sources: Option<walker::PrintSources>,
}

// The compilation of a body TLC evaluates as it starts and never again: a constant definition's
// (`processConstantDefns`) or an assumption's. An effect compiled along `path`, the nodes being
// compiled from the body down, each written in the one before, is in a closure only that body's
// evaluation runs. One compiled past a `stray`, a node written elsewhere, such as the body of an
// operator the body applies, may be in a closure the compiler keeps and uses again where the
// search evaluates it.
struct StartupDescent {
    path: Vec<NodeId>,
    strays: u32,
    effects: u32,
}

fn add_read(reads: &mut Vec<Rc<FixedPoint>>, fixed_point: &Rc<FixedPoint>) {
    if !reads.iter().any(|known| Rc::ptr_eq(known, fixed_point)) {
        reads.push(Rc::clone(fixed_point));
    }
}

/// How TLC holds the elements of the SYMMETRY definition's value, which `Tool.getSymmetryPerms`
/// requires to be function records (`FcnRcdValue`), as far as the expression tells.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SymmetryElements {
    /// A set written with no elements.
    None,
    /// Each element is a `FcnRcdValue`.
    FunctionRecords,
    /// Each element is a `FcnRcdValue` that holds its domain as an array of values, never as an
    /// interval: `Permutations`'s, `:>`'s and `@@`'s.
    DomainArrays,
    /// No element is: a tuple, a record, a lazy function, or a value that isn't a function.
    Other,
    /// Elements TLC may hold either way, or some each way.
    Unknown,
}

impl SymmetryElements {
    /// The elements of two sets together.
    fn and(self, other: SymmetryElements) -> SymmetryElements {
        match (self, other) {
            (SymmetryElements::None, elements) | (elements, SymmetryElements::None) => elements,
            (first, second) if first == second => first,
            (SymmetryElements::FunctionRecords, SymmetryElements::DomainArrays)
            | (SymmetryElements::DomainArrays, SymmetryElements::FunctionRecords) => {
                SymmetryElements::FunctionRecords
            }
            _ => SymmetryElements::Unknown,
        }
    }
}

/// What a root of the model compiles from.
#[derive(Clone, Copy, Debug)]
pub enum Root {
    /// A name the configuration gives, by the definition it names.
    Definition(Index),
    /// An expression, such as a property's.
    Expression(NodeId),
    /// `UNCHANGED e`, as an action property's subscript is checked.
    Unchanged(NodeId),
}

impl<'a> Compiler<'a> {
    /// A compiler of the IR, whose store must have been reset to the IR's ranked texts.
    pub fn new(ir: &'a Ir, store: &'a mut Store, options: Options) -> Compiler<'a> {
        Compiler {
            ir,
            store,
            options,
            program: Program {
                width: ir.variables.len(),
                slot_count: SEARCH_SLOTS.len() + 1,
                is_epoch_checked: options.is_epoch_checked,
                random_seed: ir.model.random_seed,
                fingerprint_index: ir.model.fingerprint_index,
                reads_config: ir.may_read_tlc_get("config"),
                ..Program::default()
            },
            texts: vec![None; ir.texts.len()],
            definition_cache: HashMap::new(),
            startup_definitions: ir
                .model
                .startup
                .definitions
                .iter()
                .map(|&index| (ir.definitions[index as usize], None))
                .collect(),
            startup_onces: HashMap::new(),
            recursive_operators: HashMap::new(),
            specialized: Vec::new(),
            recursive_functions: HashMap::new(),
            kept_lazy: RefCell::new(HashMap::new()),
            names_startup: RefCell::new(HashMap::new()),
            reaching_startup: RefCell::new(None),
            written_records: RefCell::new(HashMap::new()),
            conversion_onces: HashMap::new(),
            converting_references: HashSet::new(),
            is_converting: false,
            global_function_scopes: HashMap::new(),
            int_slots: HashSet::new(),
            enabled_depth: 0,
            silent_enabled_depth: 0,
            null_substituted: Vec::new(),
            variable_extent: ir.variables.len(),
            at: ir
                .texts
                .iter()
                .position(|text| &**text == "@")
                .map_or(TextId::MAX - 1, |index| index as TextId),
            depth: 0,
            reads: None,
            leading_guards: HashMap::new(),
            pieces: Vec::new(),
            binders: Vec::new(),
            first_guards: HashMap::new(),
            walked_functions: Vec::new(),
            walked_operators: Vec::new(),
            provisional: HashMap::new(),
            entry_count: 0,
            specialisations: 0,
            is_distinct_read: false,
            is_diameter_read: false,
            is_simulated_diameter_read: false,
            is_count_read: false,
            is_trace_read: false,
            is_printing: false,
            is_printing_past_startup: false,
            startup_effect_onces: Vec::new(),
            startup_descent: None,
            is_warning: false,
            is_unchanged_warning: false,
            startup_bodies: 0,
            is_ranking: false,
            is_lazy_set_held: false,
            is_held_set_enumerated: false,
            held_streams: (0..ir.variables.len())
                .map(|_| Arc::new(AtomicBool::new(false)))
                .collect(),
            pruning: None,
            unsorted_slots: HashMap::new(),
            is_native: false,
            json_files: crate::search::JsonFiles::System,
            workers: 1,
            adopter: None,
            adopted: HashSet::new(),
            simulation: None,
            is_defer_legacy: false,
            has_unsupported_deferred: false,
            is_lambda_built: false,
            applied_construction: None,
            init_predicates: HashSet::new(),
            converted_filter: None,
            is_cached: false,
            is_picking: false,
            is_tlc_cache_used: false,
            scope_contexts: HashMap::new(),
            normalized_definitions: OnceCell::new(),
            printed_variables: OnceCell::new(),
            print_sources: None,
        }
    }

    /// The program the compiled closures run with.
    pub fn finish(self) -> Program {
        Program {
            workers: self.workers,
            ..self.program
        }
    }

    /// Compiles a root of the model, as `createEngineContext` compiles it, with no scope.
    pub fn compile_root(&mut self, root: Root) -> Result<Compiled, CompileError> {
        self.compile_root_printing(root, false)
    }

    /// Compiles the body of the SYMMETRY definition, which TLC evaluates as it starts, where what
    /// it prints and draws counts, with how TLC holds the elements of its value. A set TLC may
    /// keep lazy is one TLC may reject as not a set of functions, so the interpreter takes it. A
    /// set enumeration TLC holds as built (OPCODE_se), whose elements `getSymmetryPerms` checks
    /// for function records one by one: a lazy element is one that isn't, and one TLC compares
    /// with another as it sorts the set only where there are two or more.
    /// Whether TLC holds the value as a `SetEnumValue`, the class `getSymmetryPerms` requires,
    /// comes with it; where it isn't known, nor are the elements.
    pub fn compile_symmetry(
        &mut self,
        body: NodeId,
    ) -> Result<(Compiled, SymmetryElements, bool), CompileError> {
        let is_enumerated = self.is_set_enumeration_value(body, &mut HashSet::new());
        let elements = if is_enumerated {
            self.symmetry_elements(body, &mut HashSet::new())
        } else {
            SymmetryElements::Unknown
        };
        let is_lazy = match self.node(body).1 {
            NodeKind::SetEnumeration(members) if elements != SymmetryElements::Unknown => {
                members.len() > 1
                    && members
                        .iter()
                        .any(|&member| self.may_be_lazy_at_startup(member))
            }
            _ => self.may_be_lazy(body, &mut HashSet::new()),
        };
        // A function definition TLC always holds lazy (OPCODE_rfs) where the elements aren't
        // known is one TLC may reject or compare as it sorts the set.
        let is_lazy = is_lazy
            || (elements == SymmetryElements::Unknown
                && self.names_lazy_function_definition(body, &mut HashSet::new()));
        if is_lazy {
            return unsupported("a symmetry TLC may keep lazy");
        }
        let compiled = self.compile_root_printing(Root::Expression(body), true)?;
        Ok((compiled, elements, is_enumerated))
    }

    // Whether TLC's value of an expression is a `SetEnumValue`: a set enumeration (OPCODE_se), a
    // set map (OPCODE_soa), a filter of a set it reduces (OPCODE_sso), `Permutations`'s value,
    // and the union of two such (`SetEnumValue.cup`).
    fn is_set_enumeration_value(&self, node: NodeId, seen: &mut HashSet<NodeId>) -> bool {
        let (node, kind) = self.node(node);
        if !seen.insert(node) {
            return false;
        }
        let is_enumerated = match kind {
            NodeKind::SetEnumeration(_) | NodeKind::SetMap { .. } => true,
            NodeKind::SetFilter { bound, .. } => {
                self.is_reduced_set(bound.set) || self.is_set_enumeration_value(bound.set, seen)
            }
            NodeKind::Apply { name, args }
                if args.len() == 1 && self.is_plain_builtin(name, "Permutations") =>
            {
                true
            }
            NodeKind::Apply { name, args }
                if args.len() == 2 && self.is_plain_builtin(name, "\\cup") =>
            {
                self.is_set_enumeration_value(args[0], seen)
                    && self.is_set_enumeration_value(args[1], seen)
            }
            NodeKind::Identifier(name) | NodeKind::Apply { name, .. } => self
                .named_body(name)
                .is_some_and(|body| self.is_set_enumeration_value(body, seen)),
            _ => false,
        };
        seen.remove(&node);
        is_enumerated
    }

    // Whether a name is the builtin of this name, as TLC's own module defines it.
    fn is_plain_builtin(&self, name: &Name, builtin: &str) -> bool {
        !name.is_local
            && matches!(name.resolution, Resolution::Builtin(index)
                if self.builtin_name(index) == builtin
                    && self.ir.builtins[index as usize].flags
                        & (Builtin::TABLE | Builtin::DECLINED | Builtin::EXTERNAL_CLASS)
                        == 0)
    }

    // The body of an operator a name resolves to, which TLC evaluates in its place, with its
    // arguments bound to its parameters where it has any.
    fn named_body(&self, name: &Name) -> Option<NodeId> {
        if name.is_local {
            return None;
        }
        let Resolution::Definition(index) = name.resolution else {
            return None;
        };
        let definition = self.definition(self.ir.definitions[index as usize]);
        (matches!(&definition.form, DefinitionForm::Operator(_))
            && definition.flags & Definition::RECURSIVE == 0)
            .then_some(definition.body)
    }

    // How TLC holds the elements of the set an expression's value is, as `getSymmetryPerms`
    // checks them for `FcnRcdValue`s: the elements a set enumeration was built of, those of a
    // filter's or a CHOOSE's set, and `Permutations`'s functions (`TLC.Permutations`).
    fn symmetry_elements(&self, node: NodeId, seen: &mut HashSet<NodeId>) -> SymmetryElements {
        let (node, kind) = self.node(node);
        if !seen.insert(node) {
            return SymmetryElements::Unknown;
        }
        let elements = match kind {
            NodeKind::SetEnumeration(members) => members
                .iter()
                .fold(SymmetryElements::None, |elements, &member| {
                    elements.and(self.symmetry_element(member, seen))
                }),
            NodeKind::SetFilter { bound, .. } => self.symmetry_elements(bound.set, seen),
            // `{x : x \in S}` holds the elements of S as S holds them (OPCODE_soa).
            NodeKind::SetMap { expression, bounds } => {
                match (self.node(*expression).1, bounds.as_slice()) {
                    (NodeKind::Identifier(name), [bound])
                        if name.is_local && bound.pattern == Pattern::Name(name.text) =>
                    {
                        self.symmetry_elements(bound.set, seen)
                    }
                    _ => self.symmetry_element(*expression, seen),
                }
            }
            NodeKind::Apply { name, args }
                if args.len() == 1 && self.is_plain_builtin(name, "Permutations") =>
            {
                SymmetryElements::DomainArrays
            }
            NodeKind::Apply { name, args }
                if args.len() == 2 && self.is_plain_builtin(name, "..") =>
            {
                SymmetryElements::Other
            }
            NodeKind::Apply { name, args }
                if args.len() == 2 && self.is_plain_builtin(name, "\\cup") =>
            {
                self.symmetry_elements(args[0], seen)
                    .and(self.symmetry_elements(args[1], seen))
            }
            // A parameter's argument the body names is a name the engine doesn't follow.
            NodeKind::Identifier(name) | NodeKind::Apply { name, .. } => self
                .named_body(name)
                .map_or(SymmetryElements::Unknown, |body| {
                    self.symmetry_elements(body, seen)
                }),
            _ => SymmetryElements::Unknown,
        };
        seen.remove(&node);
        elements
    }

    // How TLC holds the value of an expression, as `symmetry_elements` asks of each element: a
    // function constructor over sets TLC reduces is built at once as a `FcnRcdValue`, and one
    // over a set it doesn't is kept lazy (OPCODE_fc), as a recursive one is; `:>` and `@@` build
    // `FcnRcdValue`s (`TLC.MakeFcn`, `TLC.CombineFcn`); a tuple, a record, a number, a string and
    // a set are none.
    fn symmetry_element(&self, node: NodeId, seen: &mut HashSet<NodeId>) -> SymmetryElements {
        let (node, kind) = self.node(node);
        match kind {
            NodeKind::FunctionConstruction {
                is_recursive: true, ..
            } => SymmetryElements::Other,
            NodeKind::FunctionConstruction { bounds, .. } => {
                if bounds.iter().any(|bound| self.is_lazy_domain(bound.set)) {
                    SymmetryElements::Other
                } else if self.is_reduced_bounds(bounds) {
                    SymmetryElements::FunctionRecords
                } else {
                    SymmetryElements::Unknown
                }
            }
            NodeKind::Tuple(_)
            | NodeKind::Record(_)
            | NodeKind::Number(_)
            | NodeKind::WideNumber(_)
            | NodeKind::String(_)
            | NodeKind::SetEnumeration(_)
            | NodeKind::SetFilter { .. }
            | NodeKind::SetMap { .. }
            | NodeKind::FunctionSet { .. }
            | NodeKind::RecordSet(_)
            | NodeKind::Product(_) => SymmetryElements::Other,
            NodeKind::Apply { name, args }
                if args.len() == 2
                    && (self.is_plain_builtin(name, ":>") || self.is_plain_builtin(name, "@@")) =>
            {
                SymmetryElements::DomainArrays
            }
            // A number, a string or a boolean a builtin of TLC's own computes.
            NodeKind::Apply { name, .. }
                if self.is_scalar_valued(kind)
                    && matches!(name.resolution, Resolution::Builtin(index)
                        if self.is_plain_builtin(name, self.builtin_name(index))) =>
            {
                SymmetryElements::Other
            }
            _ if !matches!(kind, NodeKind::Apply { .. }) && self.is_scalar_valued(kind) => {
                SymmetryElements::Other
            }
            NodeKind::Choose { set: Some(set), .. } => self.symmetry_elements(*set, seen),
            // A function definition TLC evaluates as the constructor it is: a recursive one is
            // always lazy (OPCODE_rfs), and one that isn't is as `[x \in S |-> e]` (OPCODE_nrfs).
            NodeKind::Identifier(name) if self.function_definition(name).is_some() => {
                match self.function_definition(name) {
                    Some((_, true)) => SymmetryElements::Other,
                    Some((bounds, false)) => {
                        if bounds.iter().any(|bound| self.is_lazy_domain(bound.set)) {
                            SymmetryElements::Other
                        } else if self.is_reduced_bounds(bounds) {
                            SymmetryElements::FunctionRecords
                        } else {
                            SymmetryElements::Unknown
                        }
                    }
                    None => SymmetryElements::Unknown,
                }
            }
            NodeKind::Identifier(name) => match self.named_body(name) {
                Some(body) if seen.insert(node) => {
                    let element = self.symmetry_element(body, seen);
                    seen.remove(&node);
                    element
                }
                _ => SymmetryElements::Unknown,
            },
            _ => SymmetryElements::Unknown,
        }
    }

    // The bounds of the function definition a name resolves to, and whether it is recursive,
    // naming itself; none for one the configuration substitutes for.
    fn function_definition(&self, name: &Name) -> Option<(&'a [Bound], bool)> {
        if name.is_local {
            return None;
        }
        let Resolution::Definition(index) = name.resolution else {
            return None;
        };
        let definition = self.definition(self.ir.definitions[index as usize]);
        match &definition.form {
            DefinitionForm::Function(bounds) if definition.flags & Definition::SUBSTITUTED == 0 => {
                Some((
                    bounds.as_slice(),
                    definition.flags & (Definition::RECURSIVE | Definition::SELF_REFERENTIAL) != 0,
                ))
            }
            _ => None,
        }
    }

    // Whether an expression names, itself or through the definitions it names, a function
    // definition TLC always holds lazy: a recursive one (OPCODE_rfs), or one over a set TLC
    // keeps lazy (OPCODE_nrfs as OPCODE_fc).
    fn names_lazy_function_definition(&self, node: NodeId, seen: &mut HashSet<NodeId>) -> bool {
        let (node, kind) = self.node(node);
        if !seen.insert(node) {
            return false;
        }
        let name = match kind {
            NodeKind::Identifier(name) | NodeKind::Apply { name, .. } => Some(name),
            _ => None,
        };
        if let Some(name) = name {
            if let Some((bounds, is_recursive)) = self.function_definition(name)
                && (is_recursive || bounds.iter().any(|bound| self.is_lazy_domain(bound.set)))
            {
                return true;
            }
            if !name.is_local
                && let Resolution::Definition(index) = name.resolution
                && self.names_lazy_function_definition(
                    self.definition(self.ir.definitions[index as usize]).body,
                    seen,
                )
            {
                return true;
            }
        }
        kind.children()
            .into_iter()
            .any(|child| self.names_lazy_function_definition(child, seen))
    }

    // Whether TLC keeps a set lazy that a function constructor's bound ranges over, so that it
    // keeps the function lazy too (OPCODE_fc): a product, a set of functions or of records, a
    // power set, Seq, and the infinite sets.
    fn is_lazy_domain(&self, set: NodeId) -> bool {
        match self.node(set).1 {
            NodeKind::Product(_) | NodeKind::FunctionSet { .. } | NodeKind::RecordSet(_) => true,
            NodeKind::Apply { name, args } => {
                args.len() == 1
                    && (self.is_plain_builtin(name, "SUBSET") || self.is_plain_builtin(name, "Seq"))
            }
            NodeKind::Identifier(name) => ["Nat", "Int", "Real", "STRING"]
                .iter()
                .any(|builtin| self.is_plain_builtin(name, builtin)),
            _ => false,
        }
    }

    /// Compiles a root of the model where what it prints is printed, as an invariant that prints
    /// is compiled whole.
    pub fn compile_root_printing(
        &mut self,
        root: Root,
        can_print: bool,
    ) -> Result<Compiled, CompileError> {
        self.compile_scoped(root, None, can_print)
    }

    // --- the IR ---

    fn node(&self, node: NodeId) -> (NodeId, &'a NodeKind) {
        let mut id = node;
        loop {
            match &self.ir.nodes.arena[id as usize].kind {
                NodeKind::Reference(target) => id = *target,
                kind => return (id, kind),
            }
        }
    }

    fn text(&self, text: TextId) -> &'a str {
        &self.ir.texts[text as usize]
    }

    fn units(&mut self, text: TextId) -> Vec<u16> {
        let ir = self.ir;
        self.texts[text as usize]
            .get_or_insert_with(|| ir.get_text_units(text))
            .clone()
    }

    fn definition(&self, node: NodeId) -> &'a Definition {
        match self.node(node).1 {
            NodeKind::Definition(definition) => definition,
            _ => panic!("a definition index that names no definition"),
        }
    }

    // Whether the expression is an INSTANCE fact literal TLC did not initialize, or a global
    // definition without parameters that names one: a null in TLC's hands, which its record and
    // tuple constructors hold without reading.
    fn is_uninitialized_literal(&self, node: NodeId) -> bool {
        let mut node = node;
        for _ in 0..32 {
            let name = match self.node(node).1 {
                NodeKind::Identifier(name) => name,
                NodeKind::Apply { name, args } if args.is_empty() => name,
                _ => return false,
            };
            if name.is_local {
                return false;
            }
            match name.resolution {
                Resolution::Builtin(index) => {
                    return self.ir.builtins[index as usize].flags & Builtin::UNINITIALIZED_LITERAL
                        != 0;
                }
                Resolution::Definition(index) => {
                    let definition = self.definition(self.ir.definitions[index as usize]);
                    if !matches!(&definition.form, DefinitionForm::Operator(params) if params.is_empty())
                        || definition.flags & Definition::RECURSIVE != 0
                    {
                        return false;
                    }
                    node = definition.body;
                }
                _ => return false,
            }
        }
        false
    }

    // The fields of a record constructor, or the elements of a tuple constructor, that are an
    // INSTANCE fact literal TLC did not initialize, with the field's name or the element's
    // position: None where the expression is no such constructor.
    fn null_fields(&self, node: NodeId) -> Option<Vec<(NodeId, Result<TextId, usize>)>> {
        let nulls: Vec<_> = match self.node(node).1 {
            NodeKind::Record(fields) => fields
                .iter()
                .filter(|(_, value)| self.is_uninitialized_literal(*value))
                .map(|&(name, value)| (value, Ok(name)))
                .collect(),
            NodeKind::Tuple(elements) => elements
                .iter()
                .enumerate()
                .filter(|(_, element)| self.is_uninitialized_literal(**element))
                .map(|(position, &element)| (element, Err(position + 1)))
                .collect(),
            _ => return None,
        };
        (!nulls.is_empty()).then_some(nulls)
    }

    // Compiles what reads a record or tuple constructor holding a null TLC never initialized
    // where it reads none of the nulls: TLC's RecordValue and TupleValue hold a null without
    // reading it, and `apply` of another field or position, `getDomain`, and `Json.textSerialize`
    // reading the format read only what they name. The nulls compile to a value nothing reads.
    fn with_null_substituted<T>(
        &mut self,
        nulls: &[NodeId],
        compile: impl FnOnce(&mut Self) -> Compiling<T>,
    ) -> Compiling<T> {
        let before = self.null_substituted.len();
        self.null_substituted.extend_from_slice(nulls);
        let compiled = compile(self);
        self.null_substituted.truncate(before);
        compiled
    }

    fn intern(&mut self, value: &Value) -> Compiling<Id> {
        let ir = self.ir;
        Ok(match value {
            Value::Bool(value) => bool_id(*value),
            Value::Int(value) => self.store.int(i64::from(*value))?,
            Value::String(index) => {
                let units = self.units(ir.values.strings[*index as usize]);
                self.store.str(&units)
            }
            Value::ModelValue(index) => {
                let units = self.units(ir.values.strings[*index as usize]);
                self.store.model(&units)
            }
            Value::Set(elements) => {
                let ids = elements
                    .iter()
                    .map(|element| self.intern(element))
                    .collect::<Compiling<Vec<Id>>>()?;
                self.store.set_of(&ids)?
            }
            Value::Function { domain, range, .. } => {
                let keys = domain
                    .iter()
                    .map(|key| self.intern(key))
                    .collect::<Compiling<Vec<Id>>>()?;
                let values = range
                    .iter()
                    .map(|value| self.intern(value))
                    .collect::<Compiling<Vec<Id>>>()?;
                self.store.function_of(&keys, &values)?
            }
            Value::IntervalFunction { low, range, .. } => {
                let keys = (0..range.len() as i64)
                    .map(|offset| self.store.int(i64::from(*low) + offset))
                    .collect::<Outcome<Vec<Id>>>()?;
                let values = range
                    .iter()
                    .map(|value| self.intern(value))
                    .collect::<Compiling<Vec<Id>>>()?;
                self.store.function_of(&keys, &values)?
            }
        })
    }

    fn intern_value(&mut self, index: u32) -> Compiling<Id> {
        let ir = self.ir;
        self.intern(&ir.values.list[index as usize])
    }

    // --- registers and caches ---

    fn allocate_slot(&mut self) -> u32 {
        let slot = self.program.slot_count as u32;
        self.program.slot_count += 1;
        slot
    }

    fn allocate_table(&mut self, width: usize, is_kept: bool) -> usize {
        self.program.memo_tables.push((width, is_kept));
        self.program.memo_tables.len() - 1
    }

    fn allocate_once(&mut self) -> usize {
        self.program.once_count += 1;
        self.program.once_count - 1
    }

    pub(crate) fn allocate_round(&mut self) -> usize {
        self.program.round_count += 1;
        self.program.round_count - 1
    }

    fn allocate_runtime(&mut self) -> usize {
        self.program.recursives.push(None);
        self.program.recursives.len() - 1
    }

    fn next_entry(&mut self) -> u64 {
        self.entry_count += 1;
        self.entry_count
    }

    fn once(&mut self, compiled: Compiled, is_constant: bool) -> Compiled {
        if self.options.is_memo_off {
            return compiled;
        }
        let once = self.allocate_once();
        let inner = compiled.eval.clone();
        let warning_sensitive = compiled.footprint.slots.contains(&WARNING_SLOT);
        Compiled {
            is_costly: false,
            is_constant,
            ..compiled.with_eval(eval(move |machine| {
                if warning_sensitive {
                    machine.once_quiet(once, &inner)
                } else {
                    machine.once(once, &inner)
                }
            }))
        }
    }

    // While one state is expanded, an expression that reads no primed variable has one value for
    // each value of the bound names it reads, however many variables it reads.
    fn cached_in_epoch(&mut self, compiled: Compiled) -> Compiled {
        let key_footprint = compiled.footprint.without_slots(&[WARNING_SLOT]);
        let footprint = &key_footprint;
        if !footprint.primes.is_empty() || footprint.slots.len() > EPOCH_KEYS {
            return compiled;
        }
        let cache = self.program.epoch_count;
        self.program.epoch_count += 1;
        let slots = footprint.slots.clone();
        let inner = compiled.eval.clone();
        Compiled {
            is_costly: false,
            ..compiled.with_eval(eval(move |machine| {
                machine.epoch_lookup(cache, &slots, &inner)
            }))
        }
    }

    // Caches a costly expression by the ids it reads, and evaluates one that reads nothing only
    // once.
    fn cached(&mut self, compiled: Compiled) -> Compiled {
        if compiled.is_printing() || compiled.uses_registers() || self.options.is_memo_off {
            return compiled;
        }
        let key_footprint = compiled.footprint.without_slots(&[WARNING_SLOT]);
        let width = key_footprint.width();
        if width == 0 && !compiled.is_constant {
            return self.once(compiled, true);
        }
        if !compiled.is_costly {
            return compiled;
        }
        if width == 0 {
            let is_constant = compiled.is_constant;
            return self.once(compiled, is_constant);
        }
        if width > MAXIMUM_MEMO_WIDTH {
            return self.cached_in_epoch(compiled);
        }
        let table = self.allocate_table(width, false);
        let footprint = &key_footprint;
        let keys: Vec<Key> = footprint
            .vars
            .iter()
            .map(|&variable| Key::Current(variable))
            .chain(footprint.primes.iter().map(|&variable| Key::Next(variable)))
            .chain(footprint.slots.iter().map(|&slot| Key::Slot(slot)))
            .collect();
        Compiled {
            is_costly: false,
            ..compiled.with_eval(memo_lookup(table, &keys, compiled.eval.clone()))
        }
    }

    fn mark_costly(compiled: Compiled) -> Compiled {
        Compiled {
            is_costly: true,
            ..compiled
        }
    }

    // --- fixed points ---

    fn note_read(&mut self, fixed_point: &Rc<FixedPoint>) {
        if let Some(reads) = &mut self.reads
            && !fixed_point.is_settled.get()
        {
            add_read(reads, fixed_point);
        }
    }

    fn note_cached_read(&mut self, entry: u64) {
        if let Some(fixed_points) = self.provisional.get(&entry).cloned() {
            for fixed_point in &fixed_points {
                self.note_read(fixed_point);
            }
        }
    }

    // Compiles with `run`, adding what it reads of unsettled fixed points to `into` and to what
    // the compile around it reads.
    fn tracking<T>(
        &mut self,
        into: &mut Vec<Rc<FixedPoint>>,
        run: impl FnOnce(&mut Self) -> Compiling<T>,
    ) -> Compiling<T> {
        let outer = self.reads.replace(std::mem::take(into));
        let result = run(self);
        *into = self.reads.take().unwrap_or_default();
        self.reads = outer;
        if let Some(outer) = &mut self.reads {
            for fixed_point in into.iter() {
                add_read(outer, fixed_point);
            }
        }
        result
    }

    // Keeps an entry, which compiled reading `read`, until a fixed point it read that hasn't
    // settled grows, when `drop` takes it out of its cache.
    fn remember_reads(&mut self, entry: u64, read: &[Rc<FixedPoint>], drop: Dependent) {
        let unsettled: Vec<Rc<FixedPoint>> = read
            .iter()
            .filter(|fixed_point| !fixed_point.is_settled.get())
            .cloned()
            .collect();
        if unsettled.is_empty() {
            return;
        }
        for fixed_point in &unsettled {
            fixed_point.dependents.borrow_mut().push(drop);
        }
        self.provisional.insert(entry, unsettled);
    }

    fn drop_dependents(&mut self, fixed_point: &FixedPoint) {
        let dependents = std::mem::take(&mut *fixed_point.dependents.borrow_mut());
        for dependent in dependents {
            match dependent {
                Dependent::Definition {
                    definition,
                    index,
                    entry,
                } => {
                    if let Some(entries) = self.definition_cache.get_mut(&definition)
                        && entries[index].as_ref().map(|known| known.0) == Some(entry)
                    {
                        entries[index] = None;
                    }
                }
                Dependent::Operator { key, index, entry } => {
                    if let Some((_, entries)) = self.recursive_operators.get_mut(&key)
                        && entries[index].as_ref().map(|known| known.entry) == Some(entry)
                    {
                        entries[index] = None;
                    }
                }
                Dependent::Function { key, index, entry } => {
                    if let Some((_, entries)) = self.recursive_functions.get_mut(&key)
                        && entries[index].as_ref().map(|known| known.entry) == Some(entry)
                    {
                        entries[index] = None;
                    }
                }
            }
        }
    }

    // --- compile ---

    fn wrap_compile(
        &mut self,
        run: impl FnOnce(&mut Self) -> Compiling<Compiled>,
    ) -> Compiling<Compiled> {
        self.depth += 1;
        let result = if self.depth > MAXIMUM_EXPANSION {
            unsupported("expansion too deep")
        } else {
            run(self).map(|compiled| {
                if compiled.is_costly || compiled.footprint.width() == 0 {
                    self.cached(compiled)
                } else {
                    compiled
                }
            })
        };
        self.depth -= 1;
        result
    }

    pub(crate) fn compile(&mut self, node: NodeId, context: &Context) -> Compiling<Compiled> {
        if self.null_substituted.contains(&node) {
            return Ok(constant(TRUE));
        }
        self.depth += 1;
        let descended = self.descend(node);
        let result = if self.depth > MAXIMUM_EXPANSION {
            unsupported("expansion too deep")
        } else {
            let inner = if context.can_print && !self.is_evaluated_as_tlc(node, context) {
                context.without_print()
            } else {
                context.clone()
            };
            let converting = self.converting_operands(node);
            self.converting_references.extend(converting);
            let was_converting = std::mem::replace(
                &mut self.is_converting,
                self.converting_references.contains(&node),
            );
            let compiled = self.compile_node(node, &inner);
            self.is_converting = was_converting;
            compiled.and_then(|compiled| {
                // A definition compiled where it may print may be cached, then named where it
                // may not.
                if !context.can_print && compiled.is_printing() {
                    return self.decline_print("Print where TLC evaluates it otherwise");
                }
                Ok(if compiled.is_costly || compiled.footprint.width() == 0 {
                    self.cached(compiled)
                } else {
                    compiled
                })
            })
        };
        self.ascend(descended);
        self.depth -= 1;
        result
    }

    // Notes an effect being compiled: a print, a draw, a register or a file written. Only one in
    // a body TLC evaluates at startup alone, compiled as part of that body, never happens again.
    pub(crate) fn note_effect(&mut self) {
        self.is_printing = true;
        match &mut self.startup_descent {
            Some(descent) if descent.strays == 0 => descent.effects += 1,
            _ => self.is_printing_past_startup = true,
        }
    }

    // Enters a node of a body TLC evaluates at startup alone: whether it is written in the node
    // being compiled, and so part of the body, or `None` outside such a body.
    fn descend(&mut self, node: NodeId) -> Option<bool> {
        let descent = self.startup_descent.as_ref()?;
        let node = self.node(node).0;
        let is_part = descent.strays == 0
            && descent
                .path
                .last()
                .is_some_and(|&parent| self.is_written_in(parent, node));
        let descent = self.startup_descent.as_mut()?;
        if is_part {
            descent.path.push(node);
        } else {
            descent.strays += 1;
        }
        Some(is_part)
    }

    fn ascend(&mut self, descended: Option<bool>) {
        let (Some(is_part), Some(descent)) = (descended, &mut self.startup_descent) else {
            return;
        };
        if is_part {
            descent.path.pop();
        } else {
            descent.strays -= 1;
        }
    }

    // Whether a node is another or written in it, outside the definitions a LET in it makes:
    // the compiler keeps what it compiles of a definition by the definition.
    fn is_written_in(&self, parent: NodeId, node: NodeId) -> bool {
        let mut pending = vec![parent];
        let mut seen = HashSet::new();
        while let Some(next) = pending.pop() {
            let (next, kind) = self.node(next);
            if next == node {
                return true;
            }
            if !seen.insert(next) || matches!(kind, NodeKind::Definition(_)) {
                continue;
            }
            pending.extend(kind.children());
        }
        false
    }

    // Compiles a body TLC evaluates at startup alone, and counts the effects compiled as part of
    // it.
    fn compile_at_startup(
        &mut self,
        body: Option<NodeId>,
        compile: impl FnOnce(&mut Self) -> Compiling<Compiled>,
    ) -> (Compiling<Compiled>, u32) {
        let descent = body.map(|body| StartupDescent {
            path: vec![self.node(body).0],
            strays: 0,
            effects: 0,
        });
        let outer = std::mem::replace(&mut self.startup_descent, descent);
        let compiled = compile(self);
        let descent = std::mem::replace(&mut self.startup_descent, outer);
        (compiled, descent.map_or(0, |descent| descent.effects))
    }

    /// Compiles an assumption, where what it prints is printed: TLC evaluates each as it starts
    /// and never again.
    pub fn compile_assumption(&mut self, node: NodeId) -> Result<Compiled, CompileError> {
        self.compile_at_startup(Some(node), |compiler| {
            compiler.compile_root_printing(Root::Expression(node), true)
        })
        .0
    }

    // A Print where the engine doesn't evaluate as TLC does. ENABLED evaluates its action until
    // the first successor, which often passes no Print: one inside an ENABLED that doesn't print
    // stops the search only where it is evaluated.
    fn decline_print(&self, what: &str) -> Compiling<Compiled> {
        if self.silent_enabled_depth == 0 {
            return unsupported(what);
        }
        Ok(leaf(
            eval(|_| Err(Bail("Print inside ENABLED"))),
            Footprint::default(),
        ))
    }

    fn is_random_set_cardinality(&self, node: NodeId) -> bool {
        let NodeKind::Apply { name, args } = self.node(node).1 else {
            return false;
        };
        if name.is_local
            || !matches!(name.resolution, Resolution::Builtin(index) if self.builtin_name(index) == "Cardinality")
            || args.len() != 1
        {
            return false;
        }
        matches!(self.node(args[0]).1, NodeKind::Apply { name, .. } if !name.is_local && matches!(name.resolution, Resolution::Builtin(index) if self.builtin_name(index) == "RandomSetOfSubsets"))
    }

    // Whether the engine evaluates the operands of an expression exactly when TLC does, as long
    // as it so evaluates the expression.
    fn is_evaluated_as_tlc(&self, node: NodeId, context: &Context) -> bool {
        match self.node(node).1 {
            NodeKind::And(_)
            | NodeKind::Or(_)
            | NodeKind::If { .. }
            | NodeKind::Case { .. }
            | NodeKind::Let { .. }
            | NodeKind::Label { .. }
            | NodeKind::Identifier(_)
            // TLC evaluates each element, field and part once, in the order written, as the
            // engine does.
            | NodeKind::SetEnumeration(_)
            | NodeKind::Tuple(_)
            | NodeKind::Record(_)
            | NodeKind::FieldAccess { .. }
            | NodeKind::Except { .. } => true,
            // TLC applies a function (`Tool`'s OPCODE_fa) by evaluating the function, then the
            // argument, once each, as the engine does, unless the function is one it keeps lazy,
            // whose body it evaluates as it applies it, or one a definition or a LET names.
            NodeKind::FunctionApplication { function, .. } => {
                self.is_applied_as_tlc(*function, context)
            }
            // TLC evaluates the factors, the domain and then the range, or the fields as written,
            // once each, as it builds the set (`Tool`'s OPCODE_cp, OPCODE_sof and OPCODE_sor),
            // as the engine does where a part prints (`compile_lazy_set`).
            NodeKind::Product(_) | NodeKind::FunctionSet { .. } | NodeKind::RecordSet(_) => true,
            // TLC builds a function that isn't recursive over set enumerations and intervals at
            // once, unless it evaluates it as the function of an application (OPCODE_fc's
            // `toFcnRcd`, which no application compiles to print here): the body at each element
            // of the normalized domain, in order, as the engine builds it. One without effects
            // compiles as it did.
            // The constructor an application applies directly, which the engine keeps lazy as
            // TLC does (`is_applied_lazily`).
            NodeKind::FunctionConstruction { .. } if self.applied_construction == Some(node) => {
                true
            }
            NodeKind::FunctionConstruction {
                is_recursive: false,
                bounds,
                ..
            } => {
                self.is_reduced_bounds(bounds)
                    && self.may_have_effect_in(node, context, &mut HashSet::new())
            }
            // TLC filters a set it reduces, an enumeration or an interval, at once, evaluating the
            // predicate for each element in the set's normalized order (OPCODE_sso), and takes
            // the first element of such a set the predicate holds for (OPCODE_bc), as the engine
            // does.
            // A filter an equality enumerates whole (`compile_filter_compared`).
            NodeKind::SetFilter { .. } if self.converted_filter == Some(node) => true,
            NodeKind::SetFilter {
                bound:
                    Bound {
                        pattern: Pattern::Name(_),
                        set,
                    },
                ..
            }
            | NodeKind::Choose {
                pattern: Pattern::Name(_),
                set: Some(set),
                ..
            } => self.is_reduced_set(*set),
            // TLC evaluates the body once for each element of the set, in the set's order, which
            // is the engine's where TLC normalizes the set. Prints under several bounds stay
            // TLC's to check.
            // Of several bounds, TLC evaluates each bound's set once, in order, then the body for
            // each binding, the first bound varying fastest (`Tool.contexts`,
            // `ContextEnumerator`), as the engine does where it holds each set as TLC enumerates
            // it.
            NodeKind::SetMap { bounds, .. } => bounds
                .iter()
                .all(|bound| !self.may_be_lazy(bound.set, &mut HashSet::new())),
            // TLC evaluates the body for each element in the order it enumerates the set, until
            // one decides the quantifier, as the engine does for one bound where the body prints,
            // and for several where it holds each set as TLC enumerates it.
            NodeKind::Forall { bounds, .. } | NodeKind::Exists { bounds, .. } => {
                bounds.len() == 1
                    || bounds
                        .iter()
                        .all(|bound| !self.may_be_lazy(bound.set, &mut HashSet::new()))
            }
            NodeKind::Apply { name, args } => {
                if name.is_local
                    && let Some(found) = lookup(&context.scope, name.text)
                {
                    return matches!(&found.binding, Binding::Operator(operator)
                        if !operator.is_recursive
                            || self.are_arguments_effect_free(args, context));
                }
                match name.resolution {
                    Resolution::Definition(index) => {
                        let node = self.ir.definitions[index as usize];
                        let definition = self.definition(node);
                        matches!(definition.form, DefinitionForm::Operator(_))
                            && if definition.flags & Definition::RECURSIVE == 0 {
                                !context.is_expanding(node)
                            } else {
                                self.are_arguments_effect_free(args, context)
                            }
                    }
                    Resolution::Builtin(index) => match self.builtin_name(index) {
                        // TLC evaluates the operands of a builtin it implements in Java once
                        // each, in order, before it computes (`OpValue.eval`), as the engine
                        // does.
                        "<=>" | "\\equiv" | "+" | "-" | "*" | "\\div" | "%" | "^" | "-." | "<"
                        | ">" | "<=" | ">=" | "=<" | "\\leq" | "\\geq" => {
                            self.ir.builtins[index as usize].flags
                                & (Builtin::TABLE | Builtin::DECLINED)
                                == 0
                        }
                        "$Nop" | "Print" | "PrintT" | "RandomElement" | "RandomSubset" | "RandomSubsetSet" | "RandomSetOfSubsets" | "TestRandomSetOfSubsets" | "TLCEval" | "="
                        | "#" | "~" | "=>" | "TLCSet" | "TLCGet" | "TLCGetOrDefault"
                        | "TLCGetAndSet" | "_Track" | "TLCFP" | "TLCCache" | "Assert" | "AssertEq"
                        | "JsonSerialize" | "ndJsonSerialize" | "JsonDeserialize"
                        | "ndJsonDeserialize" => true,
                        // TLC evaluates the operands, then builds the set, which the engine
                        // builds the same way unless an operand is a set TLC keeps lazy.
                        "\\cup" | "\\cap" | "\\" | "UNION" => !args
                            .iter()
                            .any(|&arg| self.may_be_lazy(arg, &mut HashSet::new())),
                        // TLC evaluates the operands once each, in order, then asks the set
                        // whether it holds the element or the other set, or for its size. The
                        // engine may evaluate a set TLC keeps lazy another way, which shows only
                        // where it prints or draws.
                        // TLC evaluates DOMAIN's operand once, as it evaluates DOMAIN.
                        "DOMAIN" => matches!(args.as_slice(), [function] if self.is_test_draws(*function)),
                        "\\in" | "\\notin" | "\\subseteq" | "Cardinality" => {
                            !args.iter().any(|&arg| {
                                self.may_be_lazy(arg, &mut HashSet::new())
                                    && self.may_have_effect(arg, &mut HashSet::new())
                            })
                        }
                        _ => false,
                    },
                    _ => false,
                }
            }
            _ => false,
        }
    }

    // Whether the arguments of a call of a RECURSIVE operator neither print, draw nor set or
    // read a register: TLC binds each to a `LazyValue` it evaluates where the body first reads
    // the parameter (`Tool.evalAppl`), and the engine before the body
    // (`compile_recursive_call`), which then differs only where one fails, where the engine
    // stops. The body TLC evaluates at each call, with no memo, as the engine does where it
    // may print (`settle_runtime`).
    fn are_arguments_effect_free(&self, args: &[NodeId], context: &Context) -> bool {
        args.iter().all(|&argument| {
            !self.may_have_effect_in(argument, context, &mut HashSet::new())
                && !self.may_read_register(argument, context, &mut HashSet::new())
        })
    }

    // Whether an expression may read TLC's registers, through the definitions and the arguments
    // it names.
    fn may_read_register(
        &self,
        node: NodeId,
        context: &Context,
        seen: &mut HashSet<NodeId>,
    ) -> bool {
        if !seen.insert(node) {
            return false;
        }
        let named = match self.node(node).1 {
            NodeKind::Identifier(name) | NodeKind::Apply { name, .. } if name.is_local => {
                let found = lookup(&context.scope, name.text);
                match found.as_deref().map(|found| &found.binding) {
                    Some(Binding::Argument(argument)) => self.may_read_register(
                        argument.expression,
                        &argument_context(argument),
                        seen,
                    ),
                    Some(Binding::Slot(_)) => false,
                    _ => true,
                }
            }
            NodeKind::Identifier(name) | NodeKind::Apply { name, .. } => match name.resolution {
                Resolution::Builtin(index) => matches!(
                    self.builtin_name(index),
                    "TLCGet" | "TLCGetOrDefault" | "TLCGetAndSet" | "TLCSet"
                ),
                Resolution::Definition(index) => self.may_read_register(
                    self.definition(self.ir.definitions[index as usize]).body,
                    &context.global(false),
                    seen,
                ),
                _ => false,
            },
            NodeKind::Subexpression(_) => true,
            _ => false,
        };
        named
            || self
                .children(node)
                .into_iter()
                .any(|child| self.may_read_register(child, context, seen))
    }

    // Whether TLC applies the function an expression gives as the engine does: one it doesn't
    // keep lazy, written there or given by an operator, a variable or a bound name, rather than a
    // function a definition or a LET names, whose body the engine evaluates as its own.
    // A recursive function TLC keeps lazy as it starts the engine applies as TLC does
    // (`is_kept_lazy_at_startup`).
    fn is_applied_as_tlc(&self, function: NodeId, context: &Context) -> bool {
        if self.is_applied_lazily(function, context) {
            return true;
        }
        match self.node(function).1 {
            NodeKind::Identifier(name) if name.is_local => lookup(&context.scope, name.text)
                .is_some_and(|found| match found.binding {
                    Binding::Slot(_) => true,
                    Binding::Recursive { definition } => self.is_kept_lazy_at_startup(definition),
                    _ => false,
                }),
            NodeKind::Identifier(name) => match name.resolution {
                Resolution::Variable(_) => true,
                Resolution::Definition(index) => {
                    self.is_kept_lazy_at_startup(self.ir.definitions[index as usize])
                }
                _ => false,
            },
            NodeKind::FunctionApplication { .. }
            | NodeKind::Let { .. }
            | NodeKind::Subexpression(_)
            | NodeKind::Reference(_) => false,
            _ => {
                !self.may_be_lazy(function, &mut HashSet::new())
                    && !self.may_keep_effect_lazy(function, context, &mut HashSet::new())
            }
        }
    }

    // Whether an application's function is a constructor of one bound whose body may print,
    // draw or set a register, which TLC evaluates with KeepLazy (`Tool`'s OPCODE_fa) and so keeps
    // a `FcnLambdaValue` whatever its domain (OPCODE_fc): it evaluates the domain as it builds
    // it, then the argument, then the body only at the key (`FcnLambdaValue.apply`), once. The
    // engine builds it lazy there too (`compile_function_construction`), and stops where the key
    // is outside the domain, where TLC prints the whole function. So it is through a LET's name
    // that the LET names only so (`Argument::is_applied_function`).
    pub(super) fn is_applied_lazily(&self, function: NodeId, context: &Context) -> bool {
        self.applied_lazily(function, context).is_some()
    }

    // The constructor `is_applied_lazily` applies.
    pub(super) fn applied_lazily(&self, function: NodeId, context: &Context) -> Option<NodeId> {
        match self.node(function).1 {
            NodeKind::FunctionConstruction { .. } => {
                (!self.init_predicates.contains(&self.node(function).0)
                    && self.is_lazy_construction(function, context))
                .then_some(function)
            }
            NodeKind::Identifier(name) if name.is_local => {
                match &lookup(&context.scope, name.text)?.binding {
                    Binding::Argument(argument) if argument.is_applied_function => {
                        Some(argument.expression)
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn is_lazy_construction(&self, node: NodeId, context: &Context) -> bool {
        matches!(self.node(node).1, NodeKind::FunctionConstruction {
                is_recursive: false,
                bounds,
                body,
            } if matches!(bounds.as_slice(), [Bound { pattern: Pattern::Name(_), .. }])
                && self.may_have_effect_in(*body, context, &mut HashSet::new()))
    }

    // Whether a LET's definition is such a constructor over a domain that evaluates no
    // definition and reads no register, and the LET names it, at least once, only as the
    // function of applications: TLC evaluates it at each use, or keeps it from the first
    // (`LazyValue`), with KeepLazy, and builds no function of it, so each application evaluates
    // the body at its key, once.
    fn is_lazily_applied_definition(
        &self,
        body: NodeId,
        context: &Context,
        roots: impl IntoIterator<Item = NodeId>,
        name: TextId,
    ) -> bool {
        let NodeKind::FunctionConstruction { bounds, .. } = self.node(body).1 else {
            return false;
        };
        if !self.is_lazy_construction(body, context)
            || !bounds
                .iter()
                .all(|bound| self.is_fixed_domain(bound.set, context))
        {
            return false;
        }
        let mut uses = 0;
        roots
            .into_iter()
            .all(|root| self.is_only_function_applied(root, name, &mut uses))
            && uses > 0
    }

    // Whether an expression names a local name only as the function of applications, counting
    // them.
    fn is_only_function_applied(&self, node: NodeId, name: TextId, uses: &mut u32) -> bool {
        let is_name = |named: &Name| named.is_local && named.text == name;
        match self.node(node).1 {
            NodeKind::Identifier(named)
            | NodeKind::OperatorReference(named)
            | NodeKind::Apply { name: named, .. }
                if is_name(named) =>
            {
                false
            }
            NodeKind::Subexpression(_) => false,
            NodeKind::FunctionApplication { function, args } if matches!(self.node(*function).1, NodeKind::Identifier(named) if is_name(named)) =>
            {
                *uses += 1;
                args.iter()
                    .all(|&argument| self.is_only_function_applied(argument, name, uses))
            }
            kind => {
                let filtered = match kind {
                    NodeKind::SetFilter { bound, .. } => Some(bound.set),
                    _ => None,
                };
                kind.children()
                    .into_iter()
                    .chain(filtered)
                    .all(|child| self.is_only_function_applied(child, name, uses))
            }
        }
    }

    // Whether evaluating the function of an application, which TLC does with
    // `EvalControl.KeepLazy` (OPCODE_fa's `setKeepLazy(control)`), may meet a function
    // constructor whose body may print, draw or set a register. That control reaches what the
    // function's expression evaluates, a record's fields, an EXCEPT's parts, a set enumeration a
    // CHOOSE picks from, an operator's body and a LET definition or an argument at its first use
    // (whose `LazyValue` keeps what it computed then), and OPCODE_fc keeps a constructor it meets
    // lazy, evaluating the body only at the keys TLC applies it to, where the engine builds it:
    // `[a |-> [x \in 1..2 |-> PrintT(x)]].a[2]` prints only 2 in TLC. A definition TLC computes
    // as it starts, with `EvalControl.Clear`, it doesn't evaluate here.
    fn may_keep_effect_lazy(
        &self,
        node: NodeId,
        context: &Context,
        seen: &mut HashSet<NodeId>,
    ) -> bool {
        if !seen.insert(node) {
            return false;
        }
        match self.node(node).1 {
            NodeKind::FunctionConstruction { .. }
                if self.may_have_effect_in(node, context, &mut HashSet::new()) =>
            {
                return true;
            }
            // A subexpression selector, which names what it reaches by text, may reach anything.
            NodeKind::Subexpression(_) => return true,
            // A LET's function definition, a constructor TLC keeps lazy likewise.
            NodeKind::Definition(definition)
                if matches!(definition.form, DefinitionForm::Function(_))
                    && self.may_have_effect_in(definition.body, context, &mut HashSet::new()) =>
            {
                return true;
            }
            NodeKind::Identifier(name) | NodeKind::Apply { name, .. } if name.is_local => {
                if let Some(found) = lookup(&context.scope, name.text) {
                    let is_kept = match &found.binding {
                        Binding::Argument(argument) => self.may_keep_effect_lazy(
                            argument.expression,
                            &argument_context(argument),
                            seen,
                        ),
                        Binding::Operator(operator) => match operator.body {
                            OperatorBody::Node(body) => {
                                self.may_keep_effect_lazy(body, &operator.context, seen)
                            }
                            OperatorBody::Builtin(_) => false,
                        },
                        Binding::Value { lazy, .. } => lazy.as_ref().is_some_and(|lazy| {
                            self.may_have_effect_in(
                                self.definition(lazy.definition).body,
                                &lazy.context,
                                &mut HashSet::new(),
                            )
                        }),
                        Binding::Slot(_) | Binding::Recursive { .. } => false,
                    };
                    if is_kept {
                        return true;
                    }
                }
            }
            NodeKind::Identifier(name) | NodeKind::Apply { name, .. } => {
                if let Resolution::Definition(index) = name.resolution {
                    let definition = self.ir.definitions[index as usize];
                    if !self.startup_definitions.contains_key(&definition)
                        && self.may_keep_effect_lazy(definition, &context.global(false), seen)
                    {
                        return true;
                    }
                }
            }
            _ => {}
        }
        self.node(node)
            .1
            .children()
            .into_iter()
            .any(|child| self.may_keep_effect_lazy(child, context, seen))
    }

    // Whether TLC's value of a set is one it reduces (`Reducible`): an enumeration or an interval.
    fn is_reduced_set(&self, set: NodeId) -> bool {
        match self.node(set).1 {
            NodeKind::SetEnumeration(_) => true,
            NodeKind::Apply { name, args } if !name.is_local => {
                args.len() == 2
                    && matches!(name.resolution, Resolution::Builtin(index)
                        if self.builtin_name(index) == ".."
                            && self.ir.builtins[index as usize].flags
                                & (Builtin::TABLE | Builtin::DECLINED)
                                == 0)
            }
            _ => false,
        }
    }

    // Whether evaluating an expression may print, draw, set a TLC register, or write or read a
    // file, itself or through the definitions it names. An operator bound locally may do
    // anything.
    /// Whether evaluating an expression may have an effect, as `may_have_effect` says, in the
    /// scope it is written in: a name the scope binds to an expression, as a LET definition or an
    /// operator's argument is bound, may have what its expression may.
    pub(crate) fn may_have_effect_in(
        &self,
        node: NodeId,
        context: &Context,
        seen: &mut HashSet<NodeId>,
    ) -> bool {
        if self.may_have_effect(node, seen) {
            return true;
        }
        let mut nodes = vec![node];
        let mut walked = HashSet::new();
        while let Some(node) = nodes.pop() {
            if !walked.insert(node) {
                continue;
            }
            if let NodeKind::Identifier(name) = self.node(node).1
                && name.is_local
                && let Some(scope) = lookup(&context.scope, name.text)
            {
                let may = match &scope.binding {
                    Binding::Argument(argument) => self.may_have_effect_in(
                        argument.expression,
                        &argument_context(argument),
                        seen,
                    ),
                    Binding::Operator(_) => true,
                    Binding::Slot(_) | Binding::Value { .. } | Binding::Recursive { .. } => false,
                };
                if may {
                    return true;
                }
            }
            nodes.extend(self.evaluated_children(node));
        }
        false
    }

    // Whether evaluating an expression may evaluate a startup definition with effects
    // (`startup_definitions`), as written, through the definitions it names, or through the
    // LET definitions, arguments and substitutes of `context` it names. A local name it
    // doesn't find there, other than within a definition's body, may be anything, but for a
    // bound variable of a quantifier, CHOOSE, set constructor or function constructor within
    // the expression, which holds a value.
    fn may_reach_startup_definition(
        &self,
        node: NodeId,
        context: Option<&Context>,
        seen: &mut HashSet<NodeId>,
    ) -> bool {
        self.may_reach_startup_definition_within(node, context, seen, &mut Vec::new())
    }

    fn may_reach_startup_definition_within(
        &self,
        node: NodeId,
        context: Option<&Context>,
        seen: &mut HashSet<NodeId>,
        bound: &mut Vec<TextId>,
    ) -> bool {
        let (node, kind) = self.node(node);
        if !seen.insert(node) {
            return false;
        }
        let named = match kind {
            NodeKind::Subexpression(_) => true,
            NodeKind::Identifier(name) | NodeKind::Apply { name, .. } if name.is_local => {
                match context.and_then(|context| lookup(&context.scope, name.text)) {
                    Some(found) => match &found.binding {
                        Binding::Argument(argument) => self.may_reach_startup_definition(
                            argument.expression,
                            Some(&argument_context(argument)),
                            seen,
                        ),
                        Binding::Operator(_) => true,
                        Binding::Slot(_) | Binding::Value { .. } | Binding::Recursive { .. } => {
                            false
                        }
                    },
                    None => {
                        context.is_some()
                            && !(matches!(kind, NodeKind::Identifier(_))
                                && bound.contains(&name.text))
                    }
                }
            }
            NodeKind::Identifier(name)
            | NodeKind::OperatorReference(name)
            | NodeKind::Apply { name, .. } => match name.resolution {
                Resolution::Definition(index) => {
                    self.definition_reaches_startup(self.ir.definitions[index as usize])
                }
                _ => false,
            },
            _ => false,
        };
        if named {
            return true;
        }
        let depth = bound.len();
        let mut bind = |pattern: &Pattern| match pattern {
            Pattern::Name(name) => bound.push(*name),
            Pattern::Tuple(names) => bound.extend(names),
        };
        match kind {
            NodeKind::Forall { bounds, .. }
            | NodeKind::Exists { bounds, .. }
            | NodeKind::SetMap { bounds, .. }
            | NodeKind::FunctionConstruction { bounds, .. } => {
                bounds.iter().for_each(|each| bind(&each.pattern));
            }
            NodeKind::SetFilter { bound: each, .. } => bind(&each.pattern),
            NodeKind::Choose { pattern, .. } => bind(pattern),
            _ => {}
        }
        let reaches = self
            .evaluated_children(node)
            .into_iter()
            .any(|child| self.may_reach_startup_definition_within(child, context, seen, bound));
        bound.truncate(depth);
        reaches
    }

    // Whether a definition is a startup definition with effects or its body, read as written,
    // may evaluate one through the definitions it names (`may_reach_startup_definition` without
    // a context). The answer for every definition is found at the first question, from the
    // definitions each body names, so that asking it at each binding costs nothing more.
    fn definition_reaches_startup(&self, definition: NodeId) -> bool {
        if let Some(reaching) = &*self.reaching_startup.borrow() {
            return reaching.contains(&definition);
        }
        // Each definition's body, read without entering the definitions it names: whether it
        // has a subexpression reference, which may name anything, and which definitions it names.
        let mut named_by: HashMap<NodeId, Vec<NodeId>> = HashMap::new();
        let mut reaching: HashSet<NodeId> = HashSet::new();
        let mut pending: Vec<NodeId> = Vec::new();
        for &definition in self.startup_definitions.keys() {
            if reaching.insert(definition) {
                pending.push(definition);
            }
        }
        for &definition in &self.ir.definitions {
            let mut seen = HashSet::new();
            let mut nodes = vec![self.definition(definition).body];
            let mut is_open = false;
            while let Some(node) = nodes.pop() {
                let (node, kind) = self.node(node);
                if !seen.insert(node) {
                    continue;
                }
                match kind {
                    NodeKind::Subexpression(_) => is_open = true,
                    NodeKind::Identifier(name) | NodeKind::Apply { name, .. } if name.is_local => {}
                    NodeKind::Identifier(name)
                    | NodeKind::OperatorReference(name)
                    | NodeKind::Apply { name, .. } => {
                        if let Resolution::Definition(index) = name.resolution {
                            named_by
                                .entry(self.ir.definitions[index as usize])
                                .or_default()
                                .push(definition);
                        }
                    }
                    _ => {}
                }
                nodes.extend(self.evaluated_children(node));
            }
            if is_open && reaching.insert(definition) {
                pending.push(definition);
            }
        }
        while let Some(definition) = pending.pop() {
            for &namer in named_by.get(&definition).into_iter().flatten() {
                if reaching.insert(namer) {
                    pending.push(namer);
                }
            }
        }
        let answer = reaching.contains(&definition);
        *self.reaching_startup.borrow_mut() = Some(reaching);
        answer
    }

    pub(crate) fn may_have_effect(&self, node: NodeId, seen: &mut HashSet<NodeId>) -> bool {
        if !seen.insert(node) {
            return false;
        }
        let named = match self.node(node).1 {
            NodeKind::Apply { name, .. } if name.is_local => true,
            NodeKind::Identifier(name) | NodeKind::Apply { name, .. } if !name.is_local => {
                match name.resolution {
                    Resolution::Builtin(index) => {
                        EFFECT_BUILTINS.contains(&self.builtin_name(index))
                    }
                    Resolution::Definition(index) => self.may_have_effect(
                        self.definition(self.ir.definitions[index as usize]).body,
                        seen,
                    ),
                    _ => false,
                }
            }
            _ => false,
        };
        named
            || self
                .evaluated_children(node)
                .into_iter()
                .any(|child| self.may_have_effect(child, seen))
    }

    // The expressions directly inside one that evaluating it may evaluate: its `children`, and a
    // filter's set, which those leave out.
    fn evaluated_children(&self, node: NodeId) -> Vec<NodeId> {
        let mut children = self.children(node);
        if let NodeKind::SetFilter { bound, .. } = self.node(node).1 {
            children.push(bound.set);
        }
        children
    }

    /// Whether TLC, having failed to compute a startup definition (`processConstantDefns` swallows
    /// what it throws and keeps the definition as an operator), evaluates it again where it is used
    /// as the engine's evaluation at the use does, should no effect run before it fails: an
    /// operator without parameters whose body neither reads the state, through the definitions it
    /// names, nor has a value that depends on when or how often TLC evaluates it but by printing,
    /// drawing or setting a register, which the search sees run, nor has a value TLC may keep
    /// lazy, which may fail only where TLC applies it. An INSTANCE's copy with substitutions, which
    /// may fail in a substitute, and one that names such a copy, read what the state may hold.
    pub(crate) fn is_retried_at_use(&self, index: Index) -> bool {
        let definition = self.definition(self.ir.definitions[index as usize]);
        let is_print_t = matches!(self.node(definition.body).1,
            NodeKind::Apply { name, .. }
                if !name.is_local && matches!(name.resolution,
                    Resolution::Builtin(index) if self.builtin_name(index) == "PrintT"));
        matches!(&definition.form, DefinitionForm::Operator(params) if params.is_empty())
            && definition.flags & Definition::SUBSTITUTED == 0
            && self.is_repeatable(definition.body, &mut HashSet::new(), true)
            && !self.may_read_state(definition.body, &mut HashSet::new())
            && (self.has_failing_set_print(index)
                || !self.may_be_lazy_or_print(definition.body, &mut HashSet::new(), true)
                // A PrintT's value is TRUE, whatever it prints. The trace evaluator confirms that
                // it fails as TLC does, deep-normalizing its argument first, as `TLC.PrintT` does,
                // which changes how TLC searches the sets it holds unnormalized.
                || is_print_t)
    }

    /// Whether a constant definition TLC computes as it starts (`processConstantDefns`), other
    /// than the startup definitions the engine computes there and their dependents, which it
    /// evaluates there where one they name failed (`Startup::dependents`), names the startup
    /// definition at `index`, as written or through the definitions it names. Where that
    /// definition fails, TLC evaluates it again as it computes the other, with its prints and
    /// draws, which the engine, computing the other only where it is used, has elsewhere.
    pub(crate) fn is_named_at_startup(&self, index: Index) -> bool {
        let target = self.ir.definitions[index as usize];
        // A substitute the configuration gives a definition, which TLC computes again there.
        if self.definition(target).flags & Definition::NAMED_AT_STARTUP != 0 {
            return true;
        }
        let startup = &self.ir.model.startup;
        let listed: HashSet<NodeId> = startup
            .definitions
            .iter()
            .chain(startup.dependents.iter().map(|(_, index)| index))
            .map(|&listed| self.ir.definitions[listed as usize])
            .collect();
        self.ir.definitions.iter().any(|&other| {
            other != target
                && !listed.contains(&other)
                && self.definition(other).flags & Definition::NORMALIZED != 0
                && self.names_cached(self.definition(other).body, target)
        })
    }

    /// `names_definition` from a fresh walk, keeping what it learns of the definitions it met
    /// for the next walk for `target`.
    fn names_cached(&self, body: NodeId, target: NodeId) -> bool {
        let mut cache = self.names_startup.borrow_mut();
        let known = cache.entry(target).or_default();
        let mut met = Vec::new();
        let names = self.names_definition(body, target, &mut HashSet::new(), known, &mut met);
        // A walk that found it may have passed a definition by only as it met it again.
        if !names {
            for definition in met {
                known.insert(definition, false);
            }
        }
        names
    }

    // Whether an expression names a definition, as written or through the definitions it names;
    // a subexpression, which the walk doesn't follow, may.
    /// Whether an expression names `target`, as written or through the definitions it names,
    /// with what `known` holds of the definitions met; those on the way to where it found it go
    /// in `known` as naming it, and every other one met goes in `met`.
    fn names_definition(
        &self,
        node: NodeId,
        target: NodeId,
        seen: &mut HashSet<NodeId>,
        known: &mut HashMap<NodeId, bool>,
        met: &mut Vec<NodeId>,
    ) -> bool {
        let (node, kind) = self.node(node);
        if !seen.insert(node) {
            return false;
        }
        let names = match kind {
            NodeKind::Subexpression(_) => true,
            NodeKind::Identifier(name)
            | NodeKind::OperatorReference(name)
            | NodeKind::Apply { name, .. }
                if !name.is_local =>
            {
                match name.resolution {
                    Resolution::Definition(index) => {
                        let definition = self.ir.definitions[index as usize];
                        definition == target
                            || match known.get(&definition) {
                                Some(&names) => names,
                                None => {
                                    let names = self.names_definition(
                                        self.definition(definition).body,
                                        target,
                                        seen,
                                        known,
                                        met,
                                    );
                                    if names {
                                        known.insert(definition, true);
                                    } else {
                                        met.push(definition);
                                    }
                                    names
                                }
                            }
                    }
                    _ => false,
                }
            }
            NodeKind::SetFilter { bound, .. } => {
                self.names_definition(bound.set, target, seen, known, met)
            }
            _ => false,
        };
        names
            || self
                .children(node)
                .into_iter()
                .any(|child| self.names_definition(child, target, seen, known, met))
    }

    /// The machine's slot a compiled startup definition keeps the value it computed in, which every
    /// use of it reads.
    pub(crate) fn startup_once(&self, index: Index) -> Option<usize> {
        self.startup_onces
            .get(&self.ir.definitions[index as usize])
            .copied()
    }

    /// Whether a startup definition's body is a PrintT of an expression without effects, whose value,
    /// TRUE, the engine knows wherever TLC prints the argument: where the engine can't compute the
    /// argument (its own limit, as enumerating Nat), the trace evaluator, which holds such values
    /// as TLC does, words the print, and must compute it (`Reporter::confirm_startup`). The
    /// evaluator follows how TLC normalizes the function constructors it keeps lazy
    /// (`FcnLambdaValue.deepNormalize`), and declines where it doesn't; not a LAMBDA, which only
    /// an operator's argument is.
    pub(crate) fn is_pure_print(&self, index: Index) -> bool {
        let definition = self.definition(self.ir.definitions[index as usize]);
        let NodeKind::Apply { name, args } = self.node(definition.body).1 else {
            return false;
        };
        !name.is_local
            && matches!(name.resolution, Resolution::Builtin(index)
                if self.builtin_name(index) == "PrintT")
            && args.len() == 1
            && !self.may_have_effect(args[0], &mut HashSet::new())
    }

    // PrintT deep-normalizes its value and then calls toString. A lazy difference with
    // a non-Enumerable left operand, or a lazy union with either operand non-Enumerable,
    // necessarily fails there. An empty Reducible union instead returns its other operand.
    pub(crate) fn has_failing_set_print(&self, index: Index) -> bool {
        let definition = self.definition(self.ir.definitions[index as usize]);
        let NodeKind::Apply { name, args } = self.node(definition.body).1 else {
            return false;
        };
        if name.is_local
            || !matches!(name.resolution, Resolution::Builtin(index)
                if self.builtin_name(index) == "PrintT")
            || args.len() != 1
            || self.may_have_effect(args[0], &mut HashSet::new())
        {
            return false;
        }
        let NodeKind::Apply { name, args } = self.node(args[0]).1 else {
            return false;
        };
        if name.is_local || args.len() != 2 {
            return false;
        }
        let Resolution::Builtin(index) = name.resolution else {
            return false;
        };
        match self.builtin_name(index) {
            "\\" => self.is_non_enumerable_value(args[0]),
            "\\cup" => {
                (self.is_non_enumerable_value(args[0]) && self.keeps_failing_union(args[1]))
                    || (self.is_non_enumerable_value(args[1]) && self.keeps_failing_union(args[0]))
            }
            _ => false,
        }
    }

    fn is_non_enumerable_value(&self, node: NodeId) -> bool {
        if self.is_scalar_literal(node) || self.is_direct_infinite_value(node) {
            return true;
        }
        match self.node(node).1 {
            NodeKind::Tuple(_)
            | NodeKind::Record(_)
            | NodeKind::FunctionConstruction { .. }
            | NodeKind::Lambda { .. } => true,
            NodeKind::Apply { name, .. } if !name.is_local => {
                matches!(name.resolution, Resolution::Builtin(index)
                    if matches!(self.builtin_name(index), "SetToBag" | ":>" | "@@"))
            }
            _ => false,
        }
    }

    /// Whether the expression's value is no set wherever it evaluates: a value written so (as
    /// `is_non_enumerable_value`), a model's constant whose value isn't a set, an integer of
    /// arithmetic, a sequence of Append, Tail or `\o`, or a boolean, so that a function over it
    /// is one TLC keeps lazy (OPCODE_fc builds the function only over Reducible domains).
    pub(crate) fn is_non_set_value(&self, node: NodeId) -> bool {
        if self.is_non_enumerable_value(node) {
            return true;
        }
        match self.node(node).1 {
            NodeKind::And(_)
            | NodeKind::Or(_)
            | NodeKind::Forall { .. }
            | NodeKind::Exists { .. }
            | NodeKind::Except { .. } => true,
            NodeKind::Identifier(name) if !name.is_local => {
                match name.resolution {
                    Resolution::Constant(index) => self.ir.constants[index as usize]
                        .value
                        .is_some_and(|value| {
                            !matches!(self.ir.values.list[value as usize], tla_ir::Value::Set(_))
                        }),
                    _ => false,
                }
            }
            NodeKind::Apply { name, .. } if !name.is_local => {
                matches!(name.resolution, Resolution::Builtin(index)
                    if matches!(self.builtin_name(index),
                        "+" | "-" | "*" | "\\div" | "%" | "-." | "^" | "<" | ">" | "<=" | ">="
                        | "\\leq" | "\\geq" | "=<" | "=" | "#" | "/=" | "~" | "\\lnot"
                        | "\\neg" | "/\\" | "\\/" | "\\land" | "\\lor" | "=>" | "<=>"
                        | "\\equiv" | "\\in" | "\\notin" | "\\subseteq" | "Append" | "Tail"
                        | "\\o" | "\\circ" | "Len" | "Cardinality"))
            }
            _ => false,
        }
    }

    fn keeps_failing_union(&self, node: NodeId) -> bool {
        if self.is_non_enumerable_value(node) {
            return true;
        }
        match self.node(node).1 {
            NodeKind::SetEnumeration(elements) => !elements.is_empty(),
            NodeKind::Product(_) | NodeKind::FunctionSet { .. } | NodeKind::RecordSet(_) => true,
            NodeKind::Apply { name, args } if !name.is_local => {
                matches!(name.resolution, Resolution::Builtin(index)
                    if self.builtin_name(index) == "SUBSET")
                    || (matches!(name.resolution, Resolution::Builtin(index)
                        if self.builtin_name(index) == "..")
                        && matches!(args.as_slice(), [low, high]
                            if matches!((self.node(*low).1, self.node(*high).1),
                                (NodeKind::Number(low), NodeKind::Number(high)) if low <= high)))
            }
            _ => false,
        }
    }

    pub(crate) fn has_direct_infinite_operation(&self, index: Index) -> bool {
        let definition = self.definition(self.ir.definitions[index as usize]);
        let body = self.node(definition.body).1;
        if let NodeKind::Apply { name, args } = body
            && !name.is_local
            && let Resolution::Builtin(builtin) = name.resolution
            && matches!(self.builtin_name(builtin), "PrintT" | "Print" | "Assert")
        {
            return args
                .iter()
                .filter(|&&arg| self.is_direct_infinite_operation(arg))
                .count()
                == 1
                && args.iter().all(|&arg| {
                    self.is_direct_infinite_operation(arg) || self.is_trivial_literal(arg)
                });
        }
        self.is_direct_infinite_operation(definition.body)
    }

    fn is_direct_infinite_operation(&self, node: NodeId) -> bool {
        if let NodeKind::FunctionApplication { function, args } = self.node(node).1 {
            return self.is_direct_infinite_value(*function)
                && !args.is_empty()
                && args.iter().all(|&arg| self.is_trivial_literal(arg));
        }
        let NodeKind::Apply { name, args } = self.node(node).1 else {
            return false;
        };
        if name.is_local {
            return false;
        }
        let Resolution::Builtin(index) = name.resolution else {
            return false;
        };
        if self.builtin_name(index) == "@@"
            && args.len() == 2
            && args.iter().any(|&arg| self.is_direct_infinite_value(arg))
            && args.iter().all(|&arg| self.is_total_merge_argument(arg))
        {
            return true;
        }
        if !matches!(
            self.builtin_name(index),
            "+" | "-"
                | "*"
                | "\\div"
                | "%"
                | "^"
                | ".."
                | "-."
                | "<"
                | ">"
                | "<="
                | ">="
                | "Head"
                | "Tail"
                | "Append"
                | "\\o"
                | "@@"
        ) {
            return false;
        }
        args.iter()
            .filter(|&&arg| self.is_direct_infinite_value(arg))
            .count()
            == 1
            && args
                .iter()
                .all(|&arg| self.is_direct_infinite_value(arg) || self.is_trivial_literal(arg))
    }

    fn merge_scalar_kind(&self, node: NodeId) -> Option<u8> {
        match self.node(node).1 {
            NodeKind::Number(_) => Some(KIND_INT),
            NodeKind::String(_) => Some(KIND_STRING),
            NodeKind::Identifier(name) if !name.is_local => {
                matches!(name.resolution, Resolution::Builtin(index)
                    if matches!(self.builtin_name(index), "TRUE" | "FALSE"))
                .then_some(KIND_BOOL)
            }
            NodeKind::Apply { name, args } if !name.is_local => {
                if matches!(name.resolution, Resolution::Builtin(index)
                    if self.builtin_name(index) == "-.")
                    && matches!(args.as_slice(), [arg]
                        if matches!(self.node(*arg).1, NodeKind::Number(number)
                            if *number >= 0))
                {
                    Some(KIND_INT)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    fn is_total_merge_literal_set(&self, node: NodeId) -> bool {
        let NodeKind::SetEnumeration(elements) = self.node(node).1 else {
            return false;
        };
        let Some(&first) = elements.first() else {
            return true;
        };
        let Some(kind) = self.merge_scalar_kind(first) else {
            return false;
        };
        elements
            .iter()
            .all(|&element| self.merge_scalar_kind(element) == Some(kind))
    }

    // CombineFcn converts both arguments inside the Java method. Only constructions that cannot
    // fail or emit effects before those conversions can extend the infinite-operand certificate.
    fn is_total_merge_argument(&self, node: NodeId) -> bool {
        #[derive(Clone, Copy, PartialEq, Eq, Hash)]
        enum Requirement {
            Set,
            Argument,
        }
        use Requirement::{Argument, Set};

        // IR nodes form an arena, so syntax depth must not consume the Rust call stack. A shared
        // node can need both proofs: a tuple is an argument, but cannot be a set operand.
        let mut pending = vec![(node, Argument)];
        let mut checked = HashSet::new();
        while let Some((node, requirement)) = pending.pop() {
            let (node, kind) = self.node(node);
            if !checked.insert((node, requirement)) {
                continue;
            }
            if self.is_total_merge_literal_set(node)
                || (requirement == Argument && self.merge_scalar_kind(node).is_some())
            {
                continue;
            }
            match kind {
                NodeKind::Identifier(name) if !name.is_local => {
                    if !matches!(name.resolution, Resolution::Builtin(index)
                        if matches!(self.builtin_name(index), "Nat" | "Int" | "STRING" | "BOOLEAN"))
                    {
                        return false;
                    }
                }
                NodeKind::Product(factors) => {
                    pending.extend(factors.iter().map(|&factor| (factor, Set)));
                }
                NodeKind::FunctionSet { domain, range } => {
                    pending.extend([(*domain, Set), (*range, Set)]);
                }
                NodeKind::RecordSet(fields) => {
                    pending.extend(fields.iter().map(|&(_, field)| (field, Set)));
                }
                NodeKind::Tuple(elements) if requirement == Argument => {
                    pending.extend(elements.iter().map(|&element| (element, Argument)));
                }
                NodeKind::Record(fields) if requirement == Argument => {
                    pending.extend(fields.iter().map(|&(_, field)| (field, Argument)));
                }
                // An empty single domain proves that no body is evaluated in either phase.
                NodeKind::FunctionConstruction { bounds, .. } if requirement == Argument => {
                    if !matches!(bounds.as_slice(), [bound]
                        if matches!(self.node(bound.set).1, NodeKind::SetEnumeration(elements)
                            if elements.is_empty()))
                    {
                        return false;
                    }
                }
                NodeKind::Apply { name, args } if !name.is_local => {
                    let Resolution::Builtin(index) = name.resolution else {
                        return false;
                    };
                    match (self.builtin_name(index), args.as_slice()) {
                        ("SUBSET" | "Seq", [base]) => pending.push((*base, Set)),
                        ("..", [low, high])
                            if self.merge_scalar_kind(*low) == Some(KIND_INT)
                                && self.merge_scalar_kind(*high) == Some(KIND_INT) => {}
                        (":>", [domain, range]) if requirement == Argument => {
                            pending.extend([(*domain, Argument), (*range, Argument)]);
                        }
                        ("SetToBag", [set])
                            if requirement == Argument && self.is_total_merge_literal_set(*set) => {
                        }
                        _ => return false,
                    }
                }
                _ => return false,
            }
        }
        true
    }

    fn is_direct_infinite_value(&self, node: NodeId) -> bool {
        match self.node(node).1 {
            NodeKind::Identifier(name) if !name.is_local => {
                matches!(name.resolution, Resolution::Builtin(index)
                    if matches!(self.builtin_name(index), "Int" | "Nat" | "STRING"))
            }
            NodeKind::Apply { name, args } if !name.is_local => {
                matches!(name.resolution, Resolution::Builtin(index) if self.builtin_name(index) == "Seq")
                    && matches!(args.as_slice(), [base] if self.is_literal_small_set(*base))
            }
            _ => false,
        }
    }

    fn is_trivial_literal(&self, node: NodeId) -> bool {
        self.is_scalar_literal(node) || self.is_literal_small_set(node)
    }

    fn is_scalar_literal(&self, node: NodeId) -> bool {
        match self.node(node).1 {
            NodeKind::Number(_) | NodeKind::String(_) => true,
            NodeKind::Identifier(name) if !name.is_local => {
                matches!(name.resolution, Resolution::Builtin(index)
                    if matches!(self.builtin_name(index), "TRUE" | "FALSE"))
            }
            NodeKind::Apply { name, args } if !name.is_local => {
                matches!(name.resolution, Resolution::Builtin(index) if self.builtin_name(index) == "-.")
                    && matches!(args.as_slice(), [arg] if matches!(self.node(*arg).1, NodeKind::Number(n) if *n >= 0))
            }
            _ => false,
        }
    }

    fn is_literal_small_set(&self, node: NodeId) -> bool {
        matches!(self.node(node).1, NodeKind::SetEnumeration(elements)
            if elements.len() <= 1 && elements.iter().all(|&element| self.is_scalar_literal(element)))
    }

    // Whether an expression, through the definitions it names, its LET definitions and the bound
    // sets of its filters, has a node `is_found` accepts, given its kind and the builtin it names.
    // A subexpression selector, which names what it reaches by text, may reach anything.
    fn may_reach_kind(
        &self,
        node: NodeId,
        seen: &mut HashSet<NodeId>,
        is_found: &dyn Fn(&NodeKind, Option<&str>) -> bool,
    ) -> bool {
        let (node, kind) = self.node(node);
        if !seen.insert(node) {
            return false;
        }
        let reaches = match kind {
            NodeKind::Subexpression(_) => true,
            NodeKind::Identifier(name)
            | NodeKind::OperatorReference(name)
            | NodeKind::Apply { name, .. }
                if !name.is_local =>
            {
                match name.resolution {
                    Resolution::Builtin(index) => is_found(kind, Some(self.builtin_name(index))),
                    Resolution::Definition(index) => self.may_reach_kind(
                        self.definition(self.ir.definitions[index as usize]).body,
                        seen,
                        is_found,
                    ),
                    _ => is_found(kind, None),
                }
            }
            NodeKind::SetFilter { bound, .. } => {
                is_found(kind, None) || self.may_reach_kind(bound.set, seen, is_found)
            }
            _ => is_found(kind, None),
        };
        reaches
            || self
                .children(node)
                .into_iter()
                .any(|child| self.may_reach_kind(child, seen, is_found))
    }

    // Whether an expression is an application of TestRandomSetOfSubsets.
    pub(crate) fn is_test_draws(&self, node: NodeId) -> bool {
        matches!(self.node(node).1, NodeKind::Apply { name, .. }
            if !name.is_local && matches!(name.resolution, Resolution::Builtin(index)
                if self.builtin_name(index) == "TestRandomSetOfSubsets"))
    }

    // Whether an expression applies TestRandomSetOfSubsets's function to one key.
    pub(crate) fn is_applied_test_draws(&self, node: NodeId) -> bool {
        matches!(self.node(node).1, NodeKind::FunctionApplication { function, args }
            if args.len() == 1 && self.is_test_draws(*function))
    }

    // Whether an argument's expression reads no state: no variable, prime, UNCHANGED or ENABLED
    // in it or in the definitions it names (`may_read_state`), and no local name but a bound
    // value or another argument that reads none.
    fn is_stateless_argument(&self, argument: &Argument, depth: u32) -> bool {
        if depth > 16 || self.may_read_state(argument.expression, &mut HashSet::new()) {
            return false;
        }
        let context = argument_context(argument);
        let mut pending = vec![argument.expression];
        let mut seen = HashSet::new();
        while let Some(node) = pending.pop() {
            let (node, kind) = self.node(node);
            if !seen.insert(node) {
                continue;
            }
            match kind {
                NodeKind::Identifier(name)
                | NodeKind::Apply { name, .. }
                | NodeKind::OperatorReference(name)
                    if name.is_local =>
                {
                    let is_stateless = match lookup(&context.scope, name.text) {
                        Some(found) => match &found.binding {
                            Binding::Slot(_) | Binding::Value { .. } => true,
                            Binding::Argument(inner) => {
                                self.is_stateless_argument(inner, depth + 1)
                            }
                            _ => false,
                        },
                        // A name of the expression's own binders, which `lookup` doesn't find.
                        None => !matches!(kind, NodeKind::Apply { .. }),
                    };
                    if !is_stateless {
                        return false;
                    }
                }
                _ => {}
            }
            pending.extend(self.children(node));
        }
        true
    }

    // Whether an argument's expression may reach a startup definition
    // (`may_reach_startup_definition`).
    fn reaches_startup_definition(&self, argument: &Argument) -> bool {
        !self.startup_definitions.is_empty()
            && self.may_reach_startup_definition(
                argument.expression,
                Some(&argument_context(argument)),
                &mut HashSet::new(),
            )
    }

    // Whether an expression may read the state: a variable, a prime, UNCHANGED or ENABLED in it or
    // in a definition it names, or a definition of an instance something is substituted into,
    // whose substitutes may. A subexpression, which the walk doesn't follow, may.
    fn may_read_state(&self, node: NodeId, seen: &mut HashSet<NodeId>) -> bool {
        let (node, kind) = self.node(node);
        if !seen.insert(node) {
            return false;
        }
        let reads = match kind {
            NodeKind::Prime(_)
            | NodeKind::Unchanged(_)
            | NodeKind::Enabled(_)
            | NodeKind::Subexpression(_) => true,
            NodeKind::Identifier(name)
            | NodeKind::Apply { name, .. }
            | NodeKind::OperatorReference(name)
                if !name.is_local =>
            {
                match name.resolution {
                    Resolution::Variable(_) => true,
                    Resolution::Definition(index) => {
                        let definition = self.definition(self.ir.definitions[index as usize]);
                        definition.flags & Definition::SUBSTITUTED != 0
                            || self.may_read_state(definition.body, seen)
                    }
                    _ => false,
                }
            }
            _ => false,
        };
        reads
            || self
                .children(node)
                .into_iter()
                .any(|child| self.may_read_state(child, seen))
    }

    /// Whether TLC's predicate evaluation of an action is the walk of it as TLC generates its
    /// steps, but for the comparisons of the primed variables: no ENABLED, action composition,
    /// `[A]_v`, `<<A>>_v` or temporal operator inside, through the definitions it names but those
    /// TLC computes as it starts, and no builtin whose value depends on when or how often TLC
    /// evaluates it.
    pub(crate) fn is_walk_repeatable(&self, node: NodeId, seen: &mut HashSet<NodeId>) -> bool {
        self.is_repeatable(node, seen, false)
    }

    // `is_walk_repeatable`, but for Print, PrintT, AssertEq, RandomElement, RandomSubset and
    // TLCSet where `is_effect_seen`.
    fn is_repeatable(
        &self,
        node: NodeId,
        seen: &mut HashSet<NodeId>,
        is_effect_seen: bool,
    ) -> bool {
        let (node, kind) = self.node(node);
        if !seen.insert(node) {
            return true;
        }
        let is_repeatable = match kind {
            NodeKind::Enabled(_)
            | NodeKind::BoxAction { .. }
            | NodeKind::AngleAction { .. }
            | NodeKind::Always(_)
            | NodeKind::Eventually(_)
            | NodeKind::WeakFairness { .. }
            | NodeKind::StrongFairness { .. }
            | NodeKind::Subexpression(_) => false,
            NodeKind::Identifier(name) | NodeKind::Apply { name, .. } if !name.is_local => {
                match name.resolution {
                    Resolution::Builtin(index) => match self.builtin_name(index) {
                        "Print"
                        | "PrintT"
                        | "AssertEq"
                        | "RandomElement"
                        | "RandomSubset"
                        | "RandomSubsetSet"
                        | "RandomSetOfSubsets"
                        | "TestRandomSetOfSubsets"
                        | "TLCSet" => is_effect_seen,
                        name => !matches!(
                            name,
                            "\\cdot"
                                | "TLCGet"
                                | "TLCGetOrDefault"
                                | "TLCGetAndSet"
                                | "_Track"
                                | "TLCCache"
                                | "TLCDefer"
                                | "TLCModelValue"
                                | "JavaTime"
                                | "Trace"
                                | "JsonSerialize"
                                | "ndJsonSerialize"
                                | "JsonDeserialize"
                                | "ndJsonDeserialize"
                        ),
                    },
                    // TLC computes a constant definition once, as it starts.
                    Resolution::Definition(index) => {
                        let definition = self.definition(self.ir.definitions[index as usize]);
                        definition.flags & Definition::NORMALIZED != 0
                            || self.is_repeatable(definition.body, seen, is_effect_seen)
                    }
                    _ => true,
                }
            }
            _ => true,
        };
        is_repeatable
            && kind
                .children()
                .into_iter()
                .all(|child| self.is_repeatable(child, seen, is_effect_seen))
    }

    // Whether TLC may keep the value of an expression lazy, a set it enumerates in its own order
    // or a function it applies anew each time, rather than normalize it as the engine's value is:
    // through the branches and bodies that give the value, any set or function it builds lazily.
    // `seen` holds the nodes being looked through: one met again is a recursion, which may build
    // anything, while one looked through before, as an operator applied twice, answers again.
    fn may_be_lazy(&self, node: NodeId, seen: &mut HashSet<NodeId>) -> bool {
        self.may_be_lazy_or_print(node, seen, false)
    }

    // `may_be_lazy` of the value TLC computes for a definition as it starts (`evalConstantDefn`,
    // with `EvalControl.Clear`): a function constructor that isn't recursive, over set
    // enumerations and intervals, TLC builds at once (OPCODE_fc's `toFcnRcd`, evaluating the body
    // at each element of the domain in order), so only the values its body computes may be lazy.
    fn may_be_lazy_at_startup(&self, node: NodeId) -> bool {
        match self.node(node).1 {
            NodeKind::FunctionConstruction {
                is_recursive: false,
                bounds,
                body,
            } => !self.is_built_at_startup(bounds, *body),
            _ => self.may_be_lazy(node, &mut HashSet::new()),
        }
    }

    // Whether TLC builds a function of these bounds and body as it starts, holding none of it
    // lazy: see `may_be_lazy_at_startup`. A function definition `f[x \in S] == e` that doesn't
    // name itself is the constructor `[x \in S |-> e]` (OPCODE_nrfs).
    fn is_built_at_startup(&self, bounds: &[Bound], body: NodeId) -> bool {
        self.is_reduced_bounds(bounds) && !self.may_be_lazy_at_startup(body)
    }

    // Whether every bound of a function constructor is over a set TLC reduces (`Reducible`), so
    // that it builds the function at once where it doesn't keep it lazy (OPCODE_fc).
    fn is_reduced_bounds(&self, bounds: &[Bound]) -> bool {
        !bounds.is_empty() && bounds.iter().all(|bound| self.is_reduced_set(bound.set))
    }

    // `may_be_lazy`, or, where `is_print_seen`, a value TLC may keep lazy that PrintT prints, which
    // TLC fails on only as PrintT prints it.
    fn may_be_lazy_or_print(
        &self,
        node: NodeId,
        seen: &mut HashSet<NodeId>,
        is_print_seen: bool,
    ) -> bool {
        self.may_be_lazy_or_print_within(node, seen, is_print_seen, &mut LazyWalk::default())
    }

    // `may_be_lazy_or_print`, keeping the answer for each node looked through without meeting a
    // node being looked through (`walk`): an operator a chain of definitions applies twice at
    // each step is looked through once, not once for each path to it. Such an answer is the one
    // any other path gives: meeting a node again only answers true, so a true answer stays true,
    // and a false one looked through everything the node reaches, which a path that met one of
    // them again would have reached it from, meeting it again.
    fn may_be_lazy_or_print_within(
        &self,
        node: NodeId,
        seen: &mut HashSet<NodeId>,
        is_print_seen: bool,
        walk: &mut LazyWalk,
    ) -> bool {
        if let Some(&is_lazy) = walk.answers.get(&node) {
            return is_lazy;
        }
        if !seen.insert(node) {
            walk.met_again += 1;
            return true;
        }
        let met_again = walk.met_again;
        let is_lazy = self.is_lazy_or_print(node, seen, is_print_seen, walk);
        seen.remove(&node);
        if walk.met_again == met_again {
            walk.answers.insert(node, is_lazy);
        }
        is_lazy
    }

    // `may_be_lazy_or_print_within`'s answer for a node it hasn't met on its path.
    fn is_lazy_or_print(
        &self,
        node: NodeId,
        seen: &mut HashSet<NodeId>,
        is_print_seen: bool,
        walk: &mut LazyWalk,
    ) -> bool {
        let mut may_be_lazy_or_print =
            |node: NodeId, seen: &mut HashSet<NodeId>, is_print_seen: bool| {
                self.may_be_lazy_or_print_within(node, seen, is_print_seen, walk)
            };
        match self.node(node).1 {
            NodeKind::FunctionConstruction { .. }
            | NodeKind::Lambda { .. }
            | NodeKind::FunctionSet { .. }
            | NodeKind::RecordSet(_) => true,
            NodeKind::If {
                consequent,
                alternative,
                ..
            } => {
                may_be_lazy_or_print(*consequent, seen, is_print_seen)
                    || may_be_lazy_or_print(*alternative, seen, is_print_seen)
            }
            NodeKind::Case { arms, other } => {
                arms.iter()
                    .any(|&(_, arm)| may_be_lazy_or_print(arm, seen, is_print_seen))
                    || other.is_some_and(|other| may_be_lazy_or_print(other, seen, is_print_seen))
            }
            NodeKind::Let { body, .. } => may_be_lazy_or_print(*body, seen, is_print_seen),
            NodeKind::SetFilter { bound, .. } => {
                may_be_lazy_or_print(bound.set, seen, is_print_seen)
            }
            NodeKind::SetEnumeration(elements)
            | NodeKind::Tuple(elements)
            | NodeKind::Product(elements) => elements
                .iter()
                .any(|&element| may_be_lazy_or_print(element, seen, is_print_seen)),
            NodeKind::Record(fields) => fields
                .iter()
                .any(|&(_, field)| may_be_lazy_or_print(field, seen, is_print_seen)),
            NodeKind::Identifier(name) if !name.is_local => match name.resolution {
                Resolution::Definition(index) => may_be_lazy_or_print(
                    self.definition(self.ir.definitions[index as usize]).body,
                    seen,
                    is_print_seen,
                ),
                Resolution::Builtin(index) => {
                    matches!(self.builtin_name(index), "Nat" | "Int" | "Real" | "STRING")
                }
                _ => false,
            },
            NodeKind::Apply { name, args } if !name.is_local => match name.resolution {
                Resolution::Builtin(index) => {
                    match self.text(self.ir.builtins[index as usize].name) {
                        "SUBSET" | "Seq" => true,
                        "UNION" | "\\cup" | "\\cap" | "\\" => args
                            .iter()
                            .any(|&arg| may_be_lazy_or_print(arg, seen, is_print_seen)),
                        "$Nop" | "TLCEval" => may_be_lazy_or_print(args[0], seen, is_print_seen),
                        "Print" => args
                            .last()
                            .is_some_and(|&arg| may_be_lazy_or_print(arg, seen, is_print_seen)),
                        "PrintT" => {
                            is_print_seen
                                && args.last().is_some_and(|&arg| {
                                    !self.is_print_settled(arg, &mut Vec::new())
                                        && may_be_lazy_or_print(arg, seen, is_print_seen)
                                })
                        }
                        _ => false,
                    }
                }
                Resolution::Definition(index) => may_be_lazy_or_print(
                    self.definition(self.ir.definitions[index as usize]).body,
                    seen,
                    is_print_seen,
                ),
                _ => true,
            },
            NodeKind::Apply { .. } => true,
            _ => false,
        }
    }

    // Whether a print's argument is a set of functions, records or tuples written there, whose
    // evaluation has no effect, which the print builds as TLC holds it to find whether TLC's
    // `toString` prints it (`Lazy::check_printed`).
    pub(crate) fn is_print_checked(&self, node: NodeId) -> bool {
        matches!(
            self.node(node).1,
            NodeKind::FunctionSet { .. } | NodeKind::RecordSet(_) | NodeKind::Product(_)
        ) && !self.may_have_effect(node, &mut HashSet::new())
    }

    // `is_print_checked`, with no part that may hold a set TLC may fail to print, which the check
    // doesn't follow, itself or as a name bound around it holds (`scope`).
    fn is_print_settled(&self, node: NodeId, scope: &mut Vec<(TextId, bool)>) -> bool {
        self.is_print_checked(node)
            && self
                .node(node)
                .1
                .children()
                .into_iter()
                .all(|part| !self.reads_unsized(part, scope, &mut HashSet::new()))
    }

    // Whether an expression's value, through the definitions it names, may hold a set of tuples,
    // functions or records that TLC may fail to print: TLC prints one by sizing its parts in order
    // up to one it finds empty (`SetOfTuplesValue.toString` and its siblings), and fails on a part
    // it can't size, where the engine, having enumerated the set as TLC does to compute with it,
    // prints what it holds. A set an expression whose value is a boolean, a number or a string
    // consumes, as `Cardinality(S \X T)` does, isn't in its value. A subexpression selector,
    // which names what it reaches by text, may reach anything.
    fn may_hold_unsized(&self, node: NodeId, seen: &mut HashSet<NodeId>) -> bool {
        self.may_hold_unsized_in(node, seen, &mut Vec::new())
    }

    // `may_hold_unsized`, with the LET definitions around the expression (`lets`), each with how
    // many of them its own body sees, which a name bound there names.
    fn may_hold_unsized_in(
        &self,
        node: NodeId,
        seen: &mut HashSet<NodeId>,
        lets: &mut Vec<(TextId, NodeId, usize)>,
    ) -> bool {
        let (node, kind) = self.node(node);
        if !seen.insert(node) || self.is_scalar_valued(kind) {
            return false;
        }
        if let NodeKind::Let {
            definitions, body, ..
        } = kind
        {
            let depth = lets.len();
            let visible = depth + definitions.len();
            for &definition in definitions {
                if let NodeKind::Definition(named) = self.node(definition).1 {
                    lets.push((named.name, definition, visible));
                }
            }
            let is_held = self.may_hold_unsized_in(*body, seen, lets);
            lets.truncate(depth);
            return is_held;
        }
        // TLC writes a \cup, \cap or \ as its enumeration (`SetCupValue.toString` and its
        // siblings), which holds the operands' elements, but not the operands as built.
        if let NodeKind::Apply { name, args } = kind
            && !name.is_local
            && let Resolution::Builtin(index) = name.resolution
            && matches!(self.builtin_name(index), "\\cup" | "\\cap" | "\\")
        {
            return args
                .iter()
                .any(|&arg| self.elements_may_hold_unsized(arg, seen, lets));
        }
        let is_unsized = match kind {
            // TLC sizes the factors in order and stops at an empty one.
            NodeKind::Product(factors) => self.may_size_unsized(factors.iter().copied()),
            // TLC takes [{} -> T] as the one function, and sizes the domain, then the range.
            NodeKind::FunctionSet { domain, range } => {
                !self.is_empty_as_written(*domain)
                    && !(self.is_sized(*domain, &mut HashSet::new())
                        && self.is_sized(*range, &mut HashSet::new()))
            }
            // TLC sizes the fields in the order of their names' ranks.
            NodeKind::RecordSet(fields) => {
                let mut fields = fields.clone();
                fields.sort_by_key(|&(name, _)| name);
                if fields.iter().all(|&(name, _)| name < self.ir.ranked_count) {
                    self.may_size_unsized(fields.into_iter().map(|(_, field)| field))
                } else {
                    fields
                        .iter()
                        .any(|&(_, field)| !self.is_sized(field, &mut HashSet::new()))
                }
            }
            NodeKind::Identifier(name)
            | NodeKind::OperatorReference(name)
            | NodeKind::Apply { name, .. }
                if !name.is_local =>
            {
                matches!(name.resolution, Resolution::Definition(index)
                    if self.may_hold_unsized_in(self.ir.definitions[index as usize], seen, &mut Vec::new()))
            }
            // A LET's definition, evaluated where it is written.
            NodeKind::Identifier(name)
            | NodeKind::OperatorReference(name)
            | NodeKind::Apply { name, .. } => {
                match lets.iter().rev().find(|&&(bound, ..)| bound == name.text) {
                    Some(&(_, definition, visible)) => {
                        let mut outer = lets[..visible].to_vec();
                        self.may_hold_unsized_in(definition, seen, &mut outer)
                    }
                    None => false,
                }
            }
            NodeKind::Subexpression(_) => true,
            _ => false,
        };
        is_unsized
            || self
                .carried_children(kind)
                .into_iter()
                .any(|child| self.may_hold_unsized_in(child, seen, lets))
    }

    // Whether the elements of a set may hold a set `may_hold_unsized` finds: those of a set of
    // functions, records or tuples written there are built of its parts' elements, and those of
    // SUBSET S are sets of S's elements.
    fn elements_may_hold_unsized(
        &self,
        node: NodeId,
        seen: &mut HashSet<NodeId>,
        lets: &mut Vec<(TextId, NodeId, usize)>,
    ) -> bool {
        let parts: Vec<NodeId> = match self.node(node).1 {
            NodeKind::FunctionSet { domain, range } => vec![*domain, *range],
            NodeKind::RecordSet(fields) => fields.iter().map(|&(_, field)| field).collect(),
            NodeKind::Product(factors) => factors.clone(),
            NodeKind::Apply { name, args }
                if !name.is_local
                    && matches!(name.resolution, Resolution::Builtin(index)
                        if self.builtin_name(index) == "SUBSET") =>
            {
                args.clone()
            }
            _ => return self.may_hold_unsized_in(node, seen, lets),
        };
        parts
            .into_iter()
            .any(|part| self.elements_may_hold_unsized(part, seen, lets))
    }

    // Whether an expression's value is a boolean, a number or a string, whatever sets it reads:
    // a literal, a quantifier, a conjunction or disjunction, or a builtin that gives one, such as
    // Cardinality, a membership, a comparison or arithmetic.
    fn is_scalar_valued(&self, kind: &NodeKind) -> bool {
        match kind {
            NodeKind::Number(_)
            | NodeKind::WideNumber(_)
            | NodeKind::Decimal(_)
            | NodeKind::String(_)
            | NodeKind::And(_)
            | NodeKind::Or(_)
            | NodeKind::Forall { .. }
            | NodeKind::Exists { .. }
            | NodeKind::UnboundedQuantifier { .. }
            | NodeKind::Unchanged(_)
            | NodeKind::Enabled(_) => true,
            NodeKind::Apply { name, .. } if !name.is_local => matches!(
                name.resolution,
                Resolution::Builtin(index) if SCALAR_BUILTINS.contains(&self.builtin_name(index))
            ),
            _ => false,
        }
    }

    // Whether TLC, sizing the parts in order up to one empty as written, meets one it may fail to
    // size.
    fn may_size_unsized(&self, parts: impl Iterator<Item = NodeId>) -> bool {
        parts
            .take_while(|&part| !self.is_empty_as_written(part))
            .any(|part| !self.is_sized(part, &mut HashSet::new()))
    }

    // Whether an expression, through the definitions it names, writes the text of a value, or
    // keeps one another may write (`TEXT_BUILTINS`), that may be a set `may_hold_unsized` finds.
    // `scope` holds the names bound around it, each with whether its value may hold one.
    // `operators` holds the operators with parameters LETs around it define that they only apply,
    // each with how much of `scope` its body sees: the walk follows one into its body where it is
    // applied, with its parameters bound to what the arguments may hold there, as it follows a
    // global definition.
    fn may_write_unsized(
        &self,
        node: NodeId,
        scope: &mut Vec<(TextId, bool)>,
        operators: &mut Vec<(TextId, NodeId, usize)>,
        seen: &mut HashSet<(NodeId, Vec<bool>)>,
    ) -> bool {
        let kind = self.node(node).1;
        if let NodeKind::Let {
            definitions, body, ..
        } = kind
        {
            let (depth, operator_depth) = (scope.len(), operators.len());
            scope.extend(self.binders(kind).1);
            let mut is_written = false;
            for &definition in definitions.iter() {
                if let NodeKind::Definition(named) = self.node(definition).1
                    && let DefinitionForm::Operator(params) = &named.form
                    && !params.is_empty()
                    && definitions
                        .iter()
                        .chain([body])
                        .all(|&root| self.is_only_applied(root, named.name, params.len()))
                {
                    operators.push((named.name, definition, scope.len()));
                    continue;
                }
                if self.may_write_unsized(definition, scope, operators, seen) {
                    is_written = true;
                    break;
                }
            }
            is_written = is_written || self.may_write_unsized(*body, scope, operators, seen);
            scope.truncate(depth);
            operators.truncate(operator_depth);
            return is_written;
        }
        if let NodeKind::Apply { name, args } = kind
            && name.is_local
            && let Some(&(_, definition, depth)) = operators
                .iter()
                .rev()
                .find(|(operator, ..)| *operator == name.text)
            && let NodeKind::Definition(named) = self.node(definition).1
            && let DefinitionForm::Operator(params) = &named.form
        {
            let mut bound = scope[..depth].to_vec();
            bound.extend(params.iter().zip(args.iter()).map(|(param, &arg)| {
                (
                    param.name,
                    self.reads_unsized(arg, scope, &mut HashSet::new()),
                )
            }));
            if seen.insert((
                named.body,
                bound.iter().map(|&(_, may_hold)| may_hold).collect(),
            )) && self.may_write_unsized(named.body, &mut bound, operators, seen)
            {
                return true;
            }
        }
        if let NodeKind::Identifier(name)
        | NodeKind::OperatorReference(name)
        | NodeKind::Apply { name, .. } = kind
            && !name.is_local
        {
            match name.resolution {
                Resolution::Builtin(index) if TEXT_BUILTINS.contains(&self.builtin_name(index)) => {
                    let NodeKind::Apply { args, .. } = kind else {
                        return true;
                    };
                    let is_print = matches!(self.builtin_name(index), "Print" | "PrintT");
                    if args.iter().any(|&arg| {
                        !(is_print && self.is_print_settled(arg, scope))
                            && self.reads_unsized(arg, scope, &mut HashSet::new())
                    }) {
                        return true;
                    }
                }
                Resolution::Definition(index) => {
                    let (body, mut bound) =
                        self.applied_definition(index, kind, scope, &mut HashSet::new());
                    if seen.insert((body, bound.iter().map(|&(_, may_hold)| may_hold).collect()))
                        && self.may_write_unsized(body, &mut bound, operators, seen)
                    {
                        return true;
                    }
                }
                _ => {}
            }
        }
        if matches!(kind, NodeKind::Subexpression(_)) {
            return true;
        }
        let (before, bound, after) = self.binders(kind);
        if before
            .iter()
            .any(|&child| self.may_write_unsized(child, scope, operators, seen))
        {
            return true;
        }
        let depth = scope.len();
        scope.extend(bound);
        let is_written = after
            .iter()
            .any(|&child| self.may_write_unsized(child, scope, operators, seen));
        scope.truncate(depth);
        is_written
    }

    // Whether every use of a name a LET defines in an expression applies it to `arity` arguments,
    // rather than passing it as an operator or reaching it through a subexpression selector.
    fn is_only_applied(&self, node: NodeId, operator: TextId, arity: usize) -> bool {
        let is_applied = match self.node(node).1 {
            NodeKind::Subexpression(_) => false,
            NodeKind::Apply { name, args } if name.is_local && name.text == operator => {
                args.len() == arity
            }
            NodeKind::Identifier(name) | NodeKind::OperatorReference(name)
                if name.is_local && name.text == operator =>
            {
                false
            }
            _ => true,
        };
        is_applied
            && self
                .children(node)
                .into_iter()
                .all(|child| self.is_only_applied(child, operator, arity))
    }

    // Whether a value a builtin writes may hold a set `may_hold_unsized` finds, as
    // `may_write_unsized` asks of each argument: a print's argument TLC's own check of the set
    // settles doesn't.
    pub(crate) fn may_write_held(&self, node: NodeId, is_print: bool) -> bool {
        !(is_print && self.is_print_settled(node, &mut Vec::new()))
            && self.reads_unsized(node, &mut Vec::new(), &mut HashSet::new())
    }

    // Whether the value of an expression may hold a set `may_hold_unsized` finds: one it builds,
    // through the definitions it names, or one a name bound around it holds (`scope`), or TLC's
    // registers. A name `scope` doesn't hold is bound where the walk didn't see.
    fn reads_unsized(
        &self,
        node: NodeId,
        scope: &mut Vec<(TextId, bool)>,
        seen: &mut HashSet<(NodeId, Vec<bool>)>,
    ) -> bool {
        if self.may_hold_unsized(node, &mut HashSet::new()) {
            return true;
        }
        self.reads_unsized_name(node, scope, seen)
    }

    fn reads_unsized_name(
        &self,
        node: NodeId,
        scope: &mut Vec<(TextId, bool)>,
        seen: &mut HashSet<(NodeId, Vec<bool>)>,
    ) -> bool {
        let kind = self.node(node).1;
        if self.is_scalar_valued(kind) {
            return false;
        }
        match kind {
            NodeKind::Identifier(name)
            | NodeKind::OperatorReference(name)
            | NodeKind::Apply { name, .. } => {
                let is_read = if name.is_local {
                    scope
                        .iter()
                        .rev()
                        .find(|(bound, _)| *bound == name.text)
                        .is_none_or(|&(_, may_hold)| may_hold)
                } else {
                    match name.resolution {
                        Resolution::Builtin(index) => self.builtin_name(index) == "TLCGet",
                        // A definition met again within its own walk is a recursion, whose
                        // value may hold anything.
                        Resolution::Definition(index) => {
                            let (body, mut bound) =
                                self.applied_definition(index, kind, scope, seen);
                            let key = (body, bound.iter().map(|&(_, may_hold)| may_hold).collect());
                            if seen.contains(&key) {
                                true
                            } else {
                                seen.insert(key.clone());
                                let is_read = self.reads_unsized_name(body, &mut bound, seen);
                                seen.remove(&key);
                                is_read
                            }
                        }
                        _ => false,
                    }
                };
                if is_read {
                    return true;
                }
            }
            NodeKind::Subexpression(_) => return true,
            _ => {}
        }
        // A function written there and applied holds its body's value, with the names its
        // constructor binds bound.
        if let NodeKind::FunctionApplication { function, .. } = kind
            && let constructor @ NodeKind::FunctionConstruction { body, .. } =
                self.node(*function).1
        {
            let (_, bound, _) = self.binders(constructor);
            let depth = scope.len();
            scope.extend(bound);
            let is_read = self.reads_unsized_name(*body, scope, seen);
            scope.truncate(depth);
            return is_read;
        }
        // Only an operand whose value the expression's value may hold, which, where the expression
        // binds no names, may be one an operand holds (`carried_children`).
        let carried = self.carried_children(kind);
        let (mut before, bound, after) = self.binders(kind);
        if bound.is_empty() && after.is_empty() {
            before.clone_from(&carried);
        }
        if before
            .iter()
            .filter(|child| carried.contains(child))
            .any(|&child| self.reads_unsized_name(child, scope, seen))
        {
            return true;
        }
        let depth = scope.len();
        scope.extend(bound);
        let is_read = after
            .iter()
            .filter(|child| carried.contains(child))
            .any(|&child| self.reads_unsized_name(child, scope, seen));
        scope.truncate(depth);
        is_read
    }

    // What a definition an expression names evaluates, and its parameters, each with whether its
    // value may hold a set `may_hold_unsized` finds: the argument's, where the expression applies
    // the definition to arguments in `scope`. A definition passed by name may be applied to
    // anything.
    // `walking` holds the definitions being walked for names, each with its parameters', which
    // classifying an argument walks within.
    fn applied_definition(
        &self,
        index: Index,
        kind: &NodeKind,
        scope: &mut Vec<(TextId, bool)>,
        walking: &mut HashSet<(NodeId, Vec<bool>)>,
    ) -> (NodeId, Vec<(TextId, bool)>) {
        let node = self.ir.definitions[index as usize];
        let definition = self.definition(node);
        let DefinitionForm::Operator(params) = &definition.form else {
            return (node, Vec::new());
        };
        let args: &[NodeId] = match kind {
            NodeKind::Apply { args, .. } => args,
            _ => &[],
        };
        let bound = params
            .iter()
            .enumerate()
            .map(|(position, param)| {
                let may_hold = args
                    .get(position)
                    .is_none_or(|&arg| self.reads_unsized(arg, scope, walking));
                (param.name, may_hold)
            })
            .collect();
        (definition.body, bound)
    }

    // The expressions an expression holds: those evaluated before the names it binds, the names,
    // each with whether its value may hold a set `may_hold_unsized` finds (a parameter's may hold
    // anything), and those evaluated where the names are bound.
    fn binders(&self, kind: &NodeKind) -> (Vec<NodeId>, Vec<(TextId, bool)>, Vec<NodeId>) {
        let names = |pattern: &Pattern, set: Option<NodeId>| {
            let may_hold = set.is_none_or(|set| self.may_hold_unsized(set, &mut HashSet::new()));
            match pattern {
                Pattern::Name(name) => vec![(*name, may_hold)],
                Pattern::Tuple(names) => names.iter().map(|&name| (name, may_hold)).collect(),
            }
        };
        let bounds_names = |bounds: &[Bound]| -> Vec<(TextId, bool)> {
            bounds
                .iter()
                .flat_map(|bound| names(&bound.pattern, Some(bound.set)))
                .collect()
        };
        let sets = |bounds: &[Bound]| bounds.iter().map(|bound| bound.set).collect();
        match kind {
            NodeKind::Definition(definition) => match &definition.form {
                DefinitionForm::Operator(params) => (
                    Vec::new(),
                    params.iter().map(|param| (param.name, true)).collect(),
                    vec![definition.body],
                ),
                DefinitionForm::Function(bounds) => {
                    (sets(bounds), bounds_names(bounds), vec![definition.body])
                }
            },
            NodeKind::Let {
                definitions, body, ..
            } => (
                Vec::new(),
                definitions
                    .iter()
                    .filter_map(|&definition| match self.node(definition).1 {
                        NodeKind::Definition(named) => Some((
                            named.name,
                            self.may_hold_unsized(definition, &mut HashSet::new()),
                        )),
                        _ => None,
                    })
                    .collect(),
                definitions.iter().copied().chain([*body]).collect(),
            ),
            NodeKind::Forall { bounds, body }
            | NodeKind::Exists { bounds, body }
            | NodeKind::FunctionConstruction { bounds, body, .. } => {
                (sets(bounds), bounds_names(bounds), vec![*body])
            }
            NodeKind::SetMap { expression, bounds } => {
                (sets(bounds), bounds_names(bounds), vec![*expression])
            }
            NodeKind::SetFilter { bound, predicate } => (
                vec![bound.set],
                names(&bound.pattern, Some(bound.set)),
                vec![*predicate],
            ),
            NodeKind::Choose { pattern, set, body } => (
                set.iter().copied().collect(),
                names(pattern, *set),
                vec![*body],
            ),
            NodeKind::UnboundedQuantifier { names, body, .. } => (
                Vec::new(),
                names.iter().map(|&name| (name, true)).collect(),
                vec![*body],
            ),
            NodeKind::Lambda { params, body } => (
                Vec::new(),
                params.iter().map(|&name| (name, true)).collect(),
                vec![*body],
            ),
            _ => (kind.children(), Vec::new(), Vec::new()),
        }
    }

    // The expressions an expression holds whose value may be held in its value, so that a set one
    // of them holds may be printed with it. Each kind and builtin says which of its operands its
    // value may contain: none where its value is a boolean, a number or a string
    // (`is_scalar_valued`); the branches of an IF or a CASE, not their conditions; the set CHOOSE
    // picks from and a filter keeps elements of; the domain of a function a constructor writes,
    // not its range, under DOMAIN; the function, not the argument, of an application; one field
    // of a record written there; the second argument of Print. Any operand not known otherwise
    // may be.
    fn carried_children(&self, kind: &NodeKind) -> Vec<NodeId> {
        let bound_sets =
            |bounds: &[Bound]| bounds.iter().map(|bound| bound.set).collect::<Vec<_>>();
        if self.is_scalar_valued(kind) {
            return Vec::new();
        }
        match kind {
            NodeKind::If {
                consequent,
                alternative,
                ..
            } => vec![*consequent, *alternative],
            NodeKind::Case { arms, other } => arms
                .iter()
                .map(|&(_, arm)| arm)
                .chain(other.iter().copied())
                .collect(),
            NodeKind::Choose { set, .. } => set.iter().copied().collect(),
            NodeKind::SetFilter { bound, .. } => vec![bound.set],
            NodeKind::SetMap { expression, bounds } => {
                let mut carried = bound_sets(bounds);
                carried.push(*expression);
                carried
            }
            NodeKind::FunctionConstruction { bounds, body, .. } => {
                let mut carried = bound_sets(bounds);
                carried.push(*body);
                carried
            }
            NodeKind::FunctionApplication { function, args } => {
                match (self.node(*function).1, args.as_slice()) {
                    (NodeKind::FunctionConstruction { body, .. }, _) => vec![*body],
                    // A tuple written there, at a position written there, holds that element.
                    (NodeKind::Tuple(elements), &[position]) => match self.node(position).1 {
                        NodeKind::Number(position) => usize::try_from(*position - 1)
                            .ok()
                            .and_then(|index| elements.get(index))
                            .copied()
                            .into_iter()
                            .collect(),
                        _ => elements.clone(),
                    },
                    _ => vec![*function],
                }
            }
            // A LET's value is its body's, which holds a definition's value only where it names it.
            NodeKind::Let { body, .. } => vec![*body],
            NodeKind::FieldAccess { record, field } => match self.node(*record).1 {
                NodeKind::Record(fields) => fields
                    .iter()
                    .filter(|&&(name, _)| name == *field)
                    .map(|&(_, value)| value)
                    .collect(),
                _ => vec![*record],
            },
            NodeKind::ExceptAt
            | NodeKind::Always(_)
            | NodeKind::Eventually(_)
            | NodeKind::BoxAction { .. }
            | NodeKind::AngleAction { .. }
            | NodeKind::WeakFairness { .. }
            | NodeKind::StrongFairness { .. } => Vec::new(),
            NodeKind::Apply { name, args } if !name.is_local => match name.resolution {
                Resolution::Builtin(index) => match (self.builtin_name(index), args.as_slice()) {
                    ("PrintT" | "Assert" | "ToString" | "TLCSet" | "..", _) => Vec::new(),
                    ("Print", [_, value]) => vec![*value],
                    ("DOMAIN", &[function]) => match self.node(function).1 {
                        NodeKind::FunctionConstruction { bounds, .. } => bound_sets(bounds),
                        NodeKind::Record(_) | NodeKind::Tuple(_) => Vec::new(),
                        NodeKind::Apply { name, args }
                            if !name.is_local
                                && matches!(name.resolution, Resolution::Builtin(index)
                                    if self.builtin_name(index) == ":>") =>
                        {
                            args.first().copied().into_iter().collect()
                        }
                        _ => vec![function],
                    },
                    _ => args.clone(),
                },
                _ => kind.children(),
            },
            _ => {
                let mut children = kind.children();
                if let NodeKind::SetFilter { bound, .. } = kind {
                    children.push(bound.set);
                }
                children
            }
        }
    }

    // Whether TLC sizes a set without failing, as it does to print a set the set is a part of, and
    // the engine prints that set as TLC does: an enumeration, an interval or BOOLEAN, or a set TLC
    // builds of such sets, which it enumerates to size. `seen` holds the definitions being looked
    // through, one met again being a recursion.
    fn is_sized(&self, node: NodeId, seen: &mut HashSet<NodeId>) -> bool {
        let (node, kind) = self.node(node);
        if !seen.insert(node) {
            return false;
        }
        // The sets it is sized by sizing, or none where it isn't sized.
        let parts = match kind {
            NodeKind::SetEnumeration(_) => Some(Vec::new()),
            NodeKind::Label { body, .. } => Some(vec![*body]),
            NodeKind::If {
                consequent,
                alternative,
                ..
            } => Some(vec![*consequent, *alternative]),
            NodeKind::Product(parts) => Some(parts.clone()),
            NodeKind::FunctionSet { domain, range } => Some(vec![*domain, *range]),
            NodeKind::RecordSet(fields) => Some(fields.iter().map(|&(_, field)| field).collect()),
            NodeKind::SetFilter { bound, .. } => Some(vec![bound.set]),
            NodeKind::SetMap { bounds, .. } => Some(bounds.iter().map(|bound| bound.set).collect()),
            // A name the body binds isn't sized here.
            NodeKind::Let { body, .. } => Some(vec![*body]),
            NodeKind::Identifier(name) if !name.is_local => match name.resolution {
                Resolution::Builtin(index) => {
                    (self.builtin_name(index) == "BOOLEAN").then(Vec::new)
                }
                Resolution::Definition(index) => {
                    let definition = self.definition(self.ir.definitions[index as usize]);
                    matches!(&definition.form, DefinitionForm::Operator(params) if params.is_empty())
                        .then(|| vec![definition.body])
                }
                _ => None,
            },
            NodeKind::Apply { name, args } if !name.is_local => match name.resolution {
                Resolution::Builtin(index) => match (self.builtin_name(index), args.as_slice()) {
                    ("..", [_, _]) => Some(Vec::new()),
                    ("SUBSET", [_]) | ("\\cup" | "\\cap" | "\\", [_, _]) => Some(args.clone()),
                    // The domain of a function, tuple or record written there.
                    ("DOMAIN", &[function]) => match self.node(function).1 {
                        NodeKind::Record(_) | NodeKind::Tuple(_) => Some(Vec::new()),
                        NodeKind::FunctionConstruction { bounds, .. } => {
                            Some(bounds.iter().map(|bound| bound.set).collect())
                        }
                        NodeKind::Apply { name, .. }
                            if !name.is_local
                                && matches!(name.resolution, Resolution::Builtin(index)
                                    if self.builtin_name(index) == ":>") =>
                        {
                            Some(Vec::new())
                        }
                        _ => None,
                    },
                    ("UNION", &[sets]) => match self.node(sets).1 {
                        NodeKind::SetEnumeration(sets) => Some(sets.clone()),
                        _ => None,
                    },
                    _ => None,
                },
                _ => None,
            },
            _ => None,
        };
        let is_sized =
            parts.is_some_and(|parts| parts.iter().all(|&part| self.is_sized(part, seen)));
        seen.remove(&node);
        is_sized
    }

    // Whether a set is empty as written: `{}`, or an interval of numerals down.
    fn is_empty_as_written(&self, node: NodeId) -> bool {
        match self.node(node).1 {
            NodeKind::SetEnumeration(elements) => elements.is_empty(),
            NodeKind::Apply { name, args } if !name.is_local => {
                let is_interval = matches!(name.resolution,
                    Resolution::Builtin(index) if self.builtin_name(index) == "..");
                is_interval
                    && matches!(args.as_slice(), &[low, high] if matches!(
                        (self.node(low).1, self.node(high).1),
                        (NodeKind::Number(low), NodeKind::Number(high)) if low > high
                    ))
            }
            _ => false,
        }
    }

    fn builtin_name(&self, index: Index) -> &'a str {
        self.text(self.ir.builtins[index as usize].name)
    }

    pub(crate) fn compile_boolean(
        &mut self,
        node: NodeId,
        context: &Context,
    ) -> Compiling<Compiled> {
        let compiled = self.compile(node, context)?;
        Ok(Self::as_boolean(compiled))
    }

    pub(crate) fn as_boolean(compiled: Compiled) -> Compiled {
        if compiled.is_boolean {
            return compiled;
        }
        let inner = compiled.eval.clone();
        Compiled {
            is_boolean: true,
            ..compiled.with_eval(eval(move |machine| check_boolean(inner(machine)?)))
        }
    }

    fn read_variable(&mut self, index: u32, context: &Context) -> Compiling<Compiled> {
        if index as usize >= self.ir.variables.len() && !context.is_primed {
            return unsupported("an unprimed variable past the state's");
        }
        self.note_variable(index)?;
        if context.is_primed {
            return Ok(leaf(
                eval(move |machine| machine.read_next(index)),
                Footprint::prime(index),
            ));
        }
        // TLC fingerprints a state, which caches each lazy set in it as its normalized set, but
        // not before the initial predicate has assigned it.
        Ok(Compiled {
            shape: Shape::Current(index),
            is_in_order: !context.is_init,
            are_elements_in_order: !context.is_init,
            are_elements_of_elements_in_order: !context.is_init,
            ..leaf(
                eval(move |machine| machine.read_current(index)),
                Footprint::var(index),
            )
        })
    }

    // A variable past the state's is one ENABLED's rewrite names, which only its next state holds.
    fn note_variable(&mut self, index: u32) -> Compiling<()> {
        if (index as usize) < self.ir.variables.len() {
            return Ok(());
        }
        if self.enabled_depth == 0 {
            return unsupported("a variable past the state's outside ENABLED");
        }
        self.variable_extent = self.variable_extent.max(index as usize + 1);
        Ok(())
    }

    pub(crate) fn read_slot(&self, slot: u32) -> Compiled {
        Compiled {
            shape: if self.int_slots.contains(&slot) {
                Shape::IntSlot(slot)
            } else {
                Shape::Slot(slot)
            },
            ..leaf(
                eval(move |machine| Ok(machine.locals[slot as usize])),
                Footprint::slot(slot),
            )
        }
    }

    // Whether the compiled value is its evaluation alone, but for its predicate and an interval's
    // bounds, which a kept value drops: nothing else a parent may evaluate in its place, which
    // would pass by the slot a LET definition or an argument is kept in.
    fn is_eval_only(compiled: &Compiled) -> bool {
        compiled.member.is_none()
            && compiled.parts.is_none()
            && compiled.filter.is_none()
            && compiled.reference.is_none()
            && compiled.unsorted_first.is_none()
            && compiled.element_references.is_none()
            && compiled.subset_base.is_none()
    }

    // A use of a LET definition or an argument kept from its first use (`Argument::once_slot`):
    // the first use evaluates it, with its effects, and keeps the value; the others read it.
    fn read_once(slot: u32, compiled: &Compiled) -> Compiling<Compiled> {
        if !Self::is_eval_only(compiled) {
            return unsupported(
                "a LET definition with effects, named more than once, held in parts",
            );
        }
        let inner = compiled.eval.clone();
        Ok(Compiled {
            footprint: compiled.footprint.merge(&Footprint::slot(slot)),
            is_costly: false,
            is_constant: false,
            interval: None,
            ..compiled.with_eval(eval(move |machine| {
                let known = machine.locals[slot as usize];
                if known != crate::memo::EMPTY {
                    return Ok(known);
                }
                let value = inner(machine)?;
                if value == machine.kept_lazy_function {
                    return Err(Bail(
                        "unsupported: a LET definition with effects TLC keeps as a lazy function",
                    ));
                }
                machine.locals[slot as usize] = value;
                Ok(value)
            }))
        })
    }

    // The LET's or the operator's body, with the slots of the definitions or arguments kept from
    // their first use cleared as it begins, as TLC binds each to a new `LazyValue`
    // (`evalImplLetInKind`, `getOpContext`), and restored as it ends, for one evaluated again
    // within itself.
    fn keep_once(kept_once: &[Rc<Argument>], body: Compiled) -> Compiling<Compiled> {
        let slots: Vec<u32> = kept_once
            .iter()
            .filter(|argument| {
                argument.compiled.borrow().iter().flatten().any(|compiled| {
                    compiled.is_printing()
                        || argument.reaches_startup.get() && Self::is_eval_only(compiled)
                })
            })
            .filter_map(|argument| argument.once_slot)
            .collect();
        if slots.is_empty() {
            return Ok(body);
        }
        if !Self::is_eval_only(&body) {
            return unsupported(
                "a LET definition with effects, named more than once, held in parts",
            );
        }
        let inner = body.eval.clone();
        // The body reads the slots only as it fills them, each evaluation anew, so what it
        // reads leaves them out: a recursive operator's body that calls the operator in such
        // an argument would otherwise read a new slot at each compile, and never settle.
        let footprint = body.footprint.without_slots(&slots);
        Ok(Compiled {
            footprint,
            is_costly: false,
            is_constant: false,
            interval: None,
            ..body.with_eval(eval(move |machine| {
                let saved: Vec<Id> = slots
                    .iter()
                    .map(|&slot| {
                        std::mem::replace(&mut machine.locals[slot as usize], crate::memo::EMPTY)
                    })
                    .collect();
                let value = inner(machine);
                for (&slot, kept) in slots.iter().zip(saved) {
                    machine.locals[slot as usize] = kept;
                }
                value
            }))
        })
    }

    // A use of a LET definition, an argument or a substitute the body may read more than once,
    // whose expression may reach a startup definition that failed as TLC started: TLC binds the
    // name to a `LazyValue`, which evaluates the definition again, with its prints and draws,
    // at the first read only, and keeps that value for the others (`LazyValue.getValue`), where
    // the engine evaluates it at each read (`Machine::constant_once`). It declines such a read.
    fn guard_retried(compiled: Compiled) -> Compiled {
        let inner = compiled.eval.clone();
        let shape = compiled.shape;
        Compiled {
            shape,
            ..compiled.with_eval(eval(move |machine| {
            let before = machine.retried_reads;
            let value = inner(machine)?;
            if machine.retried_reads != before {
                return Err(Bail(
                    "unsupported: a definition that failed as TLC started, read through a name TLC binds once and the body reads again",
                ));
            }
            Ok(value)
        }))
        }
    }

    // A use of a LET definition or an argument, however often the body reads it, whose
    // expression may reach a startup definition that failed as TLC started: where TLC reads the
    // name through `getInitStates` or `getNextStates`, `getInitStatesAppl` and `getNextStates`
    // find no cached value in its `LazyValue` and evaluate its expression again at each read,
    // without keeping it, and each application of an operator binds its own; the engine may
    // evaluate it once. It declines such a read in the initial predicate or an action the walk
    // compiles (`Context::is_walked`) where evaluating the definition again had an effect, a
    // print, a draw or a register's write.
    fn guard_retried_effects(compiled: Compiled) -> Compiled {
        let inner = compiled.eval.clone();
        let shape = compiled.shape;
        Compiled {
            shape,
            ..compiled.with_eval(eval(move |machine| {
                // What the evaluation may change, counted cheaply: any output, a warning too.
                let effects = |machine: &Machine<'_>| {
                    (
                        machine.output.len(),
                        machine.random.state(),
                        machine.registers.writes,
                    )
                };
                let before = (machine.retried_reads, effects(machine));
                // A first read that fails fails as TLC's does, which evaluates it there too.
                let value = inner(machine)?;
                if machine.retried_reads != before.0 && effects(machine) != before.1 {
                    return Err(Bail(
                        "unsupported: a definition that failed as TLC started, evaluated again with effects through a name TLC may evaluate at each read",
                    ));
                }
                Ok(value)
            }))
        }
    }

    fn compile_binding(&mut self, node: &Rc<Scope>, context: &Context) -> Compiling<Compiled> {
        match &node.binding {
            Binding::Slot(slot) => Ok(self.read_slot(*slot)),
            Binding::Argument(argument) => {
                let is_primed = context.is_primed || argument.context.is_primed;
                let index = usize::from(is_primed);
                let known = argument.compiled.borrow()[index].clone();
                let compiled = match known {
                    Some(known) => known,
                    None => {
                        let compiled = self.compile(
                            argument.expression,
                            &argument_context(argument).primed(is_primed),
                        )?;
                        let compiled = if argument.is_kept {
                            Compiled::kept(compiled)
                        } else {
                            compiled
                        };
                        // Whether TLC's `LazyValue` and the engine may differ at a second read:
                        // where it may reach a startup definition that failed as TLC started.
                        let may_reach = (context.is_walked || !argument.is_read_once)
                            && !self.startup_definitions.is_empty()
                            && self.may_reach_startup_definition(
                                argument.expression,
                                Some(&argument_context(argument)),
                                &mut HashSet::new(),
                            );
                        let reaches = !argument.is_read_once && may_reach;
                        argument.reaches_startup.set(reaches);
                        let compiled = if may_reach && context.is_walked {
                            Self::guard_retried_effects(compiled)
                        } else {
                            compiled
                        };
                        let compiled = if reaches
                            && (argument.once_slot.is_none() || !Self::is_eval_only(&compiled))
                        {
                            Self::guard_retried(compiled)
                        } else {
                            compiled
                        };
                        argument.compiled.borrow_mut()[index] = Some(compiled.clone());
                        compiled
                    }
                };
                // Each application of a constructor TLC keeps lazy evaluates its body at the
                // key, whether or not TLC keeps the function from the first use.
                // One that reaches a startup definition that failed as TLC started evaluates it
                // again at its first use only, as the `LazyValue` keeps it.
                if let Some(slot) = argument.once_slot
                    && (compiled.is_printing()
                        || argument.reaches_startup.get() && Self::is_eval_only(&compiled))
                    && !argument.is_applied_function
                {
                    return Self::read_once(slot, &compiled);
                }
                if !argument.is_each_use_alike && compiled.uses_registers() {
                    return unsupported(
                        "a definition or an argument that reads a register, evaluated more than once",
                    );
                }
                Ok(compiled)
            }
            Binding::Value { compiled, lazy } => {
                let Some(lazy) = lazy
                    .as_ref()
                    .filter(|lazy| context.is_primed && !lazy.context.is_primed)
                else {
                    return Ok((**compiled).clone());
                };
                if let Some(primed) = &*lazy.primed.borrow() {
                    return Ok(primed.clone());
                }
                let DefinitionForm::Function(bounds) = &self.definition(lazy.definition).form
                else {
                    panic!("a lazy function that isn't a function definition");
                };
                let body = self.definition(lazy.definition).body;
                let construction =
                    self.compile_function_construction(bounds, body, &lazy.context.primed(true))?;
                let primed = self.cached(Self::mark_costly(construction));
                *lazy.primed.borrow_mut() = Some(primed.clone());
                Ok(primed)
            }
            Binding::Recursive { definition } => {
                let recursive =
                    self.get_recursive_function(*definition, context, Some(Rc::clone(node)))?;
                self.materialize_recursive(&recursive)
            }
            Binding::Operator(_) => unsupported("an operator used as a value"),
        }
    }

    fn compile_definition_reference(
        &mut self,
        node: NodeId,
        context: &Context,
    ) -> Compiling<Compiled> {
        let definition = self.definition(node);
        if let Some(startup) = self.startup_definitions.get(&node) {
            return match startup {
                Some(compiled) => Ok(compiled.clone()),
                None => self.compile_startup_definition(node, context),
            };
        }
        let params = match &definition.form {
            DefinitionForm::Function(_) => return self.compile_function_definition(node, context),
            DefinitionForm::Operator(params) => params,
        };
        if !params.is_empty() {
            return unsupported("an operator used as a value");
        }
        let index = definition_index(context);
        if let Some((entry, known)) = self
            .definition_cache
            .get(&node)
            .and_then(|entries| entries[index].clone())
        {
            self.note_cached_read(entry);
            return Ok(known);
        }
        if context.is_expanding(node) {
            return self.compile_recursive_reference(node, context);
        }
        let body = definition.body;
        let body_context = Context {
            expanding: context.expanding_with(node),
            ..context.global(context.can_print)
        };
        let mut read = Vec::new();
        let result = self.tracking(&mut read, |compiler| {
            let compiled = compiler.compile(body, &body_context)?;
            Ok(compiler.cached(Self::mark_costly(compiled)))
        });
        let kept = self.kept_definition(node, result?, false)?;
        let compiled = match self.adopted_definition(node, &kept) {
            Some(adopted) => {
                self.adopted.insert(node);
                adopted
            }
            None => kept,
        };
        self.cache_definition(node, index, compiled.clone(), &read);
        Ok(compiled)
    }

    // `processConstantDefns`: TLC computes each constant definition as it starts and keeps the
    // value, which every use reads. Where the engine fails on one TLC computes there, a boolean
    // without an effect or a warning (`Settings::adopter`), each use reads that value, as TLC's
    // does; the warnings the engine printed before it failed are none of TLC's, which printed
    // nothing there. Only a boolean definition the engine doesn't compute as it compiles, that
    // names nothing whose value depends on when TLC evaluates it, nothing with an effect, and no
    // state.
    fn adopted_definition(&self, node: NodeId, compiled: &Compiled) -> Option<Compiled> {
        let adopter = self.adopter.clone()?;
        let definition = self.definition(node);
        let is_computed_at_startup = definition.flags & Definition::NORMALIZED != 0
            && definition.flags & Definition::CONFIGURED_SUBSTITUTE == 0
            && matches!(&definition.form, DefinitionForm::Operator(params) if params.is_empty());
        if !is_computed_at_startup
            || !compiled.is_boolean
            || matches!(compiled.shape, Shape::Constant(_))
            || !compiled.footprint.vars.is_empty()
            || !compiled.footprint.primes.is_empty()
            || compiled.is_printing()
            || compiled.uses_registers()
            || self.may_have_effect(definition.body, &mut HashSet::new())
            || self.may_reach_kind(definition.body, &mut HashSet::new(), &|kind, builtin| {
                matches!(kind, NodeKind::Enabled(_))
                    || builtin.is_some_and(|builtin| !self.is_adoptable_builtin(builtin))
            })
        {
            return None;
        }
        let index = self
            .ir
            .definitions
            .iter()
            .position(|&other| other == node)?;
        let index = index as Index;
        let adopted: Arc<std::sync::OnceLock<Option<bool>>> = Arc::default();
        let eval = compiled.eval.clone();
        Some(
            compiled
                .clone()
                .with_eval(Arc::new(move |machine: &mut Machine<'_>| {
                    let output_at = machine.output.len();
                    match eval(machine) {
                        Err(bail) => match *adopted.get_or_init(|| (adopter.0)(index)) {
                            Some(holds) => {
                                machine.output.truncate(output_at);
                                Ok(if holds { TRUE } else { FALSE })
                            }
                            None => Err(bail),
                        },
                        computed => computed,
                    }
                })),
        )
    }

    // Whether a builtin's value is the same wherever TLC evaluates it, without an effect: not
    // one that reads TLC's registers, its statistics, the clock or a file.
    fn is_adoptable_builtin(&self, builtin: &str) -> bool {
        !EFFECT_BUILTINS.contains(&builtin)
            && !matches!(
                builtin,
                "TLCGet"
                    | "TLCGetOrDefault"
                    | "TLCGetAndSet"
                    | "TLCCache"
                    | "TLCDefer"
                    | "TLCModelValue"
                    | "TLCEval"
                    | "JavaTime"
                    | "Trace"
                    | "CounterExample"
                    | "ToTrace"
                    | "TLCEvalDefinition"
                    | "JsonDeserialize"
                    | "ndJsonDeserialize"
                    | "IOEnv"
                    | "IOExec"
                    | "IOExecTemplate"
                    | "Serialize"
                    | "Deserialize"
                    | "AssertError"
                    | "PickSuccessor"
            )
    }

    // A constant definition's value as TLC keeps it: one value for the whole run
    // (`SpecProcessor.processConstantDefns`), which a use anywhere may cache as its normalized
    // set, where the engine builds it anew at each use.
    //
    // TLC converts that one value at its first size, comparison or fingerprint, and from then on
    // reads the conversion: a filter's predicate, or a part of a `\cup`, `\cap`, `\` or UNION
    // it keeps lazy, that prints, draws or sets a register has those effects only as it first
    // converts it (`SetPredValue.convertAndCache`). The engine builds the set again at each use,
    // repeating them, so it stops at such a definition held as other than its value
    // (`Compiler::has_rebuilt_effect`).
    //
    // It stops only where TLC keeps part of that value lazy, with effects it has later, as it
    // first converts it (`Compiler::has_deferred_effect`): with `is_value_read_once`, the engine
    // reads only the value it computed once as TLC started (`compile_startup_definition`), as
    // TLC reads the value it kept, and otherwise it builds the value again at each use.
    fn kept_definition(
        &self,
        node: NodeId,
        compiled: Compiled,
        is_value_read_once: bool,
    ) -> Compiling<Compiled> {
        let is_constant =
            compiled.footprint.vars.is_empty() && compiled.footprint.primes.is_empty();
        match self.normalized_definitions().get(&node) {
            Some(&is_assigned) if is_constant => {
                if !Self::is_eval_only(&compiled)
                    && self.has_deferred_effect(
                        self.definition(node).body,
                        &[],
                        !is_value_read_once,
                        &mut HashSet::new(),
                    )
                    && self.has_rebuilt_effect(
                        self.definition(node).body,
                        // Without parameters, every name local to the body is bound within it.
                        matches!(&self.definition(node).form,
                            DefinitionForm::Operator(params) if params.is_empty()),
                        &mut HashSet::new(),
                    )
                {
                    return unsupported(KEPT_WITH_EFFECTS);
                }
                Ok(Compiled::kept_from(compiled, is_assigned))
            }
            _ => Ok(compiled),
        }
    }

    // Whether rebuilding a constant definition's value repeats an effect TLC has once. TLC
    // evaluates the elements of a set enumeration, tuple or record, the branch an IF or CASE
    // takes, and the arguments of a builtin, each once as it builds the value
    // (`Tool.evalAppl`, `OPCODE_se`, `OPCODE_tup`, `OPCODE_rc`); a draw or print written there
    // has its effect then, and the value it keeps is what the engine evaluates once at startup.
    // Anything else with an effect, such as a filter's predicate, a map's expression, a
    // function's body or a LET, the engine may evaluate again as it rebuilds the set.
    fn has_rebuilt_effect(
        &self,
        node: NodeId,
        is_closed: bool,
        seen: &mut HashSet<NodeId>,
    ) -> bool {
        if !seen.insert(node) {
            return false;
        }
        match self.node(node).1 {
            NodeKind::SetEnumeration(_)
            | NodeKind::Tuple(_)
            | NodeKind::Record(_)
            | NodeKind::If { .. }
            | NodeKind::Case { .. } => self
                .children(node)
                .into_iter()
                .any(|child| self.has_rebuilt_effect(child, is_closed, seen)),
            NodeKind::Apply { name, .. } if !name.is_local => match name.resolution {
                Resolution::Builtin(_) => self
                    .children(node)
                    .into_iter()
                    .any(|child| self.has_rebuilt_effect(child, is_closed, seen)),
                _ if is_closed => self.may_have_effect_past_arguments(node, &mut HashSet::new()),
                _ => self.may_have_effect(node, &mut HashSet::new()),
            },
            _ if is_closed => self.may_have_effect_past_arguments(node, &mut HashSet::new()),
            _ => self.may_have_effect(node, &mut HashSet::new()),
        }
    }

    // Whether a startup definition's value, which TLC computes once as it starts, holds a part TLC
    // keeps lazy whose effects it has only later, as it first converts it. TLC evaluates the
    // elements of a set enumeration, tuple or record, the branch an IF or CASE takes, the
    // conjuncts and disjuncts it reaches, and the arguments of a builtin as it builds the value
    // (`OPCODE_se`, `OPCODE_tup`, `OPCODE_rc`, `Tool.evalAppl`); a LET's body, whose definitions
    // it evaluates where, written there, it first names them (`LazyValue`); and an operator's
    // body, whose arguments it evaluates likewise. Anything else, such as a filter's predicate, a
    // map's expression or a function's body, may hold an effect TLC defers, as may a name in it
    // of a LET definition or an argument with effects (`effectful`).
    //
    // With `is_rebuilt`, where the engine builds the value again at each use, an effect counts
    // as deferred unless it is a startup definition's, which the engine computes once where TLC
    // does (`constant_once`), or again at each use where TLC failed to compute it as it started.
    fn has_deferred_effect(
        &self,
        node: NodeId,
        effectful: &[TextId],
        is_rebuilt: bool,
        seen: &mut HashSet<(NodeId, Vec<TextId>)>,
    ) -> bool {
        let recurse = |children: Vec<NodeId>, seen: &mut HashSet<(NodeId, Vec<TextId>)>| -> bool {
            children
                .into_iter()
                .any(|child| self.has_deferred_effect(child, effectful, is_rebuilt, seen))
        };
        let deferred = |node: NodeId| {
            self.may_have_effect_past_arguments(node, &mut HashSet::new())
                || effectful
                    .iter()
                    .any(|&name| self.count_names(node, name) > 0)
        };
        match self.node(node).1 {
            NodeKind::SetEnumeration(_)
            | NodeKind::Tuple(_)
            | NodeKind::Record(_)
            | NodeKind::If { .. }
            | NodeKind::Case { .. }
            | NodeKind::And(_)
            | NodeKind::Or(_) => recurse(self.children(node), seen),
            // A name of a LET definition or an argument TLC evaluates here, as it builds the value.
            NodeKind::Identifier(name) if name.is_local => false,
            NodeKind::Identifier(name) | NodeKind::Apply { name, .. } if !name.is_local => {
                let args = match self.node(node).1 {
                    NodeKind::Apply { args, .. } => args.as_slice(),
                    _ => &[],
                };
                match name.resolution {
                    Resolution::Builtin(index) => {
                        (is_rebuilt && EFFECT_BUILTINS.contains(&self.builtin_name(index)))
                            || recurse(args.to_vec(), seen)
                    }
                    Resolution::Definition(index) => {
                        let target = self.ir.definitions[index as usize];
                        if self.is_read_once(target) {
                            return false;
                        }
                        let definition = self.definition(target);
                        let DefinitionForm::Operator(params) = &definition.form else {
                            return deferred(node);
                        };
                        if is_rebuilt && !self.startup_definitions.contains_key(&target) {
                            return deferred(node);
                        }
                        if definition.flags & (Definition::RECURSIVE | Definition::SELF_REFERENTIAL)
                            != 0
                            || params.len() != args.len()
                        {
                            return deferred(node);
                        }
                        let mut inner = Vec::new();
                        for (param, &arg) in params.iter().zip(args) {
                            if !deferred(arg) {
                                continue;
                            }
                            if param.arity != 0
                                || self.has_deferred_effect(arg, effectful, is_rebuilt, seen)
                            {
                                return true;
                            }
                            inner.push(param.name);
                        }
                        // A definition's body, reached again with the same arguments with
                        // effects, was found to defer none the first time.
                        if !seen.insert((definition.body, inner.clone())) {
                            return false;
                        }
                        self.has_deferred_effect(definition.body, &inner, is_rebuilt, seen)
                    }
                    _ => deferred(node),
                }
            }
            NodeKind::Let {
                instances: 0,
                definitions,
                body,
            } => {
                let mut inner = effectful.to_vec();
                for &local in definitions {
                    let definition = self.definition(local);
                    let is_value = definition.flags & Definition::RECURSIVE == 0
                        && matches!(&definition.form,
                            DefinitionForm::Operator(params) if params.is_empty());
                    let has_effect = self.may_have_effect(definition.body, &mut HashSet::new())
                        || inner
                            .iter()
                            .any(|&name| self.count_names(definition.body, name) > 0);
                    if !has_effect {
                        continue;
                    }
                    if !is_value
                        || is_rebuilt
                        || self.has_deferred_effect(definition.body, &inner, is_rebuilt, seen)
                    {
                        return true;
                    }
                    inner.push(definition.name);
                }
                self.has_deferred_effect(*body, &inner, is_rebuilt, seen)
            }
            _ => deferred(node),
        }
    }

    // Whether the engine reads a definition as the value it computed once at startup: not one
    // that reads what may change after TLC started, as a register, where a failure there
    // (which TLC swallows, computing the definition again at each use) may not come again.
    fn is_read_once(&self, node: NodeId) -> bool {
        self.startup_definitions.contains_key(&node)
            && !self.is_kept_lazy_at_startup(node)
            && matches!(&self.definition(node).form,
                DefinitionForm::Operator(params) if params.is_empty())
            && !self.may_reach_kind(
                self.definition(node).body,
                &mut HashSet::new(),
                &|_, builtin| {
                    builtin.is_some_and(|builtin| {
                        matches!(
                            builtin,
                            "TLCGet"
                                | "TLCGetOrDefault"
                                | "TLCGetAndSet"
                                | "TLCCache"
                                | "Trace"
                                | "CounterExample"
                                | "ToTrace"
                                | "TLCEvalDefinition"
                                | "PickSuccessor"
                        )
                    })
                },
            )
    }

    // `may_have_effect` of an expression of a definition without parameters, where an operator
    // applied by a name local to a definition stands for an argument of an application, a LET's
    // definition or a LAMBDA, which the walk meets as it walks the expression, the arguments of
    // the applications in it and the bodies they name, rather than for anything.
    fn may_have_effect_past_arguments(&self, node: NodeId, seen: &mut HashSet<NodeId>) -> bool {
        if !seen.insert(node) {
            return false;
        }
        let named = match self.node(node).1 {
            NodeKind::Identifier(name) | NodeKind::Apply { name, .. } if !name.is_local => {
                match name.resolution {
                    // Reading a JSON file again reads what it read before, which shows nowhere.
                    Resolution::Builtin(index) => {
                        let builtin = self.builtin_name(index);
                        EFFECT_BUILTINS.contains(&builtin)
                            && !matches!(builtin, "JsonDeserialize" | "ndJsonDeserialize")
                    }
                    // A definition TLC computes once as it starts, which the engine reads as the
                    // value it computed then (`compile_startup_definition`, `constant_once`), has
                    // its effects there alone.
                    Resolution::Definition(index)
                        if self.is_read_once(self.ir.definitions[index as usize]) =>
                    {
                        false
                    }
                    Resolution::Definition(index) => self.may_have_effect_past_arguments(
                        self.definition(self.ir.definitions[index as usize]).body,
                        seen,
                    ),
                    _ => false,
                }
            }
            _ => false,
        };
        named
            || self
                .evaluated_children(node)
                .into_iter()
                .any(|child| self.may_have_effect_past_arguments(child, seen))
    }

    // The definitions the spec names other than as the set of `e \in S` or `e \notin S`, or the
    // set a `\A`, `\E` or CHOOSE binds over, which TLC tests, streams or enumerates without
    // caching it as its normalized set (`Tool.contexts`, `toSetEnum`): where it may size,
    // compare or fingerprint it (`convertAndCache`), as a subexpression may any definition. Each
    // with whether every such name assigns it to a variable in the initial predicate
    // (`Compiler::initial_assignments`), so that TLC caches it only once that predicate completes
    // a state.
    pub(super) fn normalized_definitions(&self) -> &HashMap<NodeId, bool> {
        self.normalized_definitions.get_or_init(|| {
            let arena = &self.ir.nodes.arena;
            if arena
                .iter()
                .any(|named| matches!(named.kind, NodeKind::Subexpression(_)))
            {
                return self
                    .ir
                    .definitions
                    .iter()
                    .map(|&node| (node, false))
                    .collect();
            }
            let tested: HashSet<NodeId> = arena
                .iter()
                .flat_map(|tested| match &tested.kind {
                    NodeKind::Apply { name, args } if !name.is_local => match name.resolution {
                        Resolution::Builtin(index)
                            if matches!(self.builtin_name(index), "\\in" | "\\notin") =>
                        {
                            args.get(1).copied().into_iter().collect()
                        }
                        _ => Vec::new(),
                    },
                    NodeKind::Forall { bounds, .. } | NodeKind::Exists { bounds, .. } => {
                        bounds.iter().map(|bound| bound.set).collect()
                    }
                    NodeKind::Choose { set, .. } => set.iter().copied().collect(),
                    _ => Vec::new(),
                })
                .collect();
            let names: Vec<(NodeId, NodeId)> = (0..arena.len() as NodeId)
                .filter(|named| !tested.contains(named))
                .filter_map(|named| {
                    let resolution = match self.node(named).1 {
                        NodeKind::Identifier(name) | NodeKind::OperatorReference(name)
                            if !name.is_local =>
                        {
                            name.resolution
                        }
                        NodeKind::Apply { name, args } if !name.is_local && args.is_empty() => {
                            name.resolution
                        }
                        _ => return None,
                    };
                    match resolution {
                        Resolution::Definition(index) => {
                            Some((named, self.ir.definitions[index as usize]))
                        }
                        _ => None,
                    }
                })
                .collect();
            let assignments = self.initial_assignments(&names);
            let mut definitions = HashMap::new();
            for (named, definition) in names {
                let is_assigned = assignments.contains(&named);
                definitions
                    .entry(definition)
                    .and_modify(|is_all: &mut bool| *is_all &= is_assigned)
                    .or_insert(is_assigned);
            }
            definitions
        })
    }

    // The names of definitions, of `names` (each with its definition), that the initial
    // predicate assigns to a variable, `v = C`, where TLC binds the value it keeps for C as
    // built (`Tool.getInitStates`) and caches it as its normalized set only once it fingerprints
    // the state (`DoInitFunctor.addElement`): an assignment the predicate walks at most once on a
    // path, outside a binder or an operator's argument or body, whose variable it names nowhere
    // else, so that no test after it compares the value as the receiver (`SetCupValue.equals`,
    // `UnionValue.equals`).
    fn initial_assignments(&self, names: &[(NodeId, NodeId)]) -> HashSet<NodeId> {
        let is_equality = |node: NodeId| {
            matches!(self.node(node).1, NodeKind::Apply { name, .. } if !name.is_local
                && matches!(name.resolution, Resolution::Builtin(index)
                    if self.builtin_name(index) == "="))
        };
        let variable = |node: NodeId| match self.node(node).1 {
            NodeKind::Identifier(name) if !name.is_local => match name.resolution {
                Resolution::Variable(variable) => Some(variable),
                _ => None,
            },
            _ => None,
        };
        let named: HashSet<NodeId> = names.iter().map(|&(named, _)| named).collect();
        // Each `v = C`, by C's name: the equality and v.
        let mut candidates = HashMap::new();
        for (node, entry) in self.ir.nodes.arena.iter().enumerate() {
            if let NodeKind::Apply { args, .. } = &entry.kind
                && let [left, right] = args[..]
                && named.contains(&right)
                && is_equality(node as NodeId)
                && let Some(variable) = variable(left)
            {
                candidates.insert(right, (node as NodeId, variable));
            }
        }
        let is_referenced = |node: NodeId| {
            self.ir
                .nodes
                .arena
                .iter()
                .any(|entry| entry.kind == NodeKind::Reference(node))
        };
        candidates.retain(|&named, _| !is_referenced(named));
        if candidates.is_empty() || self.ir.model.scope.is_some() {
            return HashSet::new();
        }
        // How often the initial predicate walks each equality, and names each variable, on a
        // path, counting one under a binder or an operator's argument or body twice.
        let mut walked: HashMap<NodeId, u32> = HashMap::new();
        let mut variables: HashMap<u32, u32> = HashMap::new();
        let mut pending = vec![(self.ir.model.init, false)];
        let mut budget = 1_000_000u32;
        while let Some((node, is_repeated)) = pending.pop() {
            let Some(left) = budget.checked_sub(1) else {
                return HashSet::new();
            };
            budget = left;
            let count = u32::from(is_repeated) + 1;
            *walked.entry(node).or_default() += count;
            if let Some(variable) = variable(node) {
                *variables.entry(variable).or_default() += count;
            }
            let kind = self.node(node).1;
            let definition = match kind {
                NodeKind::Identifier(name) | NodeKind::OperatorReference(name)
                    if !name.is_local =>
                {
                    Some(name.resolution)
                }
                NodeKind::Apply { name, .. } if !name.is_local => Some(name.resolution),
                _ => None,
            }
            .and_then(|resolution| match resolution {
                Resolution::Definition(index) => Some(self.ir.definitions[index as usize]),
                _ => None,
            });
            if let Some(definition) = definition {
                let body = self.definition(definition).body;
                let is_operator = !matches!(&self.definition(definition).form,
                    DefinitionForm::Operator(params) if params.is_empty());
                pending.push((body, is_repeated || is_operator));
                if let NodeKind::Apply { args, .. } = kind {
                    pending.extend(args.iter().map(|&arg| (arg, true)));
                }
                continue;
            }
            match kind {
                NodeKind::Reference(target) => pending.push((*target, is_repeated)),
                NodeKind::Definition(definition) => pending.push((
                    definition.body,
                    is_repeated
                        || !matches!(&definition.form,
                            DefinitionForm::Operator(params) if params.is_empty()),
                )),
                NodeKind::And(_)
                | NodeKind::Or(_)
                | NodeKind::If { .. }
                | NodeKind::Case { .. }
                | NodeKind::Label { .. }
                | NodeKind::Prime(_)
                | NodeKind::Unchanged(_) => pending.extend(
                    kind.children()
                        .into_iter()
                        .map(|child| (child, is_repeated)),
                ),
                // A builtin's arguments, which TLC evaluates once.
                NodeKind::Apply { name, args } if !name.is_local => {
                    pending.extend(args.iter().map(|&arg| (arg, is_repeated)))
                }
                _ => pending.extend(kind.children().into_iter().map(|child| (child, true))),
            }
        }
        candidates
            .into_iter()
            .filter(|(_, (equality, variable))| {
                walked.get(equality) == Some(&1) && variables.get(variable) == Some(&1)
            })
            .map(|(named, _)| named)
            .collect()
    }

    // A definition TLC evaluates once at startup: what it computes is its value from then on, so
    // its effects aren't repeated. TLC keeps a function a definition constructs lazy, applying it
    // anew each time, which the engine doesn't.
    fn compile_startup_definition(
        &mut self,
        node: NodeId,
        context: &Context,
    ) -> Compiling<Compiled> {
        if self.is_kept_lazy_at_startup(node) {
            let scope = self.global_function_scope(node);
            let recursive = self.get_recursive_function(node, context, Some(scope))?;
            return self.materialize_recursive(&recursive);
        }
        let definition = self.definition(node);
        let warning_only = definition.flags & Definition::STARTUP_WARNING_ONLY != 0;
        let is_computed = match &definition.form {
            DefinitionForm::Operator(params) => {
                params.is_empty() && (warning_only || !self.may_be_lazy_at_startup(definition.body))
            }
            DefinitionForm::Function(bounds) => {
                warning_only
                    || definition.flags & (Definition::RECURSIVE | Definition::SELF_REFERENTIAL)
                        == 0
                        && self.is_built_at_startup(bounds, definition.body)
            }
        };
        if !is_computed {
            return unsupported("a value TLC computed at startup with effects");
        }
        // A function definition binds its bounds' names around its body.
        let written = match definition.form {
            DefinitionForm::Function(_) => node,
            DefinitionForm::Operator(_) => definition.body,
        };
        if !warning_only
            && self.may_write_unsized(
                written,
                &mut Vec::new(),
                &mut Vec::new(),
                &mut HashSet::new(),
            )
        {
            return unsupported("a set TLC may fail to print, at startup");
        }
        if context.is_expanding(node) {
            return self.compile_recursive_reference(node, context);
        }
        // TLC evaluates it where it starts, which may print and draw, and from then on reading
        // it prints, draws and reads nothing.
        let body_context = Context {
            expanding: context.expanding_with(node),
            ..context.global(true)
        };
        self.startup_bodies += 1;
        // Only an operator's body is compiled whole, as itself.
        let body = matches!(&definition.form, DefinitionForm::Operator(_))
            .then_some(definition.body)
            .filter(|_| !warning_only);
        let (compiled, effects) =
            self.compile_at_startup(body, |compiler| match &definition.form {
                DefinitionForm::Function(_) if warning_only => {
                    compiler.compile_function_definition(node, &body_context)
                }
                // The constructor TLC builds at once, which may print (`is_built_at_startup`).
                DefinitionForm::Function(bounds) => compiler
                    .compile_function_construction(bounds, definition.body, &body_context)
                    .map(Self::mark_costly),
                DefinitionForm::Operator(_) => compiler.compile(definition.body, &body_context),
            });
        self.startup_bodies -= 1;
        let compiled = compiled?;
        let once = self.allocate_once();
        self.startup_onces.insert(node, once);
        let inner = compiled.eval.clone();
        let is_value_read_once = !warning_only
            && matches!(&definition.form,
                DefinitionForm::Operator(params) if params.is_empty())
            && self.may_have_effect_past_arguments(definition.body, &mut HashSet::new());
        // The effects happen once where every read is of the value computed once; a part of
        // the value evaluated in its place would have them again.
        if effects > 0 {
            if is_value_read_once {
                self.startup_effect_onces.push(once);
            } else {
                self.is_printing_past_startup = true;
            }
        }
        let compiled = self.kept_definition(
            node,
            Compiled {
                is_costly: false,
                is_constant: true,
                footprint: Footprint::default(),
                ..compiled.with_eval(eval(move |machine| machine.constant_once(once, &inner)))
            },
            is_value_read_once,
        )?;
        // TLC reads the one value `processConstantDefns` kept (`setToolObject`), deep-normalized
        // (`evalConstantDefn`), wherever the definition is used: sizing it, enumerating it or
        // testing an element of it evaluates nothing of its body again. What a parent may
        // evaluate in place of the value, as its reference, its elements' references, its
        // membership test or an interval's bounds, evaluates the body again, with its prints and
        // draws (`Cardinality(S)` of `S == {Print("e", 1), 70}`), so a definition whose body has
        // an effect keeps only its value, which the engine reads once, past `kept_definition`,
        // which declines one TLC may convert lazily, with its effects, by those parts.
        let compiled = if is_value_read_once {
            Compiled {
                member: None,
                parts: None,
                interval: None,
                filter: None,
                reference: None,
                is_reference_exact: false,
                unsorted_first: None,
                element_references: None,
                subset_base: None,
                ..compiled
            }
        } else {
            compiled
        };
        self.startup_definitions
            .insert(node, Some(compiled.clone()));
        Ok(compiled)
    }

    /// Whether TLC keeps a constant function definition lazy as it starts and its body prints:
    /// one that names itself (OPCODE_rfs), which `FcnLambdaValue.makeRecursive` binds to the very
    /// value `processConstantDefns` keeps, so that every use, its own body's too, shares it.
    /// TLC evaluates its domain there, and its body at each application, anew, until something
    /// converts it (`toFcnRcd`: equality, fingerprinting, printing it), evaluating the body at
    /// each element of the domain in order, and caching what it built (`fcnRcd`), which every
    /// application reads from then on. The engine follows that where the body's only effects are
    /// prints, over one bound name of a set enumeration or an interval, whose normalized order is
    /// the store's, and where no function constructor in the body may print, which TLC keeps
    /// lazy (the control `makeRecursive` sets is KeepLazy).
    pub(crate) fn is_kept_lazy_at_startup(&self, node: NodeId) -> bool {
        if let Some(&known) = self.kept_lazy.borrow().get(&node) {
            return known;
        }
        let definition = self.definition(node);
        let is_kept = self.startup_definitions.contains_key(&node)
            && definition.flags & Definition::STARTUP_WARNING_ONLY == 0
            && definition.flags & (Definition::RECURSIVE | Definition::SELF_REFERENTIAL) != 0
            && match &definition.form {
                DefinitionForm::Function(bounds) => match &bounds[..] {
                    [
                        bound @ Bound {
                            pattern: Pattern::Name(_),
                            ..
                        },
                    ] => {
                        self.is_reduced_set(bound.set)
                            && !self.may_have_effect(bound.set, &mut HashSet::new())
                            && !matches!(
                                self.node(definition.body).1,
                                NodeKind::FunctionConstruction { .. }
                            )
                            && !self.may_reach_kind(
                                definition.body,
                                &mut HashSet::new(),
                                &|_, builtin| {
                                    builtin.is_some_and(|builtin| {
                                        builtin != "Print"
                                            && builtin != "PrintT"
                                            && EFFECT_BUILTINS.contains(&builtin)
                                    })
                                },
                            )
                            && !self.may_keep_effect_lazy(
                                definition.body,
                                &Context::ROOT,
                                &mut HashSet::new(),
                            )
                    }
                    _ => false,
                },
                DefinitionForm::Operator(_) => false,
            };
        self.kept_lazy.borrow_mut().insert(node, is_kept);
        is_kept
    }

    /// The operands of an expression that name a recursive function TLC keeps lazy as it starts
    /// (`is_kept_lazy_at_startup`) where TLC converts it there (`toFcnRcd`) after evaluating
    /// nothing that may print or fail. Only the function's own methods convert it: `F = e` and
    /// `F # e` (`FcnLambdaValue.equals`), and `F \in [S -> T]` (`SetOfFcnsValue.member`), each
    /// once its other operand is evaluated, which must then be written of constants or name the
    /// same function, which converts it as well. Elsewhere TLC passes the lazy value along,
    /// applying it anew (`apply`), selecting each element without caching (`toTuple`, as
    /// `<<1>> = F`, `F \in Seq(Int)` or a set holding it does), or building another lazy value
    /// (`takeExcept`), so the engine stops at every other use of it as a value.
    fn converting_operands(&self, node: NodeId) -> Vec<NodeId> {
        let NodeKind::Apply { name, args } = self.node(node).1 else {
            return Vec::new();
        };
        let (Resolution::Builtin(index), false, [left, right]) =
            (name.resolution, name.is_local, &args[..])
        else {
            return Vec::new();
        };
        let Some(function) = self.kept_lazy_reference(*left) else {
            return Vec::new();
        };
        match self.builtin_name(index) {
            "=" | "#" | "/=" if self.kept_lazy_reference(*right) == Some(function) => {
                vec![*left, *right]
            }
            "=" | "#" | "/=" if self.is_inert(*right) => vec![*left],
            "\\in" | "\\notin"
                if matches!(self.node(*right).1, NodeKind::FunctionSet { domain, range }
                    if self.is_inert(*domain) && self.is_inert(*range)) =>
            {
                vec![*left]
            }
            _ => Vec::new(),
        }
    }

    // The definition a global name of a recursive function TLC keeps lazy as it starts is.
    fn kept_lazy_reference(&self, node: NodeId) -> Option<NodeId> {
        let NodeKind::Identifier(name) = self.node(node).1 else {
            return None;
        };
        let Resolution::Definition(index) = name.resolution else {
            return None;
        };
        let definition = self.ir.definitions[index as usize];
        (!name.is_local && self.is_kept_lazy_at_startup(definition)).then_some(definition)
    }

    // Whether an expression is written of constants TLC evaluates without effect or failure:
    // numbers, strings, the booleans, an interval of numbers, `Int`, `Nat`, `BOOLEAN` and
    // `STRING`, and tuples, records, set enumerations and sets of functions of them.
    fn is_inert(&self, node: NodeId) -> bool {
        match self.node(node).1 {
            NodeKind::Number(_) | NodeKind::WideNumber(_) | NodeKind::String(_) => true,
            NodeKind::Tuple(items) | NodeKind::SetEnumeration(items) => {
                items.iter().all(|&item| self.is_inert(item))
            }
            NodeKind::Record(fields) => fields.iter().all(|&(_, field)| self.is_inert(field)),
            NodeKind::FunctionSet { domain, range } => {
                self.is_inert(*domain) && self.is_inert(*range)
            }
            NodeKind::Identifier(name) if !name.is_local => matches!(name.resolution,
                Resolution::Builtin(index) if matches!(self.builtin_name(index),
                    "TRUE" | "FALSE" | "Int" | "Nat" | "BOOLEAN" | "STRING")),
            NodeKind::Apply { name, args } if !name.is_local => {
                matches!(name.resolution,
                    Resolution::Builtin(index) if self.builtin_name(index) == "..")
                    && args.iter().all(|&arg| {
                        matches!(
                            self.node(arg).1,
                            NodeKind::Number(_) | NodeKind::WideNumber(_)
                        )
                    })
            }
            _ => false,
        }
    }

    /// The startup definitions a dependent of them (`tla_ir::Startup::dependents`) names, as
    /// written or through the definitions it names, by position.
    pub(crate) fn get_startup_names(&self, index: Index) -> Vec<usize> {
        let body = self.definition(self.ir.definitions[index as usize]).body;
        self.ir
            .model
            .startup
            .definitions
            .iter()
            .enumerate()
            .filter(|&(_, &listed)| self.names_cached(body, self.ir.definitions[listed as usize]))
            .map(|(position, _)| position)
            .collect()
    }

    /// A dependent of the startup definitions compiled as TLC computes it as it starts, with
    /// `EvalControl.Clear`, or why the engine can't: one whose value TLC may keep lazy, which
    /// evaluates what it names elsewhere or never.
    pub(crate) fn compile_startup_dependent(&mut self, index: Index) -> Result<Eval, String> {
        let definition = self.definition(self.ir.definitions[index as usize]);
        if !matches!(&definition.form, DefinitionForm::Operator(params) if params.is_empty())
            || self.may_be_lazy_at_startup(definition.body)
        {
            return Err("a value TLC computed at startup with effects".into());
        }
        self.compile_root_printing(Root::Definition(index), true)
            .map(|compiled| compiled.eval)
            .map_err(|error| match error {
                CompileError::Bail(reason) | CompileError::Decline(reason) => reason,
            })
    }

    /// A definition that reaches TLCSet, compiled as TLC computes it as it starts
    /// (`tla_ir::Startup::register_probes`), or why the engine can't.
    pub(crate) fn compile_register_probe(&mut self, index: Index) -> Result<Eval, String> {
        let definition = self.definition(self.ir.definitions[index as usize]);
        if !matches!(&definition.form, DefinitionForm::Operator(params) if params.is_empty()) {
            return Err(
                "a constant definition TLC computes as it starts that sets a register".into(),
            );
        }
        self.compile_root_printing(Root::Definition(index), true)
            .map(|compiled| compiled.eval)
            .map_err(|error| match error {
                CompileError::Bail(reason) | CompileError::Decline(reason) => reason,
            })
    }

    /// What TLC computes as it starts of a recursive function it keeps lazy
    /// (`is_kept_lazy_at_startup`): its domain (OPCODE_rfs), which has no effect, and the
    /// function itself, which it converts only where it is used. The search keeps no value of
    /// it, and the trace's evaluator, which doesn't follow the conversion, takes none either.
    pub(crate) fn compile_kept_lazy_startup(&mut self, index: Index) -> Compiling<Option<Eval>> {
        let node = self.ir.definitions[index as usize];
        if !self.is_kept_lazy_at_startup(node) {
            return Ok(None);
        }
        let scope = self.global_function_scope(node);
        let recursive = self.get_recursive_function(node, &Context::ROOT, Some(scope))?;
        let domain = recursive.domain.eval.clone();
        Ok(Some(eval(move |machine| {
            domain(machine)?;
            Ok(tla_values::store::NO_VALUE)
        })))
    }

    /// The constant definitions the search compiled whose body is a CHOOSE over a set, by
    /// position in the IR's definitions: TLC computes each as it starts
    /// (`processConstantDefns`), which may search the set long, and the trace's rebuild finds
    /// the element the search's value names instead.
    pub(crate) fn get_constant_choices(&self) -> Vec<(Index, Eval)> {
        self.ir
            .definitions
            .iter()
            .enumerate()
            .filter_map(|(index, &node)| {
                let definition = self.definition(node);
                if !matches!(&definition.form, DefinitionForm::Operator(params) if params.is_empty())
                    || !matches!(
                        self.node(definition.body).1,
                        NodeKind::Choose { set: Some(_), .. }
                    )
                {
                    return None;
                }
                let (_, compiled) = self.definition_cache.get(&node)?.iter().flatten().next()?;
                (compiled.is_constant && compiled.footprint.width() == 0)
                    .then(|| (index as Index, compiled.eval.clone()))
            })
            .collect()
    }

    fn cache_definition(
        &mut self,
        node: NodeId,
        index: usize,
        compiled: Compiled,
        read: &[Rc<FixedPoint>],
    ) {
        let entry = self.next_entry();
        self.remember_reads(
            entry,
            read,
            Dependent::Definition {
                definition: node,
                index,
                entry,
            },
        );
        self.definition_cache.entry(node).or_default()[index] = Some((entry, compiled));
    }

    fn compile_identifier(&mut self, name: &Name, context: &Context) -> Compiling<Compiled> {
        if name.is_local
            && let Some(found) = lookup(&context.scope, name.text)
        {
            return self.compile_binding(&found, context);
        }
        match name.resolution {
            Resolution::Variable(index) => return self.read_variable(index, context),
            Resolution::Constant(index) => {
                // The model's constants are the values it writes, which TLC normalizes, so a set
                // and each set in it stream in order.
                return match self.ir.constants[index as usize].value {
                    Some(value) => Ok(Compiled {
                        is_reducible: matches!(
                            self.ir.values.list[value as usize],
                            tla_ir::Value::Set(_)
                        ),
                        is_in_order: true,
                        are_elements_in_order: true,
                        are_elements_of_elements_in_order: true,
                        ..constant(self.intern_value(value)?)
                    }),
                    None => decline(format!(
                        "the constant {}, whose value the IR can't hold",
                        self.text(name.text)
                    )),
                };
            }
            Resolution::Definition(index) => {
                return self
                    .compile_definition_reference(self.ir.definitions[index as usize], context);
            }
            Resolution::Builtin(index) if self.ir.builtins[index as usize].arity == 0 => {
                return self.compile_nullary_builtin(index, context);
            }
            _ => {}
        }
        if let Some(found) = lookup(&context.scope, name.text) {
            return self.compile_binding(&found, context);
        }
        unsupported(format!("the name {}", self.text(name.text)))
    }

    // --- LET ---

    // How many times an expression names a local name, or `None` where it may evaluate a name
    // more than once each time it is evaluated, under a binder, or where it isn't known.
    // `users` names the operators that may use the name in their bodies.
    fn count_uses(&self, node: NodeId, name: TextId, users: &[TextId]) -> Option<u32> {
        match self.node(node).1 {
            NodeKind::Number(_)
            | NodeKind::WideNumber(_)
            | NodeKind::Decimal(_)
            | NodeKind::String(_) => Some(0),
            NodeKind::Identifier(identifier) => {
                Some(u32::from(identifier.is_local && identifier.text == name))
            }
            NodeKind::Apply {
                name: applied,
                args,
            } => {
                // A later definition of the LET may use the name, as often as it is applied.
                if applied.is_local && users.contains(&applied.text) {
                    return None;
                }
                let own = u32::from(applied.is_local && applied.text == name);
                Some(own + self.sum_uses(name, users, args.iter().copied())?)
            }
            NodeKind::And(operands)
            | NodeKind::Or(operands)
            | NodeKind::SetEnumeration(operands)
            | NodeKind::Tuple(operands)
            | NodeKind::Product(operands) => self.sum_uses(name, users, operands.iter().copied()),
            NodeKind::Record(fields) => {
                self.sum_uses(name, users, fields.iter().map(|&(_, field)| field))
            }
            NodeKind::FieldAccess { record, .. } => self.count_uses(*record, name, users),
            NodeKind::FunctionApplication { function, args } => self.sum_uses(
                name,
                users,
                std::iter::once(*function).chain(args.iter().copied()),
            ),
            NodeKind::If {
                condition,
                consequent,
                alternative,
            } => self.sum_uses(name, users, [*condition, *consequent, *alternative]),
            NodeKind::Case { arms, other } => self.sum_uses(
                name,
                users,
                arms.iter()
                    .flat_map(|&(guard, arm)| [guard, arm])
                    .chain(*other),
            ),
            _ => None,
        }
    }

    // Whether the expressions that may use a local name TLC binds a value to, keeping it for later
    // uses (`LazyValue`), name it more than once, one of them where it may cache a set it holds as
    // its normalized set, so that a use after it streams the normalized set where the engine
    // streams the set as built.
    fn is_kept_name(&self, roots: impl IntoIterator<Item = NodeId> + Clone, name: TextId) -> bool {
        roots
            .clone()
            .into_iter()
            .map(|root| self.count_names(root, name))
            .sum::<u32>()
            > 1
            && roots
                .into_iter()
                .any(|root| self.may_normalize_name(root, name))
    }

    // How many times an expression names a local name as written, up to 2, each name under a
    // binder or in a LET's operator once.
    fn count_names(&self, node: NodeId, name: TextId) -> u32 {
        let kind = self.node(node).1;
        let own = match kind {
            NodeKind::Identifier(named) | NodeKind::Apply { name: named, .. } => {
                u32::from(named.is_local && named.text == name)
            }
            NodeKind::Subexpression(_) => 2,
            _ => 0,
        };
        let filtered = match kind {
            NodeKind::SetFilter { bound, .. } => Some(bound.set),
            _ => None,
        };
        kind.children()
            .into_iter()
            .chain(filtered)
            .fold(own, |count, child| {
                if count > 1 {
                    count
                } else {
                    count + self.count_names(child, name)
                }
            })
            .min(2)
    }

    // Whether an expression names a local name other than as the set of `e \in S` or
    // `e \notin S`, which TLC tests or streams without caching it as its normalized set: where it
    // may size, compare or fingerprint it (`convertAndCache`).
    fn may_normalize_name(&self, node: NodeId, name: TextId) -> bool {
        let kind = self.node(node).1;
        let is_name = |node: NodeId| {
            matches!(self.node(node).1, NodeKind::Identifier(named)
                if named.is_local && named.text == name)
        };
        match kind {
            NodeKind::Identifier(_) => return is_name(node),
            NodeKind::Subexpression(_) => return true,
            NodeKind::Apply {
                name: applied,
                args,
            } if !applied.is_local => {
                if let Resolution::Builtin(index) = applied.resolution
                    && matches!(self.builtin_name(index), "\\in" | "\\notin")
                    && let [element, set] = &args[..]
                {
                    return self.may_normalize_name(*element, name)
                        || (!is_name(*set) && self.may_normalize_name(*set, name));
                }
            }
            NodeKind::Apply { name: applied, .. } if applied.text == name && applied.is_local => {
                return true;
            }
            _ => {}
        }
        let filtered = match kind {
            NodeKind::SetFilter { bound, .. } => Some(bound.set),
            _ => None,
        };
        kind.children()
            .into_iter()
            .chain(filtered)
            .any(|child| self.may_normalize_name(child, name))
    }

    // `count_uses`, where an expression that is itself a LET counts the uses in its definitions'
    // bodies and its own: a definition without parameters is evaluated at most once
    // (`LazyValue`), and one with parameters or a function that names the name may evaluate it
    // more than once.
    fn count_uses_through_let(&self, node: NodeId, name: TextId, users: &[TextId]) -> Option<u32> {
        let NodeKind::Let {
            instances: 0,
            definitions,
            body,
        } = self.node(node).1
        else {
            return self.count_uses(node, name, users);
        };
        let mut count = 0;
        for &inner in definitions {
            let definition = self.definition(inner);
            let uses = self.count_uses(definition.body, name, users)?;
            let is_once = definition.flags & Definition::RECURSIVE == 0
                && matches!(&definition.form, DefinitionForm::Operator(params) if params.is_empty());
            if uses > 0 && !is_once {
                return None;
            }
            count += uses;
        }
        Some(count + self.count_uses_through_let(*body, name, users)?)
    }

    // Whether no use of a LET definition `name` without parameters, in the definitions after it
    // (`later`) and the LET's body, may be evaluated with `EvalControl.KeepLazy`, which
    // `LazyValue.getCachedValue` ignores, so that a function constructor TLC kept lazy
    // (`FcnLambdaValue`, whose values `deepNormalize` doesn't reach) there would be what a later
    // print reads: TLC evaluates the function of an application or a field's record so
    // (OPCODE_fa's `setKeepLazy`), and an operator's argument wherever its body names it. A later
    // definition naming it is evaluated where that definition is used, so its own uses count
    // too. `checked` keeps what was found of each later definition.
    fn is_used_eagerly_in_let(
        &self,
        later: &[NodeId],
        body: NodeId,
        name: TextId,
        checked: &mut HashMap<NodeId, bool>,
    ) -> bool {
        for (position, &definition_node) in later.iter().enumerate() {
            let definition = self.definition(definition_node);
            if !self.may_name(definition.body, name) {
                continue;
            }
            let is_value = definition.flags & Definition::RECURSIVE == 0
                && matches!(&definition.form, DefinitionForm::Operator(params) if params.is_empty());
            if !is_value || !self.names_only_eagerly(definition.body, name) {
                return false;
            }
            let is_eager = match checked.get(&definition_node) {
                Some(&is_eager) => is_eager,
                None => {
                    let is_eager = self.is_used_eagerly_in_let(
                        &later[position + 1..],
                        body,
                        definition.name,
                        checked,
                    );
                    checked.insert(definition_node, is_eager);
                    is_eager
                }
            };
            if !is_eager {
                return false;
            }
        }
        self.names_only_eagerly(body, name)
    }

    // `is_used_eagerly_in_let` of an expression: it names the name only where TLC evaluates it
    // with the control it evaluates the expression with, through the builtins whose arguments
    // it evaluates so (`EAGER_ARGUMENT_BUILTINS`).
    fn names_only_eagerly(&self, node: NodeId, name: TextId) -> bool {
        let kind = self.node(node).1;
        match kind {
            NodeKind::Identifier(named) if named.is_local && named.text == name => true,
            NodeKind::OperatorReference(named) if named.is_local && named.text == name => false,
            NodeKind::Apply { name: named, args } => {
                if named.is_local && named.text == name {
                    return args.is_empty();
                }
                let is_eager = !named.is_local
                    && matches!(named.resolution, Resolution::Builtin(index)
                        if EAGER_ARGUMENT_BUILTINS.contains(&self.builtin_name(index)));
                args.iter().all(|&arg| {
                    if is_eager {
                        self.names_only_eagerly(arg, name)
                    } else {
                        !self.may_name(arg, name)
                    }
                })
            }
            NodeKind::FunctionApplication { function, args } => {
                !self.may_name(*function, name)
                    && args.iter().all(|&arg| self.names_only_eagerly(arg, name))
            }
            NodeKind::FieldAccess { record, .. } => !self.may_name(*record, name),
            NodeKind::Let {
                instances: 0,
                definitions,
                body,
            } => self.is_used_eagerly_in_let(definitions, *body, name, &mut HashMap::new()),
            NodeKind::Lambda { .. }
            | NodeKind::Let { .. }
            | NodeKind::Subexpression(_)
            | NodeKind::Reference(_)
            | NodeKind::Definition(_) => !self.may_name(node, name),
            NodeKind::SetFilter { bound, predicate } => {
                self.names_only_eagerly(bound.set, name)
                    && self.names_only_eagerly(*predicate, name)
            }
            _ => kind
                .children()
                .into_iter()
                .all(|child| self.names_only_eagerly(child, name)),
        }
    }

    fn sum_uses(
        &self,
        name: TextId,
        users: &[TextId],
        nodes: impl IntoIterator<Item = NodeId>,
    ) -> Option<u32> {
        nodes.into_iter().try_fold(0, |count, node| {
            Some(count + self.count_uses(node, name, users)?)
        })
    }

    // Whether evaluating an expression may write a TLC register: it applies TLCSet or
    // TLCGetAndSet, a definition or a name of `scope` that may, or an operator it can't see the
    // body of.
    fn may_write_register(
        &self,
        node: NodeId,
        scope: &Option<Rc<Scope>>,
        seen: &mut HashSet<NodeId>,
    ) -> bool {
        let (id, kind) = self.node(node);
        if !seen.insert(id) {
            return false;
        }
        let resolution = match kind {
            NodeKind::Apply { name, .. } | NodeKind::Identifier(name) if !name.is_local => {
                Some(name.resolution)
            }
            // A name the scope doesn't bind is a definition of the LET being bound, which is
            // scanned itself.
            NodeKind::Identifier(name) => {
                return lookup(scope, name.text)
                    .map(|found| match &found.binding {
                        Binding::Slot(_) => false,
                        Binding::Argument(argument) => self.may_write_register(
                            argument.expression,
                            &argument.context.scope,
                            seen,
                        ),
                        _ => true,
                    })
                    .unwrap_or_default();
            }
            NodeKind::Apply { .. } | NodeKind::OperatorReference(_) => return true,
            _ => None,
        };
        let is_writing = match resolution {
            Some(Resolution::Builtin(index)) => {
                matches!(
                    self.builtin_name(index),
                    "TLCSet" | "TLCGetAndSet" | "_Track"
                )
            }
            Some(Resolution::Definition(index)) => self.may_write_register(
                self.definition(self.ir.definitions[index as usize]).body,
                &None,
                seen,
            ),
            _ => false,
        };
        is_writing
            || kind
                .children()
                .into_iter()
                .any(|child| self.may_write_register(child, scope, seen))
    }

    // A LET's definitions, those an INSTANCE in it copies in among them, of an expression or,
    // where not `is_expression`, of an action or the initial predicate.
    fn bind_let_definitions(
        &mut self,
        definitions: &[NodeId],
        body: NodeId,
        context: &Context,
        is_expression: bool,
    ) -> Compiling<Context> {
        Ok(self
            .bind_let_definitions_kept(definitions, body, context, is_expression, false)?
            .0)
    }

    // `bind_let_definitions`, where with `is_kept_once` a definition with effects named more than
    // once in a constant definition TLC computes as it starts is kept from its first use, as
    // `LazyValue` keeps it: the definitions so bound, whose slots the caller clears as the LET
    // begins (`keep_once`).
    fn bind_let_definitions_kept(
        &mut self,
        definitions: &[NodeId],
        body: NodeId,
        context: &Context,
        is_expression: bool,
        is_kept_once: bool,
    ) -> Compiling<(Context, Vec<Rc<Argument>>)> {
        let mut kept_once = Vec::new();
        let mut scope = context.scope.clone();
        let mut recursive = Vec::new();
        for (position, &node) in definitions.iter().enumerate() {
            let definition = self.definition(node);
            // A definition the rest of the LET names once is evaluated once, as TLC evaluates
            // it, so it may print.
            let later = &definitions[position + 1..];
            let users: Vec<TextId> = later
                .iter()
                .map(|&later| self.definition(later).name)
                .collect();
            let uses = later
                .iter()
                .map(|&later| self.definition(later).body)
                .chain([body])
                .try_fold(0, |count, root| {
                    Some(count + self.count_uses(root, definition.name, &users)?)
                });
            // TLC evaluates a constant definition as it starts with a next state, so the
            // `LazyValue` of a definition of a LET in it keeps the value of its first use
            // (`Tool.evalAppl`, `LazyValue.getValue`).
            let once_slot = (is_kept_once
                && is_expression
                && self.startup_bodies > 0
                && !context.is_primed
                && context.can_print
                && uses.is_none_or(|count| count > 1)
                && matches!(&definition.form, DefinitionForm::Operator(params) if params.is_empty())
                && definition.flags & Definition::RECURSIVE == 0)
                .then(|| self.allocate_slot());
            // An operator with parameters TLC evaluates anew at each application, as it does a
            // global one (`Tool.evalAppl`), so it prints where it is applied.
            let is_applied_anew = definition.flags & Definition::RECURSIVE == 0
                && matches!(&definition.form, DefinitionForm::Operator(params) if !params.is_empty());
            // A LET TLC may compute the initial states from evaluates its definitions as the
            // initial predicate applies them, with `EvalControl.Init` (`init_predicates`).
            let is_applied_function = is_expression
                && !self.init_predicates.contains(&self.node(body).0)
                && definition.flags & Definition::RECURSIVE == 0
                && matches!(&definition.form, DefinitionForm::Operator(params) if params.is_empty())
                && self.is_lazily_applied_definition(
                    definition.body,
                    &context.with_scope(scope.clone()),
                    later
                        .iter()
                        .map(|&later| self.definition(later).body)
                        .chain([body]),
                    definition.name,
                );
            let definition_context = Context {
                scope: scope.clone(),
                can_print: context.can_print
                    && (is_applied_anew
                        || is_applied_function
                        || once_slot.is_some()
                        || uses.is_some_and(|count| count <= 1)),
                ..context.clone()
            };
            match &definition.form {
                DefinitionForm::Function(bounds) => {
                    if definition.flags & (Definition::RECURSIVE | Definition::SELF_REFERENTIAL)
                        != 0
                    {
                        scope = bind(
                            &scope,
                            definition.name,
                            Binding::Recursive { definition: node },
                        );
                        continue;
                    }
                    let construction = self.compile_function_construction(
                        bounds,
                        definition.body,
                        &definition_context,
                    )?;
                    let compiled = self.cached(Self::mark_costly(construction));
                    scope = bind(
                        &scope,
                        definition.name,
                        Binding::Value {
                            compiled: Box::new(compiled),
                            lazy: Some(Rc::new(LazyFunction {
                                definition: node,
                                context: definition_context,
                                primed: RefCell::new(None),
                            })),
                        },
                    );
                }
                DefinitionForm::Operator(params) if params.is_empty() => {
                    if definition.flags & Definition::RECURSIVE != 0 {
                        return unsupported("a recursive LET definition");
                    }
                    let is_named_once = !is_applied_function
                        && later
                            .iter()
                            .map(|&later| self.definition(later).body)
                            .chain([body])
                            .try_fold(0, |count, root| {
                                Some(
                                    count
                                        + self.count_uses_through_let(
                                            root,
                                            definition.name,
                                            &users,
                                        )?,
                                )
                            })
                            == Some(1);
                    let is_built_alike = !is_applied_function
                        && self.is_used_eagerly_in_let(
                            later,
                            body,
                            definition.name,
                            &mut HashMap::new(),
                        );
                    let argument = Rc::new(Argument {
                        expression: definition.body,
                        is_read_once: uses.is_some_and(|count| count <= 1),
                        reaches_startup: Cell::new(false),
                        is_each_use_alike: uses.is_some_and(|count| count <= 1)
                            || !definitions.iter().chain([&body]).any(|&root| {
                                self.may_write_register(root, &scope, &mut HashSet::new())
                            }),
                        is_kept: is_expression
                            && self.is_kept_name(
                                later
                                    .iter()
                                    .map(|&later| self.definition(later).body)
                                    .chain([body]),
                                definition.name,
                            ),
                        context: definition_context,
                        compiled: RefCell::new([None, None]),
                        own_scope: RefCell::new(Weak::new()),
                        once_slot,
                        is_applied_function,
                        is_named_once,
                        is_built_alike,
                    });
                    if once_slot.is_some() {
                        kept_once.push(Rc::clone(&argument));
                    }
                    scope = bind(&scope, definition.name, Binding::Argument(argument));
                }
                DefinitionForm::Operator(params) => {
                    let is_recursive = definition.flags & Definition::RECURSIVE != 0;
                    let operator = Rc::new(Operator {
                        params: params.clone(),
                        body: OperatorBody::Node(definition.body),
                        context: definition_context,
                        is_recursive,
                        own_scope: RefCell::new(Weak::new()),
                    });
                    scope = bind(
                        &scope,
                        definition.name,
                        Binding::Operator(Rc::clone(&operator)),
                    );
                    if is_recursive && let Some(own) = &scope {
                        *operator.own_scope.borrow_mut() = Rc::downgrade(own);
                        recursive.push(operator);
                    }
                }
            }
        }
        // A RECURSIVE operator of the LET sees the others its declaration names, defined after it
        // too (`Generator.processRecursive`); SANY rejects any other forward name, and a LET
        // shadows none.
        if let Some(own) = &scope {
            for operator in recursive {
                *operator.own_scope.borrow_mut() = Rc::downgrade(own);
            }
        }
        Ok((context.with_scope(scope), kept_once))
    }

    // --- operator application ---

    // Binds the parameters of an operator to its arguments.
    // `body` is the operator's body, which says how often it uses each parameter.
    fn bind_arguments(
        &mut self,
        params: &[Param],
        args: &[NodeId],
        body: Option<NodeId>,
        caller: &Context,
        callee: Context,
    ) -> Compiling<Context> {
        Ok(self
            .bind_arguments_kept(params, args, body, caller, callee, false)?
            .0)
    }

    // `bind_arguments`, where with `is_kept_once` an argument of a call in a constant definition
    // TLC computes as it starts is kept from its first use in the body, as `getOpContext` binds
    // it to a `LazyValue` that `getValue` computes once: the arguments so bound, whose slots the
    // caller clears as the call begins (`keep_once`).
    fn bind_arguments_kept(
        &mut self,
        params: &[Param],
        args: &[NodeId],
        body: Option<NodeId>,
        caller: &Context,
        callee: Context,
        is_kept_once: bool,
    ) -> Compiling<(Context, Vec<Rc<Argument>>)> {
        if params.len() != args.len() {
            return unsupported("an operator applied to the wrong number of arguments");
        }
        let mut kept_once = Vec::new();
        let mut scope = callee.scope.clone();
        let argument_context = caller.without_print();
        for (param, &argument) in params.iter().zip(args) {
            let once_slot = (is_kept_once
                && param.arity == 0
                && body.is_some()
                && self.startup_bodies > 0
                && !caller.is_primed
                && caller.can_print)
                .then(|| self.allocate_slot());
            let binding = if param.arity > 0 {
                Binding::Operator(self.resolve_operator_argument(argument, &argument_context)?)
            } else if once_slot.is_some() {
                let kept = Rc::new(Argument {
                    expression: argument,
                    is_read_once: self.startup_definitions.is_empty()
                        || body.is_some_and(|body| {
                            self.count_uses(body, param.name, &[])
                                .is_some_and(|count| count <= 1)
                        }),
                    reaches_startup: Cell::new(false),
                    is_each_use_alike: true,
                    is_kept: body.is_some_and(|body| self.is_kept_name([body], param.name)),
                    context: caller.clone(),
                    compiled: RefCell::new([None, None]),
                    own_scope: RefCell::new(Weak::new()),
                    once_slot,
                    is_applied_function: false,
                    is_named_once: false,
                    is_built_alike: false,
                });
                kept_once.push(Rc::clone(&kept));
                Binding::Argument(kept)
            } else {
                Binding::Argument(Rc::new(Argument {
                    expression: argument,
                    reaches_startup: Cell::new(false),
                    is_read_once: self.startup_definitions.is_empty()
                        || body.is_some_and(|body| {
                            self.count_uses(body, param.name, &[])
                                .is_some_and(|count| count <= 1)
                        }),
                    is_each_use_alike: body.is_some_and(|body| {
                        self.count_uses(body, param.name, &[])
                            .is_some_and(|count| count <= 1)
                            || !self.may_write_register(body, &callee.scope, &mut HashSet::new())
                    }),
                    is_kept: body.is_some_and(|body| self.is_kept_name([body], param.name)),
                    context: argument_context.clone(),
                    compiled: RefCell::new([None, None]),
                    own_scope: RefCell::new(Weak::new()),
                    once_slot: None,
                    is_applied_function: false,
                    is_named_once: false,
                    is_built_alike: false,
                }))
            };
            scope = bind(&scope, param.name, binding);
        }
        Ok((callee.with_scope(scope), kept_once))
    }

    fn resolve_operator_argument(
        &mut self,
        argument: NodeId,
        context: &Context,
    ) -> Compiling<Rc<Operator>> {
        let name = match self.node(argument).1 {
            NodeKind::Lambda { params, body } => {
                return Ok(Operator::new(
                    params
                        .iter()
                        .map(|&name| Param { name, arity: 0 })
                        .collect(),
                    OperatorBody::Node(*body),
                    context.clone(),
                ));
            }
            NodeKind::Identifier(name) | NodeKind::OperatorReference(name) => *name,
            _ => return unsupported("an operator argument"),
        };
        if let Some(found) = lookup(&context.scope, name.text)
            && let Binding::Operator(operator) = &found.binding
        {
            return Ok(Rc::clone(operator));
        }
        match name.resolution {
            Resolution::Definition(index) => {
                let definition = self.definition(self.ir.definitions[index as usize]);
                if let DefinitionForm::Operator(params) = &definition.form
                    && definition.flags & Definition::RECURSIVE == 0
                {
                    return Ok(Operator::new(
                        params.clone(),
                        OperatorBody::Node(definition.body),
                        context.with_scope(None),
                    ));
                }
            }
            Resolution::Builtin(index) => {
                let builtin = &self.ir.builtins[index as usize];
                return Ok(Operator::new(
                    (0..builtin.arity.max(0))
                        .map(|_| Param {
                            name: u32::MAX,
                            arity: 0,
                        })
                        .collect(),
                    OperatorBody::Builtin(index),
                    context.with_scope(None),
                ));
            }
            _ => {}
        }
        unsupported(format!("the operator argument {}", self.text(name.text)))
    }

    fn compile_apply(
        &mut self,
        name: &Name,
        args: &[NodeId],
        context: &Context,
    ) -> Compiling<Compiled> {
        if name.is_local
            && let Some(found) = lookup(&context.scope, name.text)
        {
            return match &found.binding {
                Binding::Operator(operator) => {
                    let operator = Rc::clone(operator);
                    self.compile_operator_call(&operator, args, context)
                }
                _ => unsupported("applying a local value"),
            };
        }
        match name.resolution {
            Resolution::Definition(index) => {
                let node = self.ir.definitions[index as usize];
                let definition = self.definition(node);
                let DefinitionForm::Operator(params) = &definition.form else {
                    return unsupported("applying a function definition as an operator");
                };
                if definition.flags & Definition::RECURSIVE != 0 || context.is_expanding(node) {
                    return self.compile_recursive_call(
                        RecursiveTarget::Global(node),
                        args,
                        context,
                    );
                }
                let base = Context {
                    expanding: context.expanding_with(node),
                    ..context.global(context.can_print)
                };
                let is_text_serialized = self.is_text_serialized(node, params.len());
                let (callee, kept_once) = self.bind_arguments_kept(
                    params,
                    args,
                    Some(definition.body),
                    context,
                    base,
                    !is_text_serialized,
                )?;
                let compiled = self.compile(definition.body, &callee)?;
                let compiled = self.cached(Self::keep_once(&kept_once, compiled)?);
                if is_text_serialized {
                    return self.compile_text_serialize(args, compiled, context);
                }
                return Ok(compiled);
            }
            // A configuration may substitute a value such as FALSE for an operator with
            // parameters, and TLC then takes the value, without evaluating the arguments
            // (Tool.evalAppl).
            Resolution::Builtin(index) if self.ir.builtins[index as usize].arity == 0 => {
                return self.compile_nullary_builtin(index, context);
            }
            Resolution::Builtin(index) => {
                let operands: Vec<Operand> = args
                    .iter()
                    .map(|&node| Operand {
                        node,
                        context: context.clone(),
                        is_param: false,
                        slot: None,
                    })
                    .collect();
                return self.compile_builtin(index, &operands, context);
            }
            _ => {}
        }
        if let Some(found) = lookup(&context.scope, name.text)
            && let Binding::Operator(operator) = &found.binding
        {
            let operator = Rc::clone(operator);
            return self.compile_operator_call(&operator, args, context);
        }
        // TLC fails on action composition wherever it reaches it, unless a Java property enables
        // its incomplete implementation.
        if self.text(name.text) == "\\cdot" && args.len() == 2 {
            return Ok(leaf(
                eval(|_| Err(Bail("action composition"))),
                Footprint::default(),
            ));
        }
        // TLC fails on a temporal operator wherever it evaluates one (`Tool#evalAppl`), as on
        // []A, which the interpreter words.
        if matches!(self.text(name.text), "~>" | "-+->") && args.len() == 2 {
            return Ok(leaf(
                eval(|_| Err(Bail("a temporal formula in a state"))),
                Footprint::default(),
            ));
        }
        unsupported(format!("the operator {}", self.text(name.text)))
    }

    fn compile_operator_call(
        &mut self,
        operator: &Rc<Operator>,
        args: &[NodeId],
        context: &Context,
    ) -> Compiling<Compiled> {
        if operator.is_recursive {
            return self.compile_recursive_call(
                RecursiveTarget::Local(Rc::clone(operator)),
                args,
                context,
            );
        }
        let base =
            operator_context(operator).primed(context.is_primed || operator.context.is_primed);
        let body = match operator.body {
            OperatorBody::Node(body) => Some(body),
            OperatorBody::Builtin(_) => None,
        };
        let (callee, kept_once) =
            self.bind_arguments_kept(&operator.params, args, body, context, base, true)?;
        let compiled = match operator.body {
            OperatorBody::Node(body) => Self::keep_once(&kept_once, self.compile(body, &callee)?)?,
            OperatorBody::Builtin(index) => {
                // The builtin applied to its parameters, each the argument it is bound to.
                let operands: Vec<Operand> = args
                    .iter()
                    .map(|&argument| Operand {
                        node: argument,
                        context: context
                            .without_print()
                            .primed(callee.is_primed || context.is_primed),
                        is_param: true,
                        slot: None,
                    })
                    .collect();
                self.wrap_compile(|compiler| compiler.compile_builtin(index, &operands, &callee))?
            }
        };
        Ok(self.cached(compiled))
    }

    // --- recursion ---

    // A call of a RECURSIVE operator: a global one, or one a LET defines, whose body sees the
    // LET's scope.
    // IOUtils's Serialize, which TLC but 1.7.4 overrides with `Json.textSerialize`, an
    // @Evaluation method.
    pub(crate) fn is_text_serialized(&self, node: NodeId, arity: usize) -> bool {
        let definition = self.definition(node);
        arity == 3
            && self.text(definition.name) == "Serialize"
            && self.ir.nodes.arena[definition.body as usize]
                .range
                .is_some_and(|range| self.text(range.module) == "IOUtils")
            && !self
                .ir
                .model
                .version
                .is_some_and(|version| self.text(version) == "1.7.4")
    }

    // `Json.textSerialize`: it evaluates the options, then writes NDJSON itself where their
    // format is "NDJSON" and evaluates the definition where it is another string. The engine
    // writes the file where it evaluates the application as TLC does, the options are a record
    // written in place whose open options, charset and format are strings written there, and
    // the write is one it follows (`TextWrite`); elsewhere it stops where TLC writes or fails, for
    // the evaluator of failures to word.
    fn compile_text_serialize(
        &mut self,
        args: &[NodeId],
        fallback: Compiled,
        context: &Context,
    ) -> Compiling<Compiled> {
        // Options whose format is a string other than "NDJSON", written so, read none of their
        // other fields before TLC evaluates the definition.
        let format_text = self.ir.texts.iter().position(|text| &**text == "format");
        let nulls = self
            .null_fields(args[2])
            .filter(|nulls| {
                let NodeKind::Record(fields) = self.node(args[2]).1 else {
                    return false;
                };
                fields.iter().any(|&(name, value)| {
                    Some(name as usize) == format_text
                        && !nulls.iter().any(|(null, _)| *null == value)
                        && matches!(self.node(value).1, NodeKind::String(text) if &*self.ir.texts[*text as usize] != "NDJSON")
                })
            })
            .map(|nulls| nulls.into_iter().map(|(node, _)| node).collect::<Vec<_>>())
            .unwrap_or_default();
        let options =
            self.with_null_substituted(&nulls, |compiler| compiler.compile(args[2], context))?;
        // TLC evaluates the options again as the definition reads them.
        if options.is_printing() {
            return unsupported("IOUtils's Serialize of options that print");
        }
        let format: Vec<u16> = "format".encode_utf16().collect();
        let ndjson: Vec<u16> = "NDJSON".encode_utf16().collect();
        let evaluate_options = options.eval.clone();
        let evaluate_fallback = fallback.eval.clone();
        let mut footprint = options.footprint.merge(&fallback.footprint);
        let write = match self.text_write(args[2], context) {
            Some(write) => {
                let payload = self.compile(args[0], context)?;
                let path = self.compile(args[1], context)?;
                footprint = footprint
                    .merge(&payload.footprint)
                    .merge(&path.footprint)
                    .merge(&Footprint::slot(PRINT_SLOT));
                self.note_effect();
                Some((write, payload.eval, path.eval))
            }
            None => None,
        };
        Ok(leaf(
            eval(move |machine| {
                let options = evaluate_options(machine)?;
                let store = &machine.store;
                let format = tla_values::store::is_function_kind(store.kind_of(options))
                    .then(|| {
                        (0..store.size_of(options)).find_map(|position| {
                            let key = store.peek_key(options, position)?;
                            (store.kind_of(key) == KIND_STRING && store.text_of(key) == format)
                                .then(|| store.get_range_value(options, position))
                        })
                    })
                    .flatten();
                match format {
                    Some(format)
                        if store.kind_of(format) == KIND_STRING
                            && store.text_of(format) != ndjson =>
                    {
                        evaluate_fallback(machine)
                    }
                    Some(_) => match &write {
                        Some((write, payload, path)) => {
                            let payload = payload(machine)?;
                            let path = path(machine)?;
                            write.write(machine, payload, path)
                        }
                        None => Err(Bail(TEXT_SERIALIZED)),
                    },
                    None => Err(Bail(TEXT_SERIALIZED)),
                }
            }),
            footprint,
        ))
    }

    // Whether the model has IOUtils's Serialize, whose NDJSON the engine may write.
    pub(crate) fn writes_text_files(&self) -> bool {
        self.ir.definitions.iter().any(|&node| {
            matches!(&self.definition(node).form, DefinitionForm::Operator(params)
                if self.is_text_serialized(node, params.len()))
        })
    }

    // The write of `Json.textSerialize` the engine follows: where it evaluates the application as
    // TLC does, the options a record written in place whose format is "NDJSON" and whose open
    // options and charset are strings written there, each open option one of WRITE, CREATE,
    // CREATE_NEW, TRUNCATE_EXISTING and APPEND, not both of the last two, and the charset a name
    // of UTF-8, on the file system, not the host's.
    fn text_write(&self, options: NodeId, context: &Context) -> Option<TextWrite> {
        if !context.can_print || !matches!(self.json_files, crate::search::JsonFiles::System) {
            return None;
        }
        let NodeKind::Record(fields) = self.node(options).1 else {
            return None;
        };
        let string = |node: NodeId| match self.node(node).1 {
            NodeKind::String(text) => Some(self.text(*text).to_owned()),
            _ => None,
        };
        let field = |name: &str| {
            let mut found = fields
                .iter()
                .filter(|(field, _)| self.text(*field) == name)
                .map(|&(_, value)| value);
            let value = found.next()?;
            found.next().is_none().then_some(value)
        };
        if string(field("format")?)? != "NDJSON" {
            return None;
        }
        let charset = string(field("charset")?)?;
        if !matches!(
            charset.to_ascii_lowercase().as_str(),
            "utf-8" | "utf8" | "unicode-1-1-utf-8"
        ) {
            return None;
        }
        let NodeKind::Tuple(names) = self.node(field("openOptions")?).1 else {
            return None;
        };
        let names = names
            .iter()
            .map(|&name| string(name))
            .collect::<Option<Vec<String>>>()?;
        let is_named = |option: &str| names.iter().any(|name| name == option);
        if !names.iter().all(|name| {
            matches!(
                name.as_str(),
                "WRITE" | "CREATE" | "CREATE_NEW" | "TRUNCATE_EXISTING" | "APPEND"
            )
        }) || is_named("APPEND") && is_named("TRUNCATE_EXISTING")
        {
            return None;
        }
        let mut open = std::fs::OpenOptions::new();
        // `FileSystemProvider.newOutputStream`: no option is CREATE, TRUNCATE_EXISTING and
        // WRITE; others are as given, with WRITE.
        open.write(true);
        if names.is_empty() {
            open.create(true).truncate(true);
        } else {
            open.create(is_named("CREATE"))
                .create_new(is_named("CREATE_NEW"))
                .truncate(is_named("TRUNCATE_EXISTING"))
                .append(is_named("APPEND"));
        }
        Some(TextWrite { open })
    }

    // A RECURSIVE definition without parameters that names itself in its body, which TLC
    // evaluates again at each such name, as it does an operator's call (`Tool.evalAppl`): only
    // where the evaluation reaches it, so `A == IF TRUE THEN 1 ELSE A` is 1.
    fn compile_recursive_reference(
        &mut self,
        node: NodeId,
        context: &Context,
    ) -> Compiling<Compiled> {
        if self.definition(node).flags & Definition::RECURSIVE == 0 {
            return unsupported("a recursive zero-arity definition");
        }
        self.compile_recursive_call(RecursiveTarget::Global(node), &[], context)
    }

    fn compile_recursive_call(
        &mut self,
        target: RecursiveTarget,
        args: &[NodeId],
        context: &Context,
    ) -> Compiling<Compiled> {
        let (params, body, local_context, key, local) = match &target {
            RecursiveTarget::Global(node) => {
                let definition = self.definition(*node);
                let DefinitionForm::Operator(params) = &definition.form else {
                    unreachable!("a recursive call of a function");
                };
                (
                    params.clone(),
                    OperatorBody::Node(definition.body),
                    None,
                    OperatorKey::Global(*node),
                    None,
                )
            }
            RecursiveTarget::Local(operator) => (
                operator.params.clone(),
                operator.body,
                Some(operator_context(operator)),
                OperatorKey::local(operator),
                Some(Rc::clone(operator)),
            ),
        };
        let OperatorBody::Node(body) = body else {
            return unsupported("a recursive higher-order operator");
        };
        // A global operator with operator parameters, each of which every call of it in its body
        // passes on as it is, compiles for the operators the outermost call passes: TLC binds
        // each to the operator argument (`Tool.getOpContext`), the same one at every depth.
        let (key, local_context) = if params.iter().any(|param| param.arity > 0) {
            let RecursiveTarget::Global(node) = &target else {
                return unsupported("a recursive higher-order operator");
            };
            if !self.passes_operators_on(*node, &params) {
                return unsupported("a recursive higher-order operator");
            }
            let argument_context = context.without_print();
            let mut operators = Vec::new();
            let mut scope = None;
            for (param, &argument) in params.iter().zip(args) {
                if param.arity > 0 {
                    let operator = self.resolve_operator_argument(argument, &argument_context)?;
                    scope = bind(&scope, param.name, Binding::Operator(Rc::clone(&operator)));
                    operators.push(operator);
                }
            }
            let position = match self.specialized.iter().position(|(other, known)| {
                other == node
                    && known.len() == operators.len()
                    && known.iter().zip(&operators).all(|(a, b)| Rc::ptr_eq(a, b))
            }) {
                Some(position) => position,
                None => {
                    self.specialized.push((*node, operators));
                    self.specialized.len() - 1
                }
            };
            let bound = Context {
                scope,
                is_primed: false,
                ..context.global(false)
            };
            (OperatorKey::Specialized(position), Some(bound))
        } else {
            (key, local_context)
        };
        // A primed call reads the primed variables where the body names variables.
        let is_primed =
            context.is_primed || local_context.as_ref().is_some_and(|local| local.is_primed);
        let index = usize::from(is_primed);
        let known = self
            .recursive_operators
            .get(&key)
            .and_then(|(_, entries)| entries[index].clone());
        let recursive = match known {
            Some(recursive) => {
                self.note_read(&recursive.fixed_point);
                self.note_cached_read(recursive.entry);
                recursive
            }
            None => {
                let global = match &target {
                    RecursiveTarget::Global(node) => Some(*node),
                    RecursiveTarget::Local(..) => None,
                };
                self.compile_recursive_operator(
                    key,
                    local,
                    global,
                    &params,
                    body,
                    local_context,
                    is_primed,
                    context,
                )?
            }
        };
        // `Tool.evalAppl` binds each argument as a `LazyValue`, which TLC evaluates only where the
        // body reads the parameter: one the body never names is never evaluated, failing or
        // printing as it may, so the call leaves its slot unbound.
        let compiled_args = args
            .iter()
            .zip(&params)
            .map(|(&argument, param)| {
                if param.arity == 0 && self.may_name(body, param.name) {
                    self.compile(argument, context)
                } else {
                    Ok(constant(FALSE))
                }
            })
            .collect::<Compiling<Vec<Compiled>>>()?;
        let arg_evals: Vec<Eval> = compiled_args
            .iter()
            .map(|argument| argument.eval.clone())
            .collect();
        let slots = recursive.slots.clone();
        let runtime = recursive.runtime;
        // While the body compiles, a call inside it reads what the operator assumes it does.
        let read = match &*recursive.body_footprint.borrow() {
            Some(body) => body.without_slots(&recursive.slots),
            None => recursive.assumed.borrow().clone(),
        };
        // TLC evaluates an argument where the body first reads it, after what the body printed
        // or drew before: where one fails, the engine stops rather than order the two.
        let is_body_printing = read.slots.contains(&PRINT_SLOT);
        let evaluate = eval(move |machine| {
            if is_body_printing && machine.depth >= PRINTING_RECURSION_LIMIT {
                return Err(Bail(PRINTING_RECURSION_TOO_DEEP));
            }
            let at = machine.stack.len();
            for argument in &arg_evals {
                let value = match argument(machine) {
                    Ok(value) => value,
                    Err(bail) => {
                        machine.stack.truncate(at);
                        if is_body_printing {
                            return Err(Bail(RECURSIVE_ARGUMENT_FAILED));
                        }
                        return Err(bail);
                    }
                };
                machine.stack.push(value);
            }
            for (offset, &slot) in slots.iter().enumerate() {
                std::mem::swap(
                    &mut machine.locals[slot as usize],
                    &mut machine.stack[at + offset],
                );
            }
            let result = machine.call_recursive(runtime);
            for (offset, &slot) in slots.iter().enumerate() {
                machine.locals[slot as usize] = machine.stack[at + offset];
            }
            machine.stack.truncate(at);
            result
        });
        let footprint = Footprint::merge_all(
            compiled_args
                .iter()
                .map(|argument| &argument.footprint)
                .chain([&read]),
        );
        Ok(Compiled {
            is_normalized: recursive.is_normalized.get(),
            is_enumerated: recursive.is_enumerated.get(),
            ..leaf(evaluate, footprint)
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn compile_recursive_operator(
        &mut self,
        key: OperatorKey,
        local: Option<Rc<Operator>>,
        global: Option<NodeId>,
        params: &[Param],
        body: NodeId,
        local_context: Option<Context>,
        is_primed: bool,
        context: &Context,
    ) -> Compiling<Rc<RecursiveOperator>> {
        let index = usize::from(is_primed);
        let slots: Vec<u32> = params.iter().map(|_| self.allocate_slot()).collect();
        let created = Rc::new(RecursiveOperator {
            entry: self.next_entry(),
            runtime: self.allocate_runtime(),
            slots: slots.clone(),
            is_normalized: Cell::new(true),
            is_enumerated: Cell::new(true),
            assumed: RefCell::new(Footprint::default()),
            body_footprint: RefCell::new(None),
            fixed_point: Rc::new(FixedPoint {
                is_settled: Cell::new(false),
                dependents: RefCell::new(Vec::new()),
            }),
        });
        self.recursive_operators
            .entry(key)
            .or_insert_with(|| (local, [None, None]))
            .1[index] = Some(Rc::clone(&created));
        let expanding = match (global, &local_context) {
            (Some(node), _) => context.expanding_with(node),
            (None, local) => local.as_ref().and_then(|local| local.expanding.clone()),
        };
        let mut scope = local_context.and_then(|local| local.scope);
        // An operator parameter is bound in the specialization's scope.
        for (param, &slot) in params.iter().zip(&slots) {
            if param.arity == 0 {
                scope = bind(&scope, param.name, Binding::Slot(slot));
            }
        }
        // TLC evaluates the body at each call (`Tool.evalAppl`), so it may print where the call
        // is evaluated as TLC evaluates it (`are_arguments_effect_free`).
        let body_context = Context {
            scope,
            is_primed,
            is_init: context.is_init,
            can_print: context.can_print,
            is_walked: context.is_walked,
            expanding,
        };
        let mut read = Vec::new();
        let settled = self.settle_operator(&created, body, &body_context, &mut read);
        let (compiled_body, slot_start, slot_end) = match settled {
            Ok(settled) => settled,
            Err(error) => {
                // Nothing keeps what compiled against an operator whose body didn't.
                self.forget_operator(key, index, created.entry);
                self.drop_dependents(&created.fixed_point);
                return Err(error);
            }
        };
        created.fixed_point.is_settled.set(true);
        created.fixed_point.dependents.borrow_mut().clear();
        // An operator whose body called another one that hadn't settled, as mutually recursive
        // operators do, compiles again when that one's assumption grows.
        self.remember_reads(
            created.entry,
            &read,
            Dependent::Operator {
                key,
                index,
                entry: created.entry,
            },
        );
        let footprint = compiled_body.footprint.clone();
        let mut sorted_slots = slots.clone();
        sorted_slots.sort_unstable();
        let key_slots =
            slots_footprint(sorted_slots).merge(&slots_footprint(footprint.slots.clone()));
        self.settle_runtime(
            created.runtime,
            compiled_body,
            &footprint,
            &key_slots.slots,
            slot_start,
            slot_end,
            None,
        );
        Ok(created)
    }

    fn forget_operator(&mut self, key: OperatorKey, index: usize, entry: u64) {
        if let Some((_, entries)) = self.recursive_operators.get_mut(&key)
            && entries[index].as_ref().map(|known| known.entry) == Some(entry)
        {
            entries[index] = None;
        }
    }

    // Compiles a recursive operator's body until what it reads settles. Each compile can only
    // take away what the last one claimed, and add to what the body reads, so this settles.
    fn settle_operator(
        &mut self,
        created: &Rc<RecursiveOperator>,
        body: NodeId,
        body_context: &Context,
        read: &mut Vec<Rc<FixedPoint>>,
    ) -> Compiling<(Compiled, u32, u32)> {
        loop {
            let slot_start = self.program.slot_count as u32;
            let compiled = self.tracking(read, |compiler| compiler.compile(body, body_context))?;
            let slot_end = self.program.slot_count as u32;
            *created.body_footprint.borrow_mut() = Some(compiled.footprint.clone());
            let body_read = compiled.footprint.without_slots(&created.slots);
            if !((created.is_normalized.get() && !compiled.is_normalized)
                || (created.is_enumerated.get() && !compiled.is_enumerated)
                || !body_read.is_within(&created.assumed.borrow()))
            {
                return Ok((compiled, slot_start, slot_end));
            }
            created
                .is_normalized
                .set(created.is_normalized.get() && compiled.is_normalized);
            created
                .is_enumerated
                .set(created.is_enumerated.get() && compiled.is_enumerated);
            let assumed = created.assumed.borrow().merge(&body_read);
            *created.assumed.borrow_mut() = assumed;
            *created.body_footprint.borrow_mut() = None;
            self.drop_dependents(&created.fixed_point);
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn settle_runtime(
        &mut self,
        runtime: usize,
        body: Compiled,
        footprint: &Footprint,
        key_slots: &[u32],
        slot_start: u32,
        slot_end: u32,
        domain: Option<Member>,
    ) {
        let width = key_slots.len() + footprint.vars.len() + footprint.primes.len();
        // A recursive definition without parameters that reads no variable keys no table, nor
        // does one that may print or draw, which TLC evaluates again at each call.
        let table = (width > 0
            && width <= MAXIMUM_MEMO_WIDTH
            && !self.options.is_memo_off
            && !footprint.slots.contains(&PRINT_SLOT))
        .then(|| self.allocate_table(width, true));
        let keys = footprint
            .vars
            .iter()
            .map(|&variable| Key::Current(variable))
            .chain(footprint.primes.iter().map(|&variable| Key::Next(variable)))
            .chain(key_slots.iter().map(|&slot| Key::Slot(slot)))
            .collect();
        self.program.recursives[runtime] = Some(Recursive {
            body: body.eval,
            table,
            keys,
            slot_start,
            slot_end,
            domain,
        });
    }

    fn compile_function_definition(
        &mut self,
        node: NodeId,
        context: &Context,
    ) -> Compiling<Compiled> {
        let definition = self.definition(node);
        if definition.flags & (Definition::RECURSIVE | Definition::SELF_REFERENTIAL) != 0 {
            let scope = self.global_function_scope(node);
            let recursive = self.get_recursive_function(node, context, Some(scope))?;
            return self.materialize_recursive(&recursive);
        }
        let index = definition_index(context);
        if let Some((entry, known)) = self
            .definition_cache
            .get(&node)
            .and_then(|entries| entries[index].clone())
        {
            self.note_cached_read(entry);
            return Ok(known);
        }
        let DefinitionForm::Function(bounds) = &definition.form else {
            unreachable!("a function definition that isn't one");
        };
        let body_context = context.global(false);
        let mut read = Vec::new();
        let compiled = self.tracking(&mut read, |compiler| {
            let construction =
                compiler.compile_function_construction(bounds, definition.body, &body_context)?;
            Ok(compiler.cached(Self::mark_costly(construction)))
        })?;
        self.cache_definition(node, index, compiled.clone(), &read);
        Ok(compiled)
    }

    fn conversion_once(&mut self, node: NodeId) -> usize {
        if let Some(&once) = self.conversion_onces.get(&node) {
            return once;
        }
        let once = self.allocate_once();
        self.conversion_onces.insert(node, once);
        once
    }

    // A recursive function as a value: its body applied to each element of its domain. One TLC
    // keeps lazy as it starts it converts once (`FcnLambdaValue.toFcnRcd`), applying itself
    // lazily inside, and keeps what it built for the rest of the run.
    fn materialize_recursive(&mut self, recursive: &Rc<RecursiveFunction>) -> Compiling<Compiled> {
        let Some(once) = recursive.converted else {
            return Ok(self.build_recursive(recursive));
        };
        if !self.is_converting {
            return unsupported(KEPT_LAZY_USED_AS_VALUE);
        }
        let built = self.build_recursive(recursive);
        let build = built.eval;
        Ok(Compiled {
            is_costly: false,
            ..leaf(
                eval(move |machine| {
                    let known = machine.onces[once];
                    if known != crate::memo::EMPTY {
                        return Ok(known);
                    }
                    if !machine.is_starting {
                        return Err(Bail(KEPT_LAZY_AFTER_STARTUP));
                    }
                    let value = build(machine)?;
                    machine.onces[once] = value;
                    Ok(value)
                }),
                built.footprint,
            )
        })
    }

    fn build_recursive(&mut self, recursive: &Rc<RecursiveFunction>) -> Compiled {
        let domain = recursive.domain.eval.clone();
        let runtime = recursive.runtime;
        let slot = recursive.slot;
        Compiled {
            is_costly: true,
            ..leaf(
                eval(move |machine| {
                    let domain = domain(machine)?;
                    if machine.store.kind_of(domain) != tla_values::store::KIND_SET {
                        return Err(Bail("a function over a non-set"));
                    }
                    let size = machine.store.size_of(domain);
                    let at = machine.stack.len();
                    for index in 0..size {
                        let element = machine.store.element_at(domain, index);
                        match call_recursive_function(machine, runtime, slot, element) {
                            Ok(value) => machine.stack.push(value),
                            Err(bail) => {
                                machine.stack.truncate(at);
                                return Err(bail);
                            }
                        }
                    }
                    let values = machine.stack.split_off(at);
                    let function = machine.store.function_over_set(domain, &values);
                    Ok(machine.store.mark_built_as_function(function))
                }),
                recursive.footprint(),
            )
        }
    }

    // A function defined in terms of itself, such as f[n \in Nat] == IF n = 0 THEN 1 ELSE n *
    // f[n-1]. Applying it evaluates its body with the argument bound, cached by the argument and
    // whatever else the body reads.
    fn get_recursive_function(
        &mut self,
        node: NodeId,
        context: &Context,
        base_scope: Option<Rc<Scope>>,
    ) -> Compiling<Rc<RecursiveFunction>> {
        let index = usize::from(context.is_primed);
        let key = (
            node,
            base_scope
                .as_ref()
                .map_or(0, |scope| Rc::as_ptr(scope) as usize),
        );
        let known = self
            .recursive_functions
            .get(&key)
            .and_then(|(_, entries)| entries[index].clone());
        if let Some(known) = known {
            self.note_read(&known.fixed_point);
            self.note_cached_read(known.entry);
            return Ok(known);
        }
        let definition = self.definition(node);
        let DefinitionForm::Function(bounds) = &definition.form else {
            unreachable!("a recursive function that isn't one");
        };
        let Some(params) = self.parameter_paths(bounds) else {
            return unsupported("a recursive function over a tuple pattern");
        };
        let construction = match self.node(definition.body).1 {
            NodeKind::FunctionConstruction { bounds, body, .. } => {
                names_of(bounds).map(|names| (bounds, *body, parameter_paths_of_names(&names)))
            }
            _ => None,
        };
        // One TLC keeps lazy as it starts prints where it is applied or converted, which the
        // engine follows.
        let converted = self
            .is_kept_lazy_at_startup(node)
            .then(|| self.conversion_once(node));
        let outer = Context {
            scope: base_scope.clone(),
            can_print: converted.is_some(),
            ..context.clone()
        };
        let slot = self.allocate_slot();
        let mut read = Vec::new();
        let domain = self.tracking(&mut read, |compiler| match &bounds[..] {
            [bound] => compiler.compile(bound.set, &outer),
            bounds => {
                let factors = bounds
                    .iter()
                    .map(|bound| compiler.compile(bound.set, &outer))
                    .collect::<Compiling<Vec<Compiled>>>()?;
                Ok(compiler.product_of(&factors))
            }
        })?;
        let record = Rc::new(RecursiveFunction {
            entry: self.next_entry(),
            runtime: self.allocate_runtime(),
            slot,
            arity: bounds.len(),
            domain,
            element: construction
                .is_some()
                .then(|| (self.allocate_runtime(), self.allocate_slot())),
            converted,
            assumed: RefCell::new(Footprint::default()),
            body_footprint: RefCell::new(None),
            fixed_point: Rc::new(FixedPoint {
                is_settled: Cell::new(false),
                dependents: RefCell::new(Vec::new()),
            }),
        });
        self.recursive_functions
            .entry(key)
            .or_insert_with(|| (base_scope.clone(), [None, None]))
            .1[index] = Some(Rc::clone(&record));
        let scope = bind_parameters(&base_scope, &params, slot);
        let body_context = outer.with_scope(scope);
        let settled = self
            .settle_function(&record, definition.body, &body_context, &mut read)
            .and_then(|settled| {
                let element = match (record.element, &construction) {
                    (Some((_, element_slot)), Some((bounds, body, names))) => {
                        let element_context = body_context.with_scope(bind_parameters(
                            &body_context.scope,
                            names,
                            element_slot,
                        ));
                        Some(self.tracking(&mut read, |compiler| {
                            let slot_start = compiler.program.slot_count as u32;
                            let element = compiler.compile(*body, &element_context)?;
                            let slot_end = compiler.program.slot_count as u32;
                            let domain = match &bounds[..] {
                                [bound] => compiler.compile(bound.set, &body_context)?,
                                bounds => {
                                    let factors = bounds
                                        .iter()
                                        .map(|bound| compiler.compile(bound.set, &body_context))
                                        .collect::<Compiling<Vec<Compiled>>>()?;
                                    compiler.product_of(&factors)
                                }
                            };
                            Ok((element, slot_start, slot_end, compiler.member_test(&domain)))
                        })?)
                    }
                    _ => None,
                };
                Ok((settled, element))
            });
        let ((body, slot_start, slot_end), element) = match settled {
            Ok(settled) => settled,
            Err(error) => {
                if let Some((_, entries)) = self.recursive_functions.get_mut(&key)
                    && entries[index]
                        .as_ref()
                        .is_some_and(|known| Rc::ptr_eq(known, &record))
                {
                    entries[index] = None;
                }
                self.drop_dependents(&record.fixed_point);
                return Err(error);
            }
        };
        record.fixed_point.is_settled.set(true);
        record.fixed_point.dependents.borrow_mut().clear();
        self.remember_reads(
            record.entry,
            &read,
            Dependent::Function {
                key,
                index,
                entry: record.entry,
            },
        );
        let footprint = body.footprint.clone();
        let key_slots = Footprint::slot(slot).merge(&slots_footprint(footprint.slots.clone()));
        let domain_member = self.member_test(&record.domain);
        self.settle_runtime(
            record.runtime,
            body,
            &footprint,
            &key_slots.slots,
            slot_start,
            slot_end,
            Some(domain_member),
        );
        if let (Some((runtime, element_slot)), Some((element, slot_start, slot_end, member))) =
            (record.element, element)
        {
            let footprint = element.footprint.clone();
            let key_slots = Footprint::slot(slot)
                .merge(&Footprint::slot(element_slot))
                .merge(&slots_footprint(footprint.slots.clone()));
            self.settle_runtime(
                runtime,
                element,
                &footprint,
                &key_slots.slots,
                slot_start,
                slot_end,
                Some(member),
            );
        }
        Ok(record)
    }

    // A call inside the body reads what the last compile of the body read, until it reads no
    // more.
    fn settle_function(
        &mut self,
        record: &Rc<RecursiveFunction>,
        body: NodeId,
        body_context: &Context,
        read: &mut Vec<Rc<FixedPoint>>,
    ) -> Compiling<(Compiled, u32, u32)> {
        loop {
            let slot_start = self.program.slot_count as u32;
            let compiled = self.tracking(read, |compiler| compiler.compile(body, body_context))?;
            let slot_end = self.program.slot_count as u32;
            let body_read = compiled.footprint.without_slots(&[record.slot]);
            if body_read.is_within(&record.assumed.borrow()) {
                *record.body_footprint.borrow_mut() = Some(compiled.footprint.clone());
                return Ok((compiled, slot_start, slot_end));
            }
            let assumed = record.assumed.borrow().merge(&body_read);
            *record.assumed.borrow_mut() = assumed;
            self.drop_dependents(&record.fixed_point);
        }
    }

    // The recursive function an application applies, when it names one, or an operator or a LET
    // gives one, which TLC keeps lazy.
    fn get_applied_recursive_function(
        &mut self,
        function: NodeId,
        context: &Context,
    ) -> Compiling<Option<Rc<RecursiveFunction>>> {
        let name = match self.node(function).1 {
            NodeKind::Identifier(name) => *name,
            NodeKind::Let {
                definitions, body, ..
            } => {
                let inner = self.bind_let_definitions(definitions, *body, context, true)?;
                return self.get_applied_recursive_function(*body, &inner);
            }
            NodeKind::Apply { .. } => {
                return match self.resolve_action(function, context)? {
                    Some((body, inner)) => self.get_applied_recursive_function(body, &inner),
                    None => Ok(None),
                };
            }
            _ => return Ok(None),
        };
        if let Some(found) = lookup(&context.scope, name.text) {
            return match &found.binding {
                Binding::Recursive { definition } => {
                    let definition = *definition;
                    self.get_recursive_function(definition, context, Some(Rc::clone(&found)))
                        .map(Some)
                }
                // An operator's argument that names one, which TLC passes as its lazy value.
                Binding::Argument(argument) => {
                    let is_primed = context.is_primed || argument.context.is_primed;
                    let argument_context = argument_context(argument).primed(is_primed);
                    self.get_applied_recursive_function(argument.expression, &argument_context)
                }
                _ => Ok(None),
            };
        }
        let Resolution::Definition(index) = name.resolution else {
            return Ok(None);
        };
        let node = self.ir.definitions[index as usize];
        let definition = self.definition(node);
        if matches!(definition.form, DefinitionForm::Operator(_)) {
            return match self.resolve_action(function, context)? {
                Some((body, inner)) => self.get_applied_recursive_function(body, &inner),
                None => Ok(None),
            };
        }
        if definition.flags & (Definition::RECURSIVE | Definition::SELF_REFERENTIAL) == 0 {
            return Ok(None);
        }
        let scope = self.global_function_scope(node);
        self.get_recursive_function(node, context, Some(scope))
            .map(Some)
    }

    // An instance copies a recursive function with its body naming it as the module did, which
    // the interpreter binds when it builds the function, as LET binds its own.
    fn global_function_scope(&mut self, node: NodeId) -> Rc<Scope> {
        if let Some(scope) = self.global_function_scopes.get(&node) {
            return Rc::clone(scope);
        }
        let name = self.definition(node).name;
        let scope = Rc::new(Scope {
            name,
            binding: Binding::Recursive { definition: node },
            parent: None,
        });
        self.global_function_scopes.insert(node, Rc::clone(&scope));
        scope
    }
}

impl Compiler<'_> {
    // Whether the body of a global recursive operator applies it only with each of its operator
    // parameters passed on as written in its place, names it nowhere else, and names each
    // operator parameter only to apply it or to pass it on so: TLC looks a LAMBDA's names up
    // where it applies it, so one that names an operator parameter and is passed to a deeper
    // call reads that call's binding.
    fn passes_operators_on(&self, node: NodeId, params: &[Param]) -> bool {
        let definition = self.definition(node);
        let is_operator_param = |text: TextId| {
            params
                .iter()
                .any(|param| param.arity > 0 && param.name == text)
        };
        let mut seen = HashSet::new();
        let mut pending = vec![definition.body];
        while let Some(at) = pending.pop() {
            if !seen.insert(at) {
                continue;
            }
            let kind = &self.ir.nodes.arena[at as usize].kind;
            let names_this = |name: &Name| {
                !name.is_local
                    && matches!(name.resolution, Resolution::Definition(index)
                        if self.ir.definitions[index as usize] == node)
            };
            match kind {
                NodeKind::Apply { name, args } if names_this(name) => {
                    if args.len() != params.len() {
                        return false;
                    }
                    for (param, &argument) in params.iter().zip(args) {
                        if param.arity == 0 {
                            pending.push(argument);
                            continue;
                        }
                        let passed = matches!(&self.ir.nodes.arena[argument as usize].kind,
                            NodeKind::Identifier(name) | NodeKind::OperatorReference(name)
                                if name.is_local && name.text == param.name);
                        if !passed {
                            return false;
                        }
                    }
                    continue;
                }
                NodeKind::Identifier(name) | NodeKind::OperatorReference(name)
                    if names_this(name) || name.is_local && is_operator_param(name.text) =>
                {
                    return false;
                }
                NodeKind::Subexpression(_) => return false,
                NodeKind::Reference(target) => pending.push(*target),
                NodeKind::SetFilter { bound, .. } => pending.push(bound.set),
                _ => {}
            }
            pending.extend(kind.children());
        }
        true
    }

    // Whether an expression may name a text anywhere within it, a subexpression selector counting
    // as one that may.
    fn may_name(&self, root: NodeId, text: TextId) -> bool {
        let mut seen = HashSet::new();
        let mut pending = vec![root];
        while let Some(node) = pending.pop() {
            if !seen.insert(node) {
                continue;
            }
            match &self.ir.nodes.arena[node as usize].kind {
                NodeKind::Identifier(name)
                | NodeKind::OperatorReference(name)
                | NodeKind::Apply { name, .. }
                    if name.text == text =>
                {
                    return true;
                }
                NodeKind::Subexpression(_) => return true,
                NodeKind::Reference(target) => pending.push(*target),
                NodeKind::SetFilter { bound, .. } => pending.push(bound.set),
                _ => {}
            }
            pending.extend(self.ir.nodes.arena[node as usize].kind.children());
        }
        false
    }

    // Where each parameter of a function is in the argument it is applied to: the argument, or
    // with several bounds its element for the bound, and within a tuple pattern its element for
    // the name. A tuple pattern is followed where its set is a product of as many sets, so the
    // domain's membership, which TLC tests first (`FcnLambdaValue.apply`), leaves only tuples of
    // its length.
    fn parameter_paths(&self, bounds: &[Bound]) -> Option<Vec<(TextId, Vec<u32>)>> {
        let is_several = bounds.len() > 1;
        let mut paths = Vec::new();
        for (index, bound) in bounds.iter().enumerate() {
            let outer: Vec<u32> = if is_several {
                vec![index as u32]
            } else {
                Vec::new()
            };
            match &bound.pattern {
                tla_ir::Pattern::Name(name) => paths.push((*name, outer)),
                tla_ir::Pattern::Tuple(names) => {
                    if !matches!(self.node(bound.set).1, NodeKind::Product(factors) if factors.len() == names.len())
                    {
                        return None;
                    }
                    for (position, &name) in names.iter().enumerate() {
                        let mut path = outer.clone();
                        path.push(position as u32);
                        paths.push((name, path));
                    }
                }
            }
        }
        Some(paths)
    }
}

fn parameter_paths_of_names(names: &[TextId]) -> Vec<(TextId, Vec<u32>)> {
    match names {
        [name] => vec![(*name, Vec::new())],
        names => names
            .iter()
            .enumerate()
            .map(|(index, &name)| (name, vec![index as u32]))
            .collect(),
    }
}

fn names_of(bounds: &[Bound]) -> Option<Vec<TextId>> {
    bounds
        .iter()
        .map(|bound| match bound.pattern {
            tla_ir::Pattern::Name(name) => Some(name),
            tla_ir::Pattern::Tuple(_) => None,
        })
        .collect()
}

// The scope binding a function's parameters to the argument in a slot, each where
// `parameter_paths` places it.
fn bind_parameters(
    base: &Option<Rc<Scope>>,
    params: &[(TextId, Vec<u32>)],
    slot: u32,
) -> Option<Rc<Scope>> {
    params.iter().fold(base.clone(), |scope, (param, path)| {
        if path.is_empty() {
            return bind(&scope, *param, Binding::Slot(slot));
        }
        let path: Arc<[u32]> = path.as_slice().into();
        let element = leaf(
            eval(move |machine| {
                Ok(path
                    .iter()
                    .fold(machine.locals[slot as usize], |value, &index| {
                        machine.store.get_range_value(value, index)
                    }))
            }),
            Footprint::slot(slot),
        );
        let binding = Binding::Value {
            compiled: Box::new(element),
            lazy: None,
        };
        bind(&scope, *param, binding)
    })
}

fn slots_footprint(slots: Vec<u32>) -> Footprint {
    Footprint {
        slots,
        ..Footprint::default()
    }
}

enum RecursiveTarget {
    Global(NodeId),
    Local(Rc<Operator>),
}

pub(crate) fn call_recursive_function(
    machine: &mut Machine<'_>,
    runtime: usize,
    slot: u32,
    argument: Id,
) -> Outcome<Id> {
    let domain = machine.recursive_domain(runtime);
    if !domain(machine, argument)? {
        return Err(Bail("applied a recursive function outside its domain"));
    }
    let saved = machine.locals[slot as usize];
    machine.locals[slot as usize] = argument;
    let result = machine.call_recursive(runtime);
    machine.locals[slot as usize] = saved;
    result
}

// f[a][b] where f's body is a function construction, with a in f's domain: TLC applies f to a,
// keeping the construction lazy, and then applies that to b, evaluating its body for b alone.
pub(crate) fn call_recursive_element(
    machine: &mut Machine<'_>,
    slot: u32,
    (element_runtime, element_slot): (usize, u32),
    argument: Id,
    element: Id,
) -> Outcome<Id> {
    let saved = (
        machine.locals[slot as usize],
        machine.locals[element_slot as usize],
    );
    machine.locals[slot as usize] = argument;
    let element_domain = machine.recursive_domain(element_runtime);
    let result = match element_domain(machine, element) {
        Ok(true) => {
            machine.locals[element_slot as usize] = element;
            machine.call_recursive(element_runtime)
        }
        Ok(false) => Err(Bail("applied a function outside its domain")),
        Err(bail) => Err(bail),
    };
    machine.locals[slot as usize] = saved.0;
    machine.locals[element_slot as usize] = saved.1;
    result
}

/// How `Json.textSerialize` opens its file, for the NDJSON it writes there.
struct TextWrite {
    open: std::fs::OpenOptions,
}

impl TextWrite {
    // The payload `Value.toTuple` makes, each element's JSON (`getNode`) on a line of its own,
    // written in UTF-8 to the file opened as TLC opens it (`Files.newBufferedWriter`). What TLC
    // fails at, a payload that isn't a sequence, a file that isn't a string or that it can't open,
    // and a value it can't convert, after it opened the file, stops for the evaluator of failures
    // before the engine opens anything.
    fn write(&self, machine: &mut Machine<'_>, payload: Id, path: Id) -> Outcome<Id> {
        let store = &machine.store;
        if store.kind_of(payload) != tla_values::store::KIND_TUPLE
            || store.kind_of(path) != KIND_STRING
            || tla_values::json::holds_ordered_keys(store, payload)
        {
            return Err(Bail(TEXT_SERIALIZED));
        }
        let Ok(path) = String::from_utf16(store.text_of(path)) else {
            return Err(Bail(TEXT_SERIALIZED));
        };
        // `Paths.get` drops a repeated or final slash, which a failure's path would show.
        if path.is_empty() || path.contains('\0') || path.contains("//") || path.ends_with('/') {
            return Err(Bail(TEXT_SERIALIZED));
        }
        let mut text = Vec::new();
        for index in 0..store.size_of(payload) {
            tla_values::json::write_json(store, store.get_range_value(payload, index), &mut text)
                .map_err(|_| Bail(TEXT_SERIALIZED))?;
            text.push(u16::from(b'\n'));
        }
        let Ok(text) = String::from_utf16(&text) else {
            return Err(Bail(TEXT_SERIALIZED));
        };
        // A run that declines puts the file back as it was (`tla_values::written::restore`).
        let path = std::path::Path::new(&path);
        if tla_values::written::keep_file(path).is_err() {
            return Err(Bail(
                "unsupported: IOUtils's Serialize of a file that can't be read before it is written",
            ));
        }
        let mut file = self.open.open(path).map_err(|_| Bail(TEXT_SERIALIZED))?;
        std::io::Write::write_all(&mut file, text.as_bytes())
            .map_err(|_| Bail("unsupported: IOUtils's Serialize that fails to write"))?;
        Ok(TRUE)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn total_merge_proof_handles_deep_syntax_without_recursing() {
        std::thread::Builder::new()
            .stack_size(128 * 1024)
            .spawn(|| {
                let bytes = std::fs::read(concat!(
                    env!("CARGO_MANIFEST_DIR"),
                    "/../../../tests/conformance/ir/examples/specifications/ReadersWriters/MC.ir"
                ))
                .expect("a golden IR");
                let mut ir = tla_ir::decode(&bytes).expect("the golden IR decodes");
                let mut push = |kind| {
                    let id = ir.nodes.arena.len() as NodeId;
                    ir.nodes.arena.push(tla_ir::Node {
                        line: 1,
                        column: 1,
                        range: None,
                        kind,
                    });
                    id
                };
                let empty = push(NodeKind::SetEnumeration(vec![]));
                let mut set = empty;
                let mut argument = empty;
                for _ in 0..50_000 {
                    set = push(NodeKind::Product(vec![set, empty]));
                    set = push(NodeKind::FunctionSet {
                        domain: set,
                        range: empty,
                    });
                    argument = push(NodeKind::Tuple(vec![argument, set]));
                }
                // The same DAG node is admissible as an argument but not as a set.
                let invalid_set = push(NodeKind::FunctionSet {
                    domain: argument,
                    range: empty,
                });
                let mixed = push(NodeKind::Tuple(vec![invalid_set, argument]));
                let mut store = Store::new();
                let compiler = Compiler::new(&ir, &mut store, Options::default());
                assert!(compiler.is_total_merge_argument(set));
                assert!(compiler.is_total_merge_argument(argument));
                assert!(!compiler.is_total_merge_argument(mixed));
            })
            .expect("spawn proof test")
            .join()
            .expect("proof completes on a small stack");
    }

    #[test]
    fn keys_a_global_and_a_local_operator_apart() {
        let keys = HashSet::from([OperatorKey::Global(7), OperatorKey::Local(7)]);
        assert_eq!(keys.len(), 2);
    }
}
