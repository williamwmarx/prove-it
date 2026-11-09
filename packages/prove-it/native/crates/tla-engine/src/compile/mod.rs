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
mod builtins;
mod fused;
pub(crate) mod lazy;
mod nodes;
pub(crate) mod predicate;
mod sets;
mod walker;

pub use walker::ActionOptions;

use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet};
use std::fmt::Display;
use std::rc::{Rc, Weak};
use std::sync::Arc;

use tla_ir::{
    Definition, DefinitionForm, Index, Ir, Name, NodeId, NodeKind, Param, Resolution, Startup,
    TextId, Value,
};
use tla_values::store::{FALSE, Outcome, TRUE};
use tla_values::{Bail, Id, Store};

use crate::footprint::Footprint;
use crate::machine::{Eval, Key, Machine, Member, Parts, Program, Recursive};
use crate::memo::EPOCH_KEYS;

/// What TLCGet reads of TLC's search, at slots of their own so that an expression that reads one
/// is cached by its value: the level of the current state and of the next, and the number of
/// distinct states, which the search sets. An expression that prints has the print slot, which
/// nothing sets, in its footprint, and nothing caches it.
pub const LEVEL_SLOT: u32 = 0;
pub const NEXT_LEVEL_SLOT: u32 = 1;
pub const DISTINCT_SLOT: u32 = 2;
const PRINT_SLOT: u32 = 3;
const SEARCH_SLOTS: [u32; 4] = [LEVEL_SLOT, NEXT_LEVEL_SLOT, DISTINCT_SLOT, PRINT_SLOT];

const MAXIMUM_MEMO_WIDTH: usize = 6;
const MAXIMUM_EXPANSION: u32 = 2000;

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
    pub slots: Vec<u32>,
    pub tuple: bool,
    pub predicate: predicate::Test,
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
    /// provenance, such as a bound name's, may not; and whether each of its elements is.
    pub(crate) is_in_order: bool,
    pub(crate) are_elements_in_order: bool,
    /// Whether the value is always TRUE or FALSE.
    pub(crate) is_boolean: bool,
    pub(crate) is_constant: bool,
    /// Nat, Int, STRING, Seq(S), or a union with one of them, which the engine only tests.
    pub(crate) infinite: Option<&'static str>,
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
    /// For `SUBSET S`: S, which `\subseteq` of two power sets compares in their place.
    pub(crate) subset_base: Option<Box<Compiled>>,
}

impl Compiled {
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

    fn is_printing(&self) -> bool {
        self.footprint.slots.contains(&PRINT_SLOT)
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
        is_boolean: false,
        is_constant: false,
        infinite: None,
        member: None,
        parts: None,
        shape: Shape::Other,
        interval: None,
        filter: None,
        predicate: None,
        reference: None,
        subset_base: None,
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
}

impl Context {
    pub(crate) const ROOT: Context = Context {
        scope: None,
        is_primed: false,
        is_init: false,
        can_print: false,
    };

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
            is_primed: self.is_primed,
            is_init: self.is_init,
            can_print,
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
    compiled: RefCell<[Option<Compiled>; 2]>,
    /// For a binding of an instance's scope whose expression closes over that scope: the scope
    /// that binds it, which its context reaches.
    own_scope: RefCell<Weak<Scope>>,
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

#[derive(Clone, Copy)]
enum Dependent {
    Definition {
        definition: NodeId,
        index: usize,
        entry: u64,
    },
    Operator {
        key: usize,
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
    slot: u32,
    domain: Compiled,
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
// A recursive operator's entries, keyed by the operator binding, which the entry keeps alive so
// its address isn't reused, or by the definition's node.
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
    recursive_operators: HashMap<usize, OperatorEntries>,
    recursive_functions: HashMap<(NodeId, usize), FunctionEntries>,
    expanding: HashSet<NodeId>,
    /// The slots of names bound over intervals, whose values are integers.
    int_slots: HashSet<u32>,
    /// How many ENABLED actions the compiler is inside, whose private next state also holds the
    /// variables ENABLED's rewrite of an instance names (`x@ENABLED`), at slots past the state's.
    enabled_depth: u32,
    /// The variables an ENABLED's next state holds: the state's and those past it.
    variable_extent: usize,
    /// The name EXCEPT binds `@` to: its text, or one no text has if the IR holds none.
    at: TextId,
    depth: u32,
    // The unsettled fixed points the compiles under way have read, innermost first.
    reads: Option<Vec<Rc<FixedPoint>>>,
    // What cached compiles read of fixed points that hadn't settled when they compiled.
    provisional: HashMap<u64, Vec<Rc<FixedPoint>>>,
    entry_count: u64,
    /// How many continuations the walk being compiled has compiled for what its paths know.
    specialisations: usize,
    /// Whether an expression reads TLCGet("distinct"), whose slot the search must then set.
    pub is_distinct_read: bool,
    /// Whether anything compiled may print, and whether it uses ToString, which ranks strings.
    pub is_printing: bool,
    pub is_ranking: bool,
    // The contexts of the instance scopes translated so far.
    scope_contexts: HashMap<Index, Option<Context>>,
}

fn add_read(reads: &mut Vec<Rc<FixedPoint>>, fixed_point: &Rc<FixedPoint>) {
    if !reads.iter().any(|known| Rc::ptr_eq(known, fixed_point)) {
        reads.push(Rc::clone(fixed_point));
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
                slot_count: SEARCH_SLOTS.len(),
                is_epoch_checked: options.is_epoch_checked,
                ..Program::default()
            },
            texts: vec![None; ir.texts.len()],
            definition_cache: HashMap::new(),
            recursive_operators: HashMap::new(),
            recursive_functions: HashMap::new(),
            expanding: HashSet::new(),
            int_slots: HashSet::new(),
            enabled_depth: 0,
            variable_extent: ir.variables.len(),
            at: ir
                .texts
                .iter()
                .position(|text| &**text == "@")
                .map_or(TextId::MAX - 1, |index| index as TextId),
            depth: 0,
            reads: None,
            provisional: HashMap::new(),
            entry_count: 0,
            specialisations: 0,
            is_distinct_read: false,
            is_printing: false,
            is_ranking: false,
            scope_contexts: HashMap::new(),
        }
    }

    /// The program the compiled closures run with.
    pub fn finish(self) -> Program {
        self.program
    }

    /// Compiles a root of the model, as `createEngineContext` compiles it, with no scope.
    pub fn compile_root(&mut self, root: Root) -> Result<Compiled, CompileError> {
        self.compile_root_printing(root, false)
    }

    /// Compiles a root of the model where what it prints is printed, as an invariant that prints
    /// is compiled whole.
    pub fn compile_root_printing(
        &mut self,
        root: Root,
        can_print: bool,
    ) -> Result<Compiled, CompileError> {
        let context = Context {
            can_print,
            ..Context::ROOT
        };
        match root {
            Root::Definition(index) => {
                let definition = self.ir.definitions[index as usize];
                self.wrap_compile(|compiler| {
                    compiler.compile_definition_reference(definition, &context)
                })
            }
            Root::Expression(node) => self.compile(node, &context),
            Root::Unchanged(node) => {
                self.wrap_compile(|compiler| compiler.compile_unchanged(node, &context))
            }
        }
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
            .get_or_insert_with(|| ir.texts[text as usize].encode_utf16().collect())
            .clone()
    }

    fn definition(&self, node: NodeId) -> &'a Definition {
        match self.node(node).1 {
            NodeKind::Definition(definition) => definition,
            _ => panic!("a definition index that names no definition"),
        }
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

    fn allocate_table(&mut self, width: usize) -> usize {
        self.program.memo_widths.push(width);
        self.program.memo_widths.len() - 1
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
        Compiled {
            is_costly: false,
            is_constant,
            ..compiled.with_eval(eval(move |machine| machine.once(once, &inner)))
        }
    }

    // While one state is expanded, an expression that reads no primed variable has one value for
    // each value of the bound names it reads, however many variables it reads.
    fn cached_in_epoch(&mut self, compiled: Compiled) -> Compiled {
        let footprint = &compiled.footprint;
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
        if compiled.is_printing() || self.options.is_memo_off {
            return compiled;
        }
        let width = compiled.footprint.width();
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
        let table = self.allocate_table(width);
        let footprint = &compiled.footprint;
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
        self.depth += 1;
        let result = if self.depth > MAXIMUM_EXPANSION {
            unsupported("expansion too deep")
        } else {
            let inner = if context.can_print && !self.is_evaluated_as_tlc(node, context) {
                context.without_print()
            } else {
                context.clone()
            };
            self.compile_node(node, &inner).and_then(|compiled| {
                // A definition compiled where it may print may be cached, then named where it
                // may not.
                if !context.can_print && compiled.is_printing() {
                    return unsupported("Print where TLC evaluates it otherwise");
                }
                Ok(if compiled.is_costly || compiled.footprint.width() == 0 {
                    self.cached(compiled)
                } else {
                    compiled
                })
            })
        };
        self.depth -= 1;
        result
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
            | NodeKind::Identifier(_) => true,
            NodeKind::Apply { name, .. } => {
                if name.is_local
                    && let Some(found) = lookup(&context.scope, name.text)
                {
                    return matches!(&found.binding, Binding::Operator(operator) if !operator.is_recursive);
                }
                match name.resolution {
                    Resolution::Definition(index) => {
                        let node = self.ir.definitions[index as usize];
                        let definition = self.definition(node);
                        matches!(definition.form, DefinitionForm::Operator(_))
                            && definition.flags & Definition::RECURSIVE == 0
                            && !self.expanding.contains(&node)
                    }
                    Resolution::Builtin(index) => matches!(
                        self.builtin_name(index),
                        "Print" | "PrintT" | "=" | "#" | "~"
                    ),
                    _ => false,
                }
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

    fn compile_binding(&mut self, node: &Rc<Scope>, context: &Context) -> Compiling<Compiled> {
        match &node.binding {
            Binding::Slot(slot) => Ok(self.read_slot(*slot)),
            Binding::Argument(argument) => {
                let is_primed = context.is_primed || argument.context.is_primed;
                let index = usize::from(is_primed);
                if let Some(known) = &argument.compiled.borrow()[index] {
                    return Ok(known.clone());
                }
                let compiled = self.compile(
                    argument.expression,
                    &argument_context(argument).primed(is_primed),
                )?;
                argument.compiled.borrow_mut()[index] = Some(compiled.clone());
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
                Ok(self.materialize_recursive(&recursive))
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
        match definition.startup {
            Startup::Value(Some(value)) => return Ok(constant(self.intern_value(value)?)),
            Startup::Value(None) | Startup::Object => {
                return unsupported("a value TLC computed at startup with effects");
            }
            Startup::None => {}
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
        if self.expanding.contains(&node) {
            return unsupported("a recursive zero-arity definition");
        }
        self.expanding.insert(node);
        let body = definition.body;
        let body_context = context.global(context.can_print);
        let mut read = Vec::new();
        let result = self.tracking(&mut read, |compiler| {
            let compiled = compiler.compile(body, &body_context)?;
            Ok(compiler.cached(Self::mark_costly(compiled)))
        });
        self.expanding.remove(&node);
        let compiled = result?;
        self.cache_definition(node, index, compiled.clone(), &read);
        Ok(compiled)
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
                        is_in_order: true,
                        are_elements_in_order: true,
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
                return self.compile_nullary_builtin(index);
            }
            _ => {}
        }
        if let Some(found) = lookup(&context.scope, name.text) {
            return self.compile_binding(&found, context);
        }
        unsupported(format!("the name {}", self.text(name.text)))
    }

    // --- LET ---

    fn bind_let_definitions(
        &mut self,
        instances: u32,
        definitions: &[NodeId],
        context: &Context,
    ) -> Compiling<Context> {
        if instances > 0 {
            return unsupported("INSTANCE in LET");
        }
        let mut scope = context.scope.clone();
        for &node in definitions {
            let definition = self.definition(node);
            let definition_context = Context {
                scope: scope.clone(),
                can_print: false,
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
                    scope = bind(
                        &scope,
                        definition.name,
                        Binding::Argument(Rc::new(Argument {
                            expression: definition.body,
                            context: definition_context,
                            compiled: RefCell::new([None, None]),
                            own_scope: RefCell::new(Weak::new()),
                        })),
                    );
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
                    }
                }
            }
        }
        Ok(context.with_scope(scope))
    }

    // --- operator application ---

    // Binds the parameters of an operator to its arguments.
    fn bind_arguments(
        &mut self,
        params: &[Param],
        args: &[NodeId],
        caller: &Context,
        callee: Context,
    ) -> Compiling<Context> {
        if params.len() != args.len() {
            return unsupported("an operator applied to the wrong number of arguments");
        }
        let mut scope = callee.scope.clone();
        let argument_context = caller.without_print();
        for (param, &argument) in params.iter().zip(args) {
            let binding = if param.arity > 0 {
                Binding::Operator(self.resolve_operator_argument(argument, &argument_context)?)
            } else {
                Binding::Argument(Rc::new(Argument {
                    expression: argument,
                    context: argument_context.clone(),
                    compiled: RefCell::new([None, None]),
                    own_scope: RefCell::new(Weak::new()),
                }))
            };
            scope = bind(&scope, param.name, binding);
        }
        Ok(callee.with_scope(scope))
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
                if definition.flags & Definition::RECURSIVE != 0 || self.expanding.contains(&node) {
                    return self.compile_recursive_call(
                        RecursiveTarget::Global(node),
                        args,
                        context,
                    );
                }
                self.expanding.insert(node);
                let result = self
                    .bind_arguments(params, args, context, context.global(context.can_print))
                    .and_then(|callee| self.compile(definition.body, &callee));
                self.expanding.remove(&node);
                return result.map(|compiled| self.cached(compiled));
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
        let callee = self.bind_arguments(&operator.params, args, context, base)?;
        let compiled = match operator.body {
            OperatorBody::Node(body) => self.compile(body, &callee)?,
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
                    *node as usize,
                    None,
                )
            }
            RecursiveTarget::Local(operator) => (
                operator.params.clone(),
                operator.body,
                Some(operator_context(operator)),
                // A node id never reaches the address of an allocation.
                Rc::as_ptr(operator) as usize,
                Some(Rc::clone(operator)),
            ),
        };
        if params.iter().any(|param| param.arity > 0) {
            return unsupported("a recursive higher-order operator");
        }
        let OperatorBody::Node(body) = body else {
            return unsupported("a recursive higher-order operator");
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
        let compiled_args = args
            .iter()
            .map(|&argument| self.compile(argument, context))
            .collect::<Compiling<Vec<Compiled>>>()?;
        let arg_evals: Vec<Eval> = compiled_args
            .iter()
            .map(|argument| argument.eval.clone())
            .collect();
        let slots = recursive.slots.clone();
        let runtime = recursive.runtime;
        let evaluate = eval(move |machine| {
            let at = machine.stack.len();
            for argument in &arg_evals {
                let value = match argument(machine) {
                    Ok(value) => value,
                    Err(bail) => {
                        machine.stack.truncate(at);
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
        // While the body compiles, a call inside it reads what the operator assumes it does.
        let read = match &*recursive.body_footprint.borrow() {
            Some(body) => body.without_slots(&recursive.slots),
            None => recursive.assumed.borrow().clone(),
        };
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
        key: usize,
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
        let mut scope = local_context.and_then(|local| local.scope);
        for (param, &slot) in params.iter().zip(&slots) {
            scope = bind(&scope, param.name, Binding::Slot(slot));
        }
        if let Some(node) = global {
            self.expanding.insert(node);
        }
        let body_context = Context {
            scope,
            is_primed,
            is_init: context.is_init,
            can_print: false,
        };
        let mut read = Vec::new();
        let settled = self.settle_operator(&created, body, &body_context, &mut read);
        if let Some(node) = global {
            self.expanding.remove(&node);
        }
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

    fn forget_operator(&mut self, key: usize, index: usize, entry: u64) {
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
        let table = (width <= MAXIMUM_MEMO_WIDTH && !self.options.is_memo_off)
            .then(|| self.allocate_table(width));
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
            let recursive = self.get_recursive_function(node, context, None)?;
            return Ok(self.materialize_recursive(&recursive));
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
        let body_context = Context {
            scope: None,
            is_primed: context.is_primed,
            is_init: context.is_init,
            can_print: false,
        };
        let mut read = Vec::new();
        let compiled = self.tracking(&mut read, |compiler| {
            let construction =
                compiler.compile_function_construction(bounds, definition.body, &body_context)?;
            Ok(compiler.cached(Self::mark_costly(construction)))
        })?;
        self.cache_definition(node, index, compiled.clone(), &read);
        Ok(compiled)
    }

    // A recursive function as a value: its body applied to each element of its domain.
    fn materialize_recursive(&mut self, recursive: &Rc<RecursiveFunction>) -> Compiled {
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
                    Ok(machine.store.function_over_set(domain, &values))
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
        let [bound] = &bounds[..] else {
            return unsupported("a recursive function of several arguments");
        };
        let tla_ir::Pattern::Name(param) = bound.pattern else {
            return unsupported("a recursive function of several arguments");
        };
        let outer = Context {
            scope: base_scope.clone(),
            is_primed: context.is_primed,
            is_init: context.is_init,
            can_print: false,
        };
        let slot = self.allocate_slot();
        let mut read = Vec::new();
        let domain = self.tracking(&mut read, |compiler| compiler.compile(bound.set, &outer))?;
        let record = Rc::new(RecursiveFunction {
            entry: self.next_entry(),
            runtime: self.allocate_runtime(),
            slot,
            domain,
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
        let body_context = outer.with_scope(bind(&base_scope, param, Binding::Slot(slot)));
        let settled = self.settle_function(&record, definition.body, &body_context, &mut read);
        let (body, slot_start, slot_end) = match settled {
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

    // The recursive function an application applies, when it names one directly.
    fn get_applied_recursive_function(
        &mut self,
        function: NodeId,
        context: &Context,
    ) -> Compiling<Option<Rc<RecursiveFunction>>> {
        let NodeKind::Identifier(name) = self.node(function).1 else {
            return Ok(None);
        };
        if let Some(found) = lookup(&context.scope, name.text) {
            return match &found.binding {
                Binding::Recursive { definition } => {
                    let definition = *definition;
                    self.get_recursive_function(definition, context, Some(Rc::clone(&found)))
                        .map(Some)
                }
                _ => Ok(None),
            };
        }
        let Resolution::Definition(index) = name.resolution else {
            return Ok(None);
        };
        let node = self.ir.definitions[index as usize];
        let definition = self.definition(node);
        if !matches!(definition.form, DefinitionForm::Function(_))
            || definition.flags & (Definition::RECURSIVE | Definition::SELF_REFERENTIAL) == 0
        {
            return Ok(None);
        }
        self.get_recursive_function(node, context, None).map(Some)
    }
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
