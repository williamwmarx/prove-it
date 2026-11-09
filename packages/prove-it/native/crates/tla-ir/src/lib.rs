//! The engine IR: the model as `src/engine/ir.ts` lowers it, which the native engine reads in
//! place of the TypeScript AST and environment. [`decode`] reads the blob and [`encode`] writes
//! it again, byte for byte, which is how the two sides are held to one layout. `ir.ts` documents
//! the layout; the constants below are its numbers.

mod decode;
mod encode;

/// The stack the decoder and the encoder run on. Both follow nested nodes by recursion, up to the
/// decoder's limit, and a Rust stack overflow aborts the process rather than failing, so they run
/// on a thread whose stack holds that many levels. Ten thousand levels took between 128 and 256 MB
/// in a debug build and under 32 MB in a release build; each size is about twice that. The stack
/// is reserved, not committed.
const NESTING_STACK_BYTES: usize = if cfg!(debug_assertions) {
    512 * 1024 * 1024
} else {
    64 * 1024 * 1024
};

fn on_nesting_stack<T: Send>(work: impl FnOnce() -> T + Send) -> T {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(NESTING_STACK_BYTES)
            .spawn_scoped(scope, work)
            .expect("a thread for the nested nodes")
            .join()
            .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
    })
}

use std::collections::HashMap;

pub use decode::{DecodeError, decode};
pub use encode::encode;

/// The version of the layout, `IR_VERSION` in `ir.ts`.
pub const IR_VERSION: u32 = 10;

/// "PIIR" as a little-endian word.
pub const MAGIC: u32 = 0x5249_4950;

/// An index into [`Ir::texts`].
pub type TextId = u32;
/// An index into [`Nodes::arena`].
pub type NodeId = u32;
/// An index into [`Ir::definitions`], [`Ir::scopes`], [`Ir::constants`] or [`Ir::builtins`].
pub type Index = u32;

/// A decoded IR. Everything that refers to a node does so by its [`NodeId`].
#[derive(Debug, Clone, PartialEq)]
pub struct Ir {
    /// How many of the texts TLC ranks: text `i` below this has rank `i`.
    pub ranked_count: u32,
    pub texts: Vec<Box<str>>,
    /// The variables in the engine's order.
    pub variables: Vec<TextId>,
    /// TLC's order of the variables, as positions in [`Ir::variables`].
    pub tlc_order: Vec<i32>,
    pub builtins: Vec<Builtin>,
    pub constants: Vec<Constant>,
    pub scopes: Vec<Scope>,
    pub values: Values,
    pub model: Model,
    /// The definitions the model reaches: each a node of kind [`NodeKind::Definition`].
    pub definitions: Vec<NodeId>,
    pub nodes: Nodes,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Builtin {
    pub name: TextId,
    pub arity: i32,
    pub flags: i32,
}

impl Builtin {
    pub const STATE_LEVEL: i32 = 1;
    pub const LEVEL_CONSTANT: i32 = 2;
    pub const LAZY: i32 = 4;
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Constant {
    pub name: TextId,
    /// The value, or `None` for one the transfer encoding can't hold.
    pub value: Option<u32>,
}

/// A binding of an instance's scope, which the compiler translates as `contextFromScope` does.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Scope {
    pub parent: Option<Index>,
    pub name: TextId,
    pub binding: ScopeBinding,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ScopeBinding {
    /// A value, or `None` for one the transfer encoding can't hold.
    Value(Option<u32>),
    Thunk {
        expression: NodeId,
        scope: Option<Index>,
    },
    Closure {
        name: TextId,
        params: Vec<Param>,
        body: NodeId,
        scope: Option<Index>,
    },
    /// A binding the engine can't translate, such as to a builtin.
    Opaque,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Param {
    pub name: TextId,
    pub arity: i32,
}

/// The values of constants, scopes and startup values, in `transfer.ts`'s encoding.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Values {
    /// The texts the values' strings and model values name, by the encoding's string index.
    pub strings: Vec<TextId>,
    pub list: Vec<Value>,
}

/// A value as `transfer.ts` encodes it. A string or model value names its text by the index into
/// [`Values::strings`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Value {
    Bool(bool),
    Int(i32),
    String(u32),
    ModelValue(u32),
    Set(Vec<Value>),
    /// A function with its TLC class (0 none, 1 lambda, 2 tuple, 3 record).
    Function {
        class: i32,
        domain: Vec<Value>,
        range: Vec<Value>,
    },
    /// A function over the interval `low..low + range.len() - 1`.
    IntervalFunction {
        class: i32,
        low: i32,
        range: Vec<Value>,
    },
}

/// A name the configuration gives, and the definition it names.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConfigName {
    pub name: TextId,
    pub definition: Option<Index>,
}

/// A root that may print, which the engine checks whole each time, as TLC does.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Printed<T> {
    pub root: T,
    pub has_repeated_effect: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Action {
    pub expression: NodeId,
    pub scope: Option<Index>,
    /// How TLC names the action in a trace: `Inc line 5, col 8 to line 5, col 41 of module D`.
    pub label: TextId,
}

/// A `_POSSIBLE` predicate, which TLC counts the states, or with `is_action` the steps, it holds of.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Possible {
    pub name: ConfigName,
    pub is_action: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ActionProperty {
    pub action: NodeId,
    pub subscript: NodeId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AtomKind {
    State,
    /// An action, with the atom of its fairness's ENABLED, which the checker asks first.
    Action {
        unchanged: Option<NodeId>,
        enabled: Option<Index>,
    },
    Enabled {
        actions: EnabledActions,
    },
}

/// The positions of TLC's actions an ENABLED atom splits into.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EnabledActions {
    Unknown,
    All,
    Some(Vec<i32>),
}

/// A liveness atom the tableau asks about.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Atom {
    pub kind: AtomKind,
    pub expression: NodeId,
    pub scope: Option<Index>,
}

/// A term of the formula the liveness checker solves, in prefix order: a junction is followed by
/// its operands and a unary term by its body. An atom is its position among the model's atoms, or
/// past them for one the checker asks nothing of.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LiveTerm {
    Boolean(bool),
    State(Index),
    Enabled(Index),
    Action { atom: Index, enabled: Option<Index> },
    Not,
    Always,
    Eventually,
    Next,
    And(u32),
    Or(u32),
}

/// A temporal property, by name, as the liveness checker names it in a counterexample.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LiveProperty {
    pub name: TextId,
    pub formula: Vec<LiveTerm>,
}

/// What the configuration and the checker ask of the search.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Model {
    pub init: NodeId,
    pub next: NodeId,
    pub scope: Option<Index>,
    /// TLC's actions of the next-state relation, which a trace labels its steps with.
    pub actions: Vec<Action>,
    /// Whether the search takes each state's steps through the actions and labels them, which
    /// ENABLED asks for, rather than through the next-state relation.
    pub is_labelled: bool,
    pub invariants: Vec<Printed<ConfigName>>,
    pub property_invariants: Vec<Printed<NodeId>>,
    /// The name TLC gives each of `property_invariants` when it reports it violated: the operator
    /// the property asserts always holds, or the property's name.
    pub property_invariant_names: Vec<TextId>,
    pub constraints: Vec<ConfigName>,
    pub action_constraints: Vec<ConfigName>,
    pub possible: Vec<Possible>,
    pub action_properties: Vec<ActionProperty>,
    pub initial_predicates: Vec<NodeId>,
    pub view: Option<ConfigName>,
    /// The symmetry group: each permutation as the model values it moves, by text.
    pub symmetry: Option<Vec<Vec<(TextId, TextId)>>>,
    pub check_deadlock: bool,
    pub is_warning_enabled: bool,
    pub is_recording_graph: bool,
    pub version: Option<TextId>,
    /// The seed TLC reseeds its generator with for each state it expands, xored with the state's
    /// fingerprint (`RandomEnumerableValues`).
    pub random_seed: u64,
    /// The 48 bits of the generator the initial states draw from, as the assumptions left it.
    pub startup_random: u64,
    pub atoms: Vec<Atom>,
    /// The fairness and the negated properties as the liveness checker joins them, or no terms.
    pub live_formula: Vec<LiveTerm>,
    /// Each property, whose violation a counterexample's checks find, in the configuration's order.
    pub live_properties: Vec<LiveProperty>,
}

/// The nodes, in the order of the blob, and which of them are written at the top level.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct Nodes {
    pub arena: Vec<Node>,
    pub top: Vec<NodeId>,
    /// How each junction that is a bulleted list or an infix chain is written, by its node.
    pub junctions: HashMap<NodeId, Junction>,
}

/// How a junction is written: as a bulleted list, or as an infix chain such as A /\ B /\ C, which
/// SANY parses as (A /\ B) /\ C. TLC prints the range of each prefix of two or more operands, which
/// ends where `prefix_ends` says, a line and column for each.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Junction {
    pub is_bulleted: bool,
    pub prefix_ends: Vec<(i32, i32)>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Node {
    pub line: i32,
    pub column: i32,
    /// Where the node is written, which TLC's messages print, if the front end knows.
    pub range: Option<SourceRange>,
    pub kind: NodeKind,
}

/// A node's source range: its module and where it starts and ends, as TLC prints them in
/// `line 2, col 3 to line 2, col 9 of module M`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SourceRange {
    pub module: TextId,
    pub start_line: i32,
    pub start_column: i32,
    pub end_line: i32,
    pub end_column: i32,
}

/// What a name refers to outside any binding of it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Resolution {
    None,
    /// A variable by its slot, which for an instance's variable that ENABLED's rewrite names, such
    /// as `x@ENABLED`, may be past the state's variables.
    Variable(u32),
    Constant(Index),
    Definition(Index),
    Builtin(Index),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Name {
    pub text: TextId,
    pub resolution: Resolution,
    /// Whether SANY resolved the name to a binding around it, which the compiler looks up first.
    pub is_local: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Pattern {
    Name(TextId),
    Tuple(Vec<TextId>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Bound {
    pub pattern: Pattern,
    pub set: NodeId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PathStep {
    Field(TextId),
    Index(Vec<NodeId>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Update {
    pub path: Vec<PathStep>,
    pub value: NodeId,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Selector {
    Name {
        name: TextId,
        args: Vec<NodeId>,
    },
    /// An operand by number, or -1 for `<<` and -2 for `>>`.
    Operand(i32),
    Bound(Vec<NodeId>),
    At,
    Colon,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DefinitionForm {
    Operator(Vec<Param>),
    Function(Vec<Bound>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Definition {
    pub name: TextId,
    pub flags: i32,
    /// The value TLC computed at startup for a definition with effects, which the compiler reads
    /// in its place.
    pub startup: Startup,
    pub form: DefinitionForm,
    pub body: NodeId,
}

impl Definition {
    pub const RECURSIVE: i32 = 1;
    pub const LOCAL: i32 = 2;
    pub const SELF_REFERENTIAL: i32 = 4;
    pub const REPEATED_EFFECT: i32 = 8;
    pub const SUBSTITUTED: i32 = 16;
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Startup {
    None,
    /// A value the engine can't read: one TLC may keep lazy, or one the encoding can't hold.
    Object,
    /// A value, or `None` for one the transfer encoding can't hold.
    Value(Option<u32>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum NodeKind {
    Number(i32),
    /// A number outside 32 bits, by its text.
    WideNumber(TextId),
    Decimal(TextId),
    String(TextId),
    Identifier(Name),
    Apply {
        name: Name,
        args: Vec<NodeId>,
    },
    OperatorReference(Name),
    Lambda {
        params: Vec<TextId>,
        body: NodeId,
    },
    And(Vec<NodeId>),
    Or(Vec<NodeId>),
    Prime(NodeId),
    Unchanged(NodeId),
    Enabled(NodeId),
    If {
        condition: NodeId,
        consequent: NodeId,
        alternative: NodeId,
    },
    Case {
        arms: Vec<(NodeId, NodeId)>,
        other: Option<NodeId>,
    },
    Let {
        instances: u32,
        definitions: Vec<NodeId>,
        body: NodeId,
    },
    Forall {
        bounds: Vec<Bound>,
        body: NodeId,
    },
    Exists {
        bounds: Vec<Bound>,
        body: NodeId,
    },
    UnboundedQuantifier {
        is_forall: bool,
        names: Vec<TextId>,
        body: NodeId,
    },
    Choose {
        pattern: Pattern,
        set: Option<NodeId>,
        body: NodeId,
    },
    SetEnumeration(Vec<NodeId>),
    SetFilter {
        bound: Bound,
        predicate: NodeId,
    },
    SetMap {
        expression: NodeId,
        bounds: Vec<Bound>,
    },
    Tuple(Vec<NodeId>),
    FunctionConstruction {
        is_recursive: bool,
        bounds: Vec<Bound>,
        body: NodeId,
    },
    FunctionSet {
        domain: NodeId,
        range: NodeId,
    },
    Record(Vec<(TextId, NodeId)>),
    RecordSet(Vec<(TextId, NodeId)>),
    Except {
        function: NodeId,
        updates: Vec<Update>,
    },
    ExceptAt,
    FunctionApplication {
        function: NodeId,
        args: Vec<NodeId>,
    },
    Bracket(Vec<NodeId>),
    FieldAccess {
        record: NodeId,
        field: TextId,
    },
    Product(Vec<NodeId>),
    Always(NodeId),
    Eventually(NodeId),
    BoxAction {
        action: NodeId,
        subscript: NodeId,
    },
    AngleAction {
        action: NodeId,
        subscript: NodeId,
    },
    WeakFairness {
        subscript: NodeId,
        action: NodeId,
        enabled: Option<NodeId>,
    },
    StrongFairness {
        subscript: NodeId,
        action: NodeId,
        enabled: Option<NodeId>,
    },
    Label {
        name: TextId,
        params: Vec<TextId>,
        body: NodeId,
    },
    Subexpression(Vec<Selector>),
    /// A definition: a global one the model reaches, or one a LET defines.
    Definition(Definition),
    /// A node met again, written where it was first met.
    Reference(NodeId),
}

// The tags of the blob, the positions of NODE_KINDS in ir.ts.
pub(crate) mod tag {
    pub const NUMBER: i32 = 0;
    pub const DECIMAL: i32 = 1;
    pub const STRING: i32 = 2;
    pub const IDENTIFIER: i32 = 3;
    pub const APPLY: i32 = 4;
    pub const OPERATOR_REFERENCE: i32 = 5;
    pub const LAMBDA: i32 = 6;
    pub const AND: i32 = 7;
    pub const OR: i32 = 8;
    pub const PRIME: i32 = 9;
    pub const UNCHANGED: i32 = 10;
    pub const ENABLED: i32 = 11;
    pub const IF: i32 = 12;
    pub const CASE: i32 = 13;
    pub const LET: i32 = 14;
    pub const FORALL: i32 = 15;
    pub const EXISTS: i32 = 16;
    pub const UNBOUNDED_QUANTIFIER: i32 = 17;
    pub const CHOOSE: i32 = 18;
    pub const SET_ENUMERATION: i32 = 19;
    pub const SET_FILTER: i32 = 20;
    pub const SET_MAP: i32 = 21;
    pub const TUPLE: i32 = 22;
    pub const FUNCTION_CONSTRUCTION: i32 = 23;
    pub const FUNCTION_SET: i32 = 24;
    pub const RECORD: i32 = 25;
    pub const RECORD_SET: i32 = 26;
    pub const EXCEPT: i32 = 27;
    pub const EXCEPT_AT: i32 = 28;
    pub const FUNCTION_APPLICATION: i32 = 29;
    pub const BRACKET: i32 = 30;
    pub const FIELD_ACCESS: i32 = 31;
    pub const PRODUCT: i32 = 32;
    pub const ALWAYS: i32 = 33;
    pub const EVENTUALLY: i32 = 34;
    pub const BOX_ACTION: i32 = 35;
    pub const ANGLE_ACTION: i32 = 36;
    pub const WEAK_FAIRNESS: i32 = 37;
    pub const STRONG_FAIRNESS: i32 = 38;
    pub const LABEL: i32 = 39;
    pub const SUBEXPRESSION: i32 = 40;
    pub const REFERENCE: i32 = 64;
    pub const DEFINITION: i32 = 65;
    /// The one flag a node's tag word may carry above its tag.
    pub const FLAG: i32 = 1 << 8;
    /// Where a definition's flags start in its tag word.
    pub const DEFINITION_FLAGS: i32 = 8;
}

// The numbers of the other sections.
pub(crate) mod code {
    pub const RESOLUTION_NONE: i32 = 0;
    pub const RESOLUTION_VARIABLE: i32 = 1;
    pub const RESOLUTION_CONSTANT: i32 = 2;
    pub const RESOLUTION_DEFINITION: i32 = 3;
    pub const RESOLUTION_BUILTIN: i32 = 4;
    pub const NO_STARTUP_VALUE: i32 = -1;
    pub const OBJECT_STARTUP_VALUE: i32 = -2;
    pub const SCOPE_VALUE: i32 = 0;
    pub const SCOPE_THUNK: i32 = 1;
    pub const SCOPE_CLOSURE: i32 = 2;
    pub const SCOPE_OPAQUE: i32 = 3;
    pub const ATOM_STATE: i32 = 0;
    pub const ATOM_ACTION: i32 = 1;
    pub const ATOM_ENABLED: i32 = 2;
    pub const ENABLED_UNKNOWN: i32 = -2;
    pub const ENABLED_ALL: i32 = -1;
    pub const LIVE_FALSE: i32 = 0;
    pub const LIVE_TRUE: i32 = 1;
    pub const LIVE_STATE: i32 = 2;
    pub const LIVE_ENABLED: i32 = 3;
    pub const LIVE_ACTION: i32 = 4;
    pub const LIVE_NOT: i32 = 5;
    pub const LIVE_ALWAYS: i32 = 6;
    pub const LIVE_EVENTUALLY: i32 = 7;
    pub const LIVE_NEXT: i32 = 8;
    pub const LIVE_AND: i32 = 9;
    pub const LIVE_OR: i32 = 10;
    pub const FALSE: i32 = 0;
    pub const TRUE: i32 = 1;
    pub const INTEGER: i32 = 2;
    pub const STRING: i32 = 3;
    pub const MODEL_VALUE: i32 = 4;
    pub const SET: i32 = 5;
    pub const FUNCTION: i32 = 6;
    pub const INTERVAL_FUNCTION: i32 = 7;
}
