//! Expressions of the engine IR, evaluated on the evaluator's values as `evaluate.ts` evaluates
//! the AST: names resolve as the engine's compiler resolves them (bound names first where SANY
//! resolved them locally, then variables, constants, definitions and builtins), operators expand
//! at the call site with their arguments evaluated where used, and functions TLC keeps lazy, a
//! definition's or a LET's, are applied without building them.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use tla_values::random::JavaRandom;

use tla_ir::{
    Bound, Builtin, Definition, DefinitionForm, Index, Ir, Name, NodeId, NodeKind, Param, PathStep,
    Pattern, Resolution, ScopeBinding, TextId,
};

use tla_values::{Id, Store};

use crate::Unsupported;
use crate::failure::nested;
use crate::print::{format_pretty, format_printed, format_value};
use crate::random::{random_element, random_subset};
use crate::sets::{as_tuple, cardinality, difference, intersection, is_member, union};
use crate::value::{
    Class, EvalError, Evaluated, Function, Lazy, Search, Text, TlcMessage, Value, compare,
    elements, equals, fail, fail_coded, fail_runtime, fail_with, find_key, from_store,
    is_enumerable, mark_unnormalized, note_sorted, set_of, sorted_function, unnormalized,
    unsorted_failure, written_function,
};

/// The bindings an expression sees, innermost first.
#[derive(Clone, Default)]
pub struct Env(Option<Rc<Frame>>);

pub struct Frame {
    name: TextId,
    binding: Binding,
    parent: Env,
}

#[derive(Clone)]
enum Binding {
    Value(Value),
    /// An operator's argument or a zero-arity LET definition, evaluated where it is used. One that
    /// closes over the scope that binds it sees that scope (`is_self`).
    Thunk {
        node: NodeId,
        context: Context,
        is_self: bool,
    },
    Operator(Rc<Operator>),
    /// A function a LET defines, which TLC keeps lazy: applied without being built. A recursive
    /// one sees the scope that binds it.
    Function {
        definition: NodeId,
        context: Context,
        is_self: bool,
    },
}

pub struct Operator {
    params: Vec<Param>,
    body: Body,
    context: Context,
    /// A RECURSIVE operator of a LET, or a closure of an instance's scope over that scope: its
    /// body sees the scope that binds it.
    is_self: bool,
}

#[derive(Clone, Copy)]
enum Body {
    Node(NodeId),
    /// A builtin passed as an operator.
    Builtin(Index),
}

/// The predicate of a set filter TLC keeps lazy, with what it is evaluated in: the bound's
/// pattern, the context and the states the filter was built in, and how TLC prints it where it
/// can't enumerate it.
pub struct Predicate {
    pattern: Pattern,
    body: NodeId,
    context: Context,
    current: Vec<Option<Value>>,
    next: Vec<Option<Value>>,
    level: i32,
    /// `{x \in`, and ` : <expression …> }`, around the set's text.
    text: (String, String),
    /// The elements that pass, where the evaluator filtered a finite set without effects, as
    /// TLC's enumeration of the filter finds them.
    filtered: Option<Rc<Vec<Value>>>,
}

impl Predicate {
    pub fn text(&self) -> &(String, String) {
        &self.text
    }

    pub fn filtered(&self) -> Option<&Rc<Vec<Value>>> {
        self.filtered.as_ref()
    }
}

impl std::fmt::Debug for Predicate {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "Predicate({})", self.body)
    }
}

/// `[x \in S |-> e]` TLC keeps lazy (`FcnLambdaValue`) where the evaluator can't build it: its
/// parameter, domain and body, what the body is evaluated in, the EXCEPTs taken of it, each a key
/// and its value, and how TLC prints it.
pub struct Lambda {
    name: TextId,
    domain: Value,
    body: NodeId,
    context: Context,
    current: Vec<Option<Value>>,
    next: Vec<Option<Value>>,
    level: i32,
    excepts: Vec<(Value, Value)>,
    /// `[x \in`, and ` |-> <expression …>]`, around the domain's text.
    text: (String, String),
}

impl Lambda {
    pub fn text(&self) -> &(String, String) {
        &self.text
    }

    pub fn domain(&self) -> &Value {
        &self.domain
    }
}

impl std::fmt::Debug for Lambda {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "Lambda({})", self.body)
    }
}

/// Where an expression is evaluated: its bindings, whether it is under a prime, and the value `@`
/// stands for in an EXCEPT.
#[derive(Clone, Default)]
pub struct Context {
    env: Env,
    pub is_primed: bool,
    at: Option<Value>,
}

impl Context {
    pub(crate) fn primed(&self, is_primed: bool) -> Context {
        Context {
            is_primed,
            ..self.clone()
        }
    }

    fn with_env(&self, env: Env) -> Context {
        Context {
            env,
            ..self.clone()
        }
    }

    fn bind(&self, name: TextId, binding: Binding) -> Context {
        self.with_env(Env(Some(Rc::new(Frame {
            name,
            binding,
            parent: self.env.clone(),
        }))))
    }

    pub fn bind_value(&self, name: TextId, value: Value) -> Context {
        self.bind(name, Binding::Value(value))
    }

    // A definition's body is evaluated without the caller's bindings.
    fn global(&self) -> Context {
        Context {
            env: Env::default(),
            is_primed: self.is_primed,
            at: None,
        }
    }
}

fn lookup(env: &Env, name: TextId) -> Option<Rc<Frame>> {
    let mut current = env.0.as_ref();
    while let Some(frame) = current {
        if frame.name == name {
            return Some(Rc::clone(frame));
        }
        current = frame.parent.0.as_ref();
    }
    None
}

/// The expression a local name binds and the scope it is evaluated in, to find its level: a LET
/// definition's body or an operator argument. A value, a builtin or an unbound name has none.
pub(crate) fn bound_expression(context: &Context, name: TextId) -> Option<(NodeId, Context)> {
    let frame = lookup(&context.env, name)?;
    match &frame.binding {
        Binding::Value(_) => None,
        Binding::Thunk {
            node,
            context: inner,
            is_self,
        } => Some((*node, own_context(inner, &frame, *is_self))),
        Binding::Operator(operator) => match operator.body {
            Body::Node(node) => Some((
                node,
                own_context(&operator.context, &frame, operator.is_self),
            )),
            Body::Builtin(_) => None,
        },
        Binding::Function {
            definition,
            context: inner,
            is_self,
        } => Some((*definition, own_context(inner, &frame, *is_self))),
    }
}

// The context a self-closing binding's body sees: the scope that binds it.
fn own_context(context: &Context, frame: &Rc<Frame>, is_self: bool) -> Context {
    if is_self {
        context.with_env(Env(Some(Rc::clone(frame))))
    } else {
        context.clone()
    }
}

/// What a walk of bounds calls with each binding and the elements bound.
type KeyedVisit<'v, 'ir> = dyn FnMut(&mut Evaluator<'ir>, &Context, &[Value]) -> Evaluated<()> + 'v;

/// The evaluator: the IR, the texts as values, the state it evaluates in, and what it printed.
/// TLC's `CallStack`: the nodes a replay is in, which stop being popped once it fails.
#[derive(Clone, Debug, Default)]
pub struct CallStack {
    pub frames: Vec<StackFrame>,
    pub is_frozen: bool,
    /// The values the replay built that TLC's `CallStackTool` gives a source, by their address,
    /// each with the node that built it.
    sourced: HashMap<usize, NodeId>,
    /// The value each node of the replay last evaluated to.
    values: HashMap<NodeId, Value>,
    /// Whether the failure was in a method of a value with a source, which TLC reports as a
    /// FingerprintException rather than with the nested expressions.
    pub is_fingerprinted: bool,
    /// Whether the fingerprinted failure is of a membership followed to the set whose own test
    /// fails, through no set TLC searches otherwise than the evaluator does.
    pub is_member_followed: bool,
    /// The sources of the values whose methods the failure passed through, outermost first, where
    /// the failure is fingerprinted: the last frames of the call stack TLC's replay prints with
    /// the FingerprintException.
    pub fingerprinted_sources: Vec<NodeId>,
    /// Why the replay can't follow TLC to the failure, where it can't: through an assignment
    /// `x' \in S` whose set TLC streams in an order of its own.
    pub unfollowed: Option<&'static str>,
    /// Where a state the replay found fails to fingerprint: the nodes that built the values the
    /// fingerprint fails in, outermost first, as TLC's FingerprintException traces them, and the
    /// state's values as TLC prints them, in the IR's order of the variables.
    pub fingerprint: Option<(Vec<NodeId>, Vec<String>)>,
    /// Whether the replay built a set enumeration TLC fails to normalize, which TLC keeps as
    /// written until it fingerprints or prints it.
    pub is_unsorted: bool,
    /// TLC's error as it prints an initial state it failed to fingerprint, where printing it fails
    /// too: TLC reports it as an exception it didn't expect.
    pub unprintable: Option<TlcMessage>,
}

impl CallStack {
    /// The node that built a value with a source.
    pub(crate) fn source(&self, value: &Value) -> Option<NodeId> {
        self.sourced.get(&address(value)?).copied()
    }
}

// The address of a value TLC's `CallStackTool` can give a source: an object, as a set, a function
// or a lazy set is.
fn address(value: &Value) -> Option<usize> {
    match value {
        Value::Set(set) => Some(Rc::as_ptr(set) as usize),
        Value::Function(function) => Some(Rc::as_ptr(function) as usize),
        Value::Lazy(lazy) => Some(Rc::as_ptr(lazy) as *const u8 as usize),
        _ => None,
    }
}

/// A node TLC's call stack holds: a node of the IR, or the prefix of an infix chain of junctions,
/// such as A /\ B of A /\ B /\ C, which SANY parses as a node of its own.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StackFrame {
    Node(NodeId),
    /// The first `count` operands of a junction.
    Prefix(NodeId, usize),
}

/// Where TLC needed a boolean, which words its failure where the value isn't one: each is an
/// `Assert.fail` of `Tool` at d8fb231. The walk of the initial predicate, an action or ENABLED
/// (`getInitStates`, `getNextStates`, `enabled`) words its own apart from `Tool#eval`'s.
#[derive(Clone, Copy, Debug)]
pub enum Demand {
    /// A boolean TLC's wording isn't followed for: the failure declines.
    Unworded,
    /// An operand of a junction `eval` takes: of a bulleted list (`OPCODE_cl`, `OPCODE_dl`), or
    /// of SANY's nesting of an infix chain (`OPCODE_land`, `OPCODE_lor`).
    Junction {
        junction: NodeId,
        index: usize,
        is_conjunction: bool,
    },
    /// The condition of this IF, which `eval` takes (`OPCODE_ite`).
    If(NodeId),
    /// The condition of a CASE arm, which `eval` takes (`OPCODE_case`).
    CaseCondition,
    /// What the walk evaluates as a guard: an expression it doesn't walk into, or a literal,
    /// which it can't.
    Guard { is_init: bool },
    /// A conjunct the walk evaluates once every variable has a value (`allAssigned`).
    Remaining { is_init: bool },
    /// The condition of this IF, which the walk takes.
    WalkedIf { node: NodeId, is_init: bool },
    /// The condition of a CASE arm, which the walk takes: TLC names the arm's body.
    WalkedCase { body: NodeId, is_init: bool },
    /// A function's value at an argument, where the walk applies a function TLC holds built
    /// (`OPCODE_fa`, `EC.TLC_EXPECTED_EXPRESSION_IN_COMPUTING2`).
    Applied { is_init: bool },
    /// An invariant, of this expression (`EC.TLC_EXPECTED_VALUE`).
    Invariant,
}

/// The reason for a function's value the walk tests that isn't a boolean.
const APPLIED_NON_BOOLEAN: &str = "a function's value the walk tests that isn't a boolean";

/// The reason for a primed variable a state doesn't assign, before the variable's name.
pub(crate) const PRIMED_UNASSIGNED: &str = "primed variable not assigned: ";

pub struct Evaluator<'ir> {
    pub ir: &'ir Ir,
    /// Builtins that `can_read` counts as reading the state, as `is_precomputed` asks.
    pub(crate) state_builtins: &'static [&'static str],
    texts: Vec<Option<Rc<Text>>>,
    ranks: HashMap<Box<[u16]>, i32>,
    /// The texts ranked past the IR's, in order, while the startup ranks what it makes as TLC
    /// interns it; none otherwise.
    startup_ranked: Option<Vec<Box<[u16]>>>,
    constants: Vec<Option<Value>>,
    /// Zero-arity definitions that read nothing of the state, evaluated once, as TLC does.
    cache: HashMap<(NodeId, bool), Value>,
    /// The current state's values, and the next state's: `None` until assigned.
    pub current: Vec<Option<Value>>,
    pub next: Vec<Option<Value>>,
    /// How many times the evaluator read the state, so a definition that read none is cached.
    reads: u64,
    /// The value of each binding whose evaluation drew from the generator, by the address of the
    /// frame that binds it, which it keeps alive.
    drawn: HashMap<usize, (Rc<Frame>, Value)>,
    /// TLCGet("level") of the current state.
    pub level: i32,
    /// What Print and PrintT printed, each as the texts of its values.
    pub printed: Vec<Vec<String>>,
    /// The state a walk looks for, where a value that differs from it can't lead to it: a walk
    /// then drops an assignment of another value, as nothing else follows from it.
    pub target: Option<Vec<Value>>,
    /// Whether a walk is ENABLED's, which TLC's `Tool#enabled` runs.
    pub(crate) is_enabling: bool,
    /// Where a replay of a failure is, as TLC's `CallStackTool` records it: each node the walks and
    /// the evaluation are in, outermost first, frozen once an evaluation fails.
    pub call_stack: Option<CallStack>,
    /// The choices the walk made to reach where it is: at each disjunction or enumeration, the
    /// position of the branch or element it took, and whether TLC takes them in the same order.
    pub choices: Vec<(u32, bool)>,
    /// The generator RandomElement and RandomSubset draw from: seeded with the fingerprint of the
    /// state TLC expands, as its workers do, and `None` where the evaluator doesn't follow TLC's.
    pub random: Option<JavaRandom>,
    /// What TLCGet and CounterExample read once the search is over, as a postcondition reads them.
    pub runtime: Option<Runtime>,
    /// TLC's registers, which TLCSet sets and TLCGet reads, as the search left them.
    pub registers: Registers,
    /// How many times TLCSet set a register.
    pub register_writes: usize,
    /// How many times TLCGet read a register.
    pub register_reads: usize,
    /// Whether TLC runs with -tool, under which the message of an error TLC raises with a code
    /// holds the code's markers, which AssertError compares with. `None` where the caller doesn't
    /// say, and AssertError isn't followed.
    pub is_tool: Option<bool>,
    /// How many workers TLC runs, which TLCGet("config") reads. `None` where the caller doesn't
    /// say, and TLCGet("config") isn't followed.
    pub workers: Option<usize>,
    /// How many AssertError expressions the evaluator is inside, which compare a failure's
    /// message alone, without where TLC reports it.
    asserting: u32,
    /// The function constructors a LET names once, found when first asked for.
    once_named: Option<HashSet<NodeId>>,
}

/// TLC's registers (`IdThread`'s local values and named registers): the value TLCSet stored under
/// each natural number, and under each name that starts with "s:", a string.
#[derive(Clone, Debug, Default)]
pub struct Registers {
    pub numbered: Vec<Option<Value>>,
    pub named: Vec<(Value, Value)>,
}

/// The prefix of the names of TLC's named registers (`TLCGetSet.NAMED_REGISTER_PREFIX`).
const NAMED_REGISTER_PREFIX: &str = "s:";

impl Registers {
    /// The registers whose values are ids of `store`: by number, and by name.
    pub fn from_store(
        store: &Store,
        numbered: &[Option<Id>],
        named: &[(Id, Id)],
    ) -> Result<Registers, Unsupported> {
        Ok(Registers {
            numbered: numbered
                .iter()
                .map(|value| value.map(|id| from_store(store, id)).transpose())
                .collect::<Result<_, _>>()?,
            named: named
                .iter()
                .map(|&(name, value)| Ok((from_store(store, name)?, from_store(store, value)?)))
                .collect::<Result<_, Unsupported>>()?,
        })
    }
}

fn is_register_name(key: &Value) -> bool {
    matches!(key, Value::Str(text) if String::from_utf16_lossy(&text.units).starts_with(NAMED_REGISTER_PREFIX))
}

/// The values a postcondition reads of the run: TLCGet("all:named"), TLCGet("stats") and TLCExt's
/// CounterExample, built as TLC builds them.
pub struct Runtime {
    pub named: Value,
    pub stats: Value,
    pub counter_example: Value,
    /// Each `_POSSIBLE` predicate's count by name, totalled over the workers, as `_Counts` gives
    /// it.
    pub possible_counts: Value,
}

const MAXIMUM_DEPTH: u32 = 10_000;

/// The stack an evaluation's nesting may use: half the stack the search's threads have, which
/// leaves room for the frames between one nesting and the next.
const MAXIMUM_STACK_BYTES: usize = 128 * 1024 * 1024;

/// `EC.TLC_MODULE_TLCGET_UNDEFINED`, `EC.TLC_MODULE_ARGUMENT_ERROR` and
/// `EC.TLC_MODULE_ONE_ARGUMENT_ERROR`.
const TLCGET_UNDEFINED: u32 = 2145;
const ARGUMENT_ERROR: u32 = 2169;
/// `EC.TLC_MODULE_ARGUMENT_ERROR_AN`.
const ARGUMENT_ERROR_AN: u32 = 2266;
/// `EC.TLC_MODULE_DIVISION_BY_ZERO`.
const DIVISION_BY_ZERO: u32 = 2179;
const ONE_ARGUMENT_ERROR: u32 = 2283;
/// `EC.TLC_EXPECTED_EXPRESSION_IN_COMPUTING`, its `2` and `EC.TLC_EXPECTED_VALUE`.
const EXPECTED_EXPRESSION_IN_COMPUTING: u32 = 2247;
const EXPECTED_EXPRESSION_IN_COMPUTING2: u32 = 2248;
const EXPECTED_VALUE: u32 = 2215;

// TLCGet of a register TLCSet hasn't set, named by its number or its name.
fn undefined_register<T>(key: &Value) -> Evaluated<T> {
    let name = match key {
        Value::Str(text) => String::from_utf16_lossy(&text.units),
        key => format_value(key),
    };
    fail_coded(
        "TLCGet of a register TLC hasn't set",
        TLCGET_UNDEFINED,
        format!("TLCGet({name}) was undefined."),
    )
}

/// The reasons the replay can't follow TLC's frames to a failure, which change no message: TLC
/// prints no frames where an assumption fails to evaluate.
pub(crate) const UNFOLLOWED_FRAMES: [&str; 3] = [LAZY_DOMAIN, BUILT_FUNCTION, LAZY_MEMBER];
const LAZY_MEMBER: &str = "the membership of a filter TLC keeps lazy";
const LAZY_DOMAIN: &str = "the domain of a function TLC keeps lazy";
const BUILT_FUNCTION: &str = "building a function a definition defines";
/// `EC.TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE`.
const JAVA_METHOD_FAILED: u32 = 2154;

const TLC_EVAL: &str = "public static tlc2.value.impl.Value tlc2.module.TLCEval.tlcEval(tlc2.tool.impl.Tool,tla2sany.semantic.ExprOrOpArgNode[],tlc2.util.Context,tlc2.tool.TLCState,tlc2.tool.TLCState,int,tlc2.tool.coverage.CostModel)";

const RANDOM_SUBSET: &str = "public static tlc2.value.impl.Value tlc2.module.Randomization.RandomSubset(tlc2.value.impl.Value,tlc2.value.impl.Value)";

// `reportAsJavaFailure`: a failure with TLC's message, reported as the failure of the Java method
// that TLC overrides an operator with.
fn as_java_failure<T>(signature: &str, result: Evaluated<T>) -> Evaluated<T> {
    result.map_err(|error| match error.message {
        Some(message) => EvalError {
            message: Some(TlcMessage {
                text: format!(
                    "Attempted to apply the operator overridden by the Java method\n{signature},\nbut it produced the following error:\n{}",
                    message.text
                ),
                code: Some(JAVA_METHOD_FAILED),
                is_eval_exception: false,
            }),
            ..error
        },
        None => error,
    })
}

fn is_text(text: &Text, word: &str) -> bool {
    text.units.iter().copied().eq(word.encode_utf16())
}
const TO_STRING: &str =
    "public static tlc2.value.impl.Value tlc2.module.TLC.ToString(tlc2.value.impl.Value)";
const PRINT: &str = "public static tlc2.value.impl.Value tlc2.module.TLC.Print(tlc2.value.impl.Value,tlc2.value.impl.Value)";
const PRINT_T: &str =
    "public static tlc2.value.impl.Value tlc2.module.TLC.PrintT(tlc2.value.impl.Value)";

const DOMAIN_OF_NON_FUNCTION: &str = "DOMAIN of a non-function";

/// TLC's `enumBound`: the most elements a lazy set's text is expanded to.
const ENUM_BOUND: i64 = 2000;

// What `toString(sb, offset, false)` fails with, where it expands a lazy set: the sizes of its
// parts, and its elements where there are fewer than `enumBound`, through the values it holds.
// The evaluator declines a lazy set it doesn't follow there.
fn check_unchecked(value: &Value) -> Evaluated<()> {
    match value {
        Value::Set(elements) => elements.iter().try_for_each(check_unchecked),
        // `SetEnumValue.toString` normalizes the set first.
        Value::Unsorted(elements) => Err(unsorted_failure(elements)),
        Value::Function(function) => function
            .domain
            .iter()
            .chain(&function.range)
            .try_for_each(check_unchecked),
        Value::Lazy(lazy) => {
            let size = match &**lazy {
                _ if lazy.is_overridden() => return Ok(()),
                // `SetOfRcdsValue.toString` and `SetOfTuplesValue.toString`.
                Lazy::RecordSet(fields, _) => parts_size(fields.iter().map(|(_, set)| set))?,
                Lazy::Product(factors) => parts_size(factors.iter())?,
                // `SetOfFcnsValue.toString`.
                Lazy::FunctionSet(domain, range) => {
                    if is_empty(domain)? {
                        1
                    } else {
                        let domain = cardinality(domain)? as i64;
                        let range = cardinality(range)? as i64;
                        let mut size: i64 = 1;
                        for _ in 0..domain {
                            if size > i64::from(i32::MAX) {
                                break;
                            }
                            size = size.saturating_mul(range);
                        }
                        size
                    }
                }
                // Expanded whole, whatever their size.
                Lazy::Cap(..)
                | Lazy::Cup(..)
                | Lazy::Diff(..)
                | Lazy::Union(_)
                | Lazy::Filter(..) => 0,
                // `SubsetValue.toString`: expanded where its base has fewer than 7 elements, and
                // otherwise `SUBSET` its base.
                Lazy::Subset(base) => {
                    if cardinality(base)? < 7 {
                        return elements(value)?.iter().try_for_each(check_unchecked);
                    }
                    return check_unchecked(base);
                }
                _ => return fail("ToString of a lazy set"),
            };
            if size < ENUM_BOUND {
                elements(value)?.iter().try_for_each(check_unchecked)?;
            }
            Ok(())
        }
        _ => Ok(()),
    }
}

// The product of the parts' sizes, past an int no further, and 0 from an empty part on.
fn parts_size<'v>(parts: impl Iterator<Item = &'v Value>) -> Evaluated<i64> {
    let mut size: i64 = 1;
    for part in parts {
        let part = cardinality(part)? as i64;
        if part == 0 {
            return Ok(0);
        }
        if size <= i64::from(i32::MAX) {
            size = size.saturating_mul(part);
        }
    }
    Ok(size)
}

/// `EC.TLC_MODULE_COMPUTING_CARDINALITY`.
const COMPUTING_CARDINALITY: u32 = 2181;
const MODULE_OVERFLOW: u32 = 2178;
const NULL_POWER_NULL: u32 = 2180;
const IS_FINITE_SET: &str =
    "public static tlc2.value.IBoolValue tlc2.module.FiniteSets.IsFiniteSet(tlc2.value.impl.Value)";
const CARDINALITY: &str = "public static tlc2.value.impl.IntValue tlc2.module.FiniteSets.Cardinality(tlc2.value.impl.Value)";
const TEXT_SERIALIZE: &str = "public static synchronized tlc2.value.impl.Value tlc2.module.Json.textSerialize(tlc2.tool.impl.Tool,tla2sany.semantic.ExprOrOpArgNode[],tlc2.util.Context,tlc2.tool.TLCState,tlc2.tool.TLCState,int,tlc2.tool.coverage.CostModel)";

impl<'ir> Evaluator<'ir> {
    pub fn new(ir: &'ir Ir) -> Evaluator<'ir> {
        let ranks = (0..ir.ranked_count)
            .map(|rank| (ir.get_text_units(rank).into(), rank as i32))
            .collect();
        let width = ir.variables.len();
        Evaluator {
            state_builtins: &[],
            ir,
            texts: vec![None; ir.texts.len()],
            ranks,
            startup_ranked: None,
            constants: vec![None; ir.values.list.len()],
            cache: HashMap::new(),
            current: vec![None; width],
            next: vec![None; width],
            reads: 0,
            drawn: HashMap::new(),
            level: 0,
            printed: Vec::new(),
            target: None,
            is_enabling: false,
            call_stack: None,
            choices: Vec::new(),
            random: None,
            runtime: None,
            registers: Registers::default(),
            register_writes: 0,
            register_reads: 0,
            is_tool: None,
            workers: None,
            asserting: 0,
            once_named: None,
        }
    }

    // --- texts and IR values ---

    pub fn text(&mut self, id: TextId) -> Rc<Text> {
        if let Some(text) = &self.texts[id as usize] {
            return Rc::clone(text);
        }
        let units: Box<[u16]> = self.ir.get_text_units(id).into();
        let text = self.text_of(units);
        self.texts[id as usize] = Some(Rc::clone(&text));
        text
    }

    /// A text a string operator makes, which TLC interns: ranked as it is made while the startup
    /// ranks texts (`rankString`, for the strings TLC makes as it starts).
    fn made_text(&mut self, units: Box<[u16]>) -> Rc<Text> {
        if let Some(ranked) = &mut self.startup_ranked
            && !self.ranks.contains_key(&units)
        {
            self.ranks.insert(units.clone(), self.ranks.len() as i32);
            ranked.push(units.clone());
        }
        self.text_of(units)
    }

    /// A text with TLC's rank of it, or -1 for one the IR doesn't rank.
    /// A field name of the records TLC builds of its counterexample (`RecordValue`'s statics):
    /// interned as its class loads, after the spec's strings, in the order declared, unless the
    /// spec has the string.
    pub(crate) fn counterexample_field(&self, name: &str) -> Rc<Text> {
        const FIELDS: [&str; 9] = [
            "beginLine",
            "beginColumn",
            "endLine",
            "endColumn",
            "module",
            "name",
            "location",
            "context",
            "parameters",
        ];
        let units: Box<[u16]> = name.encode_utf16().collect();
        if let Some(&rank) = self.ranks.get(&units) {
            return Rc::new(Text { units, rank });
        }
        let last = self.ranks.values().copied().max().unwrap_or(-1);
        let position = FIELDS.iter().position(|field| *field == name);
        let rank = position.map_or(-1, |position| last + 1 + position as i32);
        Rc::new(Text { units, rank })
    }

    pub fn text_of(&self, units: Box<[u16]>) -> Rc<Text> {
        let rank = self.ranks.get(&units).copied().unwrap_or(-1);
        Rc::new(Text { units, rank })
    }

    pub fn name(&self, id: TextId) -> &'ir str {
        &self.ir.texts[id as usize]
    }

    fn node(&self, node: NodeId) -> (NodeId, &'ir NodeKind) {
        let mut id = node;
        loop {
            match &self.ir.nodes.arena[id as usize].kind {
                NodeKind::Reference(target) => id = *target,
                kind => return (id, kind),
            }
        }
    }

    pub fn kind(&self, node: NodeId) -> &'ir NodeKind {
        self.node(node).1
    }

    pub fn definition(&self, node: NodeId) -> &'ir Definition {
        match self.kind(node) {
            NodeKind::Definition(definition) => definition,
            _ => panic!("a definition index that names no definition"),
        }
    }

    /// A value of the IR's transfer encoding, by its index.
    pub fn value(&mut self, index: u32) -> Evaluated<Value> {
        if let Some(value) = &self.constants[index as usize] {
            return Ok(value.clone());
        }
        let value = self.convert(&self.ir.values.list[index as usize])?;
        self.constants[index as usize] = Some(value.clone());
        Ok(value)
    }

    fn convert(&mut self, value: &tla_ir::Value) -> Evaluated<Value> {
        let class = |class: i32| match class {
            1 => Class::Lambda,
            2 => Class::Tuple,
            3 => Class::Record,
            _ => Class::Plain,
        };
        Ok(match value {
            tla_ir::Value::Bool(boolean) => Value::Bool(*boolean),
            tla_ir::Value::Int(int) => Value::Int(*int),
            tla_ir::Value::String(index) => {
                Value::Str(self.text(self.ir.values.strings[*index as usize]))
            }
            tla_ir::Value::ModelValue(index) => {
                Value::Model(self.text(self.ir.values.strings[*index as usize]))
            }
            tla_ir::Value::Set(elements) => set_of(
                elements
                    .iter()
                    .map(|element| self.convert(element))
                    .collect::<Evaluated<_>>()?,
            )?,
            tla_ir::Value::Function {
                class: function_class,
                domain,
                range,
            } => {
                let keys = domain
                    .iter()
                    .map(|key| self.convert(key))
                    .collect::<Evaluated<Vec<_>>>()?;
                let values = range
                    .iter()
                    .map(|value| self.convert(value))
                    .collect::<Evaluated<Vec<_>>>()?;
                // A value TLC computed at startup is normalized.
                sorted_function(keys, values, class(*function_class))?
            }
            tla_ir::Value::IntervalFunction {
                class: function_class,
                low,
                range,
            } => Value::over_interval(
                *low,
                range
                    .iter()
                    .map(|value| self.convert(value))
                    .collect::<Evaluated<_>>()?,
                class(*function_class),
            ),
        })
    }

    // --- the state ---

    fn read_variable(
        &mut self,
        node: NodeId,
        name: &Name,
        index: u32,
        context: &Context,
    ) -> Evaluated<Value> {
        self.reads += 1;
        let state = if context.is_primed {
            &self.next
        } else {
            &self.current
        };
        match state.get(index as usize) {
            Some(Some(value)) => Ok(value.clone()),
            // TLC's `Tool#evalAppl` fails to look up a variable the state doesn't assign
            // (`createUnassignedError` in `evaluate.ts`).
            Some(None) => fail_with(
                if context.is_primed {
                    format!("{PRIMED_UNASSIGNED}{}", self.name(name.text))
                } else {
                    "variable not assigned".into()
                },
                TlcMessage {
                    text: format!(
                        "In evaluation, the identifier {} is either undefined or not an operator.\n{}",
                        self.name(name.text),
                        self.describe_range(node)
                    ),
                    code: Some(2280),
                    is_eval_exception: false,
                },
            ),
            None => fail("a variable past the state's"),
        }
    }

    // --- evaluation ---

    pub fn boolean(&mut self, node: NodeId, context: &Context) -> Evaluated<bool> {
        self.boolean_as(node, context, Demand::Unworded)
    }

    /// A boolean, failing as TLC does where it demands one and the value isn't.
    pub fn boolean_as(
        &mut self,
        node: NodeId,
        context: &Context,
        demand: Demand,
    ) -> Evaluated<bool> {
        if let Demand::Guard { is_init } = demand
            && self.is_literal(node)
        {
            return self.non_relation(node, is_init);
        }
        match self.evaluate(node, context)? {
            Value::Bool(boolean) => Ok(boolean),
            other => self.non_boolean(node, &other, demand),
        }
    }

    fn is_literal(&self, node: NodeId) -> bool {
        matches!(
            self.kind(node),
            NodeKind::Number(_)
                | NodeKind::WideNumber(_)
                | NodeKind::Decimal(_)
                | NodeKind::String(_)
        )
    }

    // What TLC computes in a walk: "initial states", "next states" or "ENABLED".
    fn computing(&self, is_init: bool) -> &'static str {
        if self.is_enabling {
            "ENABLED"
        } else if is_init {
            "initial states"
        } else {
            "next states"
        }
    }

    // The walk reaching a node that is no operator's application, such as a number, which it
    // can't walk (the `default` of `getInitStates`, `getNextStates` and `enabled`).
    fn non_relation<T>(&self, node: NodeId, is_init: bool) -> Evaluated<T> {
        let Some(written) = self.describe_node(node) else {
            return fail("a literal walked as an action, as TLC prints it");
        };
        let text = if self.is_enabling {
            format!("Attempted to compute ENABLED on a non-boolean expression.\n{written}")
        } else {
            let relation = if is_init { "init" } else { "next" };
            format!("The {relation} state relation is not a boolean expression.\n{written}")
        };
        fail_runtime("a literal walked as an action", text)
    }

    // TLC's failure where a value it demands to be a boolean isn't one.
    pub(crate) fn non_boolean<T>(
        &self,
        node: NodeId,
        value: &Value,
        demand: Demand,
    ) -> Evaluated<T> {
        let reason = format!("expected a boolean, not a {}", value.kind_name());
        let kind = kind_string(value);
        let text = match (demand, kind) {
            (
                Demand::Junction {
                    junction,
                    index,
                    is_conjunction,
                },
                Some(kind),
            ) => {
                let is_bulleted = self
                    .ir
                    .nodes
                    .junctions
                    .get(&self.resolved(junction))
                    .is_none_or(|shape| shape.is_bulleted);
                if is_bulleted {
                    let Some(operand) = self.describe_node(node) else {
                        return fail(reason);
                    };
                    let junction = if is_conjunction {
                        "conjunction"
                    } else {
                        "disjunction"
                    };
                    format!(
                        "A non-boolean expression ({kind}) was used as a formula in a {junction}.\n{operand}"
                    )
                } else {
                    let Some(range) = self.describe_prefix(junction, index.max(1) + 1) else {
                        return fail(reason);
                    };
                    let operator = if is_conjunction { "/\\" } else { "\\/" };
                    let side = if index == 0 { "P" } else { "Q" };
                    format!(
                        "Attempted to evaluate an expression of form P {operator} Q when {side} was\n{kind}.\n{range}"
                    )
                }
            }
            (Demand::If(conditional), Some(kind)) => format!(
                "A non-boolean expression ({kind}) was used as the condition of an IF.\n{}",
                self.describe_range(conditional)
            ),
            (Demand::CaseCondition, Some(kind)) => {
                let Some(condition) = self.describe_node(node) else {
                    return fail(reason);
                };
                format!(
                    "A non-boolean expression ({kind}) was used as a condition of a CASE. {condition}"
                )
            }
            (
                Demand::WalkedIf {
                    node: conditional,
                    is_init,
                },
                Some(kind),
            ) => {
                let range = self.describe_range(conditional);
                match (self.is_enabling, is_init) {
                    (true, _) => format!(
                        "In computing ENABLED, a non-boolean expression({kind}) was used as the guard condition of an IF.\n{range}"
                    ),
                    // `getInitStates` ends the sentence with a new line, `getNextStates` without.
                    (false, true) => format!(
                        "In computing initial states, a non-boolean expression ({kind}) was used as the condition of an IF.\n{range}"
                    ),
                    (false, false) => format!(
                        "In computing next states, a non-boolean expression ({kind}) was used as the condition of an IF.{range}"
                    ),
                }
            }
            (Demand::WalkedCase { body, is_init }, Some(kind)) => {
                let Some(body) = self.describe_node(body) else {
                    return fail(reason);
                };
                let computing = self.computing(is_init);
                let space = if self.is_enabling { "" } else { " " };
                format!(
                    "In computing {computing}, a non-boolean expression{space}({kind}) was used as a guard condition of a CASE.\n{body}"
                )
            }
            (Demand::Guard { is_init } | Demand::Remaining { is_init }, _) => {
                let Some(written) = self.describe_node(node) else {
                    return fail(reason);
                };
                return fail_with(
                    reason,
                    TlcMessage {
                        text: format!(
                            "In computing {}, TLC expected a boolean expression,\nbut instead found {}.\n{written}",
                            self.computing(is_init),
                            format_value(value)
                        ),
                        code: Some(EXPECTED_EXPRESSION_IN_COMPUTING),
                        is_eval_exception: false,
                    },
                );
            }
            (Demand::Applied { is_init }, _) => {
                return fail_with(
                    APPLIED_NON_BOOLEAN,
                    TlcMessage {
                        text: format!(
                            "In computing {}, TLC expected a boolean expression,\nbut didn't find one.\n{}",
                            self.computing(is_init),
                            self.describe_range(node)
                        ),
                        code: Some(EXPECTED_EXPRESSION_IN_COMPUTING2),
                        is_eval_exception: false,
                    },
                );
            }
            (Demand::Invariant, _) => {
                let Some(written) = self.describe_node(node) else {
                    return fail(reason);
                };
                return fail_with(
                    reason,
                    TlcMessage {
                        text: format!(
                            "TLC expected a boolean value, but did not find one. {written}"
                        ),
                        code: Some(EXPECTED_VALUE),
                        is_eval_exception: false,
                    },
                );
            }
            _ => return fail(reason),
        };
        fail_runtime(reason, text)
    }

    /// A node as SANY's `toString` gives it in TLC's messages: a numeral as written, any other
    /// node by its place. `None` for a numeral written otherwise than in decimal, or a decimal.
    pub fn describe_node(&self, node: NodeId) -> Option<String> {
        let resolved = &self.ir.nodes.arena[self.resolved(node) as usize];
        let written = match &resolved.kind {
            NodeKind::Number(int) => int.to_string(),
            NodeKind::WideNumber(text) => self.ir.texts[*text as usize].to_string(),
            NodeKind::Decimal(_) => return None,
            _ => return Some(self.describe_range(node)),
        };
        let range = resolved.range?;
        let width = range.end_column - range.start_column + 1;
        (range.start_line == range.end_line && usize::try_from(width).ok()? == written.len())
            .then_some(written)
    }

    // The place of the first `count` operands of an infix junction, SANY's node of that prefix.
    fn describe_prefix(&self, junction: NodeId, count: usize) -> Option<String> {
        let resolved = self.resolved(junction);
        let range = self.ir.nodes.arena[resolved as usize].range?;
        let shape = self.ir.nodes.junctions.get(&resolved)?;
        let &(end_line, end_column) = match count.checked_sub(2) {
            Some(position) if position < shape.prefix_ends.len() => &shape.prefix_ends[position],
            _ => &(range.end_line, range.end_column),
        };
        Some(format!(
            "line {}, col {} to line {}, col {} of module {}",
            range.start_line,
            range.start_column,
            end_line,
            end_column,
            self.ir.texts[range.module as usize]
        ))
    }

    pub fn evaluate(&mut self, node: NodeId, context: &Context) -> Evaluated<Value> {
        if self.call_stack.is_none() {
            return self.evaluate_node(node, context);
        }
        let (node, _) = self.node(node);
        let result = self.in_frame(StackFrame::Node(node), &mut |evaluator| {
            evaluator.evaluate_node(node, context)
        });
        let is_sourced = self.is_sourced(node);
        if let (Some(stack), Ok(value)) = (&mut self.call_stack, &result) {
            if is_sourced && let Some(address) = address(value) {
                stack.sourced.entry(address).or_insert(node);
            }
            stack.values.insert(node, value.clone());
        }
        result
    }

    // The nodes whose value TLC's `CallStackTool` gives a source (`SOURCED_KINDS` and
    // `SOURCED_OPERATORS` in `evaluate.ts`).
    fn is_sourced(&self, node: NodeId) -> bool {
        match self.kind(node) {
            NodeKind::SetEnumeration(_)
            | NodeKind::SetFilter { .. }
            | NodeKind::SetMap { .. }
            | NodeKind::Tuple(_)
            | NodeKind::FunctionSet { .. }
            | NodeKind::Record(_)
            | NodeKind::RecordSet(_)
            | NodeKind::Product(_) => true,
            NodeKind::Apply { name, .. } => {
                !name.is_local
                    && matches!(
                        self.name(name.text),
                        "SUBSET" | "UNION" | "DOMAIN" | "\\cup" | "\\cap" | "\\"
                    )
            }
            _ => false,
        }
    }

    // The operand whose method TLC calls to compute a node, as `getReceiver` in `evaluate.ts`
    // finds it: the function applied, or the set of a membership.
    fn receiver(&self, node: NodeId) -> Option<NodeId> {
        match self.kind(node) {
            NodeKind::FunctionApplication { function, .. } | NodeKind::Except { function, .. } => {
                Some(*function)
            }
            NodeKind::Apply { name, args } if !name.is_local && args.len() == 2 => {
                match self.name(name.text) {
                    "\\in" | "\\notin" => Some(args[1]),
                    "\\subseteq" | "=" | "#" | "\\" => Some(args[0]),
                    // TLC calls the method of the operand it can enumerate, or else the right one.
                    "\\cap" | "\\cup" => {
                        let left = self.resolved(args[0]);
                        let is_reducible = self.call_stack.as_ref().is_some_and(|stack| {
                            matches!(
                                stack.values.get(&left),
                                Some(Value::Set(_) | Value::Interval(..))
                            )
                        });
                        Some(if is_reducible { args[0] } else { args[1] })
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    // Marks the failure as one in a method of a value with a source, where it is.
    fn mark_fingerprinted(&mut self, frame: StackFrame, reason: &str) {
        let StackFrame::Node(node) = frame else {
            return;
        };
        // The walk tests the value a function's method gave, outside the method.
        if reason == APPLIED_NON_BOOLEAN {
            return;
        }
        // CHOOSE enumerates its set by the set's own method, which fails where TLC can't
        // enumerate the set.
        let chosen = match self.kind(node) {
            NodeKind::Choose { set: Some(set), .. } if reason == "enumerated an infinite set" => {
                Some(*set)
            }
            _ => None,
        };
        let receiver = self
            .receiver(node)
            .or(chosen)
            .map(|receiver| self.resolved(receiver));
        // The element a membership tests, whose failure passes through the sets nested in the
        // receiver that test their own members.
        let element = match self.kind(node) {
            NodeKind::Apply { name, args }
                if !name.is_local && matches!(self.name(name.text), "\\in" | "\\notin") =>
            {
                Some(self.resolved(args[0]))
            }
            _ => None,
        };
        let Some(stack) = &self.call_stack else {
            return;
        };
        let Some(received) = receiver.and_then(|receiver| stack.values.get(&receiver)) else {
            return;
        };
        let element = element
            .and_then(|element| stack.values.get(&element))
            .cloned();
        let received = received.clone();
        self.mark_failing_member(&received, element.as_ref());
    }

    // Marks a failure in a method of a set with a source as TLC's FingerprintException, through
    // the sets nested in it that test the element's parts, where an element was tested.
    fn mark_failing_member(&mut self, received: &Value, element: Option<&Value>) {
        let Some(stack) = &mut self.call_stack else {
            return;
        };
        let Some(source) = stack.source(received) else {
            return;
        };
        if stack.is_fingerprinted {
            return;
        }
        let nested = element.and_then(|element| crate::sets::failing_sets(element, received));
        // TLC searches a set enumeration it hasn't normalized, as one an evaluation just built,
        // element by element with `equals`, which fails otherwise than the search of a sorted one.
        // The evaluator searches so the sets it records as TLC holds them unnormalized.
        let is_followed = nested.as_ref().is_some_and(|nested| {
            std::iter::once(received).chain(nested).all(|set| {
                !matches!(set, Value::Set(_) | Value::Unsorted(_))
                    || stack.source(set).is_none()
                    || unnormalized(set).is_some()
            })
        });
        let sources = nested.iter().flatten().filter_map(|set| stack.source(set));
        let sources: Vec<NodeId> = std::iter::once(source).chain(sources).collect();
        stack.is_fingerprinted = true;
        stack.is_member_followed = is_followed;
        stack.fingerprinted_sources = sources;
    }

    /// Runs `run` in a frame of the call stack, which a failure freezes, as `CallStack.push` and
    /// `pop` do around each node TLC's `CallStackTool` visits.
    pub fn in_frame<T>(
        &mut self,
        frame: StackFrame,
        run: &mut dyn FnMut(&mut Self) -> Evaluated<T>,
    ) -> Evaluated<T> {
        if let Some(stack) = &mut self.call_stack {
            stack.frames.push(frame);
        }
        let result = run(self);
        if let Err(error) = &result
            && self
                .call_stack
                .as_ref()
                .is_some_and(|stack| !stack.is_frozen)
        {
            self.mark_fingerprinted(frame, &error.reason);
        }
        if let Some(stack) = &mut self.call_stack {
            stack.is_frozen |= result.is_err();
            if !stack.is_frozen {
                stack.frames.pop();
            }
        }
        result
    }

    // ENABLED A: whether A takes the current state anywhere, as `Tool.enabled` finds with a next
    // state of its own, a successor whether or not it assigns every variable, in the frames of the
    // call stack as `CallStackTool` keeps them.
    pub(crate) fn enabled(&mut self, action: NodeId, context: &Context) -> Evaluated<Value> {
        let width = self.next.len();
        let next = std::mem::replace(&mut self.next, vec![None; width]);
        let target = self.target.take();
        let is_enabling = std::mem::replace(&mut self.is_enabling, true);
        let mut is_enabled = false;
        let walked = self.walk(action, context, false, &mut |_| {
            is_enabled = true;
            Ok(false)
        });
        self.next = next;
        self.target = target;
        self.is_enabling = is_enabling;
        walked?;
        Ok(Value::Bool(is_enabled))
    }

    // TLC 1.7.4, which words some messages apart.
    pub(crate) fn is_174(&self) -> bool {
        self.ir
            .model
            .version
            .is_some_and(|version| &*self.ir.texts[version as usize] == "1.7.4")
    }

    /// Where a node is written, as TLC's messages say it: `line 2, col 3 to line 2, col 9 of
    /// module M`, or its start where the IR has no range.
    pub fn describe_range(&self, node: NodeId) -> String {
        let node = &self.ir.nodes.arena[self.resolved(node) as usize];
        match node.range {
            Some(range) => format!(
                "line {}, col {} to line {}, col {} of module {}",
                range.start_line,
                range.start_column,
                range.end_line,
                range.end_column,
                self.ir.texts[range.module as usize]
            ),
            None => format!("line {}, column {}", node.line, node.column),
        }
    }

    // `f[x]` with TLC's message where `x` isn't in the domain of `f`.
    pub(crate) fn apply_checked(&self, function: &Value, key: &Value) -> Evaluated<Value> {
        let result = apply_value(function, key);
        match (&result, function) {
            (Err(error), Value::Function(inner))
                if error.message.is_none()
                    && !self.is_174()
                    && error.reason == "applied a function outside its domain" =>
            {
                match describe_missing(function, inner.class.get(), key) {
                    Some(text) => fail_runtime(&error.reason, text),
                    None => result,
                }
            }
            _ => result,
        }
    }

    // `r.f`, with TLC's messages as `getFieldSelector` words them.
    fn select_field(&self, node: NodeId, record: &Value, field: &Value) -> Evaluated<Value> {
        let Value::Str(name) = field else {
            return fail("a field that isn't a string");
        };
        let name = String::from_utf16_lossy(&name.units);
        // `Tool`'s OPCODE_rs takes a function TLC keeps lazy as the value it builds (`toFcnRcd`).
        if let Value::Lambda(lambda) = record {
            return crate::value::lambda_as_function(lambda);
        }
        let Value::Function(inner) = record else {
            return fail_runtime(
                "selected a field of a non-record",
                format!(
                    "Attempted to select field \"{name}\" from a non-record value {}\n{}",
                    format_pretty(record),
                    self.describe_range(node)
                ),
            );
        };
        if self.is_174() {
            return apply_value(record, field);
        }
        match inner.class.get() {
            Class::Tuple => fail_runtime(
                "selected a field of a tuple",
                format!(
                    "Attempted to apply function with integer domain to the non-integer argument {}",
                    format_pretty(field)
                ),
            ),
            Class::Record => match find_key(inner, field)? {
                Some(position) => Ok(inner.range[position].clone()),
                None => fail_runtime(
                    "selected a field a record lacks",
                    format!(
                        "Attempted to select nonexistent field \"{name}\" from the record\n{}\n{}",
                        format_pretty(record),
                        self.describe_range(node)
                    ),
                ),
            },
            _ => match find_key(inner, field)? {
                Some(position) => Ok(inner.range[position].clone()),
                None => fail_runtime(
                    "applied a function outside its domain",
                    format!(
                        "Attempted to apply function:\n{}\nto argument \"{name}\", which is not in the domain of the function.",
                        format_pretty(record)
                    ),
                ),
            },
        }
    }

    // The positions of a record's fields in TLC's order of their names, which `compileRecord`
    // evaluates them in.
    fn field_order(&mut self, fields: &[(TextId, NodeId)]) -> Vec<usize> {
        let names: Vec<Value> = fields
            .iter()
            .map(|&(name, _)| Value::Str(self.text(name)))
            .collect();
        let mut order: Vec<usize> = (0..fields.len()).collect();
        order.sort_by(|&left, &right| {
            compare(&names[left], &names[right]).unwrap_or(std::cmp::Ordering::Equal)
        });
        order
    }

    /// The resolved node of a reference.
    pub fn resolved(&self, node: NodeId) -> NodeId {
        self.node(node).0
    }

    // The operands of a junction TLC walks as one: all of a bulleted list or a junction of two, or
    // otherwise a prefix of an infix chain, then its last operand, as SANY nests the chain.
    pub fn is_walked_whole(&self, node: NodeId, count: usize) -> bool {
        count <= 2
            || self
                .ir
                .nodes
                .junctions
                .get(&self.resolved(node))
                .is_some_and(|junction| junction.is_bulleted)
    }

    // The first `count` operands of a junction, evaluated as TLC evaluates SANY's nesting of an
    // infix chain: the prefix of one fewer, in a frame of its own, then the last.
    fn junction(
        &mut self,
        node: NodeId,
        operands: &[NodeId],
        count: usize,
        is_conjunction: bool,
        context: &Context,
    ) -> Evaluated<bool> {
        let demand = |index| Demand::Junction {
            junction: node,
            index,
            is_conjunction,
        };
        if self.call_stack.is_none() || self.is_walked_whole(node, count) {
            for (index, &operand) in operands[..count].iter().enumerate() {
                if self.boolean_as(operand, context, demand(index))? != is_conjunction {
                    return Ok(!is_conjunction);
                }
            }
            return Ok(is_conjunction);
        }
        let frame = StackFrame::Prefix(self.resolved(node), count - 1);
        let prefix = self.in_frame(frame, &mut |evaluator| {
            evaluator.junction(node, operands, count - 1, is_conjunction, context)
        })?;
        if prefix != is_conjunction {
            return Ok(prefix);
        }
        self.boolean_as(operands[count - 1], context, demand(count - 1))
    }

    fn evaluate_node(&mut self, node: NodeId, context: &Context) -> Evaluated<Value> {
        let kind = self.kind(node);
        match kind {
            NodeKind::Number(int) => Ok(Value::Int(*int)),
            NodeKind::WideNumber(_) => fail("an integer outside 32 bits"),
            NodeKind::Decimal(_) => fail("a real number"),
            NodeKind::String(text) => Ok(Value::Str(self.text(*text))),
            NodeKind::Identifier(name) => self.identifier(node, name, context),
            NodeKind::Apply { name, args } => match (name.resolution, &args[..]) {
                (Resolution::Builtin(index), &[left, right])
                    if self.name(self.ir.builtins[index as usize].name) == "\\subseteq" =>
                {
                    self.subset(node, left, right, context)
                }
                (Resolution::Builtin(index), &[_])
                    if self.name(self.ir.builtins[index as usize].name) == "DOMAIN" =>
                {
                    self.apply(name, args, context).map_err(|mut error| {
                        if let Some(message) = &mut error.message
                            && error.reason == DOMAIN_OF_NON_FUNCTION
                        {
                            message.text =
                                format!("{}\n{}", message.text, self.describe_range(node));
                        }
                        error
                    })
                }
                _ => self.apply(name, args, context),
            },
            NodeKind::And(operands) => Ok(Value::Bool(self.junction(
                node,
                operands,
                operands.len(),
                true,
                context,
            )?)),
            NodeKind::Or(operands) => Ok(Value::Bool(self.junction(
                node,
                operands,
                operands.len(),
                false,
                context,
            )?)),
            NodeKind::Prime(inner) => {
                if context.is_primed {
                    return fail("a prime under a prime");
                }
                self.evaluate(*inner, &context.primed(true))
            }
            NodeKind::Unchanged(inner) => {
                if context.is_primed {
                    return fail("UNCHANGED under a prime");
                }
                self.unchanged(*inner, context)
            }
            NodeKind::If {
                condition,
                consequent,
                alternative,
            } => {
                if self.boolean_as(*condition, context, Demand::If(node))? {
                    self.evaluate(*consequent, context)
                } else {
                    self.evaluate(*alternative, context)
                }
            }
            NodeKind::Case { arms, other } => {
                for &(condition, body) in arms {
                    if self.boolean_as(condition, context, Demand::CaseCondition)? {
                        return self.evaluate(body, context);
                    }
                }
                match other {
                    Some(other) => self.evaluate(*other, context),
                    None => fail("no CASE arm holds"),
                }
            }
            NodeKind::Let {
                definitions, body, ..
            } => {
                let inner = self.bind_let(definitions, context)?;
                self.evaluate(*body, &inner)
            }
            NodeKind::Forall { bounds, body } => {
                let mut holds = true;
                self.for_each_binding(bounds, context, &mut |evaluator, inner| {
                    holds = evaluator.boolean(*body, inner)?;
                    Ok(holds)
                })?;
                Ok(Value::Bool(holds))
            }
            NodeKind::Exists { bounds, body } => {
                let mut holds = false;
                self.for_each_binding(bounds, context, &mut |evaluator, inner| {
                    holds = evaluator.boolean(*body, inner)?;
                    Ok(!holds)
                })?;
                Ok(Value::Bool(holds))
            }
            NodeKind::Choose {
                pattern,
                set: Some(set),
                body,
            } => {
                let set = self.evaluate(*set, context)?;
                for element in elements(&set)?.iter() {
                    let inner = self.bind_pattern(pattern, element, context)?;
                    if self.boolean(*body, &inner)? {
                        return Ok(element.clone());
                    }
                }
                fail_runtime(
                    "CHOOSE found no element",
                    format!(
                        "Attempted to compute the value of an expression of form\nCHOOSE x \\in S: P, but no element of S satisfied P.\n{}",
                        self.describe_range(node)
                    ),
                )
            }
            // `OPCODE_uc`: TLC evaluates no CHOOSE without a bound. Where it computes ENABLED of
            // one as an action, it words the failure apart.
            NodeKind::Choose { set: None, .. } if self.is_enabling => {
                fail("an unbounded CHOOSE in ENABLED")
            }
            NodeKind::Choose { set: None, .. } => fail_runtime(
                "an unbounded CHOOSE",
                format!(
                    "TLC attempted to evaluate an unbounded CHOOSE.\nMake sure that the expression is of form CHOOSE x \\in S: P(x).\n{}",
                    self.describe_range(node)
                ),
            ),
            NodeKind::SetEnumeration(items) => {
                let values = items
                    .iter()
                    .map(|&item| self.evaluate(item, context))
                    .collect::<Evaluated<Vec<_>>>()?;
                self.held_set(values)
            }
            NodeKind::SetFilter { bound, predicate } => {
                let set = self.evaluate(bound.set, context)?;
                // `Tool`'s OPCODE_sso: TLC filters a reducible set at once, and keeps any other
                // filter lazy (`SetPredValue`), testing membership in it by the set's own member
                // first. The evaluator filters a finite one without effects ahead of time, to
                // enumerate it as TLC would, but keeps it lazy.
                if !matches!(
                    set,
                    Value::Set(_) | Value::Interval(..) | Value::Unsorted(_)
                ) {
                    let names = match &bound.pattern {
                        Pattern::Name(name) => self.name(*name).to_string(),
                        Pattern::Tuple(names) => names
                            .iter()
                            .map(|&name| self.name(name))
                            .collect::<Vec<_>>()
                            .join(", "),
                    };
                    let filtered = if is_enumerable(&set) && is_finite(&set).unwrap_or(false) {
                        self.filter_ahead(&set, &bound.pattern, *predicate, context)?
                    } else {
                        None
                    };
                    let predicate = Predicate {
                        pattern: bound.pattern.clone(),
                        body: *predicate,
                        context: context.clone(),
                        current: self.current.clone(),
                        next: self.next.clone(),
                        level: self.level,
                        text: (
                            format!("{{{names} \\in "),
                            format!(" : <expression {}> }}", self.describe_range(*predicate)),
                        ),
                        filtered,
                    };
                    return Ok(Value::Lazy(Rc::new(Lazy::Filter(set, Rc::new(predicate)))));
                }
                let mut kept = Vec::new();
                for element in elements(&set)?.iter() {
                    let inner = self.bind_pattern(&bound.pattern, element, context)?;
                    if self.boolean(*predicate, &inner)? {
                        kept.push(element.clone());
                    }
                }
                Ok(Value::Set(Rc::new(kept)))
            }
            NodeKind::SetMap { expression, bounds } => {
                let mut values = Vec::new();
                self.for_each_binding(bounds, context, &mut |evaluator, inner| {
                    values.push(evaluator.evaluate(*expression, inner)?);
                    Ok(true)
                })?;
                // `Tool`'s OPCODE_soa holds the values unnormalized too.
                self.held_set(values)
            }
            NodeKind::Tuple(items) => Ok(Value::tuple(
                items
                    .iter()
                    .map(|&item| self.evaluate(item, context))
                    .collect::<Evaluated<_>>()?,
            )),
            NodeKind::FunctionConstruction {
                is_recursive: false,
                bounds,
                body,
            } => self.construct_function(bounds, *body, context),
            NodeKind::FunctionSet { domain, range } => {
                let domain = self.evaluate(*domain, context)?;
                let range = self.evaluate(*range, context)?;
                Ok(Value::Lazy(Rc::new(Lazy::FunctionSet(domain, range))))
            }
            NodeKind::Record(fields) => {
                let mut values = vec![None; fields.len()];
                for index in self.field_order(fields) {
                    let (name, value) = fields[index];
                    values[index] = Some((self.text(name), self.evaluate(value, context)?));
                }
                self.check_fields(fields.iter().map(|field| field.0))?;
                Value::record(values.into_iter().flatten().collect())
            }
            NodeKind::RecordSet(fields) => {
                self.check_fields(fields.iter().map(|field| field.0))?;
                let mut sets = Vec::with_capacity(fields.len());
                for index in self.field_order(fields) {
                    let (name, set) = fields[index];
                    sets.push((self.text(name), self.evaluate(set, context)?, index as u32));
                }
                sets.sort_by(|left, right| {
                    compare(
                        &Value::Str(Rc::clone(&left.0)),
                        &Value::Str(Rc::clone(&right.0)),
                    )
                    .unwrap_or(std::cmp::Ordering::Equal)
                });
                let mut written = vec![0; sets.len()];
                for (position, (_, _, index)) in sets.iter().enumerate() {
                    written[*index as usize] = position as u32;
                }
                Ok(Value::Lazy(Rc::new(Lazy::RecordSet(
                    sets.into_iter().map(|(name, set, _)| (name, set)).collect(),
                    written,
                ))))
            }
            NodeKind::Except { function, updates } => {
                let mut value = self.evaluate(*function, context)?;
                for update in updates {
                    value = self.except(&value, &update.path, update.value, context)?;
                }
                Ok(value)
            }
            NodeKind::ExceptAt => match &context.at {
                Some(value) => Ok(value.clone()),
                None => fail("@ outside an EXCEPT"),
            },
            NodeKind::FunctionApplication { function, args } => {
                self.apply_function(node, *function, args, context)
            }
            NodeKind::FieldAccess { record, field } => {
                let record = self.evaluate(*record, context)?;
                let key = Value::Str(self.text(*field));
                self.select_field(node, &record, &key)
            }
            NodeKind::Product(factors) => Ok(Value::Lazy(Rc::new(Lazy::Product(
                factors
                    .iter()
                    .map(|&factor| self.evaluate(factor, context))
                    .collect::<Evaluated<_>>()?,
            )))),
            NodeKind::BoxAction { action, subscript } => {
                if self.boolean(*action, context)? {
                    return Ok(Value::Bool(true));
                }
                self.unchanged(*subscript, context)
            }
            NodeKind::AngleAction { action, subscript } => {
                if !self.boolean(*action, context)? {
                    return Ok(Value::Bool(false));
                }
                Ok(Value::Bool(!matches!(
                    self.unchanged(*subscript, context)?,
                    Value::Bool(true)
                )))
            }
            NodeKind::Label { body, .. } => self.evaluate(*body, context),
            NodeKind::Enabled(action) if !context.is_primed => self.enabled(*action, context),
            _ => fail(format!("evaluating a {}", describe(kind))),
        }
    }

    // `e = e'`, the current side first, as `Tool.evalAppl` evaluates UNCHANGED and `[A]_e`.
    fn unchanged(&mut self, subscript: NodeId, context: &Context) -> Evaluated<Value> {
        let now = self.evaluate(subscript, context)?;
        let then = self.evaluate(subscript, &context.primed(true))?;
        Ok(Value::Bool(equals(&now, &then)?))
    }

    fn check_fields(&self, names: impl Iterator<Item = TextId>) -> Evaluated<()> {
        let mut seen = Vec::new();
        for name in names {
            if seen.contains(&name) {
                return fail(format!(
                    "Field name {} occurs multiple times in record.",
                    self.name(name)
                ));
            }
            seen.push(name);
        }
        Ok(())
    }

    // --- names ---

    fn identifier(&mut self, node: NodeId, name: &Name, context: &Context) -> Evaluated<Value> {
        if name.is_local
            && let Some(frame) = lookup(&context.env, name.text)
        {
            return self.binding(&frame, context);
        }
        match name.resolution {
            Resolution::Variable(index) => return self.read_variable(node, name, index, context),
            Resolution::Constant(index) => {
                return match self.ir.constants[index as usize].value {
                    Some(value) => self.value(value),
                    None => fail(format!(
                        "the constant {}, whose value the IR can't hold",
                        self.name(name.text)
                    )),
                };
            }
            Resolution::Definition(index) => {
                return self.definition_value(self.ir.definitions[index as usize], context);
            }
            Resolution::Builtin(index) if self.ir.builtins[index as usize].arity == 0 => {
                return self.builtin(index, &[], context);
            }
            _ => {}
        }
        match lookup(&context.env, name.text) {
            Some(frame) => self.binding(&frame, context),
            None => fail(format!("the name {}", self.name(name.text))),
        }
    }

    fn binding(&mut self, frame: &Rc<Frame>, context: &Context) -> Evaluated<Value> {
        match &frame.binding {
            Binding::Value(value) => Ok(value.clone()),
            Binding::Thunk {
                node,
                context: bound,
                is_self,
            } => {
                // TLC keeps the value of an argument or a LET definition once it has evaluated
                // it (`LazyValue`), so what it drew from the generator isn't drawn again.
                let key = Rc::as_ptr(frame) as usize;
                if let Some((_, value)) = self.drawn.get(&key) {
                    return Ok(value.clone());
                }
                let inner = own_context(bound, frame, *is_self)
                    .primed(context.is_primed || bound.is_primed);
                let state = self.random.as_ref().map(JavaRandom::state);
                let value = self.evaluate(*node, &inner)?;
                if self.random.as_ref().map(JavaRandom::state) != state {
                    self.drawn.insert(key, (Rc::clone(frame), value.clone()));
                }
                Ok(value)
            }
            Binding::Function {
                definition,
                context: bound,
                is_self,
            } => {
                let definition = self.definition(*definition);
                let DefinitionForm::Function(bounds) = &definition.form else {
                    return fail("a function binding of an operator");
                };
                let inner = own_context(bound, frame, *is_self)
                    .primed(context.is_primed || bound.is_primed);
                self.defined_function(bounds, definition.body, &inner)
            }
            Binding::Operator(_) => fail("an operator used as a value"),
        }
    }

    /// Computes the model's startup definitions as TLC does when it starts, after the
    /// substitutes, drawing from the generator TLC seeds then, and keeps them as their values.
    pub(crate) fn compute_startup(&mut self) -> Evaluated<()> {
        self.compute_startup_drawing()?;
        self.random = None;
        Ok(())
    }

    /// The texts TLC interns as it computes the startup definitions, the substitutes and then
    /// `definitions` (`processConstantDefns`), past those the IR ranks, in order: those Tail,
    /// SubSeq, `\o` and ToString make, as `rankString` ranks them.
    pub(crate) fn get_startup_texts(ir: &Ir, definitions: &[Index]) -> Vec<Box<[u16]>> {
        let mut evaluator = Evaluator::new(ir);
        evaluator.startup_ranked = Some(Vec::new());
        evaluator.random = Some(JavaRandom::seeded(ir.model.random_seed));
        let substitutes = ir.model.startup.substitutes.iter().map(|&(_, index)| index);
        for index in substitutes.chain(definitions.iter().copied()) {
            let node = ir.definitions[index as usize];
            // TLC swallows what a constant definition throws, having interned what it made.
            evaluator
                .evaluate(evaluator.definition(node).body, &Context::default())
                .ok();
        }
        evaluator.startup_ranked.unwrap_or_default()
    }

    /// The startup, with the generator left where its draws left it, for the assumptions.
    pub(crate) fn compute_startup_drawing(&mut self) -> Evaluated<()> {
        let ir = self.ir;
        self.random = Some(JavaRandom::seeded(ir.model.random_seed));
        let substitutes = ir.model.startup.substitutes.iter().map(|&(_, index)| index);
        for index in substitutes.chain(ir.model.startup.definitions.iter().copied()) {
            let node = ir.definitions[index as usize];
            // `processConstantDefns`: TLC swallows whatever a constant definition throws and keeps
            // it as an operator, evaluated again, and failing again, where it is used. The front
            // end has rejected a substitute TLC checks and finds failing.
            let Ok(value) = self.evaluate(self.definition(node).body, &Context::default()) else {
                continue;
            };
            if ir.model.startup.definitions.contains(&index) {
                self.cache.insert((node, false), value.clone());
                self.cache.insert((node, true), value);
            }
        }
        Ok(())
    }

    fn get_named_register(&self, key: &Value) -> Evaluated<Option<Value>> {
        for (name, value) in &self.registers.named {
            if equals(name, key)? {
                return Ok(Some(value.clone()));
            }
        }
        Ok(None)
    }

    // TLCSet (`TLCGetSet.TLCSet`): a register's value, set; TLCSet("exit", FALSE) and
    // TLCSet("pause", FALSE) do nothing.
    fn set_register(&mut self, key: Value, value: Value) -> Evaluated<()> {
        self.register_writes += 1;
        if let Value::Int(index) = key
            && index >= 0
        {
            let index = index as usize;
            let numbered = &mut self.registers.numbered;
            if numbered.len() <= index {
                numbered.resize(index + 1, None);
            }
            numbered[index] = Some(value);
            return Ok(());
        }
        if is_register_name(&key) {
            for (name, held) in &mut self.registers.named {
                if equals(name, &key)? {
                    *held = value;
                    return Ok(());
                }
            }
            self.registers.named.push((key, value));
            return Ok(());
        }
        if let Value::Str(text) = &key {
            let text = String::from_utf16_lossy(&text.units);
            if matches!(text.as_str(), "exit" | "pause") && !matches!(value, Value::Bool(true)) {
                return Ok(());
            }
            if matches!(text.as_str(), "exit" | "pause") || text.starts_with("-D") {
                return fail("TLCSet of a key that stops or configures TLC");
            }
        }
        fail_coded(
            "TLCSet of a key that isn't a natural number",
            ARGUMENT_ERROR,
            format!(
                "The first argument of TLCSet should be a nonnegative integer, but instead it is:\n{}",
                format_pretty(&key)
            ),
        )
    }

    /// Takes the values the search computed at startup for the model's startup definitions,
    /// ids of `store` in their order, as the values of those definitions.
    pub fn set_startup(&mut self, store: &Store, values: &[Id]) -> Result<(), Unsupported> {
        for (&index, &id) in self.ir.model.startup.definitions.iter().zip(values) {
            let node = self.ir.definitions[index as usize];
            let value = from_store(store, id)?;
            self.cache.insert((node, false), value.clone());
            self.cache.insert((node, true), value);
        }
        Ok(())
    }

    fn definition_value(&mut self, node: NodeId, context: &Context) -> Evaluated<Value> {
        let definition = self.definition(node);
        let key = (node, context.is_primed);
        if let Some(value) = self.cache.get(&key) {
            return Ok(value.clone());
        }
        // The value TLC computed at startup, which the search computed and hands on.
        if self
            .ir
            .model
            .startup
            .definitions
            .iter()
            .any(|&index| self.ir.definitions[index as usize] == node)
        {
            return fail("a value TLC computed at startup with effects");
        }
        let reads = self.reads;
        let printed = self.printed.len();
        let value = match &definition.form {
            DefinitionForm::Function(bounds) => {
                self.defined_function(bounds, definition.body, &context.global())?
            }
            DefinitionForm::Operator(params) if params.is_empty() => {
                self.evaluate(definition.body, &context.global())?
            }
            DefinitionForm::Operator(_) => return fail("an operator used as a value"),
        };
        if self.reads == reads && self.printed.len() == printed {
            // TLC computed the value of a definition that reads no state as it started, and
            // sorted it.
            if matches!(&definition.form, DefinitionForm::Operator(_)) {
                note_sorted(&value);
            }
            self.cache.insert(key, value.clone());
        }
        Ok(value)
    }

    pub(crate) fn bind_let(
        &mut self,
        definitions: &[NodeId],
        context: &Context,
    ) -> Evaluated<Context> {
        let mut inner = context.clone();
        for &node in definitions {
            let definition = self.definition(node);
            let binding = match &definition.form {
                DefinitionForm::Function(_) => Binding::Function {
                    definition: node,
                    context: inner.clone(),
                    is_self: definition.flags
                        & (Definition::RECURSIVE | Definition::SELF_REFERENTIAL)
                        != 0,
                },
                DefinitionForm::Operator(params) if params.is_empty() => {
                    if definition.flags & Definition::RECURSIVE != 0 {
                        return fail("a recursive LET definition");
                    }
                    Binding::Thunk {
                        node: definition.body,
                        context: inner.clone(),
                        is_self: false,
                    }
                }
                DefinitionForm::Operator(params) => Binding::Operator(Rc::new(Operator {
                    params: params.clone(),
                    body: Body::Node(definition.body),
                    context: inner.clone(),
                    is_self: definition.flags & Definition::RECURSIVE != 0,
                })),
            };
            inner = inner.bind(definition.name, binding);
        }
        Ok(inner)
    }

    /// The context of an instance's scope, as the compiler's `context_from_scope` builds it.
    pub fn scope_context(&mut self, scope: Option<Index>) -> Evaluated<Context> {
        let Some(index) = scope else {
            return Ok(Context::default());
        };
        let ir = self.ir;
        let scope = &ir.scopes[index as usize];
        let parent = self.scope_context(scope.parent)?;
        let context_of = |evaluator: &mut Self, inner: Option<Index>| {
            if inner == Some(index) {
                Ok(parent.clone())
            } else {
                evaluator.scope_context(inner)
            }
        };
        let binding = match &scope.binding {
            ScopeBinding::Value(Some(value)) => Binding::Value(self.value(*value)?),
            ScopeBinding::Value(None) => {
                return fail("a value in an instance's scope the IR can't hold");
            }
            ScopeBinding::Thunk { expression, scope } => Binding::Thunk {
                node: *expression,
                context: context_of(self, *scope)?,
                is_self: *scope == Some(index),
            },
            ScopeBinding::Closure {
                params,
                body,
                scope,
                ..
            } => Binding::Operator(Rc::new(Operator {
                params: params.clone(),
                body: Body::Node(*body),
                context: context_of(self, *scope)?,
                is_self: *scope == Some(index),
            })),
            ScopeBinding::Opaque => return fail("a binding of an instance's scope"),
        };
        Ok(parent.bind(scope.name, binding))
    }

    // --- operators ---

    /// The body and context of an operator applied, or of a name bound to an expression, which an
    /// action walks into (`resolve_action`).
    pub fn resolve_action(
        &mut self,
        node: NodeId,
        context: &Context,
    ) -> Evaluated<Option<(NodeId, Context)>> {
        match self.kind(node) {
            NodeKind::Identifier(name) => {
                if name.is_local
                    && let Some(frame) = lookup(&context.env, name.text)
                {
                    return Ok(match &frame.binding {
                        Binding::Thunk {
                            node,
                            context: bound,
                            is_self,
                        } => Some((
                            *node,
                            own_context(bound, &frame, *is_self)
                                .primed(bound.is_primed || context.is_primed),
                        )),
                        _ => None,
                    });
                }
                let Resolution::Definition(index) = name.resolution else {
                    return Ok(None);
                };
                let definition = self.definition(self.ir.definitions[index as usize]);
                // TLC computes a definition of no parameters at startup where it is a constant
                // (`processConstantDefns`), a literal too, which the walk then takes as a value.
                let is_startup = self.ir.model.startup.definitions.contains(&index)
                    || self.is_literal(definition.body);
                Ok(match &definition.form {
                    DefinitionForm::Operator(params) if params.is_empty() && !is_startup => {
                        Some((definition.body, context.global()))
                    }
                    _ => None,
                })
            }
            NodeKind::Apply { name, args } => {
                if name.is_local
                    && let Some(frame) = lookup(&context.env, name.text)
                {
                    let Binding::Operator(operator) = &frame.binding else {
                        return Ok(None);
                    };
                    let Body::Node(body) = operator.body else {
                        return Ok(None);
                    };
                    let base = own_context(&operator.context, &frame, operator.is_self)
                        .primed(context.is_primed || operator.context.is_primed);
                    let callee = self.bind_arguments(&operator.params, args, context, base)?;
                    return Ok(Some((body, callee)));
                }
                let Resolution::Definition(index) = name.resolution else {
                    return Ok(None);
                };
                let definition = self.definition(self.ir.definitions[index as usize]);
                let DefinitionForm::Operator(params) = &definition.form else {
                    return Ok(None);
                };
                let callee = self.bind_arguments(params, args, context, context.global())?;
                Ok(Some((definition.body, callee)))
            }
            _ => Ok(None),
        }
    }

    fn bind_arguments(
        &mut self,
        params: &[Param],
        args: &[NodeId],
        caller: &Context,
        callee: Context,
    ) -> Evaluated<Context> {
        if params.len() != args.len() {
            return fail("an operator applied to the wrong number of arguments");
        }
        let mut inner = callee;
        for (param, &argument) in params.iter().zip(args) {
            let binding = if param.arity > 0 {
                Binding::Operator(self.operator_argument(argument, caller)?)
            } else {
                Binding::Thunk {
                    node: argument,
                    context: caller.clone(),
                    is_self: false,
                }
            };
            inner = inner.bind(param.name, binding);
        }
        Ok(inner)
    }

    fn operator_argument(
        &mut self,
        argument: NodeId,
        context: &Context,
    ) -> Evaluated<Rc<Operator>> {
        let name = match self.kind(argument) {
            NodeKind::Lambda { params, body } => {
                return Ok(Rc::new(Operator {
                    params: params
                        .iter()
                        .map(|&name| Param { name, arity: 0 })
                        .collect(),
                    body: Body::Node(*body),
                    context: context.clone(),
                    is_self: false,
                }));
            }
            NodeKind::Identifier(name) | NodeKind::OperatorReference(name) => *name,
            _ => return fail("an operator argument"),
        };
        if let Some(frame) = lookup(&context.env, name.text)
            && let Binding::Operator(operator) = &frame.binding
        {
            if operator.is_self {
                return Ok(Rc::new(Operator {
                    params: operator.params.clone(),
                    body: operator.body,
                    context: own_context(&operator.context, &frame, true),
                    is_self: false,
                }));
            }
            return Ok(Rc::clone(operator));
        }
        match name.resolution {
            Resolution::Definition(index) => {
                let definition = self.definition(self.ir.definitions[index as usize]);
                if let DefinitionForm::Operator(params) = &definition.form {
                    return Ok(Rc::new(Operator {
                        params: params.clone(),
                        body: Body::Node(definition.body),
                        context: context.global(),
                        is_self: false,
                    }));
                }
            }
            Resolution::Builtin(index) => {
                let builtin = &self.ir.builtins[index as usize];
                return Ok(Rc::new(Operator {
                    params: (0..builtin.arity.max(0))
                        .map(|_| Param {
                            name: u32::MAX,
                            arity: 0,
                        })
                        .collect(),
                    body: Body::Builtin(index),
                    context: context.global(),
                    is_self: false,
                }));
            }
            _ => {}
        }
        fail(format!("the operator argument {}", self.name(name.text)))
    }

    fn apply(&mut self, name: &Name, args: &[NodeId], context: &Context) -> Evaluated<Value> {
        if name.is_local
            && let Some(frame) = lookup(&context.env, name.text)
        {
            return match &frame.binding {
                Binding::Operator(operator) => {
                    let operator = Rc::clone(operator);
                    self.call_operator(&operator, &frame, args, context)
                }
                _ => fail("applying a local value"),
            };
        }
        match name.resolution {
            Resolution::Definition(index) => {
                let definition = self.definition(self.ir.definitions[index as usize]);
                let DefinitionForm::Operator(params) = &definition.form else {
                    return fail("applying a function definition as an operator");
                };
                if self.is_text_serialized(definition.name, params.len(), definition.body) {
                    return self.text_serialize(args, context, |evaluator| {
                        let callee =
                            evaluator.bind_arguments(params, args, context, context.global())?;
                        evaluator.nested(|evaluator| evaluator.evaluate(definition.body, &callee))
                    });
                }
                let callee = self.bind_arguments(params, args, context, context.global())?;
                return self.nested(|evaluator| evaluator.evaluate(definition.body, &callee));
            }
            Resolution::Builtin(index) => {
                let operands: Vec<Operand> = args
                    .iter()
                    .map(|&node| Operand::Node(node, context.clone()))
                    .collect();
                return self.builtin(index, &operands, context);
            }
            _ => {}
        }
        if let Some(frame) = lookup(&context.env, name.text)
            && let Binding::Operator(operator) = &frame.binding
        {
            let operator = Rc::clone(operator);
            return self.call_operator(&operator, &frame, args, context);
        }
        // TLC refuses action composition unless a Java property enables its incomplete
        // implementation.
        if self.name(name.text) == "\\cdot" && args.len() == 2 {
            return fail_runtime(
                "action composition",
                if self.is_174() {
                    "The current version of TLC does not support action composition.".into()
                } else {
                    "The current version of TLC does not support action composition.  An incomplete implementation can be enabled via the tlc2.tool.impl.Tool.cdot=true java property.".into()
                },
            );
        }
        fail(format!("the operator {}", self.name(name.text)))
    }

    // IOUtils's Serialize, which TLC overrides with Json.textSerialize but for TLC 1.7.4.
    fn is_text_serialized(&self, name: TextId, arity: usize, body: NodeId) -> bool {
        let node = &self.ir.nodes.arena[self.resolved(body) as usize];
        !self.is_174()
            && arity == 3
            && self.name(name) == "Serialize"
            && node
                .range
                .is_some_and(|range| &*self.ir.texts[range.module as usize] == "IOUtils")
    }

    // Json.textSerialize, an @Evaluation method of TLC's for IOUtils's Serialize, as
    // `compileTextSerialize` has it: it reads the format from the options, writes NDJSON itself,
    // and otherwise evaluates the definition, reporting any failure as its own.
    fn text_serialize(
        &mut self,
        args: &[NodeId],
        context: &Context,
        call: impl FnOnce(&mut Self) -> Evaluated<Value>,
    ) -> Evaluated<Value> {
        let result = (|| {
            let options = self.evaluate(args[2], context)?;
            let fields = match &options {
                Value::Function(function)
                    if function
                        .domain
                        .iter()
                        .all(|key| matches!(key, Value::Str(_))) =>
                {
                    function
                }
                _ => {
                    return fail_runtime(
                        "Serialize's options",
                        format!(
                            "The third argument of ndJsonSerialize should be a sequence, but instead it is:\n{}",
                            format_value(&options)
                        ),
                    );
                }
            };
            // Value.toRcd makes an empty function the empty record.
            if fields.domain.is_empty() {
                return fail_runtime(
                    "Serialize's options",
                    "Attempted to access nonexistent field 'format' of record\n[]".into(),
                );
            }
            let format = fields
                .domain
                .iter()
                .position(|key| matches!(key, Value::Str(text) if is_text(text, "format")))
                .map(|position| &fields.range[position]);
            match format {
                Some(Value::Str(text)) if is_text(text, "NDJSON") => {
                    fail("IOUtils's Serialize with the NDJSON format")
                }
                Some(Value::Str(_)) => call(self),
                _ => fail("IOUtils's Serialize with a format that isn't a string"),
            }
        })();
        as_java_failure(TEXT_SERIALIZE, result)
    }

    fn call_operator(
        &mut self,
        operator: &Rc<Operator>,
        frame: &Rc<Frame>,
        args: &[NodeId],
        context: &Context,
    ) -> Evaluated<Value> {
        let base = own_context(&operator.context, frame, operator.is_self)
            .primed(context.is_primed || operator.context.is_primed);
        match operator.body {
            Body::Node(body) => {
                let callee = self.bind_arguments(&operator.params, args, context, base)?;
                self.nested(|evaluator| evaluator.evaluate(body, &callee))
            }
            Body::Builtin(index) => {
                let operands: Vec<Operand> = args
                    .iter()
                    .map(|&node| Operand::Node(node, context.clone()))
                    .collect();
                self.builtin(index, &operands, &base)
            }
        }
    }

    // Applies an operator argument, such as SelectSeq's test, to values.
    fn call_with_values(&mut self, operator: &Operator, values: &[Value]) -> Evaluated<Value> {
        if operator.params.len() != values.len() {
            return fail("an operator applied to the wrong number of arguments");
        }
        match operator.body {
            Body::Node(body) => {
                let mut inner = operator.context.clone();
                for (param, value) in operator.params.iter().zip(values) {
                    inner = inner.bind_value(param.name, value.clone());
                }
                self.nested(|evaluator| evaluator.evaluate(body, &inner))
            }
            Body::Builtin(index) => {
                let operands: Vec<Operand> = values.iter().cloned().map(Operand::Value).collect();
                self.builtin(index, &operands, &operator.context)
            }
        }
    }

    fn nested<T>(&mut self, work: impl FnOnce(&mut Self) -> Evaluated<T>) -> Evaluated<T> {
        thread_local! {
            static DEPTH: std::cell::Cell<u32> = const { std::cell::Cell::new(0) };
            // Where the outermost nesting's frame is, which the stack grows from.
            static BASE: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
        }
        let depth = DEPTH.get();
        // How deep the frames are depends on the build, so the stack the nesting uses is bounded
        // too, by its distance from the outermost frame.
        let frame = 0u8;
        let here = std::ptr::addr_of!(frame) as usize;
        if depth == 0 {
            BASE.set(here);
        }
        if depth > MAXIMUM_DEPTH || BASE.get().abs_diff(here) > MAXIMUM_STACK_BYTES {
            return fail("recursion too deep");
        }
        DEPTH.set(depth + 1);
        let result = work(self);
        DEPTH.set(depth);
        result
    }

    // --- bound names ---

    pub fn bind_pattern(
        &mut self,
        pattern: &Pattern,
        value: &Value,
        context: &Context,
    ) -> Evaluated<Context> {
        match pattern {
            Pattern::Name(name) => Ok(context.bind_value(*name, value.clone())),
            Pattern::Tuple(names) => {
                let Some(tuple) = as_tuple(value).filter(|tuple| tuple.len() == names.len()) else {
                    return fail("a tuple pattern that doesn't match");
                };
                let mut inner = context.clone();
                for (&name, element) in names.iter().zip(tuple) {
                    inner = inner.bind_value(name, element.clone());
                }
                Ok(inner)
            }
        }
    }

    /// Calls `visit` with each binding of the bounds, the last bound varying fastest, until it
    /// returns false.
    /// Visits the bindings of bounds in the order TLC's `ContextEnumerator` gives them, until
    /// `visit` returns false: each bound's set evaluated first, then the first bound varying
    /// fastest, each binding made as it is visited.
    pub fn for_each_binding(
        &mut self,
        bounds: &[Bound],
        context: &Context,
        visit: &mut dyn FnMut(&mut Self, &Context) -> Evaluated<bool>,
    ) -> Evaluated<bool> {
        let mut sets = Vec::with_capacity(bounds.len());
        for bound in bounds {
            let set = self.evaluate(bound.set, context)?;
            self.check_enumerable(&set, bound.set)?;
            sets.push(elements(&set)?);
        }
        if sets.iter().any(|set| set.is_empty()) {
            return Ok(true);
        }
        let mut positions = vec![0; bounds.len()];
        loop {
            let mut inner = context.clone();
            for (level, bound) in bounds.iter().enumerate() {
                inner =
                    self.bind_pattern(&bound.pattern, &sets[level][positions[level]], &inner)?;
            }
            if !visit(self, &inner)? {
                return Ok(false);
            }
            let mut level = 0;
            while level < positions.len() {
                positions[level] += 1;
                if positions[level] < sets[level].len() {
                    break;
                }
                positions[level] = 0;
                level += 1;
            }
            if level == positions.len() {
                return Ok(true);
            }
        }
    }

    // TLC's failure quantifying over a set it implements in Java and can't enumerate
    // (`Tool.contexts`), which it explains for all but STRING since 1.7.4.
    fn check_enumerable(&self, set: &Value, node: NodeId) -> Evaluated<()> {
        let Value::Lazy(lazy) = set else {
            return Ok(());
        };
        let text = format_value(set);
        let quantified = format!(
            "universally (\\A) or existentially (\\E) quantify over {text}, because this would require checking an\ninfinite number of cases."
        );
        let explanation = match **lazy {
            Lazy::Nat | Lazy::Int | Lazy::Real => format!(
                "The set {text} contains infinitely many elements. As a result, TLC cannot evaluate expressions that\n{quantified} Note that TLC handles set membership like T \\subseteq {text} for any finite set T."
            ),
            Lazy::Seq(_) => format!(
                "In TLA+, Seq(S) represents the set of all finite sequences whose elements come from the set S. Even when S\nis a finite set, the number of possible sequences in Seq(S) is unbounded because sequences can have any\nfinite length (e.g., length 0, 1, 2, and so on). As a result, TLC cannot evaluate expressions that\n{quantified} Note that for a finite set of sequences s, TLC handles s \\subseteq Seq(S).\nSee https://explain.tlapl.us/seq-unenumerable for additional details."
            ),
            Lazy::Strings => String::new(),
            _ => return Ok(()),
        };
        let range = self.describe_range(node);
        fail_runtime(
            "enumerated an infinite set",
            if explanation.is_empty() || self.is_174() {
                format!("TLC encountered a non-enumerable quantifier bound\n{text}.\n{range}")
            } else {
                format!(
                    "TLC encountered the non-enumerable quantifier bound\n{text}\n{range}\n{explanation}"
                )
            },
        )
    }

    // --- functions ---

    // A function a definition or a LET defines. TLC builds it in the frame of the definition,
    // which the replay doesn't record, so a failure building it isn't one the replay follows.
    fn defined_function(
        &mut self,
        bounds: &[Bound],
        body: NodeId,
        context: &Context,
    ) -> Evaluated<Value> {
        // A function whose definition reaches itself as it is built recurses as an operator does.
        let result = self.nested(|evaluator| evaluator.construct_function(bounds, body, context));
        if result.is_err()
            && let Some(stack) = &mut self.call_stack
        {
            stack.unfollowed.get_or_insert(BUILT_FUNCTION);
        }
        result
    }

    fn construct_function(
        &mut self,
        bounds: &[Bound],
        body: NodeId,
        context: &Context,
    ) -> Evaluated<Value> {
        // A function over an interval keeps it as its domain.
        if let [bound] = bounds
            && let Pattern::Name(name) = bound.pattern
        {
            let set = self.evaluate(bound.set, context)?;
            // `Tool`'s OPCODE_fc keeps a function lazy unless its domain is reducible, which
            // the evaluator follows where it can't build the function.
            if !matches!(set, Value::Set(_) | Value::Interval(..))
                && (!is_enumerable(&set) || !is_finite(&set).unwrap_or(false))
            {
                let text = (
                    format!("[{} \\in ", self.name(name)),
                    format!(" |-> <expression {}>]", self.describe_range(body)),
                );
                return Ok(Value::Lambda(Rc::new(Lambda {
                    name,
                    domain: set,
                    body,
                    context: context.clone(),
                    current: self.current.clone(),
                    next: self.next.clone(),
                    level: self.level,
                    excepts: Vec::new(),
                    text,
                })));
            }
            if let Value::Interval(low, high) = set {
                let mut values = Vec::new();
                for key in low..=high {
                    values.push(
                        self.function_body(body, &context.bind_value(name, Value::Int(key)))?,
                    );
                }
                return Ok(Value::over_interval(low, values, Class::Lambda));
            }
            let mut keys = Vec::new();
            let mut values = Vec::new();
            for element in elements(&set)?.iter() {
                keys.push(element.clone());
                values.push(self.function_body(body, &context.bind_value(name, element.clone()))?);
            }
            let function = sorted_function(keys, values, Class::Lambda)?;
            // Applied while TLC keeps it lazy, the function asks its bound's set for the
            // argument, which TLC has sorted where a definition that reads no state names it.
            if let Value::Function(inner) = &function
                && self.is_sorted_constant(bound.set)
            {
                inner.search.set(Search::SortedDomain);
            }
            return Ok(function);
        }
        // TLC evaluates every domain before it enumerates any (`Tool.evalAppl`'s
        // `OPCODE_fc`), so a later domain fails even when an earlier one is empty.
        let mut sets = Vec::with_capacity(bounds.len());
        for bound in bounds {
            sets.push(self.evaluate(bound.set, context)?);
        }
        // TLC keeps such a function lazy too, and applies it without enumerating its domains,
        // which the evaluator doesn't follow for several bounds or a tuple pattern.
        if sets
            .iter()
            .any(|set| !is_enumerable(set) || !is_finite(set).unwrap_or(false))
        {
            return fail("a function of several bounds or a tuple pattern TLC keeps lazy");
        }
        let mut keys = Vec::new();
        let mut values = Vec::new();
        self.for_each_keyed(
            bounds,
            context,
            &mut Vec::new(),
            &mut |evaluator, inner, bound| {
                // The key is the element of a single bound, or the tuple of the bounds' elements.
                keys.push(match bound {
                    [element] => element.clone(),
                    _ => Value::tuple(bound.to_vec()),
                });
                values.push(evaluator.function_body(body, inner)?);
                Ok(())
            },
        )?;
        let function = sorted_function(keys, values, Class::Lambda)?;
        if let ([bound], Value::Function(inner)) = (bounds, &function)
            && self.is_sorted_constant(bound.set)
        {
            inner.search.set(Search::SortedDomain);
        }
        Ok(function)
    }

    // Whether an expression names a definition whose value TLC computed and sorted as it
    // started, which the evaluator has found to read no state.
    fn is_sorted_constant(&self, node: NodeId) -> bool {
        let NodeKind::Identifier(name) = self.kind(node) else {
            return false;
        };
        let Resolution::Definition(index) = name.resolution else {
            return false;
        };
        let definition = self.ir.definitions[index as usize];
        !name.is_local
            && matches!(&self.definition(definition).form, DefinitionForm::Operator(params) if params.is_empty())
            && self.cache.contains_key(&(definition, false))
    }

    // A function's value at one key. TLC builds the function in a method of the FcnLambdaValue
    // that `CallStackTool` gives a source, so a failure there is a FingerprintException, as
    // `headFingerprint` in `evaluate.ts` marks it.
    fn function_body(&mut self, body: NodeId, context: &Context) -> Evaluated<Value> {
        let result = self.evaluate(body, context);
        if result.is_err()
            && let Some(stack) = &mut self.call_stack
        {
            stack.is_fingerprinted = true;
        }
        result
    }

    // Each binding of the bounds with the elements bound, the last bound varying fastest.
    fn for_each_keyed(
        &mut self,
        bounds: &[Bound],
        context: &Context,
        bound: &mut Vec<Value>,
        visit: &mut KeyedVisit<'_, 'ir>,
    ) -> Evaluated<()> {
        let Some((first, rest)) = bounds.split_first() else {
            return visit(self, context, bound);
        };
        let set = self.evaluate(first.set, context)?;
        for element in elements(&set)?.iter() {
            let inner = self.bind_pattern(&first.pattern, element, context)?;
            bound.push(element.clone());
            self.for_each_keyed(rest, &inner, bound, visit)?;
            bound.pop();
        }
        Ok(())
    }

    fn apply_function(
        &mut self,
        node: NodeId,
        function: NodeId,
        args: &[NodeId],
        context: &Context,
    ) -> Evaluated<Value> {
        let argument = |evaluator: &mut Self| {
            if args.len() == 1 {
                return evaluator.evaluate(args[0], context);
            }
            Ok(Value::tuple(
                args.iter()
                    .map(|&arg| evaluator.evaluate(arg, context))
                    .collect::<Evaluated<_>>()?,
            ))
        };
        // A function TLC keeps lazy, a definition's or a LET's, is applied without being built.
        if let NodeKind::Identifier(name) = self.kind(function)
            && let Some((bounds, body, inner)) = self.lazy_function(name, context)?
            && let [bound] = bounds
        {
            let set = self.evaluate(bound.set, &inner);
            // TLC builds the function, its domain in the frames of the name and the definition,
            // which the replay doesn't record.
            if set.is_err()
                && let Some(stack) = &mut self.call_stack
            {
                stack.unfollowed.get_or_insert(LAZY_DOMAIN);
            }
            let set = set?;
            let argument = argument(self)?;
            if !is_member(&argument, &set)? {
                return fail("applied a function outside its domain");
            }
            let bound_context = self.bind_pattern(&bound.pattern, &argument, &inner)?;
            return self.nested(|evaluator| evaluator.evaluate(body, &bound_context));
        }
        // `evalAppl` checks that it applies a function before it evaluates the argument.
        let function_node = function;
        let function = self.evaluate(function, context)?;
        if let Some(kind) = non_function_kind(&function) {
            return fail_runtime(
                "applied a non-function",
                format!(
                    "A non-function ({kind}) was applied as a function.\n{}",
                    self.describe_range(node)
                ),
            );
        }
        let argument = argument(self)?;
        if let Value::Lambda(lambda) = &function {
            return self.apply_lambda(lambda, &argument);
        }
        let result = self.apply_checked(&function, &argument);
        // TLC evaluates the function it applies keeping a constructor lazy
        // (`EvalControl.KeepLazy`), and `FcnLambdaValue.apply` words a key outside the domain
        // with the function as its `FcnRcdValue` prints. It reports the failure with where the
        // function was built, which only AssertError leaves out.
        match (&result, &function) {
            (Err(error), Value::Function(inner))
                if error.message.is_none()
                    && error.reason == "applied a function outside its domain"
                    && inner.class.get() == Class::Lambda
                    && self.asserting > 0
                    && !self.is_174()
                    && self.is_kept_lazy(function_node, context) =>
            {
                fail_runtime(
                    &error.reason,
                    format!(
                        "In applying the function\n{},\nthe first argument is:\n{}\nwhich is not in its domain.\n",
                        format_pretty(&function),
                        format_pretty(&argument)
                    ),
                )
            }
            _ => result,
        }
    }

    // Whether the function `f[e]` applies is certainly one TLC still keeps lazy there: a
    // constructor of one name written in place, or a LET's name for one that the LET names
    // nowhere else, so no earlier evaluation has built it (a LET's value is cached as first
    // evaluated).
    fn is_kept_lazy(&mut self, function: NodeId, context: &Context) -> bool {
        let is_constructor = |evaluator: &Self, node: NodeId| {
            matches!(
                evaluator.kind(node),
                NodeKind::FunctionConstruction { is_recursive: false, bounds, .. }
                    if matches!(&bounds[..], [bound] if matches!(bound.pattern, Pattern::Name(_)))
            )
        };
        match self.kind(function) {
            NodeKind::FunctionConstruction { .. } => is_constructor(self, function),
            NodeKind::Identifier(name) if name.is_local => {
                let Some(frame) = lookup(&context.env, name.text) else {
                    return false;
                };
                let Binding::Thunk { node, .. } = &frame.binding else {
                    return false;
                };
                let node = self.resolved(*node);
                is_constructor(self, node) && self.once_named().contains(&node)
            }
            _ => false,
        }
    }

    // The bodies of the LET definitions that are function constructors named once in their LET.
    fn once_named(&mut self) -> &HashSet<NodeId> {
        if self.once_named.is_none() {
            let ir = self.ir;
            let mut found = HashSet::new();
            for node in &ir.nodes.arena {
                let NodeKind::Let {
                    definitions, body, ..
                } = &node.kind
                else {
                    continue;
                };
                for &definition_node in definitions {
                    let definition = self.definition(definition_node);
                    let is_named_value = matches!(&definition.form, DefinitionForm::Operator(params) if params.is_empty());
                    let constructor = self.resolved(definition.body);
                    if !is_named_value
                        || !matches!(
                            self.kind(constructor),
                            NodeKind::FunctionConstruction { .. }
                        )
                    {
                        continue;
                    }
                    let uses: usize = definitions
                        .iter()
                        .map(|&other| self.definition(other).body)
                        .chain([*body])
                        .map(|root| self.count_names(root, definition.name))
                        .sum();
                    if uses == 1 {
                        found.insert(constructor);
                    }
                }
            }
            self.once_named = Some(found);
        }
        self.once_named.as_ref().expect("the set just found")
    }

    // How many times an expression names `name`, whatever binds it there.
    fn count_names(&self, node: NodeId, name: TextId) -> usize {
        let kind = self.kind(node);
        let own = match kind {
            NodeKind::Identifier(named) | NodeKind::Apply { name: named, .. } => {
                usize::from(named.text == name)
            }
            _ => 0,
        };
        own + kind
            .children()
            .into_iter()
            .map(|child| self.count_names(child, name))
            .sum::<usize>()
    }

    // `FcnLambdaValue.apply`: the value of the last EXCEPT at the key, or else the body on a key
    // in the domain, in the states the function was built in.
    fn apply_lambda(&mut self, lambda: &Lambda, key: &Value) -> Evaluated<Value> {
        for (except, value) in lambda.excepts.iter().rev() {
            if equals(except, key)? {
                return Ok(value.clone());
            }
        }
        let is_member = self.member(key, &lambda.domain);
        // A domain TLC built of other sets, such as `Nat \ {0}` or `Nat \X Nat`, keeps its source,
        // and TLC reports a test of it that fails as a value it can't fingerprint
        // (`FingerprintException.getNewHead`), which the replay doesn't word. Nat, Int, STRING and
        // Seq(S) report the failure itself.
        if is_member.is_err()
            && matches!(&lambda.domain, Value::Lazy(lazy)
                if !matches!(**lazy, Lazy::Nat | Lazy::Int | Lazy::Real | Lazy::Strings | Lazy::Seq(_)))
        {
            return fail("a failing test of a lazy function's domain TLC built from an expression");
        }
        if !is_member? {
            return fail("applied a function outside its domain");
        }
        let context = lambda.context.bind_value(lambda.name, key.clone());
        let current = std::mem::replace(&mut self.current, lambda.current.clone());
        let next = std::mem::replace(&mut self.next, lambda.next.clone());
        let level = std::mem::replace(&mut self.level, lambda.level);
        let result = self.function_body(lambda.body, &context);
        self.current = current;
        self.next = next;
        self.level = level;
        result
    }

    /// For `f[e]` in an action where TLC keeps `f` lazy, a function constructor or a LET's
    /// function: its bound, its body and the context the body is walked in, which the walk binds
    /// to the argument (`resolve_lazy_application` in the engine's walker).
    pub(crate) fn walked_function(
        &mut self,
        function: NodeId,
        context: &Context,
    ) -> Evaluated<Option<(&'ir Bound, NodeId, Context)>> {
        let (bounds, body, base) = match self.kind(function) {
            NodeKind::FunctionConstruction {
                is_recursive: false,
                bounds,
                body,
            } => (bounds, *body, context.clone()),
            NodeKind::Identifier(name) if name.is_local => {
                let Some(frame) = lookup(&context.env, name.text) else {
                    return Ok(None);
                };
                let Binding::Function {
                    definition,
                    context: bound,
                    is_self: false,
                } = &frame.binding
                else {
                    return Ok(None);
                };
                let definition = self.definition(*definition);
                let DefinitionForm::Function(bounds) = &definition.form else {
                    return Ok(None);
                };
                (
                    bounds,
                    definition.body,
                    bound.primed(context.is_primed || bound.is_primed),
                )
            }
            // A function a definition defines, which TLC holds as a FcnLambdaValue unless it
            // computed it at startup.
            NodeKind::Identifier(name) => {
                let Resolution::Definition(index) = name.resolution else {
                    return Ok(None);
                };
                let definition = self.definition(self.ir.definitions[index as usize]);
                let DefinitionForm::Function(bounds) = &definition.form else {
                    return Ok(None);
                };
                if definition.flags & (Definition::RECURSIVE | Definition::SELF_REFERENTIAL) != 0
                    || self.ir.model.startup.definitions.contains(&index)
                {
                    return Ok(None);
                }
                (bounds, definition.body, context.global())
            }
            _ => return Ok(None),
        };
        match &bounds[..] {
            [
                bound @ Bound {
                    pattern: Pattern::Name(_),
                    ..
                },
            ] => Ok(Some((bound, body, base))),
            _ => fail("walking a lazy function of several arguments"),
        }
    }

    // The bounds, body and context of a function definition or LET function a name refers to.
    fn lazy_function(
        &mut self,
        name: &Name,
        context: &Context,
    ) -> Evaluated<Option<(&'ir [Bound], NodeId, Context)>> {
        if name.is_local
            && let Some(frame) = lookup(&context.env, name.text)
        {
            return Ok(match &frame.binding {
                Binding::Function {
                    definition,
                    context: bound,
                    is_self,
                } => {
                    let definition = self.definition(*definition);
                    match &definition.form {
                        DefinitionForm::Function(bounds) => Some((
                            &bounds[..],
                            definition.body,
                            own_context(bound, &frame, *is_self)
                                .primed(context.is_primed || bound.is_primed),
                        )),
                        _ => None,
                    }
                }
                // A recursive function an instance's scope binds, as a LET's in an action's scope.
                Binding::Thunk {
                    node,
                    context: bound,
                    is_self,
                } => match self.kind(*node) {
                    NodeKind::FunctionConstruction {
                        is_recursive: true,
                        bounds,
                        body,
                    } => Some((
                        &bounds[..],
                        *body,
                        own_context(bound, &frame, *is_self)
                            .primed(context.is_primed || bound.is_primed),
                    )),
                    _ => None,
                },
                _ => None,
            });
        }
        let Resolution::Definition(index) = name.resolution else {
            return Ok(None);
        };
        let definition = self.definition(self.ir.definitions[index as usize]);
        let is_startup = self.ir.model.startup.definitions.contains(&index);
        Ok(match &definition.form {
            DefinitionForm::Function(bounds) if !is_startup => {
                Some((&bounds[..], definition.body, context.global()))
            }
            _ => None,
        })
    }

    fn except(
        &mut self,
        value: &Value,
        path: &[PathStep],
        update: NodeId,
        context: &Context,
    ) -> Evaluated<Value> {
        let Some((step, rest)) = path.split_first() else {
            let inner = Context {
                at: Some(value.clone()),
                ..context.clone()
            };
            return self.evaluate(update, &inner);
        };
        let key = match step {
            PathStep::Field(name) => Value::Str(self.text(*name)),
            PathStep::Index(args) if args.len() == 1 => self.evaluate(args[0], context)?,
            PathStep::Index(args) => Value::tuple(
                args.iter()
                    .map(|&arg| self.evaluate(arg, context))
                    .collect::<Evaluated<_>>()?,
            ),
        };
        // `FcnLambdaValue.takeExcept`: the EXCEPT is kept, whatever the key, and `@` is the
        // function's value at it.
        if let Value::Lambda(lambda) = value {
            if !rest.is_empty() {
                return fail("an EXCEPT of a lazy function past its first key");
            }
            let at = self.apply_lambda(lambda, &key)?;
            let next = self.except(&at, rest, update, context)?;
            let mut excepts = lambda.excepts.clone();
            excepts.push((key, next));
            return Ok(Value::Lambda(Rc::new(Lambda {
                name: lambda.name,
                domain: lambda.domain.clone(),
                body: lambda.body,
                context: lambda.context.clone(),
                current: lambda.current.clone(),
                next: lambda.next.clone(),
                level: lambda.level,
                excepts,
                text: lambda.text.clone(),
            })));
        }
        let Value::Function(function) = value else {
            return fail(format!(
                "Attempted to apply EXCEPT construct to the value {}.",
                format_value(value)
            ));
        };
        // TLC leaves a function as it is where the key isn't in its domain.
        let Some(position) = find_key(function, &key)? else {
            return Ok(value.clone());
        };
        let next = self.except(&function.range[position], rest, update, context)?;
        let mut range = function.range.clone();
        range[position] = next;
        Ok(Value::Function(Rc::new(Function {
            domain: function.domain.clone(),
            range,
            class: function.class.clone(),
            written: function.written.clone(),
            search: function.search.clone(),
            interval: function.interval,
        })))
    }

    // --- builtins ---

    fn operand(&mut self, operand: &Operand) -> Evaluated<Value> {
        match operand {
            Operand::Node(node, context) => self.evaluate(*node, context),
            Operand::Value(value) => Ok(value.clone()),
        }
    }

    fn operand_boolean(&mut self, operand: &Operand) -> Evaluated<bool> {
        match self.operand(operand)? {
            Value::Bool(boolean) => Ok(boolean),
            other => fail(format!("expected a boolean, not a {}", other.kind_name())),
        }
    }

    fn operand_int(&mut self, operand: &Operand) -> Evaluated<i64> {
        match self.operand(operand)? {
            Value::Int(int) => Ok(i64::from(int)),
            other => fail(format!("expected an integer, not a {}", other.kind_name())),
        }
    }

    fn operand_operator(&mut self, operand: &Operand) -> Evaluated<Rc<Operator>> {
        match operand {
            Operand::Node(node, context) => self.operator_argument(*node, context),
            Operand::Value(_) => fail("an operator argument"),
        }
    }

    // Membership in a set, through the operands of a `\\cup`, `\\cap` or `\\`, as TLC's lazy
    // `SetCupValue`, `SetCapValue` and `SetDiffValue` test it, so that an infinite operand such as
    // Nat isn't enumerated.
    fn is_member_of(&mut self, element: &Value, set: &Operand) -> Evaluated<bool> {
        let combined = self.combined_set(set)?;
        let result = combined.has(self, element);
        // TLC's \\cup, \\cap and \\ have a source, so a failure in testing their members is a
        // FingerprintException.
        if result.is_err()
            && matches!(combined, Combined::Operation(..))
            && let Some(stack) = &mut self.call_stack
            && !stack.is_frozen
        {
            stack.is_fingerprinted = true;
        }
        result
    }

    /// Membership as TLC's lazy sets test it, the predicate of a lazy filter evaluated
    /// (`SetPredValue.member`), through the sets it is combined in.
    pub(crate) fn member(&mut self, element: &Value, set: &Value) -> Evaluated<bool> {
        let Value::Lazy(lazy) = set else {
            return is_member(element, set);
        };
        match &**lazy {
            Lazy::Filter(base, predicate) => {
                if !self.member(element, base)? {
                    return Ok(false);
                }
                self.filters(element, base, predicate)
            }
            Lazy::Cap(left, right) => {
                Ok(self.member(element, left)? && self.member(element, right)?)
            }
            Lazy::Cup(left, right) => {
                Ok(self.member(element, left)? || self.member(element, right)?)
            }
            Lazy::Diff(left, right) => {
                Ok(self.member(element, left)? && !self.member(element, right)?)
            }
            Lazy::Union(sets) if is_enumerable(sets) => {
                for inner in elements(sets)?.iter() {
                    if self.member(element, inner)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            _ => is_member(element, set),
        }
    }

    // `Tool`'s OPCODE_subseteq: an S TLC can't enumerate fails, and otherwise each element of it
    // is tested for membership in T (`isSubsetEq`).
    fn subset(
        &mut self,
        node: NodeId,
        left: NodeId,
        right: NodeId,
        context: &Context,
    ) -> Evaluated<Value> {
        let left = self.evaluate(left, context)?;
        let right = self.evaluate(right, context)?;
        if matches!(&left, Value::Lazy(lazy) if lazy.is_overridden()) {
            return fail_runtime(
                "\\subseteq of a set TLC doesn't enumerate",
                format!(
                    "Attempted to evaluate an expression of form S \\subseteq T, but S was not enumerable.\n{}",
                    self.describe_range(node)
                ),
            );
        }
        for element in elements(&left)?.iter() {
            // `isSubsetEq` tests each element in T's own `member`, so a failure there is in a
            // method of T, which TLC reports as a FingerprintException where T has a source.
            let is_member = self.member(element, &right);
            if is_member.is_err()
                && self
                    .call_stack
                    .as_ref()
                    .is_some_and(|stack| !stack.is_frozen)
            {
                self.mark_failing_member(&right, Some(element));
            }
            if !is_member? {
                return Ok(Value::Bool(false));
            }
        }
        Ok(Value::Bool(true))
    }

    // A lazy filter's predicate on an element of its set, in the states the filter was built in.
    fn filters(&mut self, element: &Value, base: &Value, predicate: &Predicate) -> Evaluated<bool> {
        let context = match &predicate.pattern {
            Pattern::Name(_) => {
                self.bind_pattern(&predicate.pattern, element, &predicate.context)?
            }
            // TLC fails on an element that isn't a tuple of as many.
            Pattern::Tuple(names) => match as_tuple(element) {
                Some(tuple) if tuple.len() == names.len() => {
                    self.bind_pattern(&predicate.pattern, element, &predicate.context)?
                }
                _ => return fail("a lazy filter's element that isn't a tuple of its names"),
            },
        };
        let current = std::mem::replace(&mut self.current, predicate.current.clone());
        let next = std::mem::replace(&mut self.next, predicate.next.clone());
        let level = std::mem::replace(&mut self.level, predicate.level);
        let result = self.evaluate(predicate.body, &context);
        self.current = current;
        self.next = next;
        self.level = level;
        match result {
            Ok(Value::Bool(holds)) => Ok(holds),
            Ok(_) => fail("a lazy filter's predicate that isn't a boolean"),
            // `SetPredValue.member` words an EvalException as its own failure, whose frames the
            // replay doesn't follow.
            Err(error)
                if error
                    .message
                    .as_ref()
                    .is_some_and(|message| message.is_eval_exception) =>
            {
                if let Some(stack) = &mut self.call_stack {
                    stack.unfollowed.get_or_insert(LAZY_MEMBER);
                }
                fail_runtime(
                    "a lazy filter's predicate that fails",
                    format!(
                        "Cannot decide if element:\n{}\n is element of:\n{}\nand satisfies the predicate {}",
                        format_pretty(element),
                        format_pretty(base),
                        self.describe_range(predicate.body)
                    ),
                )
            }
            Err(error) => Err(error),
        }
    }

    // A set as TLC builds it, both operands of each `\\cup`, `\\cap` or `\\` evaluated.
    fn combined_set(&mut self, set: &Operand) -> Evaluated<Combined> {
        if let Operand::Node(node, context) = set
            && let NodeKind::Apply { name, args } = self.kind(*node)
            && let [left, right] = args[..]
            && !name.is_local
            && let Resolution::Builtin(index) = name.resolution
        {
            // TLC builds a union, intersection or difference of enumerable sets at once, testing
            // their elements, so a failure replay builds each rather than test the membership
            // lazily.
            let operation = match self.name(self.ir.builtins[index as usize].name) {
                _ if self.call_stack.is_some() => None,
                "\\cup" => Some(SetOperation::Union),
                "\\cap" => Some(SetOperation::Intersection),
                "\\" => Some(SetOperation::Difference),
                _ => None,
            };
            if let Some(operation) = operation {
                let left = self.combined_set(&Operand::Node(left, context.clone()))?;
                let right = self.combined_set(&Operand::Node(right, context.clone()))?;
                return Ok(Combined::Operation(
                    operation,
                    Box::new(left),
                    Box::new(right),
                ));
            }
        }
        Ok(Combined::Set(self.operand(set)?))
    }

    // A set enumeration as TLC builds it, of the values as written, which it normalizes only as it
    // uses it: the replay follows that as far as fingerprinting and printing the state, and
    // counting it, and keeps track of the set TLC still holds unnormalized, which it tests for
    // membership element by element.
    fn held_set(&mut self, values: Vec<Value>) -> Evaluated<Value> {
        match set_of(values.clone()) {
            Err(error)
                if error
                    .message
                    .as_ref()
                    .is_some_and(|message| !message.is_eval_exception) =>
            {
                if let Some(stack) = &mut self.call_stack {
                    stack.is_unsorted = true;
                }
                Ok(Value::Unsorted(Rc::new(values)))
            }
            Ok(set) if self.call_stack.is_some() => {
                mark_unnormalized(&set, values);
                Ok(set)
            }
            set => set,
        }
    }

    // A value whose filters TLC keeps lazy are enumerated, at its top or in the tuples and records
    // it is, as what uses it enumerates them (`SetPredValue.toSetEnum`): the predicate evaluated
    // on each element of the set in turn, where the evaluator didn't filter the set ahead.
    fn settle(&mut self, value: &Value) -> Evaluated<Value> {
        Ok(self.settled(value)?.unwrap_or_else(|| value.clone()))
    }

    // `settle`'s value, where it differs.
    fn settled(&mut self, value: &Value) -> Evaluated<Option<Value>> {
        match value {
            Value::Lazy(lazy) => match &**lazy {
                Lazy::Filter(base, predicate)
                    if predicate.filtered().is_none()
                        && is_enumerable(base)
                        && is_finite(base).unwrap_or(false) =>
                {
                    let mut kept = Vec::new();
                    for element in elements(base)?.iter() {
                        if self.passes(element, predicate)? {
                            kept.push(element.clone());
                        }
                    }
                    Ok(Some(Value::Set(Rc::new(kept))))
                }
                _ => Ok(None),
            },
            Value::Function(function)
                if matches!(function.class.get(), Class::Tuple | Class::Record) =>
            {
                let mut range = function.range.clone();
                let mut is_settled = false;
                for element in &mut range {
                    if let Some(settled) = self.settled(element)? {
                        *element = settled;
                        is_settled = true;
                    }
                }
                Ok(is_settled.then(|| {
                    Value::Function(Rc::new(Function {
                        domain: function.domain.clone(),
                        range,
                        class: function.class.clone(),
                        written: function.written.clone(),
                        search: function.search.clone(),
                        interval: function.interval,
                    }))
                }))
            }
            _ => Ok(None),
        }
    }

    // Whether an element passes the predicate of a filter, evaluated where the filter was built.
    fn passes(&mut self, element: &Value, predicate: &Predicate) -> Evaluated<bool> {
        let context = self.bind_pattern(&predicate.pattern, element, &predicate.context)?;
        let current = std::mem::replace(&mut self.current, predicate.current.clone());
        let next = std::mem::replace(&mut self.next, predicate.next.clone());
        let level = std::mem::replace(&mut self.level, predicate.level);
        let result = self.boolean(predicate.body, &context);
        self.current = current;
        self.next = next;
        self.level = level;
        result
    }

    // The elements of a finite set that pass the predicate of a filter TLC keeps lazy, as TLC's
    // enumeration of the filter finds them. None where the predicate fails, which TLC meets only
    // as it uses the filter (`settle`). The evaluator declines a predicate with effects, which
    // TLC has each time it enumerates it.
    fn filter_ahead(
        &mut self,
        set: &Value,
        pattern: &Pattern,
        predicate: NodeId,
        context: &Context,
    ) -> Evaluated<Option<Rc<Vec<Value>>>> {
        let Ok(elements) = elements(set) else {
            return Ok(None);
        };
        let effects = (
            self.printed.len(),
            self.register_writes,
            self.random.as_ref().map(|random| random.state()),
        );
        let call_stack = self.call_stack.clone();
        let mut kept = Vec::new();
        let mut is_failed = false;
        for element in elements.iter() {
            let test = self
                .bind_pattern(pattern, element, context)
                .and_then(|inner| self.boolean(predicate, &inner));
            match test {
                Ok(true) => kept.push(element.clone()),
                Ok(false) => {}
                Err(_) => {
                    self.call_stack = call_stack;
                    is_failed = true;
                    break;
                }
            }
        }
        if effects
            != (
                self.printed.len(),
                self.register_writes,
                self.random.as_ref().map(|random| random.state()),
            )
        {
            return fail("a filter TLC keeps lazy whose predicate has effects");
        }
        Ok((!is_failed).then(|| Rc::new(kept)))
    }

    fn builtin(
        &mut self,
        index: Index,
        operands: &[Operand],
        context: &Context,
    ) -> Evaluated<Value> {
        let builtin = &self.ir.builtins[index as usize];
        // An operator the configuration defines by a table of its values, each row's arguments as
        // a tuple.
        if builtin.flags & Builtin::TABLE != 0 {
            let mut arguments = Vec::with_capacity(operands.len());
            for operand in operands {
                arguments.push(self.operand(operand)?);
            }
            let arguments = Value::tuple(arguments);
            for &(row, value) in &builtin.table {
                let (Some(row), Some(value)) = (row, value) else {
                    return fail("a value of an operator's table the IR can't hold");
                };
                if equals(&self.value(row)?, &arguments)? {
                    return self.value(value);
                }
            }
            return fail("an operator's table applied outside its rows");
        }
        let name = self.name(builtin.name);
        let arity = |count: usize| {
            if operands.len() == count {
                Ok(())
            } else {
                fail("an operator applied to the wrong number of arguments")
            }
        };
        let int = |value: i64| match i32::try_from(value) {
            Ok(value) => Ok(Value::Int(value)),
            Err(_) => fail("integer overflow"),
        };
        Ok(match name {
            "TRUE" => Value::Bool(true),
            "FALSE" => Value::Bool(false),
            "BOOLEAN" => Value::Set(Rc::new(vec![Value::Bool(false), Value::Bool(true)])),
            "Nat" => Value::Lazy(Rc::new(Lazy::Nat)),
            "Any" => Value::Lazy(Rc::new(Lazy::Any)),
            "Int" => Value::Lazy(Rc::new(Lazy::Int)),
            "Real" => Value::Lazy(Rc::new(Lazy::Real)),
            "STRING" => Value::Lazy(Rc::new(Lazy::Strings)),
            "=" | "#" => {
                arity(2)?;
                let left = self.operand(&operands[0])?;
                let right = self.operand(&operands[1])?;
                // The comparison enumerates a filter TLC keeps lazy, the left first.
                let left = self.settle(&left)?;
                let right = self.settle(&right)?;
                Value::Bool(equals(&left, &right)? == (name == "="))
            }
            "~" => {
                arity(1)?;
                Value::Bool(!self.operand_boolean(&operands[0])?)
            }
            "/\\" => {
                for operand in operands {
                    if !self.operand_boolean(operand)? {
                        return Ok(Value::Bool(false));
                    }
                }
                Value::Bool(true)
            }
            "\\/" => {
                for operand in operands {
                    if self.operand_boolean(operand)? {
                        return Ok(Value::Bool(true));
                    }
                }
                Value::Bool(false)
            }
            "=>" => {
                arity(2)?;
                Value::Bool(
                    !self.operand_boolean(&operands[0])? || self.operand_boolean(&operands[1])?,
                )
            }
            "<=>" | "\\equiv" => {
                arity(2)?;
                Value::Bool(
                    self.operand_boolean(&operands[0])? == self.operand_boolean(&operands[1])?,
                )
            }
            "\\in" | "\\notin" => {
                arity(2)?;
                let element = self.operand(&operands[0])?;
                Value::Bool(self.is_member_of(&element, &operands[1])? == (name == "\\in"))
            }
            "\\subseteq" => {
                arity(2)?;
                let left = self.operand(&operands[0])?;
                let right = self.operand(&operands[1])?;
                let mut is_subset = true;
                for element in elements(&left)?.iter() {
                    if !self.member(element, &right)? {
                        is_subset = false;
                        break;
                    }
                }
                Value::Bool(is_subset)
            }
            "\\cup" | "\\cap" | "\\" => {
                arity(2)?;
                let left = self.operand(&operands[0])?;
                let right = self.operand(&operands[1])?;
                match name {
                    "\\cup" => union(&left, &right)?,
                    "\\cap" => intersection(&left, &right)?,
                    _ => difference(&left, &right)?,
                }
            }
            "SUBSET" => {
                arity(1)?;
                let base = self.operand(&operands[0])?;
                if !base.is_set() && !matches!(base, Value::Unsorted(_)) {
                    return fail("SUBSET of a non-set");
                }
                Value::Lazy(Rc::new(Lazy::Subset(base)))
            }
            // `UnionValue.union`: the elements of set enumerations, and otherwise a lazy union.
            "UNION" => {
                arity(1)?;
                let sets = self.operand(&operands[0])?;
                match &sets {
                    Value::Set(sets) if sets.iter().all(|set| matches!(set, Value::Set(_))) => {
                        let mut all = Vec::new();
                        for set in sets.iter() {
                            all.extend(elements(set)?.iter().cloned());
                        }
                        set_of(all)?
                    }
                    _ => Value::Lazy(Rc::new(Lazy::Union(sets))),
                }
            }
            "DOMAIN" => {
                arity(1)?;
                match self.operand(&operands[0])? {
                    // `FcnLambdaValue.getDomain`: its domain, whatever the EXCEPTs.
                    Value::Lambda(lambda) => lambda.domain.clone(),
                    Value::Function(function) => match function.interval {
                        Some((low, high)) => Value::Interval(low, high),
                        None => Value::Set(Rc::new(function.domain.clone())),
                    },
                    // `Tool`'s OPCODE_domain, whose message the application ends with where it is.
                    value => match non_function_kind(&value) {
                        Some(kind) => {
                            return fail_runtime(
                                DOMAIN_OF_NON_FUNCTION,
                                format!(
                                    "Attempted to apply the operator DOMAIN to a non-function\n({kind})"
                                ),
                            );
                        }
                        None => return fail(DOMAIN_OF_NON_FUNCTION),
                    },
                }
            }
            ".." => {
                arity(2)?;
                let low = self.operand_int(&operands[0])?;
                let high = self.operand_int(&operands[1])?;
                Value::Interval(low as i32, high as i32)
            }
            // TLC evaluates both arguments, then its method checks the first and the second
            // (`Naturals.LT` and the like).
            "<" | ">" | "<=" | ">=" => {
                arity(2)?;
                let left = self.operand(&operands[0])?;
                let right = self.operand(&operands[1])?;
                // `tlc2.module.Naturals#GEQ` names itself > in its errors.
                let shown = if builtin.flags & Builtin::NATURALS_GEQ != 0 {
                    ">"
                } else {
                    name
                };
                let (left, right) = match (&left, &right) {
                    (Value::Int(left), Value::Int(right)) => (*left, *right),
                    _ => {
                        let (position, value) = match left {
                            Value::Int(_) => ("second", &right),
                            _ => ("first", &left),
                        };
                        return fail_coded(
                            "expected an integer",
                            ARGUMENT_ERROR_AN,
                            format!(
                                "The {position} argument of {shown} should be an integer, but instead it is:\n{}",
                                format_pretty(value)
                            ),
                        );
                    }
                };
                Value::Bool(match name {
                    "<" => left < right,
                    ">" => left > right,
                    "<=" => left <= right,
                    _ => left >= right,
                })
            }
            "+" | "-" | "*" | "\\div" | "%" | "^" => {
                arity(2)?;
                let left = self.operand_int(&operands[0])?;
                let right = self.operand_int(&operands[1])?;
                match name {
                    "+" => int(left + right)?,
                    "-" => int(left - right)?,
                    "*" => int(left * right)?,
                    "\\div" => {
                        if right == 0 {
                            return fail_coded(
                                "division by zero",
                                DIVISION_BY_ZERO,
                                "The second argument of \\div is 0.".into(),
                            );
                        }
                        int(left.div_euclid(right)
                            - i64::from(right < 0 && left.rem_euclid(right) != 0))?
                    }
                    "%" => {
                        if right <= 0 {
                            return fail_coded(
                                "modulus by a non-positive number",
                                ARGUMENT_ERROR,
                                format!(
                                    "The second argument of % should be a positive number, but instead it is:\n{right}"
                                ),
                            );
                        }
                        int(left.rem_euclid(right))?
                    }
                    "^" => {
                        if right < 0 {
                            return fail_coded(
                                "a negative exponent",
                                ARGUMENT_ERROR,
                                format!(
                                    "The second argument of ^ should be a natural number, but instead it is:\n{right}"
                                ),
                            );
                        }
                        if left == 0 && right == 0 {
                            return fail_coded(
                                "zero to the power of zero",
                                NULL_POWER_NULL,
                                "0^0 is undefined.".into(),
                            );
                        }
                        match u32::try_from(right)
                            .ok()
                            .and_then(|exponent| left.checked_pow(exponent))
                        {
                            Some(power) => int(power)?,
                            None => return fail("integer overflow"),
                        }
                    }
                    _ => unreachable!("an arithmetic operator"),
                }
            }
            "-." => {
                arity(1)?;
                int(-self.operand_int(&operands[0])?)?
            }
            // `TLCExt.assertError`: whether evaluating the expression fails with this message.
            "AssertError" => {
                arity(2)?;
                let Some(is_tool) = self.is_tool else {
                    return fail("AssertError, whose messages depend on -tool");
                };
                let is_literal = match &operands[0] {
                    Operand::Node(node, _) => {
                        matches!(
                            self.ir.nodes.arena[*node as usize].kind,
                            NodeKind::String(_)
                        )
                    }
                    Operand::Value(_) => false,
                };
                if !is_literal {
                    return fail("AssertError of a message that isn't a string");
                }
                self.asserting += 1;
                let asserted = self.operand(&operands[1]);
                self.asserting -= 1;
                let message = match asserted {
                    Ok(_) => return Ok(Value::Bool(false)),
                    Err(EvalError {
                        message: Some(message),
                        ..
                    }) => message,
                    Err(error) => return Err(error),
                };
                let Value::Str(expected) = self.operand(&operands[0])? else {
                    return fail("AssertError of a message that isn't a string");
                };
                let text = if is_tool {
                    nested(&message)
                } else {
                    message.text
                };
                Value::Bool(text.encode_utf16().eq(expected.units.iter().copied()))
            }
            // TLC reports what fails as it counts, but an EvalException, as the failure of the Java
            // method `FiniteSets.Cardinality` (`MethodValue.eval`).
            "Cardinality" => {
                arity(1)?;
                let set = self.operand(&operands[0])?;
                // `SetPredValue.size` enumerates a filter TLC keeps lazy.
                let set = self.settle(&set)?;
                // `FiniteSets.Cardinality` counts an `Enumerable` value.
                let is_enumerable = match &set {
                    Value::Lazy(lazy) => !lazy.is_overridden(),
                    Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::Model(_) => false,
                    _ => true,
                };
                if !is_enumerable {
                    return fail_coded(
                        "Cardinality of a value TLC doesn't enumerate",
                        COMPUTING_CARDINALITY,
                        format!(
                            "Attempted to compute cardinality of the value\n{}",
                            format_pretty(&set)
                        ),
                    );
                }
                // TLC normalizes a set enumeration as it counts it.
                if let Value::Unsorted(values) = &set
                    && let Some(error) = crate::value::normalize_failure(values)
                {
                    return as_java_failure(CARDINALITY, Err(error));
                }
                let counted = cardinality(&set);
                let counted = match &counted {
                    Err(EvalError {
                        message: Some(message),
                        ..
                    }) if !message.is_eval_exception => as_java_failure(CARDINALITY, counted),
                    _ => counted,
                };
                int(counted? as i64)?
            }
            // TLC reports what fails, but an EvalException, as the failure of the Java method
            // `FiniteSets.IsFiniteSet` (`MethodValue.eval`).
            "IsFiniteSet" => {
                arity(1)?;
                let set = self.operand(&operands[0])?;
                let checked = is_finite(&set);
                let checked = match &checked {
                    Err(EvalError {
                        message: Some(message),
                        ..
                    }) if !message.is_eval_exception => as_java_failure(IS_FINITE_SET, checked),
                    _ => checked,
                };
                Value::Bool(checked?)
            }
            "Seq" => {
                arity(1)?;
                Value::Lazy(Rc::new(Lazy::Seq(self.operand(&operands[0])?)))
            }
            // A string is as long as its characters (`Sequences.Len`).
            "Len" => {
                arity(1)?;
                match self.operand(&operands[0])? {
                    Value::Str(text) => int(text.units.len() as i64)?,
                    sequence => int(argument_sequence("Len", &sequence)?.len() as i64)?,
                }
            }
            "Head" => {
                arity(1)?;
                let sequence = self.operand(&operands[0])?;
                match argument_sequence("Head", &sequence)?.first() {
                    Some(head) => head.clone(),
                    None => return fail("Head of the empty sequence"),
                }
            }
            "Tail" => {
                arity(1)?;
                let sequence = self.operand(&operands[0])?;
                // A string's tail is the string of the characters past its first.
                if let Value::Str(text) = &sequence {
                    if text.units.is_empty() {
                        return fail("Tail of the empty string");
                    }
                    return Ok(Value::Str(self.made_text(text.units[1..].into())));
                }
                let elements = argument_sequence("Tail", &sequence)?;
                if elements.is_empty() {
                    return fail("Tail of the empty sequence");
                }
                Value::tuple(elements[1..].to_vec())
            }
            "Append" => {
                arity(2)?;
                let sequence = self.operand(&operands[0])?;
                let element = self.operand(&operands[1])?;
                let mut elements = sequence_of(&sequence)?.to_vec();
                elements.push(element);
                Value::tuple(elements)
            }
            "\\o" => {
                arity(2)?;
                let left = self.operand(&operands[0])?;
                let right = self.operand(&operands[1])?;
                if let (Value::Str(left), Value::Str(right)) = (&left, &right) {
                    let units: Box<[u16]> = left
                        .units
                        .iter()
                        .chain(right.units.iter())
                        .copied()
                        .collect();
                    return Ok(Value::Str(self.made_text(units)));
                }
                let mut elements = sequence_of(&left)?.to_vec();
                elements.extend(sequence_of(&right)?.iter().cloned());
                Value::tuple(elements)
            }
            "SubSeq" => {
                arity(3)?;
                let sequence = self.operand(&operands[0])?;
                let from = self.operand_int(&operands[1])?;
                let to = self.operand_int(&operands[2])?;
                // A string slices as the sequence of its characters, and stays a string.
                let length = match &sequence {
                    Value::Str(text) => text.units.len(),
                    _ => sequence_of(&sequence)?.len(),
                };
                let range = if from > to {
                    0..0
                } else if from < 1 || to > length as i64 {
                    return fail("SubSeq outside the sequence's domain");
                } else {
                    from as usize - 1..to as usize
                };
                match &sequence {
                    Value::Str(text) => Value::Str(self.made_text(text.units[range].into())),
                    _ => Value::tuple(sequence_of(&sequence)?[range].to_vec()),
                }
            }
            "SelectSeq" => {
                arity(2)?;
                let sequence = self.operand(&operands[0])?;
                let test = self.operand_operator(&operands[1])?;
                let mut kept = Vec::new();
                for element in sequence_of(&sequence)? {
                    match self.call_with_values(&test, std::slice::from_ref(element))? {
                        Value::Bool(true) => kept.push(element.clone()),
                        Value::Bool(false) => {}
                        _ => return fail("a SelectSeq test that isn't a boolean"),
                    }
                }
                Value::tuple(kept)
            }
            ":>" => {
                arity(2)?;
                let key = self.operand(&operands[0])?;
                let value = self.operand(&operands[1])?;
                Value::function(vec![key], vec![value], Class::Plain)
            }
            "@@" => {
                arity(2)?;
                let left = self.operand(&operands[0])?;
                let right = self.operand(&operands[1])?;
                let (Value::Function(left), Value::Function(right)) = (&left, &right) else {
                    return fail("@@ of a non-function");
                };
                // The keys of the left in its written order, then those only the right has.
                let mut keys = Vec::new();
                let mut values = Vec::new();
                let order: Vec<usize> = match &*left.written.borrow() {
                    Some(written) => written.iter().map(|&position| position as usize).collect(),
                    None => (0..left.domain.len()).collect(),
                };
                for position in order {
                    keys.push(left.domain[position].clone());
                    values.push(left.range[position].clone());
                }
                let right_order: Vec<usize> = match &*right.written.borrow() {
                    Some(written) => written.iter().map(|&position| position as usize).collect(),
                    None => (0..right.domain.len()).collect(),
                };
                for position in right_order {
                    if find_key(left, &right.domain[position])?.is_none() {
                        keys.push(right.domain[position].clone());
                        values.push(right.range[position].clone());
                    }
                }
                // TLC keeps the written order of a function of strings, which prints as a record.
                if keys.iter().all(|key| matches!(key, Value::Str(_))) {
                    written_function(keys, values, Class::Plain)?
                } else {
                    sorted_function(keys, values, Class::Plain)?
                }
            }
            // TLC evaluates both arguments, as it does any Java method's, then tests the first.
            "Assert" => {
                arity(2)?;
                let holds = self.operand_boolean(&operands[0])?;
                let message = self.operand(&operands[1])?;
                if holds {
                    Value::Bool(true)
                } else {
                    return fail_coded(
                        "an assertion failed",
                        2132,
                        format!(
                            "The first argument of Assert evaluated to FALSE; the second argument was:\n{}",
                            format_pretty(&message)
                        ),
                    );
                }
            }
            "Print" | "PrintT" => {
                let mut values = Vec::with_capacity(operands.len());
                for operand in operands {
                    values.push(self.operand(operand)?);
                }
                let expected = if name == "Print" { 2 } else { 1 };
                if values.len() != expected {
                    return fail("an operator applied to the wrong number of arguments");
                }
                let signature = if name == "Print" { PRINT } else { PRINT_T };
                // Print's Java method enumerates a filter TLC keeps lazy as it prints it.
                for value in &mut values {
                    *value = as_java_failure(signature, self.settle(value))?;
                }
                // TLC prints each value with `toStringUnchecked`, which fails where a lazy set's
                // expansion fails.
                let checked = values.iter().try_for_each(check_unchecked);
                if let Err(EvalError {
                    message: Some(message),
                    ..
                }) = &checked
                    && !message.is_eval_exception
                {
                    return as_java_failure(signature, checked.map(|()| Value::Bool(true)));
                }
                checked?;
                self.printed
                    .push(values.iter().map(format_printed).collect());
                if name == "Print" {
                    values[1].clone()
                } else {
                    Value::Bool(true)
                }
            }
            "RandomElement" | "RandomSubset" => {
                let values = operands
                    .iter()
                    .map(|operand| self.operand(operand))
                    .collect::<Evaluated<Vec<_>>>()?;
                // A draw is never the same twice, so what reads one isn't cached.
                self.reads += 1;
                let is_174 = self.is_174();
                let Some(random) = self.random.as_mut() else {
                    return fail(
                        "a random draw where the evaluator doesn't follow TLC's generator",
                    );
                };
                match (name, values.as_slice()) {
                    ("RandomElement", [set]) => random_element(random, set)?,
                    // TLC 1.7.4 draws a subset's indices another way.
                    ("RandomSubset", [Value::Int(count), set]) if *count >= 0 && !is_174 => {
                        random_subset(random, *count as u64, set)?
                    }
                    // `SetEnumValue.getRandomSubset` and `IntervalValue.getRandomSubset` make room
                    // for the subset first, which Java refuses for a negative count.
                    ("RandomSubset", [Value::Int(count), Value::Set(_) | Value::Interval(..)])
                        if *count < 0 && !is_174 =>
                    {
                        return as_java_failure(
                            RANDOM_SUBSET,
                            fail_runtime("RandomSubset of a negative count", count.to_string()),
                        );
                    }
                    _ => return fail(name.to_string()),
                }
            }
            "_Counts" if self.runtime.is_some() => {
                arity(0)?;
                self.reads += 1;
                self.runtime
                    .as_ref()
                    .expect("the runtime")
                    .possible_counts
                    .clone()
            }
            "CounterExample" if self.runtime.is_some() => {
                arity(0)?;
                self.reads += 1;
                self.runtime
                    .as_ref()
                    .expect("the runtime")
                    .counter_example
                    .clone()
            }
            // The states of a CounterExample as a sequence, each at its number
            // (`CounterExample.toTrace`).
            "ToTrace" => {
                arity(1)?;
                let counter_example = self.operand(&operands[0])?;
                let key = Value::Str(self.text_of("state".encode_utf16().collect()));
                let states = match &counter_example {
                    Value::Function(record) => match find_key(record, &key)? {
                        Some(position) => record.range[position].clone(),
                        None => return fail("ToTrace of a record without states"),
                    },
                    _ => return fail("ToTrace of a value that isn't a CounterExample"),
                };
                let states = elements(&states)?;
                let mut trace = vec![None; states.len()];
                for state in states.iter() {
                    let Some([Value::Int(number), record]) = as_tuple(state) else {
                        return fail("ToTrace of a state that isn't numbered");
                    };
                    match trace.get_mut((*number as usize).wrapping_sub(1)) {
                        Some(slot) => *slot = Some(record.clone()),
                        None => return fail("ToTrace of a state numbered past the trace"),
                    }
                }
                match trace.into_iter().collect::<Option<Vec<_>>>() {
                    Some(trace) => Value::tuple(trace),
                    None => return fail("ToTrace of a trace missing a state"),
                }
            }
            // The Json module's Java methods, whose arguments TLC evaluates first, as their failure
            // shows; reading and writing the files is the engine's, not the replay's.
            "JsonSerialize" | "ndJsonSerialize" | "JsonDeserialize" | "ndJsonDeserialize" => {
                arity(if name.ends_with("Serialize") { 2 } else { 1 })?;
                for operand in operands {
                    self.operand(operand)?;
                }
                return fail(format!(
                    "{name}, whose file the replay doesn't read or write"
                ));
            }
            // TLC's TLCEval is an @Evaluation method that evaluates its argument itself, and
            // reports its failure as its own, which TLC 1.7.4's Java override didn't.
            "TLCEval" => {
                arity(1)?;
                let value = self.operand(&operands[0]);
                if self.is_174() {
                    value?
                } else {
                    as_java_failure(TLC_EVAL, value)?
                }
            }
            // `TLC.ToString` prints with `toStringUnchecked`, where what the expansion of a lazy
            // set fails with fails, reported, but an EvalException, as its Java method's.
            "ToString" => {
                arity(1)?;
                let value = self.operand(&operands[0])?;
                let checked = check_unchecked(&value);
                if let Err(EvalError {
                    message: Some(message),
                    ..
                }) = &checked
                    && !message.is_eval_exception
                {
                    return as_java_failure(TO_STRING, checked.map(|()| Value::Bool(true)));
                }
                checked?;
                let units: Box<[u16]> = format_value(&value).encode_utf16().collect();
                Value::Str(self.made_text(units))
            }
            // TLC's empty bag is the empty function (`Bags.EmptyBag`).
            "EmptyBag" => {
                arity(0)?;
                Value::function(Vec::new(), Vec::new(), Class::Plain)
            }
            // A bag's copies of the first's elements, then of the second's others, added
            // (`Bags.BagCup`), or the first's less the second's, kept where some remain
            // (`Bags.BagDiff`).
            "\\oplus" | "\\ominus" => {
                arity(2)?;
                let left = self.operand(&operands[0])?;
                let right = self.operand(&operands[1])?;
                let (left, right) = (bag_counts(&left)?, bag_counts(&right)?);
                let count_in = |bag: &[(Value, i32)], key: &Value| -> Evaluated<Option<i32>> {
                    for (element, count) in bag {
                        if equals(element, key)? {
                            return Ok(Some(*count));
                        }
                    }
                    Ok(None)
                };
                let mut keys = Vec::new();
                let mut values = Vec::new();
                for (element, count) in &left {
                    let other = count_in(&right, element)?.unwrap_or(0);
                    let total = if name == "\\oplus" {
                        Some(add_counts(*count, other)?)
                    } else {
                        count.checked_sub(other)
                    };
                    let Some(total) = total else {
                        return fail("a bag's count past an int");
                    };
                    if total > 0 {
                        keys.push(element.clone());
                        values.push(Value::Int(total));
                    }
                }
                if name == "\\oplus" {
                    for (element, count) in &right {
                        if count_in(&left, element)?.is_none() {
                            keys.push(element.clone());
                            values.push(Value::Int(*count));
                        }
                    }
                }
                written_function(keys, values, Class::Plain)?
            }
            // Each element of a set once (`Bags.SetToBag`).
            "SetToBag" => {
                arity(1)?;
                let set = self.operand(&operands[0])?;
                let keys = elements(&set)?.to_vec();
                let values = vec![Value::Int(1); keys.len()];
                sorted_function(keys, values, Class::Plain)?
            }
            // The copies a bag holds (`Bags.BagCardinality`), which TLC adds in an int.
            "BagCardinality" => {
                arity(1)?;
                let bag = self.operand(&operands[0])?;
                let mut size = 0;
                for (_, count) in positive_counts(&bag)? {
                    size = add_counts(size, count)?;
                }
                Value::Int(size)
            }
            // The sum of a set's bags in the set's order (`Bags.BagUnion`).
            "BagUnion" => {
                arity(1)?;
                let set = self.operand(&operands[0])?;
                let bags = elements(&set)?;
                match bags.as_slice() {
                    [] => Value::function(Vec::new(), Vec::new(), Class::Plain),
                    [bag] => bag.clone(),
                    [first, rest @ ..] => {
                        let mut counts = bag_counts(first)?;
                        for bag in rest {
                            merge_counts(&mut counts, bag_counts(bag)?)?;
                        }
                        counted_bag(counts)?
                    }
                }
            }
            // The elements a bag holds (`Bags.BagToSet`).
            "BagToSet" => {
                arity(1)?;
                let bag = self.operand(&operands[0])?;
                set_of(bag_counts(&bag)?.into_iter().map(|(key, _)| key).collect())?
            }
            // The model value of a name (`TLCExt.tlcModelValue`), which compares by the name's
            // rank, as TLC ranks it.
            "TLCModelValue" => {
                arity(1)?;
                match self.operand(&operands[0])? {
                    Value::Str(name) if name.rank >= 0 => Value::Model(name),
                    Value::Str(_) => return fail("TLCModelValue of a name TLC ranks as it runs"),
                    _ => return fail("TLCModelValue of a value that isn't a string"),
                }
            }
            "TLCSet" => {
                arity(2)?;
                let key = self.operand(&operands[0])?;
                let value = self.operand(&operands[1])?;
                // What sets a register is never the same twice, so what calls it isn't cached.
                self.reads += 1;
                self.set_register(key, value)?;
                Value::Bool(true)
            }
            // `TLCExt.tlcFingerprint`: TLC's fingerprint of the value, as an int.
            "TLCFP" => {
                arity(1)?;
                let value = self.operand(&operands[0])?;
                let mut fingerprints = tla_values::fingerprint::Fingerprints::new();
                match crate::fingerprint::state_fingerprint(&mut fingerprints, &[&value]) {
                    Some(fingerprint) => Value::Int(fingerprint as i32),
                    None => return fail("TLCFP of a value the evaluator doesn't fingerprint"),
                }
            }
            // `TLCExt.tlcDefer`: TLC's breadth-first search never runs the deferred expression.
            "TLCDefer" => {
                arity(1)?;
                Value::Bool(true)
            }
            "TLCGet" => {
                arity(1)?;
                match self.operand(&operands[0])? {
                    // A register, whose value no cache may keep.
                    key @ Value::Int(index) if index >= 0 => {
                        self.reads += 1;
                        self.register_reads += 1;
                        match self.registers.numbered.get(index as usize) {
                            Some(Some(value)) => value.clone(),
                            _ => return undefined_register(&key),
                        }
                    }
                    key if is_register_name(&key) => {
                        self.reads += 1;
                        self.register_reads += 1;
                        match self.get_named_register(&key)? {
                            Some(value) => value,
                            None => return undefined_register(&key),
                        }
                    }
                    key @ (Value::Int(_)
                    | Value::Bool(_)
                    | Value::Model(_)
                    | Value::Set(_)
                    | Value::Interval(..)
                    | Value::Function(_)
                    | Value::Lazy(_)) => {
                        return fail_coded(
                            "TLCGet of a key that isn't a natural number",
                            ONE_ARGUMENT_ERROR,
                            format!(
                                "The argument of TLCGet should be a nonnegative integer, but instead it is:\n{}",
                                format_pretty(&key)
                            ),
                        );
                    }
                    // The specification's record, as the interpreter computes it for TLC's.
                    Value::Str(key) if *key.units == *"spec".encode_utf16().collect::<Vec<_>>() => {
                        let ir = self.ir;
                        match ir.model.tlc_spec {
                            Some(index) => self.convert(&ir.values.list[index as usize])?,
                            None => return fail("TLCGet(\"spec\") the IR doesn't hold"),
                        }
                    }
                    // `AbstractChecker.createConfig`, as the engine words it: TLC's install is
                    // where its jar is, which the native checker has none of.
                    Value::Str(key)
                        if *key.units == *"config".encode_utf16().collect::<Vec<_>>() =>
                    {
                        let Some(workers) = self.workers else {
                            return fail("TLCGet(\"config\") without the run's workers");
                        };
                        let model = &self.ir.model;
                        let text = |text: &str| self.text_of(text.encode_utf16().collect());
                        let string = |value: &str| Value::Str(text(value));
                        Value::record(vec![
                            (text("mode"), string("bfs")),
                            (text("deadlock"), Value::Bool(model.check_deadlock)),
                            (text("worker"), Value::Int(workers as i32)),
                            (
                                text("seed"),
                                string(&(model.random_seed as i64).to_string()),
                            ),
                            (
                                text("fingerprint"),
                                string(&(tla_values::fingerprint::INITIAL as i64).to_string()),
                            ),
                            (text("install"), string("unknown")),
                        ])?
                    }
                    Value::Str(key)
                        if *key.units == *"level".encode_utf16().collect::<Vec<_>>() =>
                    {
                        self.reads += 1;
                        Value::Int(self.level + i32::from(context.is_primed))
                    }
                    // Once the search is over, the run's counts, and its named registers, each
                    // the tuple of one worker's value.
                    Value::Str(key) if self.runtime.is_some() => {
                        self.reads += 1;
                        let key = String::from_utf16_lossy(&key.units);
                        let runtime = self.runtime.as_ref().expect("the runtime");
                        match key.as_str() {
                            "all:named" => runtime.named.clone(),
                            "all" => {
                                let (indices, values) = self
                                    .registers
                                    .numbered
                                    .iter()
                                    .enumerate()
                                    .filter_map(|(index, value)| {
                                        let value = value.clone()?;
                                        Some((Value::Int(index as i32), Value::tuple(vec![value])))
                                    })
                                    .unzip();
                                sorted_function(indices, values, Class::Plain)?
                            }
                            "stats" => runtime.stats.clone(),
                            "generated" | "distinct" | "queue" | "diameter" => {
                                let Value::Function(stats) = &runtime.stats else {
                                    return fail("TLCGet");
                                };
                                let position = stats.domain.iter().position(|field| {
                                    matches!(field, Value::Str(name) if String::from_utf16_lossy(&name.units) == key)
                                });
                                match position {
                                    Some(position) => stats.range[position].clone(),
                                    None => return fail("TLCGet"),
                                }
                            }
                            _ => return fail("TLCGet"),
                        }
                    }
                    _ => return fail("TLCGet"),
                }
            }
            "Permutations" => {
                arity(1)?;
                let set = self.operand(&operands[0])?;
                let elements = elements(&set)?;
                if elements.len() > 8 {
                    return fail("Permutations of a set too large to build");
                }
                let mut permutations = Vec::new();
                permute(
                    &elements,
                    &mut Vec::new(),
                    &mut vec![false; elements.len()],
                    &mut permutations,
                );
                set_of(
                    permutations
                        .into_iter()
                        .map(|image| Value::function(elements.to_vec(), image, Class::Plain))
                        .collect(),
                )?
            }
            other => return fail(format!("the builtin {other}")),
        })
    }
}

fn permute(
    elements: &[Value],
    image: &mut Vec<Value>,
    used: &mut [bool],
    out: &mut Vec<Vec<Value>>,
) {
    if image.len() == elements.len() {
        out.push(image.clone());
        return;
    }
    for index in 0..elements.len() {
        if !used[index] {
            used[index] = true;
            image.push(elements[index].clone());
            permute(elements, image, used, out);
            image.pop();
            used[index] = false;
        }
    }
}

/// An argument of a builtin: an expression as written, or a value an operator argument is
/// applied to.
enum SetOperation {
    Union,
    Intersection,
    Difference,
}

enum Combined {
    Set(Value),
    Operation(SetOperation, Box<Combined>, Box<Combined>),
}

impl Combined {
    // Membership, testing the right operand only where the left one doesn't decide it.
    fn has(&self, evaluator: &mut Evaluator<'_>, element: &Value) -> Evaluated<bool> {
        match self {
            Combined::Set(set) => evaluator.member(element, set),
            Combined::Operation(operation, left, right) => Ok(match operation {
                SetOperation::Union => {
                    left.has(evaluator, element)? || right.has(evaluator, element)?
                }
                SetOperation::Intersection => {
                    left.has(evaluator, element)? && right.has(evaluator, element)?
                }
                SetOperation::Difference => {
                    left.has(evaluator, element)? && !right.has(evaluator, element)?
                }
            }),
        }
    }
}

enum Operand {
    Node(NodeId, Context),
    Value(Value),
}

// Whether a set (or a function, which the engine counts as a finite set) is finite, without
// enumerating it: a lazy set is when its parts are.
// `isFinite` of TLC's set values: a set of functions, records or tuples is finite where one of
// its finite parts is empty, and `Seq(S)` where S is.
fn is_finite(value: &Value) -> Evaluated<bool> {
    Ok(match value {
        Value::Lazy(lazy) => match &**lazy {
            Lazy::Nat | Lazy::Int | Lazy::Real | Lazy::Strings | Lazy::Any => false,
            Lazy::Seq(range) => is_finite(range)? && is_empty(range)?,
            Lazy::Subset(base) => is_finite(base)?,
            Lazy::FunctionSet(domain, range) => {
                let is_domain_finite = is_finite(domain)?;
                if is_domain_finite && is_empty(domain)? {
                    return Ok(true);
                }
                let is_range_finite = is_finite(range)?;
                (is_range_finite && is_empty(range)?)
                    || (is_domain_finite && is_range_finite)
                    || (is_range_finite && cardinality(range)? == 1)
            }
            Lazy::RecordSet(fields, _) => is_all_finite(fields.iter().map(|(_, set)| set))?,
            Lazy::Product(factors) => is_all_finite(factors.iter())?,
            // `SetCapValue.isFinite`, `SetCupValue.isFinite` and `SetDiffValue.isFinite`.
            Lazy::Cap(left, right) => {
                if !is_finite(left)? && !is_finite(right)? {
                    return finiteness_failure(value);
                }
                true
            }
            Lazy::Cup(left, right) => is_finite(left)? && is_finite(right)?,
            // `SetPredValue.isFinite`: finite where S is.
            Lazy::Filter(base, _) => {
                if !is_finite(base)? {
                    return fail_runtime(
                        "whether a filter of an infinite set is finite",
                        format!(
                            "Attempted to check if expression of form {{x \\in S : p(x)}} is a finite set, but cannot check if S:\n{}\nis finite.",
                            format_pretty(base)
                        ),
                    );
                }
                true
            }
            // `UnionValue.isFinite`: every element of an enumerable set of sets.
            Lazy::Union(sets) => {
                if !is_enumerable(sets) {
                    return fail("whether the union of a set TLC doesn't enumerate is finite");
                }
                for set in elements(sets)?.iter() {
                    if !is_finite(set)? {
                        return Ok(false);
                    }
                }
                true
            }
            Lazy::Diff(left, right) => {
                if is_finite(left)? {
                    return Ok(true);
                }
                if !is_finite(right)? {
                    return finiteness_failure(value);
                }
                false
            }
        },
        // `isFinite` of a value that isn't a set.
        Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::Model(_) => {
            let kind = match value {
                Value::Bool(_) => "boolean",
                Value::Int(_) => "integer",
                Value::Str(_) => "string",
                _ => "model value",
            };
            return fail_runtime(
                "IsFiniteSet of a non-set",
                format!(
                    "Attempted to check if the {kind} {} is a finite set.",
                    format_pretty(value)
                ),
            );
        }
        Value::Function(function) if function.class.get() == Class::Lambda => {
            return fail_runtime(
                "IsFiniteSet of a function",
                format!(
                    "Attempted to check if the function:\n{}\nis a finite set.",
                    format_pretty(value)
                ),
            );
        }
        _ => true,
    })
}

fn finiteness_failure(set: &Value) -> Evaluated<bool> {
    fail_runtime(
        "checked whether a lazy set of infinite operands is finite",
        format!(
            "Attempted to check if the set {}is finite.",
            format_pretty(set)
        ),
    )
}

// `SetOfRcdsValue.isFinite` and `SetOfTuplesValue.isFinite`: finite where a finite part is empty,
// or every part is finite.
fn is_all_finite<'v>(parts: impl Iterator<Item = &'v Value>) -> Evaluated<bool> {
    let mut is_all_finite = true;
    for part in parts {
        if !is_finite(part)? {
            is_all_finite = false;
        } else if is_empty(part)? {
            return Ok(true);
        }
    }
    Ok(is_all_finite)
}

// `Value.isEmpty` of a set whose finiteness TLC checks first, so it never enumerates an infinite
// one.
pub(crate) fn is_empty(value: &Value) -> Evaluated<bool> {
    Ok(match value {
        Value::Set(elements) => elements.is_empty(),
        Value::Interval(low, high) => low > high,
        Value::Lazy(lazy) => match &**lazy {
            Lazy::Nat | Lazy::Int | Lazy::Real | Lazy::Strings | Lazy::Seq(_) | Lazy::Subset(_) => {
                false
            }
            // `UserObj.isEmpty`, which `AnySet` keeps.
            Lazy::Any => {
                return fail_runtime(
                    "isEmpty of Any",
                    "Shouldn't call isEmpty() on value ANY".into(),
                );
            }
            Lazy::FunctionSet(domain, range) => !is_empty(domain)? && is_empty(range)?,
            Lazy::RecordSet(fields, _) => {
                for (_, set) in fields {
                    if is_empty(set)? {
                        return Ok(true);
                    }
                }
                false
            }
            Lazy::Product(factors) => {
                for factor in factors {
                    if is_empty(factor)? {
                        return Ok(true);
                    }
                }
                false
            }
            // TLC enumerates them for a first element, as their enumerators find it.
            Lazy::Cap(left, right) => {
                let (enumerated, tested) = if is_enumerable(left) {
                    (left, right)
                } else if is_enumerable(right) {
                    (right, left)
                } else {
                    return elements(value).map(|elements| elements.is_empty());
                };
                for element in elements(enumerated)?.iter() {
                    if is_member(element, tested)? {
                        return Ok(false);
                    }
                }
                true
            }
            Lazy::Cup(left, right) if is_enumerable(left) && is_enumerable(right) => {
                is_empty(left)? && is_empty(right)?
            }
            Lazy::Diff(left, right) if is_enumerable(left) => {
                for element in elements(left)?.iter() {
                    if !is_member(element, right)? {
                        return Ok(false);
                    }
                }
                true
            }
            Lazy::Union(sets) if is_enumerable(sets) => {
                for (index, inner) in elements(sets)?.iter().enumerate() {
                    if !is_enumerable(inner) {
                        // Past the first, TLC words the failure with the union's text.
                        if index > 0 {
                            return fail("a union with a later set TLC doesn't enumerate");
                        }
                        return elements(value).map(|elements| elements.is_empty());
                    }
                    if !is_empty(inner)? {
                        return Ok(false);
                    }
                }
                true
            }
            Lazy::Cup(..) | Lazy::Diff(..) | Lazy::Union(_) | Lazy::Filter(..) => {
                elements(value)?.is_empty()
            }
        },
        Value::Unsorted(elements) => elements.is_empty(),
        _ => {
            return fail_runtime(
                "isEmpty of a non-set",
                format!("Shouldn't call isEmpty() on value {}", format_pretty(value)),
            );
        }
    })
}

// TLC's `getKindString` of a value that isn't a function, whose class the evaluator knows: a
// scalar or a lazy set, but not a set enumeration, which TLC may hold as another class.
fn non_function_kind(value: &Value) -> Option<&'static str> {
    match value {
        Value::Bool(_) => Some("a Boolean value"),
        Value::Int(_) => Some("an integer"),
        Value::Str(_) => Some("a string"),
        Value::Model(_) => Some("a model value"),
        Value::Lazy(lazy) => match &**lazy {
            Lazy::Nat | Lazy::Int | Lazy::Strings | Lazy::Seq(_) => Some("a special set constant"),
            Lazy::Filter(..) => Some("a set of the form {x \\in S : expr}"),
            Lazy::FunctionSet(..) => Some("a set of the form [S -> T]"),
            Lazy::RecordSet(..) => Some("a set of the form [d1 : S1, ... , dN : SN]"),
            Lazy::Product(_) => Some("a cartesian product"),
            Lazy::Subset(_) => Some("a set of the form SUBSET S"),
            Lazy::Diff(..) => Some("a set of the form S \\ T"),
            Lazy::Cap(..) => Some("a set of the form S \\cap T"),
            Lazy::Cup(..) => Some("a set of the form S \\cup T"),
            Lazy::Union(_) => Some("a set of the form UNION  S"),
            _ => None,
        },
        _ => None,
    }
}

// TLC's `getKindString` of a value whose class the evaluator knows: one `non_function_kind`
// knows, or a function TLC holds as a `TupleValue`, a `RecordValue` or a `FcnRcdValue`.
fn kind_string(value: &Value) -> Option<&'static str> {
    match value {
        Value::Function(function) => match function.class.get() {
            Class::Tuple => Some("a tuple"),
            Class::Record => Some("a record"),
            Class::Plain => Some("a function  of the form (d1 :> e1 @@ ... @@ dN :> eN)"),
            Class::Lambda => None,
        },
        _ => non_function_kind(value),
    }
}

// The sequence the argument of Len, Head or Tail must be (`EC.TLC_MODULE_ONE_ARGUMENT_ERROR`).
fn argument_sequence<'v>(name: &str, value: &'v Value) -> Evaluated<&'v [Value]> {
    match as_tuple(value) {
        Some(elements) => Ok(elements),
        None => fail_coded(
            format!("{name} of a non-sequence"),
            ONE_ARGUMENT_ERROR,
            format!(
                "The argument of {name} should be a sequence, but instead it is:\n{}",
                format_pretty(value)
            ),
        ),
    }
}

fn sequence_of(value: &Value) -> Evaluated<&[Value]> {
    match as_tuple(value) {
        Some(elements) => Ok(elements),
        None => fail(format!("expected a sequence, not {}", format_value(value))),
    }
}

/// `f[x]`: a function applied to a key in its domain.
pub fn apply_value(function: &Value, key: &Value) -> Evaluated<Value> {
    let Value::Function(inner) = function else {
        return fail(format!(
            "applied a non-function: {}",
            format_value(function)
        ));
    };
    match find_key(inner, key)? {
        Some(position) => Ok(inner.range[position].clone()),
        None => fail("applied a function outside its domain"),
    }
}

// TLC's message for a function applied outside its domain, by the class of the function, as
// `describeMissingArgument` in `values.ts` words it after TLC 1.7.4. A lambda has none here: TLC
// keeps a function constructor lazy only where it evaluates it so (`EvalControl.KeepLazy`), and
// turns one of enumerable domains into a `FcnRcdValue` elsewhere, as at startup, which the
// evaluator doesn't follow yet.
fn describe_missing(function: &Value, class: Class, key: &Value) -> Option<String> {
    let shown = format_pretty(function);
    let shown_key = format_pretty(key);
    Some(match (class, key) {
        (Class::Lambda, _) => return None,
        (Class::Tuple, Value::Int(index)) => {
            format!("Attempted to access index {index} of tuple\n{shown}\nwhich is out of bounds.")
        }
        (Class::Tuple, _) => {
            format!("Attempted to access tuple at a non integral index: {shown_key}")
        }
        (Class::Record, Value::Str(field)) => format!(
            "Attempted to access nonexistent field '{}' of record\n{shown}",
            String::from_utf16_lossy(&field.units)
        ),
        (Class::Record, _) => {
            format!("Attempted to access record by a non-string argument: {shown_key}")
        }
        (Class::Plain, _) => format!(
            "Attempted to apply function:\n{shown}\nto argument {shown_key}, which is not in the domain of the function."
        ),
    })
}

fn describe(kind: &NodeKind) -> &'static str {
    match kind {
        NodeKind::Enabled(_) => "ENABLED",
        NodeKind::Lambda { .. } => "LAMBDA",
        NodeKind::OperatorReference(_) => "an operator reference",
        NodeKind::UnboundedQuantifier { .. } => "an unbounded quantifier",
        NodeKind::FunctionConstruction { .. } => "a recursive function",
        NodeKind::Always(_) | NodeKind::Eventually(_) => "a temporal formula",
        NodeKind::WeakFairness { .. } | NodeKind::StrongFairness { .. } => "a fairness",
        NodeKind::Subexpression(_) => "a subexpression",
        NodeKind::Bracket(_) => "a bracket",
        _ => "node",
    }
}

// TLC's sum of two counts (`Bags.addCounts`), which fails where an int overflows.
fn add_counts(left: i32, right: i32) -> Evaluated<i32> {
    match left.checked_add(right) {
        Some(sum) => Ok(sum),
        None => fail_coded(
            "an overflow adding the counts of a bag",
            MODULE_OVERFLOW,
            format!("Overflow when computing {left}+{right}"),
        ),
    }
}

// The counts of a bag, each of which TLC requires to be positive (`Bags.IsABag`).
fn positive_counts(bag: &Value) -> Evaluated<Vec<(Value, i32)>> {
    let counts = bag_counts(bag)?;
    if counts.iter().any(|&(_, count)| count <= 0) {
        return fail("a bag with a count that isn't positive");
    }
    Ok(counts)
}

// Adds a bag's counts to those gathered, a new element after them.
fn merge_counts(counts: &mut Vec<(Value, i32)>, added: Vec<(Value, i32)>) -> Evaluated<()> {
    for (key, count) in added {
        let mut held = None;
        for (index, (inner_key, _)) in counts.iter().enumerate() {
            if equals(inner_key, &key)? {
                held = Some(index);
                break;
            }
        }
        match held {
            Some(index) => counts[index].1 = add_counts(counts[index].1, count)?,
            None => counts.push((key, count)),
        }
    }
    Ok(())
}

// The bag of the counts gathered, in their order, as TLC builds it before it normalizes it.
fn counted_bag(counts: Vec<(Value, i32)>) -> Evaluated<Value> {
    let (keys, values) = counts
        .into_iter()
        .map(|(key, count)| (key, Value::Int(count)))
        .unzip();
    written_function(keys, values, Class::Plain)
}

// A bag's elements with their counts, in the order of its domain, as TLC reads a bag's function.
fn bag_counts(bag: &Value) -> Evaluated<Vec<(Value, i32)>> {
    let Value::Function(function) = bag else {
        return fail("a bag that isn't a function");
    };
    function
        .domain
        .iter()
        .zip(&function.range)
        .map(|(key, count)| match count {
            Value::Int(count) => Ok((key.clone(), *count)),
            _ => fail("a bag whose count isn't an integer"),
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lazy(lazy: Lazy) -> Value {
        Value::Lazy(Rc::new(lazy))
    }

    #[test]
    fn finds_a_set_finite_as_tlc_does() {
        let nat = || lazy(Lazy::Nat);
        let empty = || Value::Set(Rc::new(Vec::new()));
        let one = || Value::Interval(0, 0);
        // [Nat -> {}] and [Nat -> {0}] are finite, [Nat -> 0..1] isn't.
        assert!(is_finite(&lazy(Lazy::FunctionSet(nat(), empty()))).expect("finite"));
        assert!(is_finite(&lazy(Lazy::FunctionSet(nat(), one()))).expect("finite"));
        assert!(
            !is_finite(&lazy(Lazy::FunctionSet(nat(), Value::Interval(0, 1)))).expect("infinite")
        );
        // Nat \X {} and Seq({}) are finite, Seq({1}) isn't.
        assert!(is_finite(&lazy(Lazy::Product(vec![nat(), empty()]))).expect("finite"));
        assert!(is_finite(&lazy(Lazy::Seq(empty()))).expect("finite"));
        assert!(!is_finite(&lazy(Lazy::Seq(one()))).expect("infinite"));
    }
}
