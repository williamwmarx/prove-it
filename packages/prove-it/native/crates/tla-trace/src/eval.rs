//! Expressions of the engine IR, evaluated on the evaluator's values as `evaluate.ts` evaluates
//! the AST: names resolve as the engine's compiler resolves them (bound names first where SANY
//! resolved them locally, then variables, constants, definitions and builtins), operators expand
//! at the call site with their arguments evaluated where used, and functions TLC keeps lazy, a
//! definition's or a LET's, are applied without building them.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use tla_values::random::JavaRandom;

use tla_ir::{
    Bound, Definition, DefinitionForm, Index, Ir, Name, NodeId, NodeKind, Param, PathStep, Pattern,
    Resolution, ScopeBinding, TextId,
};

use tla_values::{Id, Store};

use crate::print::{format_pretty, format_printed, format_value};
use crate::random::{random_element, random_subset};
use crate::sets::{as_tuple, cardinality, difference, intersection, is_member, is_subset, union};
use crate::value::{
    Class, EvalError, Evaluated, Function, Lazy, Text, TlcMessage, Value, compare, elements,
    equals, fail, fail_coded, fail_runtime, fail_with, find_key, from_store, set_of,
    sorted_function, written_function,
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
#[derive(Debug, Default)]
pub struct CallStack {
    pub frames: Vec<StackFrame>,
    pub is_frozen: bool,
    /// The values the replay built that TLC's `CallStackTool` gives a source, by their address.
    sourced: HashSet<usize>,
    /// The value each node of the replay last evaluated to.
    values: HashMap<NodeId, Value>,
    /// Whether the failure was in a method of a value with a source, which TLC reports as a
    /// FingerprintException rather than with the nested expressions.
    pub is_fingerprinted: bool,
    /// Why the replay can't follow TLC to the failure, where it can't: through an assignment
    /// `x' \in S` whose set TLC streams in an order of its own, or through a filter TLC keeps lazy.
    pub unfollowed: Option<&'static str>,
    /// Where the frames of the predicate of a filter TLC keeps lazy start, when it failed: TLC
    /// evaluates the predicate only as a method of the value enumerates it, as Print's does.
    pub lazy_filter: Option<usize>,
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

pub struct Evaluator<'ir> {
    pub ir: &'ir Ir,
    texts: Vec<Option<Rc<Text>>>,
    ranks: HashMap<Box<[u16]>, i32>,
    constants: Vec<Option<Value>>,
    /// Zero-arity definitions that read nothing of the state, evaluated once, as TLC does.
    cache: HashMap<(NodeId, bool), Value>,
    /// The current state's values, and the next state's: `None` until assigned.
    pub current: Vec<Option<Value>>,
    pub next: Vec<Option<Value>>,
    /// How many times the evaluator read the state, so a definition that read none is cached.
    reads: u64,
    /// TLCGet("level") of the current state.
    pub level: i32,
    /// What Print and PrintT printed, each as the texts of its values.
    pub printed: Vec<Vec<String>>,
    /// The state a walk looks for, where a value that differs from it can't lead to it: a walk
    /// then drops an assignment of another value, as nothing else follows from it.
    pub target: Option<Vec<Value>>,
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
}

/// The values a postcondition reads of the run: TLCGet("all:named"), TLCGet("stats") and TLCExt's
/// CounterExample, built as TLC builds them.
pub struct Runtime {
    pub named: Value,
    pub stats: Value,
    pub counter_example: Value,
}

const MAXIMUM_DEPTH: u32 = 10_000;

const LAZY_FILTER: &str = "a filter TLC keeps lazy";
/// `EC.TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE`.
const JAVA_METHOD_FAILED: u32 = 2154;

impl<'ir> Evaluator<'ir> {
    pub fn new(ir: &'ir Ir) -> Evaluator<'ir> {
        let ranks = ir.texts[..ir.ranked_count as usize]
            .iter()
            .enumerate()
            .map(|(rank, text)| (text.encode_utf16().collect(), rank as i32))
            .collect();
        let width = ir.variables.len();
        Evaluator {
            ir,
            texts: vec![None; ir.texts.len()],
            ranks,
            constants: vec![None; ir.values.list.len()],
            cache: HashMap::new(),
            current: vec![None; width],
            next: vec![None; width],
            reads: 0,
            level: 0,
            printed: Vec::new(),
            target: None,
            call_stack: None,
            choices: Vec::new(),
            random: None,
            runtime: None,
        }
    }

    // --- texts and IR values ---

    pub fn text(&mut self, id: TextId) -> Rc<Text> {
        if let Some(text) = &self.texts[id as usize] {
            return Rc::clone(text);
        }
        let units: Box<[u16]> = self.ir.texts[id as usize].encode_utf16().collect();
        let text = self.text_of(units);
        self.texts[id as usize] = Some(Rc::clone(&text));
        text
    }

    /// A text with TLC's rank of it, or -1 for one the IR doesn't rank.
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
                    "primed variable not assigned"
                } else {
                    "variable not assigned"
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
        match self.evaluate(node, context)? {
            Value::Bool(boolean) => Ok(boolean),
            other => fail(format!("expected a boolean, not a {}", other.kind_name())),
        }
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
                stack.sourced.insert(address);
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
    fn mark_fingerprinted(&mut self, frame: StackFrame) {
        let StackFrame::Node(node) = frame else {
            return;
        };
        let receiver = self.receiver(node).map(|receiver| self.resolved(receiver));
        let Some(stack) = &mut self.call_stack else {
            return;
        };
        let is_sourced = receiver
            .and_then(|receiver| stack.values.get(&receiver))
            .and_then(address)
            .is_some_and(|address| stack.sourced.contains(&address));
        stack.is_fingerprinted |= is_sourced;
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
        if result.is_err()
            && self
                .call_stack
                .as_ref()
                .is_some_and(|stack| !stack.is_frozen)
        {
            self.mark_fingerprinted(frame);
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
    // state of its own, a successor whether or not it assigns every variable. A failure inside it
    // is one the replay doesn't follow, since `enabled` evaluates apart from the walk.
    fn enabled(&mut self, action: NodeId, context: &Context) -> Evaluated<Value> {
        let width = self.next.len();
        let next = std::mem::replace(&mut self.next, vec![None; width]);
        let target = self.target.take();
        let mut is_enabled = false;
        let walked = self.walk(action, context, false, &mut |_| {
            is_enabled = true;
            Ok(false)
        });
        self.next = next;
        self.target = target;
        if walked.is_err()
            && let Some(stack) = &mut self.call_stack
        {
            stack.unfollowed.get_or_insert("a failure inside ENABLED");
        }
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
    fn apply_checked(&self, function: &Value, key: &Value) -> Evaluated<Value> {
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
                        format_value(record),
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
        if self.call_stack.is_none() || self.is_walked_whole(node, count) {
            for &operand in &operands[..count] {
                if self.boolean(operand, context)? != is_conjunction {
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
        self.boolean(operands[count - 1], context)
    }

    fn evaluate_node(&mut self, node: NodeId, context: &Context) -> Evaluated<Value> {
        let kind = self.kind(node);
        match kind {
            NodeKind::Number(int) => Ok(Value::Int(*int)),
            NodeKind::WideNumber(_) => fail("an integer outside 32 bits"),
            NodeKind::Decimal(_) => fail("a real number"),
            NodeKind::String(text) => Ok(Value::Str(self.text(*text))),
            NodeKind::Identifier(name) => self.identifier(node, name, context),
            NodeKind::Apply { name, args } => self.apply(name, args, context),
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
                if self.boolean(*condition, context)? {
                    self.evaluate(*consequent, context)
                } else {
                    self.evaluate(*alternative, context)
                }
            }
            NodeKind::Case { arms, other } => {
                for &(condition, body) in arms {
                    if self.boolean(condition, context)? {
                        return self.evaluate(body, context);
                    }
                }
                match other {
                    Some(other) => self.evaluate(*other, context),
                    None => fail("no CASE arm holds"),
                }
            }
            NodeKind::Let {
                instances,
                definitions,
                body,
            } => {
                let inner = self.bind_let(*instances, definitions, context)?;
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
                fail("CHOOSE found no element")
            }
            NodeKind::SetEnumeration(items) => {
                let values = items
                    .iter()
                    .map(|&item| self.evaluate(item, context))
                    .collect::<Evaluated<Vec<_>>>()?;
                set_of(values)
            }
            NodeKind::SetFilter { bound, predicate } => {
                let set = self.evaluate(bound.set, context)?;
                let mut kept = Vec::new();
                for element in elements(&set)?.iter() {
                    let inner = self.bind_pattern(&bound.pattern, element, context)?;
                    let start = self.call_stack.as_ref().map(|stack| stack.frames.len());
                    let test = self.boolean(*predicate, &inner);
                    // TLC filters a set it can't enumerate lazily, so its predicate fails only
                    // where TLC uses the result, which the replay follows only into Print.
                    if test.is_err()
                        && !matches!(set, Value::Set(_) | Value::Interval(..))
                        && let Some(stack) = &mut self.call_stack
                        && stack.unfollowed.is_none()
                    {
                        stack.unfollowed = Some(LAZY_FILTER);
                        stack.lazy_filter = start;
                    }
                    if test? {
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
                set_of(values)
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
                let inner = own_context(bound, frame, *is_self)
                    .primed(context.is_primed || bound.is_primed);
                self.evaluate(*node, &inner)
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
        let ir = self.ir;
        self.random = Some(JavaRandom::seeded(ir.model.random_seed));
        let substitutes = ir.model.startup.substitutes.iter().map(|&(_, index)| index);
        for index in substitutes.chain(ir.model.startup.definitions.iter().copied()) {
            let node = ir.definitions[index as usize];
            let value = self.evaluate(self.definition(node).body, &Context::default())?;
            if ir.model.startup.definitions.contains(&index) {
                self.cache.insert((node, false), value.clone());
                self.cache.insert((node, true), value);
            }
        }
        self.random = None;
        Ok(())
    }

    /// Takes the values the search computed at startup for the model's startup definitions,
    /// ids of `store` in their order, as the values of those definitions.
    pub fn set_startup(&mut self, store: &Store, values: &[Id]) {
        for (&index, &id) in self.ir.model.startup.definitions.iter().zip(values) {
            let node = self.ir.definitions[index as usize];
            let value = from_store(store, id);
            self.cache.insert((node, false), value.clone());
            self.cache.insert((node, true), value);
        }
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
            self.cache.insert(key, value.clone());
        }
        Ok(value)
    }

    pub(crate) fn bind_let(
        &mut self,
        instances: u32,
        definitions: &[NodeId],
        context: &Context,
    ) -> Evaluated<Context> {
        if instances > 0 {
            return fail("INSTANCE in LET");
        }
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
                let is_startup = self.ir.model.startup.definitions.contains(&index);
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
        fail(format!("the operator {}", self.name(name.text)))
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
        }
        let depth = DEPTH.get();
        if depth > MAXIMUM_DEPTH {
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

    // --- functions ---

    // A function a definition or a LET defines. TLC builds it in the frame of the definition,
    // which the replay doesn't record, so a failure building it isn't one the replay follows.
    fn defined_function(
        &mut self,
        bounds: &[Bound],
        body: NodeId,
        context: &Context,
    ) -> Evaluated<Value> {
        let result = self.construct_function(bounds, body, context);
        if result.is_err()
            && let Some(stack) = &mut self.call_stack
        {
            stack
                .unfollowed
                .get_or_insert("building a function a definition defines");
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
            return sorted_function(keys, values, Class::Lambda);
        }
        // TLC evaluates every domain before it enumerates any (`Tool.evalAppl`'s
        // `OPCODE_fc`), so a later domain fails even when an earlier one is empty.
        for bound in bounds {
            self.evaluate(bound.set, context)?;
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
        sorted_function(keys, values, Class::Lambda)
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
                stack
                    .unfollowed
                    .get_or_insert("the domain of a function TLC keeps lazy");
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
        let function = self.evaluate(function, context)?;
        if let Some(kind) = scalar_kind(&function) {
            return fail_runtime(
                "applied a non-function",
                format!(
                    "A non-function ({kind}) was applied as a function.\n{}",
                    self.describe_range(node)
                ),
            );
        }
        let argument = argument(self)?;
        self.apply_checked(&function, &argument)
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
        let result = combined.has(element);
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

    // A failure in the predicate of a filter TLC keeps lazy, which TLC meets as Print's Java method
    // enumerates the filter it prints: the frames from the predicate's on, after Print's own, in
    // the error of the method.
    fn printed_filter_failure(
        &mut self,
        name: &str,
        frame: Option<usize>,
        error: EvalError,
    ) -> EvalError {
        let Some(stack) = &mut self.call_stack else {
            return error;
        };
        let (Some(frame), Some(start), Some(message)) = (frame, stack.lazy_filter, &error.message)
        else {
            return error;
        };
        if stack.unfollowed != Some(LAZY_FILTER) || start < frame {
            return error;
        }
        stack.frames.drain(frame..start);
        stack.unfollowed = None;
        stack.lazy_filter = None;
        let parameters = if name == "Print" {
            "tlc2.value.impl.Value,tlc2.value.impl.Value"
        } else {
            "tlc2.value.impl.Value"
        };
        EvalError {
            message: Some(TlcMessage {
                text: format!(
                    "Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.impl.Value tlc2.module.TLC.{name}({parameters}),\nbut it produced the following error:\n{}",
                    message.text
                ),
                code: Some(JAVA_METHOD_FAILED),
                is_eval_exception: false,
            }),
            ..error
        }
    }

    fn builtin(
        &mut self,
        index: Index,
        operands: &[Operand],
        context: &Context,
    ) -> Evaluated<Value> {
        let name = self.name(self.ir.builtins[index as usize].name);
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
            "Int" => Value::Lazy(Rc::new(Lazy::Int)),
            "Real" => Value::Lazy(Rc::new(Lazy::Real)),
            "STRING" => Value::Lazy(Rc::new(Lazy::Strings)),
            "=" | "#" => {
                arity(2)?;
                let left = self.operand(&operands[0])?;
                let right = self.operand(&operands[1])?;
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
                Value::Bool(is_subset(&left, &right)?)
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
                if !base.is_set() {
                    return fail("SUBSET of a non-set");
                }
                Value::Lazy(Rc::new(Lazy::Subset(base)))
            }
            "UNION" => {
                arity(1)?;
                let sets = self.operand(&operands[0])?;
                let mut all = Vec::new();
                for set in elements(&sets)?.iter() {
                    all.extend(elements(set)?.iter().cloned());
                }
                set_of(all)?
            }
            "DOMAIN" => {
                arity(1)?;
                match self.operand(&operands[0])? {
                    Value::Function(function) => match function.interval {
                        Some((low, high)) => Value::Interval(low, high),
                        None => Value::Set(Rc::new(function.domain.clone())),
                    },
                    _ => return fail("DOMAIN of a non-function"),
                }
            }
            ".." => {
                arity(2)?;
                let low = self.operand_int(&operands[0])?;
                let high = self.operand_int(&operands[1])?;
                Value::Interval(low as i32, high as i32)
            }
            "+" | "-" | "*" | "\\div" | "%" | "^" | "<" | ">" | "<=" | ">=" => {
                arity(2)?;
                let left = self.operand_int(&operands[0])?;
                let right = self.operand_int(&operands[1])?;
                match name {
                    "+" => int(left + right)?,
                    "-" => int(left - right)?,
                    "*" => int(left * right)?,
                    "\\div" => {
                        if right == 0 {
                            return fail("division by zero");
                        }
                        int(left.div_euclid(right)
                            - i64::from(right < 0 && left.rem_euclid(right) != 0))?
                    }
                    "%" => {
                        if right <= 0 {
                            return fail("modulus by a non-positive number");
                        }
                        int(left.rem_euclid(right))?
                    }
                    "^" => {
                        if right < 0 {
                            return fail("a negative exponent");
                        }
                        match u32::try_from(right)
                            .ok()
                            .and_then(|exponent| left.checked_pow(exponent))
                        {
                            Some(power) => int(power)?,
                            None => return fail("integer overflow"),
                        }
                    }
                    "<" => Value::Bool(left < right),
                    ">" => Value::Bool(left > right),
                    "<=" => Value::Bool(left <= right),
                    _ => Value::Bool(left >= right),
                }
            }
            "-." => {
                arity(1)?;
                int(-self.operand_int(&operands[0])?)?
            }
            "Cardinality" => {
                arity(1)?;
                let set = self.operand(&operands[0])?;
                int(cardinality(&set)? as i64)?
            }
            "IsFiniteSet" => {
                arity(1)?;
                let set = self.operand(&operands[0])?;
                if matches!(
                    set,
                    Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::Model(_)
                ) {
                    return fail("IsFiniteSet of a non-set");
                }
                Value::Bool(is_finite(&set))
            }
            "Seq" => {
                arity(1)?;
                Value::Lazy(Rc::new(Lazy::Seq(self.operand(&operands[0])?)))
            }
            "Len" => {
                arity(1)?;
                let sequence = self.operand(&operands[0])?;
                int(sequence_of(&sequence)?.len() as i64)?
            }
            "Head" => {
                arity(1)?;
                let sequence = self.operand(&operands[0])?;
                match sequence_of(&sequence)?.first() {
                    Some(head) => head.clone(),
                    None => return fail("Head of the empty sequence"),
                }
            }
            "Tail" => {
                arity(1)?;
                let sequence = self.operand(&operands[0])?;
                let elements = sequence_of(&sequence)?;
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
                    return Ok(Value::Str(self.text_of(units)));
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
                    Value::Str(text) => Value::Str(self.text_of(text.units[range].into())),
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
            "Assert" => {
                arity(2)?;
                if self.operand_boolean(&operands[0])? {
                    Value::Bool(true)
                } else {
                    let message = self.operand(&operands[1])?;
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
                // The frame of the application, which Print's Java method fails in.
                let frame = self
                    .call_stack
                    .as_ref()
                    .filter(|stack| !stack.is_frozen)
                    .map(|stack| stack.frames.len());
                let mut values = Vec::with_capacity(operands.len());
                for (position, operand) in operands.iter().enumerate() {
                    match self.operand(operand) {
                        Ok(value) => values.push(value),
                        Err(error) => {
                            // TLC evaluates the rest of the arguments before Print enumerates
                            // the filter, outside the frames of the failure.
                            let stack = self.call_stack.take();
                            let is_rest_evaluated = operands[position + 1..]
                                .iter()
                                .all(|operand| self.operand(operand).is_ok());
                            self.call_stack = stack;
                            return Err(if is_rest_evaluated {
                                self.printed_filter_failure(name, frame, error)
                            } else {
                                error
                            });
                        }
                    }
                }
                let expected = if name == "Print" { 2 } else { 1 };
                if values.len() != expected {
                    return fail("an operator applied to the wrong number of arguments");
                }
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
                    _ => return fail(name.to_string()),
                }
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
            "TLCEval" => {
                arity(1)?;
                self.operand(&operands[0])?
            }
            "ToString" => {
                arity(1)?;
                let value = self.operand(&operands[0])?;
                let units: Box<[u16]> = format_value(&value).encode_utf16().collect();
                Value::Str(self.text_of(units))
            }
            "TLCGet" => {
                arity(1)?;
                match self.operand(&operands[0])? {
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
    fn has(&self, element: &Value) -> Evaluated<bool> {
        match self {
            Combined::Set(set) => is_member(element, set),
            Combined::Operation(operation, left, right) => Ok(match operation {
                SetOperation::Union => left.has(element)? || right.has(element)?,
                SetOperation::Intersection => left.has(element)? && right.has(element)?,
                SetOperation::Difference => left.has(element)? && !right.has(element)?,
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
fn is_finite(value: &Value) -> bool {
    match value {
        Value::Lazy(lazy) => match &**lazy {
            Lazy::Nat | Lazy::Int | Lazy::Real | Lazy::Strings | Lazy::Seq(_) => false,
            Lazy::Subset(base) => is_finite(base),
            Lazy::FunctionSet(domain, range) => is_finite(domain) && is_finite(range),
            Lazy::RecordSet(fields, _) => fields.iter().all(|(_, set)| is_finite(set)),
            Lazy::Product(factors) => factors.iter().all(is_finite),
        },
        _ => true,
    }
}

// TLC's `getKindString` of a value that isn't a set or a function, whose class the evaluator
// knows: a set it may hold as another class than TLC does.
fn scalar_kind(value: &Value) -> Option<&'static str> {
    match value {
        Value::Bool(_) => Some("a Boolean value"),
        Value::Int(_) => Some("an integer"),
        Value::Str(_) => Some("a string"),
        Value::Model(_) => Some("a model value"),
        _ => None,
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
        NodeKind::Choose { .. } => "an unbounded CHOOSE",
        NodeKind::FunctionConstruction { .. } => "a recursive function",
        NodeKind::Always(_) | NodeKind::Eventually(_) => "a temporal formula",
        NodeKind::WeakFairness { .. } | NodeKind::StrongFairness { .. } => "a fairness",
        NodeKind::Subexpression(_) => "a subexpression",
        NodeKind::Bracket(_) => "a bracket",
        _ => "node",
    }
}
