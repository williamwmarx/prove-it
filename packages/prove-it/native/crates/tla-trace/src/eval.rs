//! Expressions of the engine IR, evaluated on the evaluator's values as `evaluate.ts` evaluates
//! the AST: names resolve as the engine's compiler resolves them (bound names first where SANY
//! resolved them locally, then variables, constants, definitions and builtins), operators expand
//! at the call site with their arguments evaluated where used, and functions TLC keeps lazy, a
//! definition's or a LET's, are applied without building them.

mod charsets;

/// Whether `Charset.forName` of the pinned JVM finds a charset by this name, in any case of its
/// ASCII letters.
pub fn is_jvm_charset(name: &str) -> bool {
    charsets::JVM_CHARSETS
        .binary_search(&name.to_ascii_lowercase().as_str())
        .is_ok()
}
mod json;

use std::cell::{Cell, RefCell};
use std::collections::{HashMap, HashSet};
use std::rc::{Rc, Weak};

use tla_values::fingerprint::{Fingerprints, Polynomial};
use tla_values::random::JavaRandom;
use tla_values::{JAVA_PROPERTY_PREFIX, NAMED_REGISTER_PREFIX, is_settable_property};

use tla_ir::{
    Bound, Builtin, Definition, DefinitionForm, EvaluatedDefinition, Index, Ir, Name, NodeId,
    NodeKind, Param, PathStep, Pattern, Resolution, ScopeBinding, TextId,
};

use tla_values::store::NO_VALUE;
use tla_values::{Id, Store, is_unknown_tlc_get_key};

use crate::Unsupported;
use crate::failure::nested;
use crate::pretty::pretty_print;
use crate::print::{
    format_pretty, format_printed, format_units, format_value, holds_install, holds_unknown_key,
};
use crate::random::{random_element, random_subset, random_subset_set};
use crate::sets::{
    UNION_FIRST_NON_SET, UNION_NON_SET, as_tuple, cardinality, difference, failing_operation,
    intersection, is_failing_union, is_member, is_reducible, member_filtered, union,
};
use crate::value::{
    Class, EvalError, Evaluated, Function, Lazy, RECORD_VALUE_FIELDS, RuntimeException, Search,
    SetClass, Text, TlcMessage, Value, compare, elements, equals, fail, fail_coded, fail_runtime,
    fail_with, failing_comparisons, find_key, from_store, holds_record_out_of_order,
    index_out_of_bounds, is_enumerable, java_set_class, lambda_as_function, lambda_as_tuple,
    normalize, note_sorted, print_failure, push_set_element, set_of, settle_deep, sorted_function,
    suppress_new_function_diagnostic, take_is_record_built, unnormalized, unsorted_failure,
    written_function,
};

/// The bindings an expression sees, innermost first.
#[derive(Clone, Default)]
pub struct Env(Option<Rc<Frame>>);

pub struct Frame {
    name: TextId,
    binding: Binding,
    parent: Env,
    /// Whether a thunk's value has been evaluated once.
    is_evaluated: Cell<bool>,
    /// Whether a function a LET defines has been built here once, whatever the control.
    is_built: Cell<bool>,
    /// Whether the value here holds a lazy function whose body printed as the evaluator built
    /// it, which TLC may force, or apply, again where the evaluator reads it again.
    holds_lazy_print: Cell<bool>,
    /// Whether every function a LET defines here, built, was one TLC keeps lazy whose body
    /// printed, and TLC hasn't forced the one it holds (`toFcnRcd`): it builds it again at each
    /// use, as the evaluator does, but for the domain.
    is_lazy_unforced: Cell<bool>,
    /// Whether a thunk's value is one function TLC keeps lazy whose body printed as the
    /// evaluator built it, and TLC hasn't forced the one its LazyValue holds (`toFcnRcd`): a print
    /// forces a copy (`deepCopy`), which leaves it unforced, so TLC builds it again at each use, as
    /// the evaluator does where it builds the thunk's value again (`binding`).
    is_thunk_unforced: Cell<bool>,
    cached: RefCell<Option<BoundValue>>,
    /// Whether the binding is a LET definition a walk of the initial predicate or the next-state
    /// relation bound, which TLC's `getInitStates`, `getNextStates` and `getActions` don't add to
    /// their `Context`, as `evalImplLetInKind` does.
    is_walked: Cell<bool>,
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

#[derive(Clone)]
struct BoundValue {
    evaluator: Rc<()>,
    value: Value,
    current: Vec<Option<Value>>,
    next: Vec<Option<Value>>,
    is_primed: bool,
    is_enabling: bool,
    reads: u64,
    captures: u64,
}

fn state_extends(current: &[Option<Value>], cached: &[Option<Value>]) -> bool {
    cached.iter().enumerate().all(|(index, value)| match value {
        None => true,
        Some(value) => current
            .get(index)
            .and_then(Option::as_ref)
            .is_some_and(|current| same_cached_value(current, value)),
    })
}

fn configuration_literal(value: &Value) -> Option<Value> {
    match value {
        Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::Model(_) => Some(value.clone()),
        Value::Set(set) => Some(Value::set(
            set.iter()
                .map(configuration_literal)
                .collect::<Option<Vec<_>>>()?,
        )),
        _ => None,
    }
}

fn same_cached_value(left: &Value, right: &Value) -> bool {
    let shared = match (left, right) {
        (Value::Set(left) | Value::Unsorted(left), Value::Set(right) | Value::Unsorted(right)) => {
            Rc::ptr_eq(left, right)
        }
        (Value::Function(left), Value::Function(right)) => Rc::ptr_eq(left, right),
        (Value::Lambda(left), Value::Lambda(right)) => Rc::ptr_eq(left, right),
        (Value::Lazy(left), Value::Lazy(right)) => Rc::ptr_eq(left, right),
        (Value::Str(left), Value::Str(right)) | (Value::Model(left), Value::Model(right)) => {
            Rc::ptr_eq(left, right)
        }
        _ => false,
    };
    shared || equals(left, right).unwrap_or(false)
}

pub struct Operator {
    params: Vec<Param>,
    body: Body,
    context: Context,
    /// A RECURSIVE operator of a LET, or a closure of an instance's scope over that scope: its
    /// body sees the scope that binds it.
    is_self: bool,
    /// For a RECURSIVE operator of a LET, the scope that binds the whole LET, where it sees the
    /// operators its declaration names that the LET defines after it.
    group_env: RefCell<Weak<Frame>>,
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
    /// Whether TLC built the filter with a `Tool` that keeps no call stack, as it computed a
    /// definition as it started: the filter evaluates its predicate with that `Tool` until
    /// `CallStackTool.evalAppl` copies it (`retraced`).
    is_untraced: bool,
    /// The elements that pass, where the evaluator filtered a finite set without effects, as
    /// TLC's enumeration of the filter finds them.
    filtered: Option<Rc<Vec<Value>>>,
    converted: RefCell<Option<Rc<Vec<Value>>>>,
}

enum SpeculativeChange {
    Conversion(Weak<Predicate>, Option<Rc<Vec<Value>>>),
    Thunk(Weak<Frame>, Option<BoundValue>, bool),
}

thread_local! {
    /// How many filters were converted (`convertAndCache`), which tells whether a replay's
    /// copies of them may matter (`Predicate::copied`).
    static FILTER_CONVERSIONS: Cell<u64> = const { Cell::new(0) };
    static FILTER_CONVERSION_JOURNALS: RefCell<Vec<Vec<SpeculativeChange>>> = const { RefCell::new(Vec::new()) };
}

/// How many filters were converted so far.
pub(crate) fn filter_conversions() -> u64 {
    FILTER_CONVERSIONS.with(Cell::get)
}

pub(crate) struct FilterConversionRollback {
    active: bool,
}

pub(crate) fn rollback_filter_conversions() -> FilterConversionRollback {
    FILTER_CONVERSION_JOURNALS.with(|journals| journals.borrow_mut().push(Vec::new()));
    FilterConversionRollback { active: true }
}

impl FilterConversionRollback {
    fn commit(mut self) {
        FILTER_CONVERSION_JOURNALS.with(|journals| {
            let mut journals = journals.borrow_mut();
            let changes = journals.pop().expect("conversion journal");
            if let Some(parent) = journals.last_mut() {
                parent.extend(changes);
            }
        });
        self.active = false;
    }

    fn has_changes(&self) -> bool {
        FILTER_CONVERSION_JOURNALS.with(|journals| {
            journals.borrow().last().is_some_and(|changes| {
                changes
                    .iter()
                    .any(|change| matches!(change, SpeculativeChange::Conversion(..)))
            })
        })
    }
}

impl Drop for FilterConversionRollback {
    fn drop(&mut self) {
        if !self.active {
            return;
        }
        FILTER_CONVERSION_JOURNALS.with(|journals| {
            let changes = journals.borrow_mut().pop().expect("conversion journal");
            for change in changes.into_iter().rev() {
                match change {
                    SpeculativeChange::Conversion(predicate, old) => {
                        if let Some(predicate) = predicate.upgrade() {
                            *predicate.converted.borrow_mut() = old;
                        }
                    }
                    SpeculativeChange::Thunk(frame, old, evaluated) => {
                        if let Some(frame) = frame.upgrade() {
                            *frame.cached.borrow_mut() = old;
                            frame.is_evaluated.set(evaluated);
                        }
                    }
                }
            }
        });
    }
}

impl Predicate {
    // `CallStackTool.evalAppl`'s copy of a filter (`new SetPredValue(value, this)`), which
    // evaluates its predicate with the `CallStackTool` and holds no conversion yet.
    fn retraced(&self) -> Predicate {
        Predicate {
            pattern: self.pattern.clone(),
            body: self.body,
            context: self.context.clone(),
            current: self.current.clone(),
            next: self.next.clone(),
            level: self.level,
            text: self.text.clone(),
            is_untraced: false,
            filtered: self.filtered.clone(),
            converted: RefCell::new(None),
        }
    }

    pub fn text(&self) -> &(String, String) {
        &self.text
    }

    pub fn filtered(&self) -> Option<&Rc<Vec<Value>>> {
        self.filtered.as_ref()
    }

    pub(crate) fn converted(&self) -> Option<Rc<Vec<Value>>> {
        self.converted.borrow().clone()
    }

    // `new SetPredValue(SetPredValue, ITool)`, which `CallStackTool.eval` returns of each
    // `SetPredValue` a node evaluates to: the same set, whose conversion (`convertAndCache`)
    // then stays with the copy, so that a filter a definition holds converts anew wherever the
    // replay reads it.
    fn copied(&self) -> Predicate {
        Predicate {
            pattern: self.pattern.clone(),
            body: self.body,
            context: self.context.clone(),
            current: self.current.clone(),
            next: self.next.clone(),
            level: self.level,
            text: self.text.clone(),
            // The copy evaluates its predicate with the `CallStackTool` that made it.
            is_untraced: false,
            filtered: self.filtered.clone(),
            converted: RefCell::new(self.converted()),
        }
    }

    pub(crate) fn cache_conversion(self: &Rc<Self>, elements: Rc<Vec<Value>>) {
        FILTER_CONVERSIONS.with(|count| count.set(count.get() + 1));
        FILTER_CONVERSION_JOURNALS.with(|journals| {
            if let Some(journal) = journals.borrow_mut().last_mut() {
                journal.push(SpeculativeChange::Conversion(
                    Rc::downgrade(self),
                    self.converted(),
                ));
            }
        });
        *self.converted.borrow_mut() = Some(elements);
    }
}

impl std::fmt::Debug for Predicate {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "Predicate({})", self.body)
    }
}

/// A group of a function's parameters as `FcnParams` holds it: the names a domain bounds,
/// whether they form a tuple, and the domain.
type ParamGroup = (Vec<TextId>, bool, Value);

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
    /// Where the function has several parameters or a tuple pattern: its `FcnParams`, each
    /// group of names a domain bounds, whether it is a tuple, and the domain. `domain` is then
    /// `getDomain`'s, and `text` the whole of `toString`'s but its body.
    params: Option<Rc<Vec<ParamGroup>>>,
    /// Whether the function is a constructor written in place whose build failed in its body
    /// (`construct_in_place`), or an EXCEPT of one: TLC applies it in the frames of the
    /// application, which the replay records.
    is_in_place: bool,
}

impl Lambda {
    /// The domain of each group of its parameters, as `FcnParams` sizes them.
    pub(crate) fn domains(&self) -> Vec<&Value> {
        match &self.params {
            None => vec![&self.domain],
            Some(groups) => groups.iter().map(|(_, _, domain)| domain).collect(),
        }
    }

    /// Whether TLC prints the function with its domain between its texts.
    pub fn is_domain_printed(&self) -> bool {
        self.params.is_none()
    }

    pub fn text(&self) -> &(String, String) {
        &self.text
    }

    pub fn domain(&self) -> &Value {
        &self.domain
    }

    /// Whether `FcnParams.size` fails, without effects, as `toFcnRcd` sizes the domains: each is
    /// a set enumeration, an interval, or Nat, Int, Real or STRING, which TLC overrides and can't
    /// count, and one is such a set.
    pub fn is_unbuildable(&self) -> bool {
        let is_overridden = |domain: &Value| {
            matches!(domain, Value::Lazy(lazy)
                if matches!(***lazy, Lazy::Nat | Lazy::Int | Lazy::Real | Lazy::Strings))
        };
        match &self.params {
            None => is_overridden(&self.domain),
            Some(groups) => {
                groups.iter().any(|(_, _, domain)| is_overridden(domain))
                    && groups.iter().all(|(_, _, domain)| {
                        is_overridden(domain)
                            || matches!(domain, Value::Set(_) | Value::Interval(..))
                    })
            }
        }
    }

    /// How `FcnLambdaValue.toFcnRcd` fails before it evaluates the body. `FcnParams.size` asks
    /// each domain's `size` in turn, once for a tuple pattern and once for each name otherwise,
    /// which fails on a value that isn't a set and on a set TLC can't count. `FcnParams.elements`
    /// then rejects a domain that isn't `Enumerable` and enumerates the others; of several
    /// parameters, its `Enumerator` does so in order and stops at an empty domain. A failure
    /// the evaluator words there is TLC's. Otherwise the evaluator declines: an overflow of the
    /// product, or a build that goes on to the body, which it doesn't follow for a function it
    /// holds lazy.
    pub(crate) fn build_failure(&self) -> EvalError {
        let unfollowed =
            || fail::<()>("built a function over an infinite set").expect_err("a failure");
        let single = [(Vec::new(), false, self.domain.clone())];
        let groups: &[ParamGroup] = match &self.params {
            Some(groups) => groups,
            None => &single,
        };
        let mut size: i64 = 1;
        for (names, is_tuple, domain) in groups {
            let part = match printed_size(domain) {
                Ok(part) => part,
                Err(error) => return error,
            };
            let times = if *is_tuple { 1 } else { names.len().max(1) };
            for _ in 0..times {
                size = size.saturating_mul(part);
                if size > i64::from(i32::MAX) {
                    return unfollowed();
                }
            }
        }
        // `FcnParams.length`: a tuple pattern is one argument, each name another.
        let arguments: usize = groups
            .iter()
            .map(|(names, is_tuple, _)| if *is_tuple { 1 } else { names.len().max(1) })
            .sum();
        let text = if arguments == 1 {
            "The domains of formal parameters must be enumerable."
        } else {
            "The domains of the parameters must be enumerable."
        };
        for (_, _, domain) in groups {
            if !is_enumerable(domain) {
                return fail_runtime::<()>(
                    "built a function over a non-enumerable value",
                    text.into(),
                )
                .expect_err("a failure");
            }
            match elements(domain) {
                Err(error) => return error,
                Ok(elements) if elements.is_empty() => return unfollowed(),
                Ok(_) => {}
            }
        }
        unfollowed()
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
    /// What TLC's `Context` holds of the caller's bindings where a definition's body is evaluated:
    /// TLC evaluates a body in the context of the expression that names it (`getOpContext`
    /// conses the parameters onto it), where the evaluator sees no bindings of the caller.
    caller: Held,
}

/// Whether TLC's `Context` holds a binding (`isDeepEmpty`), as far as the evaluator knows it:
/// none, perhaps some, or some.
#[derive(Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Held {
    #[default]
    Empty,
    Unknown,
    Bound,
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
            is_evaluated: Cell::new(false),
            is_built: Cell::new(false),
            holds_lazy_print: Cell::new(false),
            is_lazy_unforced: Cell::new(false),
            is_thunk_unforced: Cell::new(false),
            cached: RefCell::new(None),
            is_walked: Cell::new(false),
        }))))
    }

    /// What TLC's `Context` holds where this context is: the caller's bindings, `@` of an EXCEPT
    /// (`EXCEPT_AT`), each bound name, operator argument, zero-arity LET definition
    /// (`evalImplLetInKind`'s `LazyValue`) and function definition. A LET operator with
    /// parameters, which TLC doesn't add, and an operator argument, which it does, are both an
    /// `Operator`, and a LET definition a walk bound TLC doesn't add, so neither says.
    pub(crate) fn held(&self) -> Held {
        if self.at.is_some() || self.caller == Held::Bound {
            return Held::Bound;
        }
        let mut held = self.caller;
        let mut current = self.env.0.as_ref();
        while let Some(frame) = current {
            if frame.is_walked.get() || matches!(frame.binding, Binding::Operator(_)) {
                held = Held::Unknown;
            } else {
                return Held::Bound;
            }
            current = frame.parent.0.as_ref();
        }
        held
    }

    /// Marks the bindings this context holds over `outer`'s as LET definitions a walk bound.
    pub(crate) fn mark_walked(&self, outer: &Context) {
        let stop = outer.env.0.as_ref().map(Rc::as_ptr);
        let mut current = self.env.0.as_ref();
        while let Some(frame) = current
            && Some(Rc::as_ptr(frame)) != stop
        {
            frame.is_walked.set(true);
            current = frame.parent.0.as_ref();
        }
    }

    pub fn bind_value(&self, name: TextId, value: Value) -> Context {
        self.bind(name, Binding::Value(value))
    }

    // A definition's body is evaluated without the caller's bindings, which TLC's `Context`
    // holds.
    fn global(&self) -> Context {
        Context {
            env: Env::default(),
            is_primed: self.is_primed,
            at: None,
            caller: self.held(),
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
            Body::Node(node) => Some((node, operator_context(operator, &frame))),
            Body::Builtin(_) => None,
        },
        Binding::Function {
            definition,
            context: inner,
            is_self,
        } => Some((*definition, own_context(inner, &frame, *is_self))),
    }
}

// The context an operator binding's body sees: a RECURSIVE one's of a LET, the LET's whole
// scope, or a self-closing one's, the scope that binds it.
fn operator_context(operator: &Operator, frame: &Rc<Frame>) -> Context {
    if operator.is_self
        && let Some(group) = operator.group_env.borrow().upgrade()
    {
        return operator.context.with_env(Env(Some(group)));
    }
    own_context(&operator.context, frame, operator.is_self)
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
/// The nodes only the copies an INSTANCE with substitutions makes hold, the copies' indices, and
/// whether a copy is given as an operator's argument (`check_substituted_frames`).
struct CopyFrames {
    nodes: HashSet<NodeId>,
    copies: HashSet<Index>,
    is_argument: bool,
    /// The names of the copies an INSTANCE in a LET with substitutions makes of such a copy.
    nested_local: HashSet<TextId>,
}

/// TLC's `CallStack`: the nodes a replay is in, which stop being popped once it fails.
#[derive(Clone, Debug, Default)]
pub struct CallStack {
    pub frames: Vec<StackFrame>,
    pub is_frozen: bool,
    /// Whether the failure the replay follows is one TLC met in `Tool` rather than in
    /// `CallStackTool`, as an assumption's, which gives no value a source.
    pub is_unsourced: bool,
    /// The values the replay built that TLC's `CallStackTool` gives a source, by their address,
    /// each with the node that built it. Each is kept, so that no other value takes its address
    /// while the replay runs.
    sourced: HashMap<usize, (NodeId, Value)>,
    /// The addresses of values another node than the one that built them gave a source again,
    /// as TLC's `setSource` does of the very value an operator returns (`SetEnumValue.cup` and
    /// `IntervalValue.cup` of an empty set, `FcnLambdaValue.getDomain`): TLC's source of such a
    /// value is the last node's, as `source` gives it, but where the replay's values are shared
    /// otherwise than TLC's objects the last may differ, so a few failures through one decline.
    resourced: HashSet<usize>,
    /// The value each node of the replay last evaluated to.
    values: HashMap<NodeId, Value>,
    /// Whether the failure was in a method of a value with a source, which TLC reports as a
    /// FingerprintException rather than with the nested expressions.
    pub is_fingerprinted: bool,
    /// Whether the fingerprinted failure is of a membership followed to the set whose own test
    /// fails, through no set TLC searches otherwise than the evaluator does.
    pub is_member_followed: bool,
    /// Whether the fingerprinted failure is a subscript's comparison (`subscript_equals`), which
    /// TLC's rerun of a liveness atom throws past its worker.
    pub is_subscript_fingerprinted: bool,
    /// The sources of the values whose methods the failure passed through, outermost first, where
    /// the failure is fingerprinted: the last frames of the call stack TLC's replay prints with
    /// the FingerprintException.
    pub fingerprinted_sources: Vec<NodeId>,
    /// Whether the failure may be in a method of an interval with a source: TLC gives one the
    /// interval DOMAIN builds, where the replay, which holds an interval without an address,
    /// gives none.
    pub is_interval_unplaced: bool,
    /// Whether the fingerprinted failure froze the call stack before a function TLC was building
    /// with a source threw it on as a FingerprintException, which then adds no frames to the
    /// stack TLC prints (`CallStack.freeze` of a frozen stack).
    pub is_frozen_before_fingerprint: bool,
    /// Why the replay can't follow TLC to the failure, where it can't: through an assignment
    /// `x' \in S` whose set TLC streams in an order of its own.
    pub unfollowed: Option<&'static str>,
    /// Whether a `\cup` of an empty set enumeration or interval returned its other operand, a
    /// value that isn't a set, which `CallStackTool.setSource` gives the union's source over any
    /// it had: a scalar TLC shares (`IntValue.gen`, `BoolValue.ValTrue`) then has one wherever it
    /// is, so a failure in a method of a value may be a FingerprintException the replay doesn't
    /// follow.
    sourced_non_set: bool,
    /// Whether the fingerprinted failure is a membership in a union of a set enumeration TLC
    /// holds unnormalized, which fails sorting it (`UnionValue.member`), where TLC's
    /// FingerprintException holds the sources of the set and of the element it sorts in, which
    /// the replay doesn't follow.
    pub is_unsorted_union_member: bool,
    /// Whether the fingerprinted failure is a membership in a union, an intersection, a
    /// difference or a UNION one of whose sets is a function set, a record set or a product over
    /// a set enumeration TLC holds unnormalized: in a step TLC's FingerprintException holds that
    /// set enumeration's source too, as the enumeration of the holder reads it, which the replay
    /// doesn't follow.
    pub is_unsorted_held_member: bool,
    /// Whether the failure is in a method of a value after such a union, which the replay can't
    /// word.
    is_source_unfollowed: bool,
    /// Whether a TLCEval caught a FingerprintException and failed again (`catch_fingerprint`), or
    /// failed converting a value its argument evaluated to, which has a source in TLC.
    caught_fingerprint: bool,
    /// Whether the call stack froze within a definition an INSTANCE with substitutions copies
    /// (`check_substituted_frames`), whose frames the replay can't print as TLC does.
    pub is_substituted: bool,
    /// The frames of the `SubstInNode`s of the copies the call stack froze within, each after
    /// the index of the frame that names its copy (`substitution_frames`).
    pub substitution_frames: Vec<(usize, tla_ir::SourceRange)>,
    /// Where a state the replay found fails to fingerprint: the nodes that built the values the
    /// fingerprint fails in, outermost first, as TLC's FingerprintException traces them, and the
    /// state's values as TLC prints them, in the IR's order of the variables.
    pub fingerprint: Option<(Vec<NodeId>, Vec<String>)>,
    /// Whether the replay built a set enumeration TLC fails to normalize, which TLC keeps as
    /// written until it fingerprints or prints it.
    pub is_unsorted: bool,
    /// How many set enumerations TLC fails to normalize the replay built.
    unsorted_built: usize,
    /// Whether value-evaluation failures had only scalar state slots and fresh call-stack frames.
    /// None leaves state-search and fingerprint callback failures unproved.
    pub(crate) scalar_state_at_value_failure: Option<bool>,
    /// TLC's error as it prints an initial state it failed to fingerprint, where printing it fails
    /// too: TLC reports it as an exception it didn't expect.
    pub unprintable: Option<TlcMessage>,
    /// An initial state the initial predicate leaves without a value for some variable, its
    /// values as TLC prints them, `null` for those it lacks, in the IR's order of the variables.
    pub incomplete: Option<Vec<String>>,
}

impl CallStack {
    /// The node that built a value with a source.
    pub(crate) fn source(&self, value: &Value) -> Option<NodeId> {
        self.sourced.get(&address(value)?).map(|&(node, _)| node)
    }

    /// Whether a node other than the one that built a value gave it a source again.
    pub(crate) fn is_resourced(&self, value: &Value) -> bool {
        address(value).is_some_and(|address| self.resourced.contains(&address))
    }

    /// Whether a node gave a source to Any, Nat, Int, Real or STRING, which TLC shares.
    fn sources_shared(&self) -> bool {
        self.sourced
            .keys()
            .any(|&address| address < SHARED_ADDRESSES)
    }

    // Gives a value the source of the node that returned it, over any it had.
    fn replace_source(&mut self, value: &Value, node: NodeId) {
        if let Some(address) = address(value) {
            self.resourced.remove(&address);
            self.sourced.insert(address, (node, value.clone()));
        }
    }

    // Gives a value the replay built the node that returned it as its source. TLC's
    // `CallStackTool.setSource` sets the source of the very object each node returns, so the
    // last node that returned a value names it: `{} \cup S` returns S itself
    // (`SetEnumValue.cup` of an empty receiver), which then fails at the union's place. A value
    // given a second source is resourced, but for Any, Nat, Int, Real and STRING, which TLC
    // shares and whose source is simply the last node's.
    fn give_source(&mut self, value: &Value, node: NodeId) {
        if let Some(address) = address(value) {
            if address >= SHARED_ADDRESSES
                && let Some(&(built, _)) = self.sourced.get(&address)
                && built != node
                && !matches!(value, Value::Lazy(lazy) if matches!(***lazy, Lazy::Any))
            {
                self.resourced.insert(address);
            }
            self.sourced.insert(address, (node, value.clone()));
        }
    }
}

// The address of a value TLC's `CallStackTool` can give a source: an object, as a set, a function
// or a lazy set is. Nat, Int, Real and STRING are each one `UserValue` TLC shares wherever the
// spec names it, so a source a node gives it (`SetEnumValue.cup` of an empty set returns it) is
// its source wherever it is next; the replay, which builds each anew, gives each one address of
// its own, below any an allocation takes.
const SHARED_ADDRESSES: usize = 5;

fn address(value: &Value) -> Option<usize> {
    match value {
        Value::Lazy(lazy) if lazy.java_class == Some(SetClass::Overridden) => match &***lazy {
            Lazy::Nat => Some(1),
            Lazy::Int => Some(2),
            Lazy::Real => Some(3),
            Lazy::Strings => Some(4),
            _ => Some(Rc::as_ptr(lazy) as *const u8 as usize),
        },
        Value::Set(set) => Some(Rc::as_ptr(set) as usize),
        Value::Function(function) => Some(Rc::as_ptr(function) as usize),
        Value::Lazy(lazy) => Some(Rc::as_ptr(lazy) as *const u8 as usize),
        Value::Unsorted(values) => Some(Rc::as_ptr(values) as usize),
        _ => None,
    }
}

/// Where an EXCEPT's `select` of its path (`Value.select(Value[])`) failed: in the method itself,
/// at a part of the path that isn't a function, or in the `select` of the record or tuple
/// reached, at a key of a class its keys can't be.
enum ExceptSelect {
    Path,
    Selected(Value),
}

/// What the method of a value that failed was given: the element a membership tests, the value an
/// equality compares with, or neither.
#[derive(Clone, Copy)]
enum Given<'v> {
    Element(&'v Value),
    Equated(&'v Value),
    /// The argument a function of one key searches its key for (`selectLinearSearch`).
    Keyed(&'v Value),
    Nothing,
}

/// A node TLC's call stack holds: a node of the IR, or the prefix of an infix chain of junctions,
/// such as A /\ B of A /\ B /\ C, which SANY parses as a node of its own.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StackFrame {
    Node(NodeId),
    /// The first `count` operands of a junction.
    Prefix(NodeId, usize),
    /// The tuple of the arguments of a function application of several, which SANY builds as a
    /// node of its own with the application's range (`f[a, b]` is `f[<<a, b>>]`).
    Arguments(NodeId),
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
    /// The predicate of a filter of a set TLC filters at once (`OPCODE_sso` of a Reducible: a
    /// set enumeration or an interval).
    Filter,
    /// The body of this bounded quantifier or CHOOSE, which `eval` takes (`OPCODE_be`,
    /// `OPCODE_bf`, `OPCODE_bc`, `EC.TLC_EXPECTED_VALUE`).
    Quantifier(NodeId),
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
    /// The action of this `[A]_e`, which `eval` takes (`OPCODE_sa`).
    SquareAction(NodeId),
}

/// The reason for a function's value the walk tests that isn't a boolean.
const APPLIED_NON_BOOLEAN: &str = "a function's value the walk tests that isn't a boolean";
const SUBSET_NON_ENUMERABLE: &str = "\\subseteq of a set TLC doesn't enumerate";
/// `x \in S` of a variable with S a value that is no set, which `Tool.getInitStatesAppl`,
/// `getNextStatesAppl` and `enabled` reject outside any of the value's methods.
pub(crate) const ASSIGNED_NON_ENUMERABLE: &str = "an assignment from a value that is no set";
const SUBSET_NON_SET: &str = "SUBSET of a non-set";
// Whether a record's text is that of TLCGet("spec"), whose fields name the implied formulas.
fn is_spec_description(text: &str) -> bool {
    text.contains("impliedinits |->") && text.contains("impliedtemporals |->")
}

const SOURCED_DOMAIN_SIZED: &str =
    "a function TLC keeps lazy over a domain with a source that fails to count";
const SHARED_DOMAIN_SOURCED: &str =
    "a function TLC builds over a domain it shares, which a node gave a source";
const UNPLACED_ENUMERATOR: &str =
    "a set TLC fails to enumerate in a method the evaluator doesn't place";

// Whether TLC's enumerator of a set failed as it was built, in the set's `elements`, with the
// error it throws there, which no Java method wrapped (`Assert.fail` in each `Enumerator`).
fn is_enumerator_failure(error: &EvalError) -> bool {
    error.message.as_ref().is_some_and(|message| {
        message.code.is_none()
            && !message.is_eval_exception
            && message.text.starts_with("Attempted to enumerate ")
    })
}

// Whether a value is a set enumeration TLC holds unnormalized, or a tuple, a record or a function
// that holds one among its values, whose `equals` compares its values in turn
// (`TupleValue.equals`, `RecordValue.equals`, `FcnRcdValue.equals`).
fn holds_unsorted_value(value: &Value) -> bool {
    match value {
        Value::Unsorted(_) => true,
        Value::Function(function) => function.range.iter().any(holds_unsorted_value),
        _ => false,
    }
}

// Whether a filter of a set TLC can't enumerate failed in its own Enumerator
// (`SetPredValue.Enumerator`).
fn is_own_filter_failure(error: &EvalError) -> bool {
    is_enumerator_failure(error)
        && error.message.as_ref().is_some_and(|message| {
            message
                .text
                .starts_with("Attempted to enumerate { x \\in S : p(x) } when S:\n")
        })
}

// Whether a set TLC can't count failed as it was counted (`UserValue.size`, `IntervalValue.size`),
// which a power set's enumerator does to its base (`SubsetValue.elementsNormalized`).
fn is_sizing_failure(error: &EvalError) -> bool {
    error.message.as_ref().is_some_and(|message| {
        message.code.is_none()
            && !message.is_eval_exception
            && (message.text.starts_with(
                "Attempted to compute the number of elements in the overridden value ",
            ) || message
                .text
                .starts_with("Size of interval value exceeds the maximum representable size"))
    })
}

// Whether the failure is `IntervalValue.size`'s, of an interval of more than 2^31 - 1 elements.
fn is_interval_sizing_failure(error: &EvalError) -> bool {
    error
        .message
        .as_ref()
        .is_some_and(|message| message.text.starts_with("Size of interval"))
}

/// The reason for a primed variable a state doesn't assign, before the variable's name.
pub(crate) const PRIMED_UNASSIGNED: &str = "primed variable not assigned: ";

/// The states the builtin Trace holds at a position of a trace: the first `length` of the
/// trace's records. The records are shared between positions, and the tuple is built only when an
/// ALIAS reads Trace, so an ALIAS that doesn't costs nothing per state.
#[derive(Clone, Copy)]
pub(crate) enum TraceContext {
    Printed(usize),
    WorkerPrefix(usize),
    WorkerUnrecorded { workers: usize },
    Unfollowed,
}

#[derive(Clone)]
pub struct TracePrefix {
    pub records: std::rc::Rc<[Value]>,
    pub(crate) context: TraceContext,
}

/// The state `Evaluator::is_unsure_startup_failure` compares with, taken before a failed
/// startup definition is evaluated again (`Evaluator::startup_failure_counts`).
pub(crate) struct StartupFailureCounts {
    lazy_unions: usize,
    lazy_domains: usize,
    unfollowed_constructions: usize,
    print_normalizations: usize,
    was_frozen: bool,
    unsorted_built: usize,
    combination_sort_failures: usize,
    normalized_print_failure: Option<EvalError>,
}

pub struct Evaluator<'ir> {
    closed_java_context: bool,
    /// The nodes of the definitions INSTANCEs with substitutions copy (`check_substituted_frames`).
    substituted_nodes: Option<HashSet<NodeId>>,
    /// The nodes only those copies hold, and the copies' indices (`check_substituted_frames`).
    copy_frames: Option<CopyFrames>,
    pub ir: &'ir Ir,
    /// Builtins that `can_read` counts as reading the state, as `is_precomputed` asks.
    pub(crate) state_builtins: &'static [&'static str],
    /// Whether `can_read` bounds the level as TLC's `getLevelBound` does, for `may_reach_bound`.
    pub(crate) is_level_bound: bool,
    /// What `may_reach_bound` found of each definition.
    pub(crate) level_bounds: HashMap<NodeId, bool>,
    /// What `passes_operators_lexically` found of each RECURSIVE definition's body.
    lexical_recursions: HashMap<NodeId, bool>,
    texts: Vec<Option<Rc<Text>>>,
    /// The value of each string literal, by its node.
    literals: HashMap<NodeId, Rc<Text>>,
    ranks: HashMap<Box<[u16]>, i32>,
    /// The texts ranked past the IR's, in order, while the startup ranks what it makes as TLC
    /// interns it; none otherwise.
    startup_ranked: Option<Vec<Box<[u16]>>>,
    constants: Vec<Option<Value>>,
    configured_values: HashMap<u32, Value>,
    /// Zero-arity definitions that read nothing of the state, evaluated once, as TLC does.
    pub(crate) cache: HashMap<(NodeId, bool), Value>,
    /// The startup definitions that failed as TLC started, which it evaluates again where they are
    /// used (`processConstantDefns` swallows what one throws).
    pub(crate) failed_startup: HashSet<NodeId>,
    // An actual NO_VALUE result without proof that a warning preceded the startup failure.
    pub(crate) uncomputed_warning_startup: HashSet<NodeId>,
    /// Whether the evaluator took which startup definitions failed as the search started
    /// (`set_failed_startup`), so that any other it holds no value of is one TLC computed.
    pub(crate) is_startup_known: bool,
    /// The startup definitions the search found failing as TLC started.
    searched_failing: HashSet<NodeId>,
    /// Of those, the ones it failed at a limit of its own before any warning
    /// (`set_searched_limited`).
    searched_limited: HashSet<NodeId>,
    /// The warning-only startup definitions the search failed on before any warning other than
    /// at a limit of its own, which TLC may compute and warn on as it starts.
    searched_unwarned: HashSet<NodeId>,
    /// How many prints the search made of each startup definition before it stopped
    /// (`set_searched_printed`).
    searched_printed: HashMap<NodeId, usize>,
    /// How many prints each startup definition made as the search evaluated it, and whether it
    /// drew (`set_searched_effects`).
    searched_effects: HashMap<NodeId, (usize, bool)>,
    /// The startup prints the search couldn't compute, which the evaluator words
    /// (`set_searched_unworded`).
    searched_unworded: HashSet<NodeId>,
    /// How many of the startup definitions the startup computes, where it stops before the rest
    /// (`Rebuilder::compute_startup_until`).
    pub(crate) startup_limit: Option<usize>,
    /// The value the search computed of each constant definition whose body is a CHOOSE over a
    /// set, and whose evaluation has no effect but its value, by its node (`set_chosen`).
    chosen: HashMap<NodeId, Value>,
    /// The current state's values, and the next state's: `None` until assigned.
    pub current: Vec<Option<Value>>,
    pub next: Vec<Option<Value>>,
    /// How many times the evaluator read the state, so a definition that read none is cached.
    reads: u64,
    /// How many times the evaluator applied TLCGet to a key the search or the split makes
    /// (`is_varying_tlc_get_key`), which an \E's bound in the split of the next-state relation
    /// reads as TLC starts (`Splitter::evaluate_bound`).
    pub(crate) varying_tlc_gets: u64,
    /// How many lazy functions and filters the evaluator built, each holding the states to
    /// evaluate later in them: a definition that built one isn't the same value in other states.
    captures: u64,
    /// The tool identity of cached lazy bindings, including those in captured contexts.
    identity: Rc<()>,
    cached_frames: Vec<Weak<Frame>>,
    /// TLCGet("level") of the current state.
    pub level: i32,
    /// TLCGet("level") of the next state, where it isn't one past the current's.
    pub next_level: Option<i32>,
    /// What Print and PrintT printed, each as the texts of its values.
    pub printed: Vec<crate::OutputEvent>,
    has_uninitialized_literals: bool,
    /// The state a walk looks for, where a value that differs from it can't lead to it: a walk
    /// then drops an assignment of another value, as nothing else follows from it.
    pub target: Option<Vec<Value>>,
    /// Whether a walk is ENABLED's, which TLC's `Tool#enabled` runs.
    pub(crate) is_enabling: bool,
    /// The function application the walk tests, and whether it walks the initial predicate:
    /// `getInitStates`, `getNextStates` and `enabled` word a non-function applied there apart.
    pub(crate) walked_application: Option<(NodeId, bool)>,
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
    /// Whether a failure came from what a walk goes on to once a value is chosen, the rest of the
    /// predicate or the check of the state it gives, and passed no frame since: TLC's
    /// `getInitStates` and `getNextStates` call that from `Tool`, after the set's enumerator
    /// returned, so the failure is in no method of the set.
    pub(crate) is_continued_failure: bool,
    /// Where an EXCEPT's `select` of its path failed, for the EXCEPT to place the failure
    /// (`place_except_failure`).
    except_selected: Option<ExceptSelect>,
    /// Whether the failure the EXCEPT placed needs no other placing (`mark_fingerprinted`).
    is_except_placed: bool,
    /// Whether a failure of TLC's enumerator of a set must be placed among the values whose
    /// `elements` it passes through: where the search stopped at a set it can't enumerate,
    /// which TLC may fail at in a method of a value with a source.
    pub(crate) is_enumerator_placed: bool,
    /// Whether the evaluator walks the initial predicate, where TLCExt's Trace is the record of
    /// the state, once all its variables are assigned (`TLCExt.getTrace`).
    pub(crate) is_initial_walk: bool,
    /// How many UNIONs the evaluator held lazy, as TLC's `UnionValue`.
    lazy_unions: usize,
    /// How many times Print or PrintT failed normalizing a value deeply where the evaluator
    /// knows the order TLC walks it in (`deep_normalize`), with the last such failure's reason.
    print_normalizations: (usize, String),
    /// How many times the evaluator evaluated a startup definition that failed as TLC started.
    pub(crate) failed_startup_uses: usize,
    /// The last failure of Print or PrintT where the evaluator followed TLC's `deepNormalize` of
    /// every value it prints, through sets whose Java class it knows.
    normalized_print_failure: Option<EvalError>,
    /// The functions the evaluator built that TLC keeps lazy (`FcnLambdaValue`), by address,
    /// recorded as a failure is evaluated, and how many times DOMAIN read one: TLC's DOMAIN of
    /// one gives the set it holds as its domain, which may be lazy where the evaluator's isn't.
    kept_lazy: HashSet<usize>,
    /// The functions TLC keeps lazy over the set enumeration of one bound, by the function's
    /// address, with the elements of that set as written where TLC holds it unnormalized: the
    /// function asks the set whether it holds the argument it is applied to
    /// (`FcnLambdaValue.apply`), and builds a FcnRcdValue of the set's elements, which its
    /// enumeration sorts (`toFcnRcd`). Each entry holds the function's allocation, so that no
    /// other function takes its address.
    held_lazy_domains: HashMap<usize, (Weak<Function>, Option<Vec<Value>>)>,
    /// The functions TLC keeps lazy over an interval or a lazy set of one bound, by the
    /// function's address, with that set: the function asks it whether it holds the argument it
    /// is applied to (`FcnLambdaValue.apply`), which fails as the set's `member` does.
    lazy_domain_sets: HashMap<usize, (Weak<Function>, Value)>,
    lazy_domains: usize,
    /// How many function constructors failed after their domains, other than one of a single
    /// name over a set enumeration or an interval TLC builds as it meets it (`construct_function`).
    unfollowed_constructions: usize,
    /// How many function bodies produced effects while TLC keeps the function lazy.
    lazy_body_effects: usize,
    /// Print forcing a lazy value can reword an exception according to a source not retained.
    printing_values: usize,
    /// How many prints the evaluator wrote without following how TLC deep-normalizes the value
    /// first (`deepNormalize`), which may fail there.
    pub(crate) unfollowed_print_normalizations: usize,
    /// How many times TLCGet read a register.
    pub register_reads: usize,
    /// Whether TLC runs with -tool, under which the message of an error TLC raises with a code
    /// holds the code's markers, which AssertError compares with. `None` where the caller doesn't
    /// say, and AssertError isn't followed.
    pub is_tool: Option<bool>,
    /// Whether the evaluator evaluates an assumption that failed as TLC started, which TLC
    /// evaluates with no `CallStackTool`, so that no value it builds has a source, and reports
    /// with the failure's message alone, with no stack of the values it failed in.
    pub(crate) is_assumption: bool,
    /// Whether the evaluator evaluates an assumption the search found holding, or failing with a
    /// message AssertError compares, which TLC evaluates with `Tool`, so that no value it builds
    /// has a source: a startup definition that failed there is followed within a call stack of
    /// its own (`evaluate_failed_startup`).
    pub(crate) is_checking_assumption: bool,
    /// Whether the evaluator evaluates the assumptions as TLC checks them, after it built its
    /// model checker and before it computes a state (`ModelChecker.modelCheck`), which TLCGet's
    /// keys of the search read as such.
    pub(crate) is_in_assumptions: bool,
    /// Whether each node of the call stack's replay that evaluates to a filter gives a copy of
    /// it, as TLC's `CallStackTool.eval` does (`Predicate::copied`).
    pub(crate) copies_filters: bool,
    /// The builtin Trace as TLC binds it while it evaluates the ALIAS as it prints a trace
    /// (`Tool.evalAlias`): a record of each state it holds, in TLC's order of the variables.
    /// `None` elsewhere, where TLC evaluates the Java method, which isn't followed.
    pub trace: Option<TracePrefix>,
    /// How many workers TLC runs, which TLCGet("config") reads. `None` where the caller doesn't
    /// say, and TLCGet("config") isn't followed.
    pub workers: Option<usize>,
    /// Whether TLC simulates the model (`-simulate`), whose run TLCGet reads otherwise than the
    /// model checker's: TLC has no model checker to read the counts of then.
    pub(crate) is_simulation: bool,
    /// Whether the files the Json module's operators read are the file system's, which the replay
    /// then reads as TLC does where it fails to.
    pub(crate) reads_files: bool,
    /// The directories, and the files, TLC makes before it evaluates anything, which the replay
    /// doesn't: its metadir and its dumps. `None` where the caller doesn't say, and a file TLC
    /// fails to open isn't followed.
    pub(crate) made_paths: Option<Vec<std::path::PathBuf>>,
    /// How many AssertError expressions the evaluator is inside, which compare a failure's
    /// message alone, without where TLC reports it.
    asserting: u32,
    /// Whether the evaluator evaluates as TLC's own tool does as it starts, computing the
    /// constant definitions (`processConstantDefns`) and checking the assumptions
    /// (`checkAssumptions`), whose report holds an error's message alone: no `CallStackTool`
    /// gives a value a source there, so no failure becomes a FingerprintException.
    pub(crate) is_starting: bool,
    /// Whether the evaluator computes the substitutes and the constant definitions as TLC does
    /// as it processes the spec (`SpecProcessor.processConstantDefns`), before it has made its
    /// checker or simulator (`TLCGlobals.mainChecker`), whose registers TLCExt reads.
    pub(crate) is_processing_constants: bool,
    /// Of each constant definition a walk reached, whether TLC keeps the value it computed as it
    /// started (`is_kept_at_startup`).
    kept_at_startup: HashMap<NodeId, bool>,
    /// Whether the model may read TLCGet("config"), whose install the evaluator writes "unknown"
    /// where TLC writes where its jar is (`TLCGlobals.Version.installLocation`): a value TLC
    /// prints or writes that holds that string is then one the evaluator can't word.
    is_install_read: bool,
    /// Whether the SUBSET evaluated next is PrintT's argument as TLC starts, and the value
    /// that isn't a set it was of, which PrintT prints as TLC does (`print_subset_of_non_set`).
    printed_subset: bool,
    printed_subset_base: Option<Value>,
    /// How many function applications the evaluator is evaluating the function of, which TLC
    /// evaluates keeping a function constructor in it lazy (`EvalControl.KeepLazy`).
    keeping_lazy: u32,
    /// Whether the evaluator is evaluating TLCEval's argument of constant level again as TLC
    /// does (`tlcEvalConst`), where TLC builds each function constructor it doesn't keep lazy
    /// (`toFcnRcd`) and fails as its domain's `normalize` does (`counted_unsorted_failure`).
    builds_unsorted_domains: bool,
    /// Whether the last body of a function TLC keeps lazy that failed as the evaluator built it
    /// failed as TLC words a failure, rather than where the evaluator declines.
    is_lazy_body_failure_worded: bool,
    /// Whether the function constructor evaluated next is one an application applies in place,
    /// whose domain TLC doesn't enumerate (`FcnLambdaValue.apply`).
    preserves_lazy_domain: bool,
    /// The constructors written in place that the application evaluated next applies directly,
    /// itself or through the EXCEPTs it updates, which `construct_in_place` may hold as the
    /// FcnLambdaValue TLC keeps: TLC applies that and drops it.
    in_place_functions: Vec<NodeId>,
    /// Whether the next bounds `for_each_binding` enumerates are a set map's, which declines
    /// one TLC fails to sort outside its startup (`UNSORTED_STATE_BOUND`).
    declines_unsorted_bound: bool,
    /// The functions TLC keeps lazy whose bodies printed as the evaluator built them, in the
    /// order it built them, which an operation that forces them has yet to take.
    lazy_prints: Vec<LazyPrint>,
    /// How many lazy functions whose bodies printed the evaluator has held, which numbers them.
    lazy_print_count: u64,
    /// The operation that forces the lazy functions its arguments hold, as it evaluates them.
    forcing: Option<Forcing>,
    /// Where the first body that printed of the function being built began.
    lazy_print_start: Option<Effects>,
    /// The keys of the bodies that printed of the function being built.
    lazy_print_keys: Vec<Value>,
    cache_control_primed: bool,
    /// The function constructors a LET names once, found when first asked for.
    once_named: Option<HashSet<NodeId>>,
    /// Where the evaluator made a value TLC shares with another, or shared one TLC made again,
    /// which a dumped trace, writing each object once, would show.
    pub(crate) unshared: Option<&'static str>,
}

/// TLC's registers (`IdThread`'s local values and named registers): the value TLCSet stored under
/// each natural number, and under each name that starts with "s:", a string.
#[derive(Clone, Debug, Default)]
pub struct Registers {
    pub numbered: Vec<Option<Value>>,
    pub named: Vec<(Value, Value)>,
    /// The system properties TLCSet("-D<name>", v) set, by name, each the string of the value's
    /// text (`System.setProperty`).
    pub properties: Vec<(Vec<u16>, Value)>,
}

/// The name the front end gives the operator a selection with arguments applies.
const SELECTION_NAME: &str = "$subexpression";

/// Whether a value's text (`Value.toString`) is the one `format_value` gives whatever TLC built
/// it as: a scalar, or a tuple of them.
fn has_plain_text(value: &Value) -> bool {
    match value {
        Value::Int(_) | Value::Bool(_) | Value::Str(_) | Value::Model(_) => true,
        _ => as_tuple(value).is_some_and(|items| items.iter().all(has_plain_text)),
    }
}

impl Registers {
    /// The registers whose values are ids of `store`: by number, and by name.
    pub fn from_store(
        store: &Store,
        numbered: &[Option<Id>],
        named: &[(Id, Id)],
        properties: &[(Vec<u16>, Id)],
    ) -> Result<Registers, Unsupported> {
        Ok(Registers {
            properties: properties
                .iter()
                .map(|(name, value)| Ok((name.clone(), from_store(store, *value)?)))
                .collect::<Result<_, Unsupported>>()?,
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

/// How many calls of RECURSIVE operators and recursive functions may nest, as the engine bounds
/// them at 3,000 (`MAXIMUM_RECURSION` there), past which TLC's 2 MB thread stack overflowed on the
/// cheapest recursion, `G(n) == IF n = 0 THEN 0 ELSE G(n - 1)`, in every probe. The evaluator
/// answers what the engine stops on, under a larger bound: the corpus's `engine262` assumptions,
/// recorded with a 64 MB stack (their `stack:` header, which the binary isn't told of), nest about
/// 5,800 such calls here. A recursion from 3,000 to 6,000 calls that the evaluator answers is a
/// known wrong output under a 2 MB stack (fallback.md); past 6,000 it declines.
const MAXIMUM_RECURSION: u32 = 6_000;

/// The stack an evaluation's nesting may use: half the stack the search's threads have, which
/// leaves room for the frames between one nesting and the next.
const MAXIMUM_STACK_BYTES: usize = 128 * 1024 * 1024;

thread_local! {
    static DEPTH: std::cell::Cell<u32> = const { std::cell::Cell::new(0) };
    // How many of those nestings are calls of a RECURSIVE operator or a recursive function.
    static RECURSIONS: std::cell::Cell<u32> = const { std::cell::Cell::new(0) };
    // Where the outermost nesting's frame is, which the stack grows from.
    static BASE: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    // Whether a nesting went too deep inside the outermost one, where TLC's stack overflowed and
    // it stopped: each nesting fails at once until the outermost ends, so that an evaluation that
    // tries another way at each depth where the one below failed doesn't try again at every
    // depth on the way out.
    static TOO_DEEP: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    // Whether the nesting that last went too deep is a recursion TLC never finishes, reached only
    // through what TLC evaluates in `Tool` itself (`Evaluator::is_endless_recursion`).
    static ENDLESS: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Whether the nesting that last went too deep, since this was last asked, is a recursion TLC
/// never finishes, where TLC's stack overflows whatever its size: a `StackOverflowError`, which
/// no method of `Tool` or of the values it evaluates catches on the way.
pub fn take_endless_recursion() -> bool {
    ENDLESS.replace(false)
}

/// How many calls deeper a recursive function's argument, stepped by a constant, may go before it
/// overflows an int, past which no JVM thread's stack (at most 1 GB, `-Xss`) holds TLC's frames
/// of the calls, a few hundred bytes each.
const UNREACHABLE_CALLS: i64 = 10_000_000;

/// The depth and base outside a nesting, which it restores however it ends, as where a reused
/// thread catches a panic.
struct Nesting {
    depth: u32,
    recursions: u32,
    base: usize,
}

impl Drop for Nesting {
    fn drop(&mut self) {
        DEPTH.set(self.depth);
        RECURSIONS.set(self.recursions);
        BASE.set(self.base);
        if self.depth == 0 {
            TOO_DEEP.set(false);
        }
    }
}

/// `EC.TLC_MODULE_TLCGET_UNDEFINED`, `EC.TLC_MODULE_ARGUMENT_ERROR` and
/// `EC.TLC_MODULE_ONE_ARGUMENT_ERROR`.
const TLCGET_UNDEFINED: u32 = 2145;
const ARGUMENT_ERROR: u32 = 2169;
/// `EC.TLC_MODULE_ARGUMENT_ERROR_AN`.
const ARGUMENT_ERROR_AN: u32 = 2266;
/// `EC.TLC_MODULE_DIVISION_BY_ZERO`.
const DIVISION_BY_ZERO: u32 = 2179;
const ONE_ARGUMENT_ERROR: u32 = 2283;
/// `EC.TLC_MODULE_EVALUATING`.
const MODULE_EVALUATING: u32 = 2182;
/// `EC.TLC_MODULE_APPLYING_TO_WRONG_VALUE`.
const APPLYING_TO_WRONG_VALUE: u32 = 2176;
/// `EC.TLC_MODULE_ARGUMENT_NOT_IN_DOMAIN` and `EC.TLC_MODULE_APPLY_EMPTY_SEQ`.
const ARGUMENT_NOT_IN_DOMAIN: u32 = 2183;
const APPLY_EMPTY_SEQ: u32 = 2184;
/// `EC.TLC_ARGUMENT_MISMATCH`.
const ARGUMENT_MISMATCH: u32 = 2170;
const TUPLE_MISMATCH: &str = "a tuple pattern that doesn't match";
/// `EC.TLC_EXPECTED_EXPRESSION_IN_COMPUTING`, its `2` and `EC.TLC_EXPECTED_VALUE`.
const EXPECTED_EXPRESSION_IN_COMPUTING: u32 = 2247;
const EXPECTED_EXPRESSION_IN_COMPUTING2: u32 = 2248;
const EXPECTED_VALUE: u32 = 2215;

// TLCGet of a register TLCSet hasn't set, named by its number or its name.
// Whether TLCGet of this key reads a simulation's run, which differs from the model checker's:
// any key `TLCGetStringValue` knows but the state's level, a Java property and the spec.
fn is_simulation_run_key(key: &[u16]) -> bool {
    let key = String::from_utf16_lossy(key);
    !matches!(key.as_str(), "level" | "spec")
        && !is_unknown_tlc_get_key(&key)
        && !key.starts_with(JAVA_PROPERTY_PREFIX)
}

// Whether TLCGet of this key reads what the search or the split makes, so that TLC's split, which
// reads it once as TLC starts, and an evaluation at each state read different values: the
// search's statistics and the state's level (`TLCGetSet.TLCGetStringValue`), and the spec, whose
// actions the split is still building. The other keys TLC fixes for the run, or read registers
// and properties, which change only where the spec sets them (`Splitter::evaluate_bound`).
fn is_varying_tlc_get_key(key: &Value) -> bool {
    let Value::Str(key) = key else {
        return false;
    };
    let key = String::from_utf16_lossy(&key.units);
    matches!(
        key.as_str(),
        "level" | "diameter" | "generated" | "distinct" | "queue" | "duration" | "stats" | "spec"
    )
}

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
/// prints no frames where an assumption fails to evaluate. A failure comparing the sets a lazy
/// set is built of is placed by the FingerprintException a value with a source heads, and
/// `checkAssumptions` evaluates with `Tool`, whose values have none.
pub(crate) const UNFOLLOWED_FRAMES: [&str; 12] = [
    UNSORTED_BOUND_SOURCED,
    LAZY_ARGUMENT_LIST,
    UNSORTED_PRINT,
    LAZY_DOMAIN,
    BUILT_FUNCTION,
    LAZY_MEMBER,
    LAZY_BODY,
    STANDARD_MODULE,
    LAZY_DOMAIN_MEMBER,
    UNPLACED_KEY_SEARCH,
    UNPLACED_UNCOUNTED_PART,
    crate::value::UNPLACED_COMPONENT_FAILURE,
];
const STANDARD_MODULE: &str = "the frames of a standard module's definition";
pub(crate) const SUBSTITUTED_FRAMES: &str =
    "a call stack within a definition an INSTANCE with substitutions copies";
const LAZY_MEMBER: &str = "the membership of a filter TLC keeps lazy";
const LAZY_DOMAIN: &str = "the domain of a function TLC keeps lazy";
const BUILT_FUNCTION: &str = "building a function a definition defines";
const LAZY_BODY: &str = "the body of a function TLC keeps lazy";
const LAZY_BODY_AT_KEY: &str =
    "the body of a function TLC keeps lazy, at a key it may not evaluate";
const LAZY_DOMAIN_MEMBER: &str = "the membership in the domain of a function TLC keeps lazy";
const UNSORTED_LAZY_DOMAIN: &str = "a function TLC keeps lazy over a set enumeration it can't sort";
const LAZY_ARGUMENT_LIST: &str = "the argument list of a function TLC keeps lazy";
// A function constructor over a set enumeration TLC fails to sort: TLC keeps the function lazy
// (`FcnLambdaValue`) and applies it searching the domain as written (`SetEnumValue.member`, each
// element the receiver of `equals`), where the evaluator builds it sorted.
const UNSORTED_DOMAIN: &str = "a function over a set TLC fails to sort";
// A filter or map, past TLC's startup, of a set enumeration TLC fails to sort: TLC fails as it
// fingerprints the state (a FingerprintException), where the evaluator fails as it enumerates.
const UNSORTED_STATE_BOUND: &str = "a filter or map of a set TLC fails to sort, in a state";
/// Where a set of functions, of records or of tuples fails printing the element it words in its
/// message deeper than in that element's own normalization, or in that of an element the replay
/// holds without the source TLC gives it (`Evaluator::mark_failing_member`).
const NESTED_PRINTED_ELEMENT: &str =
    "a membership's message that fails printing a set nested in the element";
const UNSORTED_PRINT: &str = "a comparison that fails printing a set TLC holds unnormalized";
// The set of a CHOOSE, a quantifier, a set filter or a set map that is a set enumeration TLC
// fails to sort: TLC's enumeration of it (`SetEnumValue.elements`, `normalize`) throws the failure
// on as a FingerprintException with the set's source, even of a set a constant definition
// computed as TLC started, and those of the sets nested in it whose `compareTo` failed, which the
// replay doesn't follow.
const UNSORTED_BOUND_SOURCED: &str =
    "the enumeration of a bound set enumeration TLC fails to sort, with its source";
const UNPLACED_KEY_SEARCH: &str =
    "a function's search of its keys whose frames the call stack doesn't place";
const UNPLACED_UNCOUNTED_PART: &str =
    "an interval TLC fails to count within a bound the evaluator doesn't place";
/// `EC.TLC_MODULE_VALUE_JAVA_METHOD_OVERRIDE`.
pub(crate) const JAVA_METHOD_FAILED: u32 = 2154;

const TLC_EVAL: &str = "public static tlc2.value.impl.Value tlc2.module.TLCEval.tlcEval(tlc2.tool.impl.Tool,tla2sany.semantic.ExprOrOpArgNode[],tlc2.util.Context,tlc2.tool.TLCState,tlc2.tool.TLCState,int,tlc2.tool.coverage.CostModel)";

const TLC_GET_EVAL: &str = "public static tlc2.value.impl.Value tlc2.module.TLCGetSet.TLCGetEval(tlc2.tool.impl.Tool,tla2sany.semantic.ExprOrOpArgNode[],tlc2.util.Context,tlc2.tool.TLCState,tlc2.tool.TLCState,int,tlc2.tool.coverage.CostModel)";

const FINGERPRINT: &str = "public static synchronized tlc2.value.impl.IntValue tlc2.module.TLCExt.tlcFingerprint(tlc2.value.impl.Value)";

const EVAL2: &str = "public static tlc2.value.impl.Value tlc2.module.TLCExt.tlcEval2(tlc2.tool.impl.Tool,tla2sany.semantic.ExprOrOpArgNode[],tlc2.util.Context,tlc2.tool.TLCState,tlc2.tool.TLCState,int,tlc2.tool.coverage.CostModel)";

const DEF_BY_NAME: &str = "public static tlc2.value.impl.Value tlc2.module.TLCExt.tlcDefByName(tlc2.tool.impl.Tool,tla2sany.semantic.ExprOrOpArgNode[],tlc2.util.Context,tlc2.tool.TLCState,tlc2.tool.TLCState,int,tlc2.tool.coverage.CostModel)";

const PICK_SUCCESSOR: &str = "public static synchronized tlc2.value.impl.Value tlc2.module.TLCExt.pickSuccessor(tlc2.tool.impl.Tool,tla2sany.semantic.ExprOrOpArgNode[],tlc2.util.Context,tlc2.tool.TLCState,tlc2.tool.TLCState,int,tlc2.tool.coverage.CostModel)";

const RANDOM_SUBSET_SET: &str = "public static tlc2.value.impl.Value tlc2.module.Randomization.RandomSubsetSet(tlc2.value.impl.Value,tlc2.value.impl.Value,tlc2.value.impl.Value)";
const RANDOM_ELEMENT: &str =
    "public static tlc2.value.impl.Value tlc2.module.TLC.RandomElement(tlc2.value.impl.Value)";
const RANDOM_SET_OF_SUBSETS: &str = "public static tlc2.value.impl.Value tlc2.module.Randomization.RandomSetOfSubsets(tlc2.value.impl.Value,tlc2.value.impl.Value,tlc2.value.impl.Value)";

const RANDOM_SUBSET: &str = "public static tlc2.value.impl.Value tlc2.module.Randomization.RandomSubset(tlc2.value.impl.Value,tlc2.value.impl.Value)";

// `reportAsJavaFailure`: a failure with TLC's message, reported as the failure of the Java method
// that TLC overrides an operator with.
fn as_java_failure<T>(signature: &str, result: Evaluated<T>) -> Evaluated<T> {
    // `MethodValue.eval` throws a NullPointerException on as an EvalException, and reports
    // any other with `Assert.fail`.
    result.map_err(|error| match error.message {
        Some(message) => EvalError {
            runtime_exception: RuntimeException::Runtime,
            message: Some(TlcMessage {
                text: format!(
                    "Attempted to apply the operator overridden by the Java method\n{signature},\nbut it produced the following error:\n{}",
                    message.text
                ),
                code: Some(JAVA_METHOD_FAILED),
                is_eval_exception: error.runtime_exception == RuntimeException::NullPointer,
                inner: Some(Box::new(message)),
            }),
            ..error
        },
        None => error,
    })
}

// `MethodValue.apply` reports what fails in the Java method, but an EvalException, as the
// method's failure, such as what fails in an operator argument the method applies.
fn as_java_runtime_failure<T>(signature: &str, result: Evaluated<T>) -> Evaluated<T> {
    match &result {
        Err(EvalError {
            message: Some(message),
            ..
        }) if !message.is_eval_exception => as_java_failure(signature, result),
        _ => result,
    }
}

const ASSERT_ERROR: &str = "public static synchronized tlc2.value.impl.Value tlc2.module.TLCExt.assertError(tlc2.tool.impl.Tool,tla2sany.semantic.ExprOrOpArgNode[],tlc2.util.Context,tlc2.tool.TLCState,tlc2.tool.TLCState,int,tlc2.tool.coverage.CostModel)";
const SELECT_SEQ: &str = "public static tlc2.value.impl.Value tlc2.module.Sequences.SelectSeq(tlc2.value.impl.Value,tlc2.value.impl.Value)";
const SORT_SEQ: &str = "public static tlc2.value.impl.Value tlc2.module.TLC.SortSeq(tlc2.value.impl.Value,tlc2.value.impl.Value)";
const TO_TRACE: &str =
    "public static tlc2.value.impl.Value tlc2.module.TLCExt.lassoOrdinal(tlc2.value.impl.Value)";
const WARSHALL: &str = "public static tlc2.value.impl.Value tlc2.module.TransitiveClosure.Warshall(tlc2.value.impl.Value)";

// Whether `Warshall`'s Hashtable finds one endpoint as another: values of different kinds have
// different fingerprints, so it compares only values of one kind, which the evaluator compares
// where it can't fail.
fn warshall_node_equals(left: &Value, right: &Value) -> Evaluated<bool> {
    match (left, right) {
        (Value::Int(left), Value::Int(right)) => Ok(left == right),
        (Value::Bool(left), Value::Bool(right)) => Ok(left == right),
        (Value::Str(_), Value::Str(_))
        | (Value::Model(_), Value::Model(_))
        | (Value::Function(_), Value::Function(_))
        | (Value::Set(_) | Value::Interval(..), Value::Set(_) | Value::Interval(..)) => {
            match equals(left, right) {
                Ok(is_equal) => Ok(is_equal),
                Err(_) => fail("Warshall of endpoints TLC may fail to compare"),
            }
        }
        (
            Value::Int(_)
            | Value::Bool(_)
            | Value::Str(_)
            | Value::Model(_)
            | Value::Function(_)
            | Value::Set(_)
            | Value::Interval(..),
            Value::Int(_)
            | Value::Bool(_)
            | Value::Str(_)
            | Value::Model(_)
            | Value::Function(_)
            | Value::Set(_)
            | Value::Interval(..),
        ) => Ok(false),
        _ => fail("Warshall of an endpoint the evaluator doesn't fingerprint"),
    }
}

const COMBINE_FCN: &str = "public static tlc2.value.impl.Value tlc2.module.TLC.CombineFcn(tlc2.value.impl.Value,tlc2.value.impl.Value)";

fn is_text(text: &Text, word: &str) -> bool {
    text.units.iter().copied().eq(word.encode_utf16())
}
const CARDINALITY: &str = "public static tlc2.value.impl.IntValue tlc2.module.FiniteSets.Cardinality(tlc2.value.impl.Value)";
const TO_STRING: &str =
    "public static tlc2.value.impl.Value tlc2.module.TLC.ToString(tlc2.value.impl.Value)";
const PRINT: &str = "public static tlc2.value.impl.Value tlc2.module.TLC.Print(tlc2.value.impl.Value,tlc2.value.impl.Value)";
const PRINT_T: &str =
    "public static tlc2.value.impl.Value tlc2.module.TLC.PrintT(tlc2.value.impl.Value)";

const DOMAIN_OF_NON_FUNCTION: &str = "DOMAIN of a non-function";

// Print deep-copies and deep-normalizes its argument. The lazy binary set values and
// sets of functions and records retain their operands on deepCopy. Follow only graphs whose
// values can be normalized without a failure, so no first error or effect can move.
fn normalize_simple_print_difference(value: &Value) -> bool {
    fn known(value: &Value, seen: &mut HashSet<usize>) -> bool {
        if value.is_set() && !crate::value::has_java_set_representation(value) {
            return false;
        }
        match value {
            Value::Int(_)
            | Value::Bool(_)
            | Value::Str(_)
            | Value::Model(_)
            | Value::Interval(..) => true,
            Value::Set(elements) => elements.iter().all(|value| known(value, seen)),
            Value::Function(function) => {
                let id = Rc::as_ptr(function) as usize;
                if !seen.insert(id) {
                    return false;
                }
                let result = matches!(
                    (function.class.get(), function.java_class.get()),
                    (Class::Tuple, Some(Class::Tuple)) | (Class::Record, Some(Class::Record))
                ) && function.domain.iter().chain(&function.range).all(|item| {
                    !matches!(item, Value::Set(_) | Value::Unsorted(_) | Value::Lazy(_))
                        && known(item, seen)
                });
                seen.remove(&id);
                result
            }
            Value::Lazy(lazy) => match &***lazy {
                Lazy::Diff(left, right) | Lazy::Cup(left, right) | Lazy::Cap(left, right) => {
                    known(left, seen) && known(right, seen)
                }
                Lazy::FunctionSet(domain, range) => {
                    matches!(domain, Value::Set(elements) if elements.len() <= 1)
                        && known(domain, seen)
                        && known(range, seen)
                }
                Lazy::RecordSet(fields, _) => fields.iter().all(|(_, set)| known(set, seen)),
                Lazy::Product(factors) => factors.iter().all(|factor| known(factor, seen)),
                _ => false,
            },
            _ => false,
        }
    }
    fn apply(value: &Value) {
        match value {
            Value::Set(elements) => {
                for element in elements.iter() {
                    apply(element);
                }
                normalize(value);
            }
            Value::Function(_) => settle_deep(value),
            Value::Lazy(lazy) => match &***lazy {
                Lazy::Diff(left, right)
                | Lazy::Cup(left, right)
                | Lazy::Cap(left, right)
                | Lazy::FunctionSet(left, right) => {
                    apply(left);
                    apply(right);
                }
                Lazy::RecordSet(fields, _) => {
                    for (_, set) in fields {
                        apply(set);
                    }
                }
                Lazy::Product(factors) => {
                    for factor in factors {
                        apply(factor);
                    }
                }
                _ => {}
            },
            _ => {}
        }
    }
    if matches!(value, Value::Lazy(lazy) if lazy.java_class == Some(SetClass::Difference)
    && matches!(&***lazy, Lazy::Diff(left, right)
        if match (java_set_class(left), java_set_class(right)) {
            (Some(SetClass::Functions | SetClass::Records), Some(right)) => {
                matches!(right, SetClass::Enumeration | SetClass::Predicate)
            }
            (Some(SetClass::Product), Some(right)) => right == SetClass::Enumeration,
            _ => false,
        }))
        && known(value, &mut HashSet::new())
    {
        apply(value);
        true
    } else {
        false
    }
}

// `TLC.Print` and `PrintT` deep-copy and deep-normalize each value before they print it
// (`IValue.deepNormalize`). A set enumeration's copy is the set itself, so normalizing sorts the
// set TLC holds, which every later search of it then searches sorted, with `compareTo`, rather
// than element by element with `equals`. The lazy sets normalize their operands (`SetCupValue`,
// `SetCapValue`, `SetDiffValue`, `SetOfFcnsValue`, `SetOfRcdsValue`, `SetOfTuplesValue`,
// `SubsetValue`, `UnionValue`, and `SetPredValue` its base), tuples, records and functions their
// values, and the sets the standard modules override (`UserValue`) nothing.
// It normalizes each set enumeration it holds unnormalized and reaches so, and fails where TLC
// fails to sort one (`SetEnumValue.normalize`), each element first. It declines where it reaches
// one through a value whose normalization it doesn't follow (a function TLC keeps lazy, a
// function's domain of two or more keys, which sorts), and then normalizes nothing.
fn deep_normalize_print(value: &Value) -> Evaluated<()> {
    enum Stop {
        Unfollowed,
        Failed(EvalError),
    }
    fn unfollowed_if(is_unfollowed: bool) -> Result<(), Stop> {
        if is_unfollowed {
            Err(Stop::Unfollowed)
        } else {
            Ok(())
        }
    }
    fn visit(value: &Value, found: &mut Vec<Value>, seen: &mut HashSet<usize>) -> Result<(), Stop> {
        match value {
            Value::Null
            | Value::Bool(_)
            | Value::Int(_)
            | Value::Str(_)
            | Value::Model(_)
            | Value::Interval(..) => Ok(()),
            Value::Set(set) => {
                if !seen.insert(Rc::as_ptr(set) as usize) {
                    return Ok(());
                }
                let written = unnormalized(value);
                // `SetEnumValue.deepNormalize`: each element, then the set.
                for element in written.as_deref().unwrap_or(&set[..]) {
                    visit(element, found, seen)?;
                }
                if written.is_some() {
                    found.push(value.clone());
                }
                Ok(())
            }
            Value::Unsorted(set) => {
                for element in set.iter() {
                    visit(element, found, seen)?;
                }
                Err(Stop::Failed(unsorted_failure(set)))
            }
            // A `FcnLambdaValue` TLC hasn't fingerprinted normalizes its domain set, which the
            // function the evaluator built doesn't hold, but not its values, which TLC computes
            // again as it prints them: the evaluator follows one that holds no set TLC holds
            // unnormalized. A function's domain sorts as it normalizes (`FcnRcdValue.normalize`),
            // which compares its keys, and so normalizes those that are sets, only where it has
            // two or more.
            Value::Function(function) => {
                if function.class.get() == Class::Lambda
                    || function.domain.len() > 1 && function.domain.iter().any(holds_unnormalized)
                {
                    return unfollowed_if(holds_unnormalized(value));
                }
                if !seen.insert(Rc::as_ptr(function) as usize) {
                    return Ok(());
                }
                function
                    .range
                    .iter()
                    .try_for_each(|value| visit(value, found, seen))
            }
            // `FcnLambdaValue.deepNormalize` normalizes its EXCEPTs' paths and values and its
            // domain.
            Value::Lambda(lambda) => {
                lambda.excepts.iter().try_for_each(|(key, value)| {
                    visit(value, found, seen)?;
                    visit(key, found, seen)
                })?;
                visit(&lambda.domain, found, seen)
            }
            Value::Lazy(lazy) => match &***lazy {
                Lazy::Nat | Lazy::Int | Lazy::Real | Lazy::Strings | Lazy::Any | Lazy::Seq(_) => {
                    Ok(())
                }
                Lazy::Subset(base) | Lazy::Union(base) | Lazy::Filter(base, _) => {
                    visit(base, found, seen)
                }
                Lazy::FunctionSet(left, right)
                | Lazy::Cap(left, right)
                | Lazy::Cup(left, right)
                | Lazy::Diff(left, right) => {
                    visit(left, found, seen)?;
                    visit(right, found, seen)
                }
                Lazy::RecordSet(fields, _) => fields
                    .iter()
                    .try_for_each(|(_, set)| visit(set, found, seen)),
                Lazy::Product(sets) => sets.iter().try_for_each(|set| visit(set, found, seen)),
            },
        }
    }
    let mut found = Vec::new();
    match visit(value, &mut found, &mut HashSet::new()) {
        Ok(()) => {
            found.iter().for_each(normalize);
            Ok(())
        }
        Err(Stop::Failed(error)) => Err(error),
        Err(Stop::Unfollowed) => fail(UNFOLLOWED_PRINT),
    }
}

// Whether TLC's `equals` and `compareTo` of a value with a lazy function force the function: a
// function, tuple or record converts it (`toFcnRcd`), and an integer, string or boolean prints
// it in the failure.
fn forces_compared(value: &Value) -> bool {
    matches!(
        value,
        Value::Function(_) | Value::Int(_) | Value::Str(_) | Value::Bool(_)
    )
}

/// A print of a set of functions, records or tuples TLC expands in the order it builds it, one
/// of whose component sets holds ANY (`print::holds_any_expansion`).
const ANY_EXPANSION_PRINT: &str =
    "printing a set of functions, records or tuples over ANY, which TLC expands as it builds it";
const LAZY_BODY_EFFECTS: &str = "effects in the body of a function TLC keeps lazy (FcnLambdaValue)";

/// The prints, TLCGet reads, TLCSet writes and random draws so far, which tell whether anything
/// had effects between two points.
type Effects = (usize, usize, usize, Option<u64>);

/// A function TLC keeps lazy whose body printed as the evaluator built it: where its first body
/// that printed began and where the function was built.
struct LazyPrint {
    id: u64,
    start: Effects,
    end: Effects,
    function: Rc<Function>,
    /// The LET whose function this is, which TLC holds once.
    origin: Option<Weak<Frame>>,
    /// Whether a print has built a copy of it, which leaves TLC's unforced.
    is_copied: bool,
    /// The thunk whose value it is (`Frame::is_thunk_unforced`), and whether the evaluator built
    /// it again for a later use of the thunk, where TLC holds one function for both.
    thunk: Option<(Weak<Frame>, bool)>,
    /// The keys whose bodies printed.
    keys: Vec<Value>,
}

/// An operation that forces the lazy functions in its arguments (`toFcnRcd`): the number the
/// first lazy function its arguments build takes, and where a print it forced one for printed.
struct Forcing {
    first: u64,
    printed_at: Option<Effects>,
}

/// How an operation forces the lazy functions its arguments hold (`force_lazy_prints`).
#[derive(Clone, Copy)]
enum Force<'v> {
    /// `toFcnRcd` of these arguments, in order.
    Built(&'v [&'v Value]),
    /// A print of a copy of the first value, and of the second, which the operation returns, and
    /// whether the first is written of names of LETs' functions, which nothing else reached.
    Copied(&'v Value, Option<&'v Value>, bool),
    /// `toString` of the value.
    Shown(&'v Value),
}

const BUILT_LET_FUNCTION_EFFECTS: &str =
    "a function a LET defines, used again, whose body has effects TLC has once";

const UNFOLLOWED_PRINT: &str = "a printed value whose normalization the evaluator doesn't follow";

// Whether a value holds a set enumeration TLC holds unnormalized, or one it fails to sort,
// anywhere in it.
fn holds_unnormalized(value: &Value) -> bool {
    fn visit(value: &Value, seen: &mut HashSet<usize>) -> bool {
        match value {
            Value::Null
            | Value::Bool(_)
            | Value::Int(_)
            | Value::Str(_)
            | Value::Model(_)
            | Value::Interval(..) => false,
            Value::Set(set) => {
                seen.insert(Rc::as_ptr(set) as usize)
                    && (unnormalized(value).is_some() || set.iter().any(|value| visit(value, seen)))
            }
            Value::Unsorted(_) => true,
            Value::Lambda(lambda) => {
                visit(&lambda.domain, seen)
                    || lambda
                        .excepts
                        .iter()
                        .any(|(key, value)| visit(key, seen) || visit(value, seen))
            }
            Value::Function(function) => {
                seen.insert(Rc::as_ptr(function) as usize)
                    && function
                        .domain
                        .iter()
                        .chain(&function.range)
                        .any(|value| visit(value, seen))
            }
            Value::Lazy(lazy) => match &***lazy {
                Lazy::Nat | Lazy::Int | Lazy::Real | Lazy::Strings | Lazy::Any => false,
                Lazy::Subset(base)
                | Lazy::Union(base)
                | Lazy::Filter(base, _)
                | Lazy::Seq(base) => visit(base, seen),
                Lazy::FunctionSet(left, right)
                | Lazy::Cap(left, right)
                | Lazy::Cup(left, right)
                | Lazy::Diff(left, right) => visit(left, seen) || visit(right, seen),
                Lazy::RecordSet(fields, _) => fields.iter().any(|(_, set)| visit(set, seen)),
                Lazy::Product(sets) => sets.iter().any(|set| visit(set, seen)),
            },
        }
    }
    visit(value, &mut HashSet::new())
}

// A freshly constructed SetPred over SUBSET has not been converted in TLC. Its
// deepNormalize follows only the base; the enclosing SetDiff then normalizes its right side.
fn normalize_fresh_filter_difference(value: &Value) -> bool {
    let Value::Lazy(diff) = value else {
        return false;
    };
    if diff.java_class != Some(SetClass::Difference) {
        return false;
    }
    let Lazy::Diff(left, right) = &***diff else {
        return false;
    };
    let Value::Lazy(filter) = left else {
        return false;
    };
    if filter.java_class != Some(SetClass::Predicate) {
        return false;
    }
    let Lazy::Filter(base, predicate) = &***filter else {
        return false;
    };
    if predicate.converted().is_some() {
        return false;
    }
    let Value::Lazy(subset) = base else {
        return false;
    };
    if subset.java_class != Some(SetClass::Subset) {
        return false;
    }
    let Lazy::Subset(inner) = &***subset else {
        return false;
    };
    let scalar_set = |value: &Value| {
        matches!(value, Value::Set(set)
        if set.java_class == Some(SetClass::Enumeration)
            && set.iter().all(|value| matches!(value, Value::Int(_) | Value::Bool(_) | Value::Str(_))))
    };
    if !scalar_set(inner) || !scalar_set(right) {
        return false;
    }
    normalize(inner);
    normalize(right);
    true
}

// `Value.deepNormalize`, which Print and PrintT apply to a copy of each value before they print
// it (`TLC.PrintT`): the parts a set TLC keeps lazy holds (`SetCupValue.deepNormalize` its first
// set, then its second), the elements of a set enumeration and the values of a function, tuple
// or record before the set or function itself normalizes, so a set TLC can't normalize fails
// there as the walk first reaches it (`SetEnumValue.normalize`). A value that holds no such set
// walks as nothing. Where the evaluator doesn't know the order TLC walks one in, in a function's
// domain or a lambda, of a record or function with another, or under a lazy set of a physical
// class evaluation lost, the walk claims nothing, and printing the value fails as it does.
// Print normalizes its first argument before its second, so where the walk of one argument claims
// nothing, it claims nothing for the arguments after it either: TLC may fail inside that one.
// Whether the walk knew TLC's order through every value, or claimed nothing from one on.
pub(crate) fn deep_normalize(values: &[Value]) -> Evaluated<bool> {
    enum Walk {
        Failed(EvalError),
        Unknown,
    }
    fn walk(value: &Value) -> Result<(), Walk> {
        if !holds_unsorted_deep(value) {
            return Ok(());
        }
        match value {
            Value::Set(_) => held_order(value)
                .map_err(Walk::Failed)?
                .iter()
                .try_for_each(walk),
            Value::Unsorted(elements) => {
                elements.iter().try_for_each(walk)?;
                Err(Walk::Failed(unsorted_failure(elements)))
            }
            Value::Function(function) => {
                let class = function.class.get();
                if class == Class::Lambda
                    || function.domain.iter().any(holds_unsorted_deep)
                    || (class != Class::Tuple
                        && function
                            .range
                            .iter()
                            .filter(|value| holds_unsorted_deep(value))
                            .count()
                            > 1)
                {
                    return Err(Walk::Unknown);
                }
                function.range.iter().try_for_each(walk)
            }
            Value::Lazy(lazy) => {
                if !crate::value::has_java_set_representation(value) {
                    return Err(Walk::Unknown);
                }
                match &lazy.construction {
                    Lazy::Cap(left, right) | Lazy::Cup(left, right) | Lazy::Diff(left, right) => {
                        walk(left)?;
                        walk(right)
                    }
                    Lazy::Subset(base) | Lazy::Union(base) | Lazy::Filter(base, _) => walk(base),
                    Lazy::FunctionSet(domain, range) => {
                        walk(domain)?;
                        walk(range)
                    }
                    Lazy::Product(factors) => factors.iter().try_for_each(walk),
                    Lazy::RecordSet(fields, _) => fields.iter().try_for_each(|(_, set)| walk(set)),
                    _ => Err(Walk::Unknown),
                }
            }
            _ => Err(Walk::Unknown),
        }
    }
    for value in values {
        match walk(value) {
            Ok(()) => {}
            Err(Walk::Failed(error)) => return Err(error),
            Err(Walk::Unknown) => return Ok(false),
        }
    }
    Ok(true)
}

// `FcnParams.size` of a function constructor's domains, which `toFcnRcd` counts before it
// enumerates any: each domain's `size` in order, which normalizes a set enumeration and fails
// where TLC can't sort it, even past an empty domain the enumeration stops at; and past 2^31 - 1
// elements an overflow, whose message prints every domain (`FcnParams.toString`), normalizing
// each in order, so it fails on the first TLC can't sort. A set enumeration fails as its
// `elements` does where `is_comparing`, and as its `normalize` alone otherwise. `Ok(true)` where
// it counted them all, `Ok(false)` where the evaluator doesn't follow the count: a domain neither
// a set nor an interval, one that sorts though held unsorted, or an overflow where no domain
// fails to print or one holds a set TLC can't sort, which printing may meet first. `is_enumerated`
// stays true while a failure would be at a domain the enumeration of the domains in order also
// reaches: none before it empty, too large to build or overflowing the count.
fn count_domains(sets: &[Value], is_comparing: bool, is_enumerated: &mut bool) -> Evaluated<bool> {
    let normalize = |set: &Value| -> Evaluated<Option<usize>> {
        match set {
            Value::Unsorted(items) if !is_comparing => {
                match crate::value::normalize_unsorted_failure(items) {
                    Some(failure) => Err(failure),
                    None => Ok(None),
                }
            }
            Value::Set(_) | Value::Unsorted(_) => Ok(Some(elements(set)?.len())),
            _ => Ok(None),
        }
    };
    let mut size: i64 = 1;
    for (index, set) in sets.iter().enumerate() {
        let count = match set {
            Value::Interval(low, high, _) => {
                if i64::from(*high) - i64::from(*low) >= crate::value::MAXIMUM_INTERVAL as i64 {
                    *is_enumerated = false;
                }
                crate::value::interval_size(*low, *high)?
            }
            Value::Set(_) | Value::Unsorted(_) => match normalize(set)? {
                Some(count) => count,
                None => return Ok(false),
            },
            _ => return Ok(false),
        };
        if count == 0 {
            *is_enumerated = false;
        }
        size = size.saturating_mul(i64::try_from(count).unwrap_or(i64::MAX));
        if size > i64::from(i32::MAX) {
            *is_enumerated = false;
            if sets.iter().any(|set| {
                set.set_items()
                    .is_some_and(|items| items.iter().any(holds_unsorted_deep))
            }) {
                return Ok(false);
            }
            for set in &sets[index + 1..] {
                match set {
                    Value::Interval(..) => {}
                    Value::Set(_) | Value::Unsorted(_) => {
                        if normalize(set)?.is_none() {
                            return Ok(false);
                        }
                    }
                    _ => return Ok(false),
                }
            }
            return Ok(false);
        }
    }
    Ok(true)
}

// A failure `count_domains` found that TLC words, or none.
fn worded_failure(counted: Evaluated<bool>) -> Option<EvalError> {
    counted.err().filter(|failure| failure.message.is_some())
}

// Whether a value holds a set TLC can't normalize anywhere in it.
fn holds_unsorted_deep(value: &Value) -> bool {
    match value {
        Value::Unsorted(_) => true,
        Value::Set(elements) => elements.iter().any(holds_unsorted_deep),
        Value::Function(function) => function
            .domain
            .iter()
            .chain(&function.range)
            .any(holds_unsorted_deep),
        Value::Lazy(lazy) => match &lazy.construction {
            Lazy::Cap(left, right)
            | Lazy::Cup(left, right)
            | Lazy::Diff(left, right)
            | Lazy::FunctionSet(left, right) => {
                holds_unsorted_deep(left) || holds_unsorted_deep(right)
            }
            Lazy::Subset(base) | Lazy::Union(base) | Lazy::Filter(base, _) | Lazy::Seq(base) => {
                holds_unsorted_deep(base)
            }
            Lazy::Product(factors) => factors.iter().any(holds_unsorted_deep),
            Lazy::RecordSet(fields, _) => fields.iter().any(|(_, set)| holds_unsorted_deep(set)),
            Lazy::Nat | Lazy::Int | Lazy::Real | Lazy::Strings | Lazy::Any => false,
        },
        Value::Lambda(lambda) => {
            holds_unsorted_deep(lambda.domain())
                || lambda
                    .excepts
                    .iter()
                    .any(|(path, value)| holds_unsorted_deep(path) || holds_unsorted_deep(value))
        }
        _ => false,
    }
}

// Whether a printed value's expansion, after `deepNormalize`, is one whose first failure the
// evaluator finds as TLC does: a value that holds no lazy set, a set of tuples, records or
// functions or a SUBSET of sets that hold none, or a union of such sets.
fn is_followed_expansion(value: &Value) -> bool {
    fn is_plain(value: &Value) -> bool {
        match value {
            Value::Lazy(_) | Value::Lambda(_) | Value::Null => false,
            Value::Set(set) | Value::Unsorted(set) => set.iter().all(is_plain),
            Value::Function(function) => {
                function.domain.iter().chain(&function.range).all(is_plain)
            }
            _ => true,
        }
    }
    fn is_part(value: &Value) -> bool {
        match value {
            Value::Lazy(lazy) => match &***lazy {
                Lazy::Subset(base) => is_plain(base),
                Lazy::Product(factors) => factors.iter().all(is_plain),
                Lazy::FunctionSet(domain, range) => is_plain(domain) && is_plain(range),
                Lazy::RecordSet(fields, _) => fields.iter().all(|(_, set)| is_plain(set)),
                _ => false,
            },
            _ => is_plain(value),
        }
    }
    match value {
        Value::Lazy(lazy) => match &***lazy {
            Lazy::Cup(left, right) => is_part(left) && is_part(right),
            _ => is_part(value),
        },
        _ => is_plain(value),
    }
}

/// TLC's `enumBound`: the most elements a lazy set's text is expanded to.
const ENUM_BOUND: i64 = 2000;

// What `toString(sb, offset, false)` fails with, where it expands a lazy set: the sizes of its
// parts, and its elements where there are fewer than `enumBound`, through the values it holds.
// The evaluator declines a lazy set it doesn't follow there.
/// `deepNormalize` of the copy PrintT prints (`TLC.PrintT`), where the value is a set of
/// tuples, functions or records TLC keeps lazy, built of sets each of which is a set
/// enumeration of scalars, an interval or a set enumeration TLC holds as written: it normalizes
/// each part in turn (`SetOfTuplesValue.deepNormalize`, `SetOfFcnsValue.deepNormalize`,
/// `SetOfRcdsValue.deepNormalize`), and so fails at the first written one whose elements don't
/// compare, even where an empty part spares it the printing.
fn normalize_printed_parts(value: &Value) -> Evaluated<()> {
    let Value::Lazy(lazy) = value else {
        return Ok(());
    };
    if lazy.is_overridden() {
        return Ok(());
    }
    let parts: Vec<&Value> = match &***lazy {
        Lazy::Product(factors) => factors.iter().collect(),
        Lazy::FunctionSet(domain, range) => vec![domain, range],
        Lazy::RecordSet(fields, _) => fields.iter().map(|(_, set)| set).collect(),
        _ => return Ok(()),
    };
    let is_scalar = |value: &Value| matches!(value, Value::Int(_) | Value::Bool(_) | Value::Str(_));
    let is_plain = |part: &Value| match part {
        Value::Set(elements) | Value::Unsorted(elements) => elements.iter().all(is_scalar),
        Value::Interval(..) => true,
        _ => false,
    };
    if !parts.iter().all(|part| is_plain(part)) {
        return Ok(());
    }
    for part in parts {
        if let Value::Unsorted(elements) = part {
            return Err(unsorted_failure(elements));
        }
    }
    Ok(())
}

/// Where TLC's `toStringUnchecked` of a value fails (`toString` without swallowing).
pub(crate) fn check_unchecked(value: &Value) -> Evaluated<()> {
    check_to_string(value, false)
}

/// Where TLC's `toString(sb, offset, swallow)` of a value fails, class by class. A lazy set that
/// expands itself to print (`TLCGlobals.expand`) swallows its expansion's failure where
/// `swallow` asks and prints its operation instead, but a `UnionValue`, which catches nothing, and
/// a `SubsetValue` of a base under 7 elements, which expands outside its catch. A function TLC
/// keeps lazy swallows whatever building it throws, and prints each domain with `Value.toString`,
/// which swallows (`FcnLambdaValue.toString`, `FcnParams.toString`).
pub(crate) fn check_to_string(value: &Value, swallow: bool) -> Evaluated<()> {
    let check = |value: &Value| check_to_string(value, swallow);
    match value {
        Value::Set(elements) => elements.iter().try_for_each(check),
        // `SetEnumValue.toString` normalizes the set first.
        Value::Unsorted(elements) => Err(unsorted_failure(elements)),
        Value::Function(function) => function
            .domain
            .iter()
            .chain(&function.range)
            .try_for_each(check),
        Value::Lambda(lambda) => match &lambda.params {
            None => check_to_string(lambda.domain(), true),
            Some(groups) => groups
                .iter()
                .try_for_each(|(_, _, domain)| check_to_string(domain, true)),
        },
        Value::Lazy(lazy) => {
            // What the set prints where its expansion failed and `swallow` swallowed it.
            let operation = || -> Evaluated<()> {
                match &***lazy {
                    Lazy::Cap(left, right) | Lazy::Cup(left, right) | Lazy::Diff(left, right) => {
                        check(left)?;
                        check(right)
                    }
                    // `SetPredValue.toString` concatenates its set's `toString`.
                    Lazy::Filter(base, _) => check_to_string(base, true),
                    Lazy::FunctionSet(domain, range) => {
                        check(domain)?;
                        check(range)
                    }
                    Lazy::RecordSet(fields, _) => fields.iter().try_for_each(|(_, set)| check(set)),
                    Lazy::Product(factors) => factors.iter().try_for_each(check),
                    _ => Ok(()),
                }
            };
            let swallowed = |error: EvalError| if swallow { operation() } else { Err(error) };
            let size = match &***lazy {
                // `Sequences.toString` of Seq(S) prints `Seq(` and S's text, which a set
                // enumeration TLC can't normalize fails to write (`SetEnumValue.toString`).
                Lazy::Seq(base) => return check(base),
                _ if lazy.is_overridden() => return Ok(()),
                // `UnionValue.toString` expands the union outside of any catch.
                Lazy::Union(_) => return elements(value)?.iter().try_for_each(check),
                // `SetCupValue.toString` and its siblings print the set they expand into within
                // their catch, which would leave its text half written where that fails.
                Lazy::Cap(..) | Lazy::Cup(..) | Lazy::Diff(..) | Lazy::Filter(..) => {
                    return match elements(value) {
                        Ok(expanded) => match expanded.iter().try_for_each(check) {
                            Err(error) if swallow => fail(format!(
                                "a lazy set whose expansion fails to print, which TLC swallows: {}",
                                error.reason
                            )),
                            printed => printed,
                        },
                        Err(error) => swallowed(error),
                    };
                }
                // `SubsetValue.toString`: expanded, outside its catch, where its base has fewer
                // than 7 elements, and otherwise `SUBSET` its base.
                Lazy::Subset(base) => {
                    return match cardinality(base) {
                        Ok(size) if size < 7 => elements(value)?.iter().try_for_each(check),
                        Ok(_) => check(base),
                        Err(_) if swallow => check(base),
                        Err(error) => Err(error),
                    };
                }
                // `SetOfRcdsValue.toString` and `SetOfTuplesValue.toString`.
                Lazy::RecordSet(fields, _) => parts_size(fields.iter().map(|(_, set)| set)),
                Lazy::Product(factors) => parts_size(factors.iter()),
                // `SetOfFcnsValue.toString`.
                Lazy::FunctionSet(domain, range) => (|| {
                    if is_empty(domain)? {
                        return Ok(1);
                    }
                    let domain = printed_size(domain)?;
                    let range = printed_size(range)?;
                    let mut size: i64 = 1;
                    // The loop has no observations after the two size calls. Zero and one
                    // ranges reach fixed points, even for a very large domain.
                    if domain > 0 && (range == 0 || range == 1) {
                        size = range;
                    } else {
                        for _ in 0..domain {
                            if size > i64::from(i32::MAX) {
                                break;
                            }
                            size = size.saturating_mul(range);
                        }
                    }
                    Ok(size)
                })(),
                _ => return fail("ToString of a lazy set"),
            };
            let size = match size {
                Ok(size) => size,
                Err(error) => return swallowed(error),
            };
            if size >= ENUM_BOUND {
                return operation();
            }
            // `elements` asks each part whether it is empty, up to an empty one, before it
            // enumerates any (`Value.isEmpty`), which fails on a part that isn't a set.
            let expanded = (|| {
                let is_empty_set = match &***lazy {
                    Lazy::RecordSet(fields, _) => parts_empty(fields.iter().map(|(_, set)| set))?,
                    Lazy::Product(factors) => parts_empty(factors.iter())?,
                    Lazy::FunctionSet(domain, range) => !is_empty(domain)? && is_empty(range)?,
                    _ => false,
                };
                if is_empty_set {
                    Ok(None)
                } else {
                    elements(value).map(Some)
                }
            })();
            match expanded {
                // The set it expands into prints outside the catch.
                Ok(Some(expanded)) => expanded.iter().try_for_each(check),
                Ok(None) => Ok(()),
                Err(error) => swallowed(error),
            }
        }
        _ => Ok(()),
    }
}

// The product of the parts' sizes, past an int no further, and 0 from an empty part on.
fn parts_size<'v>(parts: impl Iterator<Item = &'v Value>) -> Evaluated<i64> {
    let mut size: i64 = 1;
    for part in parts {
        let part = printed_size(part)?;
        if part == 0 {
            return Ok(0);
        }
        if size <= i64::from(i32::MAX) {
            size = size.saturating_mul(part);
        }
    }
    Ok(size)
}

// Whether a part is empty, asking each in turn up to an empty one.
fn parts_empty<'v>(mut parts: impl Iterator<Item = &'v Value>) -> Evaluated<bool> {
    parts.try_fold(false, |is_empty_set, part| {
        Ok(is_empty_set || is_empty(part)?)
    })
}

// A part's `size` as TLC's `toString` of a set of functions, records or tuples asks it: a
// function's, tuple's or record's number of keys, one TLC keeps lazy its domain's
// (`FcnLambdaValue.size`), a set's number of elements, and a failure for any other value
// (`IntValue.size` and its siblings).
fn printed_size(part: &Value) -> Evaluated<i64> {
    let kind = match part {
        Value::Function(function) => return Ok(function.domain.len() as i64),
        Value::Lambda(lambda) => return Ok(cardinality(lambda.domain())? as i64),
        Value::Int(_) => "integer",
        Value::Bool(_) => "boolean",
        Value::Str(_) => "string",
        Value::Model(_) => "model value",
        _ => return Ok(cardinality(part)? as i64),
    };
    fail_runtime(
        "sized a value that isn't a set",
        format!(
            "Attempted to compute the number of elements in the {kind} {}.",
            format_pretty(part)
        ),
    )
}

/// `EC.TLC_MODULE_COMPUTING_CARDINALITY`.
const COMPUTING_CARDINALITY: u32 = 2181;
const MODULE_OVERFLOW: u32 = 2178;
const NULL_POWER_NULL: u32 = 2180;
const IS_FINITE_SET: &str =
    "public static tlc2.value.IBoolValue tlc2.module.FiniteSets.IsFiniteSet(tlc2.value.impl.Value)";
const TEXT_SERIALIZE: &str = "public static synchronized tlc2.value.impl.Value tlc2.module.Json.textSerialize(tlc2.tool.impl.Tool,tla2sany.semantic.ExprOrOpArgNode[],tlc2.util.Context,tlc2.tool.TLCState,tlc2.tool.TLCState,int,tlc2.tool.coverage.CostModel)";

struct CacheNode {
    strong: usize,
    incoming: usize,
    edges: Vec<usize>,
}

#[derive(Default)]
struct CacheGraph(HashMap<usize, CacheNode>);

impl CacheGraph {
    fn add<T>(&mut self, parent: Option<usize>, value: &Rc<T>) -> (usize, bool) {
        let key = Rc::as_ptr(value) as usize;
        if let Some(parent) = parent {
            self.0
                .get_mut(&parent)
                .expect("a visited parent")
                .edges
                .push(key);
        }
        let is_new = !self.0.contains_key(&key);
        let node = self.0.entry(key).or_insert_with(|| CacheNode {
            strong: Rc::strong_count(value),
            incoming: 0,
            edges: Vec::new(),
        });
        node.incoming += usize::from(parent.is_some());
        (key, is_new)
    }

    fn context(&mut self, parent: usize, context: &Context) {
        if let Some(frame) = &context.env.0 {
            self.frame(Some(parent), frame);
        }
        if let Some(value) = &context.at {
            self.value(parent, value);
        }
    }

    fn state(&mut self, parent: usize, state: &[Option<Value>]) {
        for value in state.iter().flatten() {
            self.value(parent, value);
        }
    }

    fn frame(&mut self, parent: Option<usize>, frame: &Rc<Frame>) {
        let (key, is_new) = self.add(parent, frame);
        if !is_new {
            return;
        }
        if let Some(parent) = &frame.parent.0 {
            self.frame(Some(key), parent);
        }
        match &frame.binding {
            Binding::Value(value) => self.value(key, value),
            Binding::Thunk { context, .. } | Binding::Function { context, .. } => {
                self.context(key, context)
            }
            Binding::Operator(operator) => {
                let (operator_key, is_new) = self.add(Some(key), operator);
                if is_new {
                    self.context(operator_key, &operator.context);
                }
            }
        }
        if let Some(cached) = frame.cached.borrow().as_ref() {
            self.value(key, &cached.value);
            self.state(key, &cached.current);
            self.state(key, &cached.next);
        }
    }

    fn value(&mut self, parent: usize, value: &Value) {
        match value {
            Value::Null => {}
            Value::Set(set) | Value::Unsorted(set) => {
                let (key, is_new) = self.add(Some(parent), set);
                if is_new {
                    let (key, is_new) = self.add(Some(key), &set.elements);
                    if is_new {
                        for value in set.elements.iter() {
                            self.value(key, value);
                        }
                    }
                }
            }
            Value::Function(function) => {
                let (key, is_new) = self.add(Some(parent), function);
                if is_new {
                    for value in function.domain.iter().chain(&function.range) {
                        self.value(key, value);
                    }
                }
            }
            Value::Lambda(lambda) => {
                let (key, is_new) = self.add(Some(parent), lambda);
                if is_new {
                    self.context(key, &lambda.context);
                    self.value(key, &lambda.domain);
                    self.state(key, &lambda.current);
                    self.state(key, &lambda.next);
                    for (domain, range) in &lambda.excepts {
                        self.value(key, domain);
                        self.value(key, range);
                    }
                }
            }
            Value::Lazy(lazy) => {
                let (key, is_new) = self.add(Some(parent), lazy);
                if !is_new {
                    return;
                }
                match &lazy.construction {
                    Lazy::Subset(value) | Lazy::Seq(value) | Lazy::Union(value) => {
                        self.value(key, value)
                    }
                    Lazy::FunctionSet(left, right)
                    | Lazy::Cap(left, right)
                    | Lazy::Cup(left, right)
                    | Lazy::Diff(left, right) => {
                        self.value(key, left);
                        self.value(key, right);
                    }
                    Lazy::RecordSet(fields, _) => {
                        for (_, value) in fields {
                            self.value(key, value);
                        }
                    }
                    Lazy::Product(values) => {
                        for value in values {
                            self.value(key, value);
                        }
                    }
                    Lazy::Filter(domain, predicate) => {
                        self.value(key, domain);
                        let (key, is_new) = self.add(Some(key), predicate);
                        if is_new {
                            self.context(key, &predicate.context);
                            self.state(key, &predicate.current);
                            self.state(key, &predicate.next);
                            if let Some(values) = &predicate.filtered {
                                let (key, is_new) = self.add(Some(key), values);
                                if is_new {
                                    for value in values.iter() {
                                        self.value(key, value);
                                    }
                                }
                            }
                            if let Some(values) = predicate.converted.borrow().as_ref() {
                                let (key, is_new) = self.add(Some(key), values);
                                if is_new {
                                    for value in values.iter() {
                                        self.value(key, value);
                                    }
                                }
                            }
                        }
                    }
                    Lazy::Nat | Lazy::Int | Lazy::Real | Lazy::Strings | Lazy::Any => {}
                }
            }
            Value::Bool(_)
            | Value::Int(_)
            | Value::Interval(..)
            | Value::Str(_)
            | Value::Model(_) => {}
        }
    }
}

impl Drop for Evaluator<'_> {
    fn drop(&mut self) {
        for frame in self
            .cached_frames
            .drain(..)
            .filter_map(|frame| frame.upgrade())
        {
            let mut cached = frame.cached.borrow_mut();
            if cached
                .as_ref()
                .is_some_and(|value| Rc::ptr_eq(&value.evaluator, &self.identity))
            {
                cached.take();
            }
        }
    }
}

impl<'ir> Evaluator<'ir> {
    fn collect_cached_frames(&mut self) {
        let mut seen = HashSet::new();
        let frames: Vec<_> = self
            .cached_frames
            .iter()
            .filter_map(Weak::upgrade)
            .filter(|frame| seen.insert(Rc::as_ptr(frame) as usize))
            .collect();
        let mut graph = CacheGraph::default();
        for frame in &frames {
            graph.frame(None, frame);
        }
        let mut reachable = HashSet::new();
        let mut pending: Vec<_> = graph
            .0
            .iter()
            .filter_map(|(&key, node)| {
                let held = usize::from(seen.contains(&key));
                (node.strong > node.incoming + held).then_some(key)
            })
            .collect();
        while let Some(key) = pending.pop() {
            if reachable.insert(key) {
                pending.extend(&graph.0[&key].edges);
            }
        }
        for frame in &frames {
            if !reachable.contains(&(Rc::as_ptr(frame) as usize)) {
                let mut cached = frame.cached.borrow_mut();
                if cached
                    .as_ref()
                    .is_some_and(|value| Rc::ptr_eq(&value.evaluator, &self.identity))
                {
                    cached.take();
                }
            }
        }
    }

    pub fn new(ir: &'ir Ir) -> Evaluator<'ir> {
        let ranks = (0..ir.ranked_count)
            .map(|rank| (ir.get_text_units(rank).into(), rank as i32))
            .collect();
        let width = ir.variables.len();
        Evaluator {
            substituted_nodes: None,
            copy_frames: None,
            closed_java_context: ir
                .builtins
                .iter()
                .any(|builtin| builtin.flags & Builtin::CLOSED_JAVA_CONTEXT != 0),
            state_builtins: &[],
            is_level_bound: false,
            level_bounds: HashMap::new(),
            lexical_recursions: HashMap::new(),
            ir,
            texts: vec![None; ir.texts.len()],
            literals: HashMap::new(),
            ranks,
            startup_ranked: None,
            constants: vec![None; ir.values.list.len()],
            configured_values: HashMap::new(),
            cache: HashMap::new(),
            failed_startup: HashSet::new(),
            uncomputed_warning_startup: HashSet::new(),
            is_startup_known: false,
            searched_failing: HashSet::new(),
            searched_limited: HashSet::new(),
            searched_unwarned: HashSet::new(),
            varying_tlc_gets: 0,
            searched_printed: HashMap::new(),
            searched_effects: HashMap::new(),
            searched_unworded: HashSet::new(),
            startup_limit: None,
            chosen: HashMap::new(),
            current: vec![None; width],
            next: vec![None; width],
            reads: 0,
            captures: 0,
            identity: Rc::new(()),
            cached_frames: Vec::new(),
            level: 0,
            next_level: None,
            printed: Vec::new(),
            has_uninitialized_literals: ir
                .builtins
                .iter()
                .any(|builtin| builtin.flags & Builtin::UNINITIALIZED_LITERAL != 0),
            target: None,
            is_enabling: false,
            walked_application: None,
            call_stack: None,
            choices: Vec::new(),
            random: None,
            runtime: None,
            registers: Registers::default(),
            register_writes: 0,
            is_continued_failure: false,
            except_selected: None,
            is_except_placed: false,
            is_enumerator_placed: false,
            is_initial_walk: false,
            lazy_unions: 0,
            print_normalizations: (0, String::new()),
            failed_startup_uses: 0,
            kept_lazy: HashSet::new(),
            held_lazy_domains: HashMap::new(),
            lazy_domain_sets: HashMap::new(),
            lazy_domains: 0,
            unfollowed_constructions: 0,
            lazy_body_effects: 0,
            printing_values: 0,
            unfollowed_print_normalizations: 0,
            normalized_print_failure: None,
            register_reads: 0,
            is_tool: None,
            is_assumption: false,
            is_checking_assumption: false,
            is_in_assumptions: false,
            copies_filters: false,
            trace: None,
            workers: None,
            is_simulation: false,
            reads_files: false,
            made_paths: None,
            asserting: 0,
            is_starting: false,
            is_processing_constants: false,
            kept_at_startup: HashMap::new(),
            // Any evaluator of the model may print a value another built, so each counts the
            // install read wherever the model names "config".
            is_install_read: ir.may_read_tlc_get("config"),
            printed_subset: false,
            printed_subset_base: None,
            keeping_lazy: 0,
            builds_unsorted_domains: false,
            is_lazy_body_failure_worded: false,
            preserves_lazy_domain: false,
            in_place_functions: Vec::new(),
            declines_unsorted_bound: false,
            lazy_prints: Vec::new(),
            lazy_print_count: 0,
            forcing: None,
            lazy_print_start: None,
            lazy_print_keys: Vec::new(),
            cache_control_primed: false,
            once_named: None,
            unshared: None,
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

    /// A text a string operator makes, which TLC interns: ranked as it is made while the evaluator
    /// ranks texts (`rankString`, for the strings TLC makes as it starts).
    fn made_text(&mut self, units: Box<[u16]>) -> Rc<Text> {
        self.rank_record_fields();
        self.rank_made(&units);
        self.text_of(units)
    }

    fn rank_made(&mut self, units: &[u16]) {
        if let Some(ranked) = &mut self.startup_ranked
            && !self.ranks.contains_key(units)
        {
            self.ranks.insert(units.into(), self.ranks.len() as i32);
            ranked.push(units.into());
        }
    }

    // RecordValue's field names, which TLC interns as it builds its first record, where the
    // evaluator has built one since it last looked.
    fn rank_record_fields(&mut self) {
        if self.startup_ranked.is_some() && take_is_record_built() {
            for field in RECORD_VALUE_FIELDS {
                self.rank_made(&field.encode_utf16().collect::<Vec<u16>>());
            }
        }
    }

    /// Ranks what the evaluator makes from now on, as TLC interns it.
    pub(crate) fn start_ranking(&mut self) {
        take_is_record_built();
        self.startup_ranked = Some(Vec::new());
    }

    pub(crate) fn stop_ranking(&mut self) {
        self.startup_ranked = None;
    }

    /// A field name of the records TLC builds of its counterexample (`RecordValue`'s statics):
    /// interned as its class loads, after the spec's strings, in the order declared, unless the
    /// spec has the string. Where TLC dumps the trace (`is_dumped`), the trace modules it parses
    /// after the spec's (`_TLCTrace.tla`, `_JsonTrace.tla`) intern `state`, `vars` and
    /// `counterexample`, in that order, before SANY's semantic prelude, whose first text the IR
    /// ranks; `action` they write as a string, which TLC interns as it runs.
    pub(crate) fn counterexample_field(&self, name: &str, is_dumped: bool) -> Rc<Text> {
        const PARSED: [&str; 3] = ["state", "vars", "counterexample"];
        let units: Box<[u16]> = name.encode_utf16().collect();
        if let Some(&rank) = self.ranks.get(&units) {
            return Rc::new(Text { units, rank });
        }
        // Ranks of the prelude's texts, which no field is compared with, may be shared.
        let prelude: Box<[u16]> = "$$InAssume".encode_utf16().collect();
        let parsed = PARSED.iter().position(|field| *field == name);
        if let (true, Some(position), Some(&prelude)) =
            (is_dumped, parsed, self.ranks.get(&prelude))
        {
            return Rc::new(Text {
                units,
                rank: prelude + position as i32,
            });
        }
        let last = self.ranks.values().copied().max().unwrap_or(-1);
        let fields = if is_dumped { &PARSED[..] } else { &[] };
        let position = fields
            .iter()
            .chain(&RECORD_VALUE_FIELDS)
            .position(|field| *field == name);
        let rank = position.map_or(-1, |position| last + 1 + position as i32);
        Rc::new(Text { units, rank })
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

    // Whether a LET is the front end's of a selection with arguments, which defines only the
    // selected operator, by a name no module can write.
    pub(crate) fn is_selection_let(&self, node: NodeId) -> bool {
        matches!(self.kind(node), NodeKind::Let { definitions, .. }
            if matches!(definitions.as_slice(), [definition]
                if self.name(self.definition(*definition).name) == SELECTION_NAME))
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

    // Configuration assignments have a distinct producer: ModelConfig.parseValue constructs
    // every set as SetEnumValue. Other reads of the same transfer-pool entry lack that proof.
    fn configuration_value(&mut self, index: u32) -> Evaluated<Value> {
        if let Some(value) = self.configured_values.get(&index) {
            return Ok(value.clone());
        }
        let value = self.value(index)?;
        let value = configuration_literal(&value).unwrap_or(value);
        self.configured_values.insert(index, value.clone());
        Ok(value)
    }

    fn convert(&mut self, value: &tla_ir::Value) -> Evaluated<Value> {
        let class = |class: i32| match class {
            1 => Class::Lambda,
            2 => Class::Tuple,
            3 => Class::Record,
            _ => Class::Plain,
        };
        let converted = match value {
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
        };
        if let Value::Function(function) = &converted {
            function.java_class.set(None);
            function.is_counter_example.set(None);
        }
        Ok(match converted {
            Value::Set(set) => Value::set_from_rc(Rc::clone(&set.elements), None),
            other => other,
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
            Some(None) if self.cache_control_primed && !self.is_enabling && !self.is_174() => {
                fail_with(
                    "variable not assigned",
                    TlcMessage {
                        text: format!(
                            "The action formula A appearing in a WF_v(A) or SF_v(A) operator does not specify the primed value of the variable {} occurring in the state formula v.\n",
                            self.name(name.text)
                        ),
                        code: Some(2148),
                        is_eval_exception: false,
                        inner: None,
                    },
                )
            }
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
                    inner: None,
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

    // `Tool.getInitStatesAppl` uses an uncoded Assert.fail for its built-in
    // default branch; an operator value and an already-assigned remainder use 2247.
    fn is_init_builtin_guard(&self, node: NodeId) -> bool {
        match self.kind(node) {
            NodeKind::SetEnumeration(_)
            | NodeKind::SetFilter { .. }
            | NodeKind::SetMap { .. }
            | NodeKind::Tuple(_)
            | NodeKind::FunctionConstruction { .. }
            | NodeKind::FunctionSet { .. }
            | NodeKind::Record(_)
            | NodeKind::RecordSet(_)
            | NodeKind::Except { .. }
            | NodeKind::FieldAccess { .. }
            | NodeKind::Product(_)
            | NodeKind::Choose { .. } => true,
            NodeKind::Apply { name, .. }
                if !name.is_local && matches!(name.resolution, Resolution::Builtin(_)) =>
            {
                matches!(
                    self.name(name.text),
                    "SUBSET" | "UNION" | "DOMAIN" | "\\cup" | "\\cap" | "\\"
                )
            }
            _ => false,
        }
    }

    // What TLC computes in a walk: "initial states", "next states" or "ENABLED".
    pub(crate) fn computing(&self, is_init: bool) -> &'static str {
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
            (Demand::Filter, Some(kind)) => {
                let Some(predicate) = self.describe_node(node) else {
                    return fail(reason);
                };
                format!(
                    "Attempted to evaluate an expression of form {{x \\in S : P(x)}} when P was {kind}.\n{predicate}"
                )
            }
            // `Tool.evalAppl` names neither the value nor its kind (`OPCODE_sa`).
            (Demand::SquareAction(square), _) => format!(
                "Attempted to evaluate an expression of form [A]_e, but A was not a boolean.\n{}",
                self.describe_range(square)
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
                        code: if matches!(demand, Demand::Guard { is_init: true })
                            && !self.is_enabling
                            && self.is_init_builtin_guard(node)
                        {
                            None
                        } else {
                            Some(EXPECTED_EXPRESSION_IN_COMPUTING)
                        },
                        is_eval_exception: false,
                        inner: None,
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
                        inner: None,
                    },
                );
            }
            (Demand::Invariant | Demand::Quantifier(_), _) => {
                let written_node = match demand {
                    Demand::Quantifier(quantifier) => quantifier,
                    _ => node,
                };
                let Some(written) = self.describe_node(written_node) else {
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
                        inner: None,
                    },
                );
            }
            _ => return fail(reason),
        };
        fail_runtime(reason, text)
    }

    /// The text of the expression a lazy value prints where it doesn't evaluate it (`<expression
    /// ...>` of `FcnLambdaValue.toString` and `SetPredValue.toString`): SANY's `toString` of the
    /// node, which is a numeral's image.
    fn expression_text(&self, node: NodeId) -> Evaluated<String> {
        if let Some(text) = self.describe_node(node) {
            return Ok(text);
        }
        // A decimal's `DecimalNode.toString`, its integral and fractional parts as written.
        let resolved = &self.ir.nodes.arena[self.resolved(node) as usize];
        if let (NodeKind::Decimal(text), Some(range)) = (&resolved.kind, resolved.range) {
            let written = &self.ir.texts[*text as usize];
            if range.start_line == range.end_line
                && usize::try_from(range.end_column - range.start_column + 1).ok()
                    == Some(written.len())
            {
                return Ok(written.to_string());
            }
        }
        // A node SANY didn't parse has no image, and is named by its place as any other.
        if self.ir.nodes.arena[self.resolved(node) as usize]
            .range
            .is_none()
        {
            return Ok(self.describe_range(node));
        }
        fail("a lazy value's expression written as a numeral the evaluator can't word")
    }

    /// A node as SANY's `toString` gives it in TLC's messages: a numeral as written, any other
    /// node by its place. `None` for a numeral whose node doesn't span its image, or a decimal.
    pub fn describe_node(&self, node: NodeId) -> Option<String> {
        let id = self.resolved(node);
        let resolved = &self.ir.nodes.arena[id as usize];
        let written = match &resolved.kind {
            // A numeral written otherwise than its value in decimal, as written.
            NodeKind::Number(_) if let Some(&image) = self.ir.nodes.numerals.get(&id) => {
                self.ir.texts[image as usize].to_string()
            }
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
        let scalar_state = self
            .current
            .iter()
            .chain(&self.next)
            .flatten()
            .all(|value| {
                matches!(
                    value,
                    Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::Model(_)
                )
            })
            && self
                .call_stack
                .as_ref()
                .is_some_and(|stack| !stack.is_frozen);
        // A use of an INSTANCE's substitute where the instantiated module names the declaration:
        // `CallStackTool` evaluates the declaration's node there, in a frame of its own, which
        // looks up the `LazyValue` its `SubstInNode` bound and evaluates the substitute in turn.
        let written = &self.ir.nodes.arena[node as usize];
        if let NodeKind::Reference(target) = written.kind
            && written.range.is_some()
        {
            return self.in_frame(StackFrame::Node(node), &mut |evaluator| {
                evaluator.evaluate(target, context)
            });
        }
        let (node, _) = self.node(node);
        // SANY makes a selection with arguments, as `V(1)!L`, one application of a LAMBDA, the
        // frame TLC's call stack holds; the front end writes it as a LET of that operator around
        // its application at the same place, whose LET is no node of TLC's.
        let mut result = if self.is_selection_let(node) {
            self.evaluate_node(node, context)
        } else {
            self.in_frame(StackFrame::Node(node), &mut |evaluator| {
                evaluator.evaluate_node(node, context)
            })
        };
        if let Ok(Value::Lazy(lazy)) = &result
            && let Lazy::Filter(base, predicate) = &***lazy
            && predicate.is_untraced
        {
            result = Ok(Value::lazy_with_class(
                Lazy::Filter(base.clone(), Rc::new(predicate.retraced())),
                lazy.java_class,
            ));
        }
        if let Some(stack) = &mut self.call_stack {
            if result.is_err() {
                stack.scalar_state_at_value_failure = Some(
                    stack.scalar_state_at_value_failure.unwrap_or(true)
                        && scalar_state
                        && self.captures == 0,
                );
            } else if stack.is_frozen
                || matches!(&result, Ok(Value::Lazy(lazy))
                    if lazy.java_class != Some(SetClass::Overridden))
            {
                // A caught error or deferred normalization can hide the original evaluation phase.
                stack.scalar_state_at_value_failure = Some(false);
            }
        }
        let is_sourced = self.is_sourced(node);
        let is_non_set_union = is_sourced
            && matches!(&result, Ok(value) if !value.is_set() && !matches!(value, Value::Unsorted(_)))
            && matches!(self.kind(node), NodeKind::Apply { name, .. }
                if !name.is_local && self.name(name.text) == "\\cup");
        // `CallStackTool.eval` returns a copy of a `SetPredValue`, which has no source.
        let result = match result {
            Ok(Value::Lazy(lazy)) if self.copies_filters && matches!(**lazy, Lazy::Filter(..)) => {
                let Lazy::Filter(base, predicate) = &**lazy else {
                    unreachable!("a filter")
                };
                Ok(Value::lazy_with_class(
                    Lazy::Filter(base.clone(), Rc::new(predicate.copied())),
                    lazy.java_class,
                ))
            }
            result => result,
        };
        // `SetEnumValue.cup` and `IntervalValue.cup` of an empty receiver return the other
        // operand itself, whose source `CallStackTool.setSource` then replaces with the union's.
        let returned_operand = match self.kind(node) {
            NodeKind::Apply { name, args }
                if is_sourced && !name.is_local && self.name(name.text) == "\\cup" =>
            {
                args.iter().map(|&arg| self.resolved(arg)).find(|&arg| {
                    self.call_stack.as_ref().is_some_and(|stack| {
                        matches!((&result, stack.values.get(&arg)), (Ok(value), Some(operand))
                            if address(value).is_some() && address(value) == address(operand))
                    })
                })
            }
            _ => None,
        };
        if let (Some(stack), Ok(value)) = (&mut self.call_stack, &result) {
            stack.sourced_non_set |= is_non_set_union;
            let is_copied =
                matches!(value, Value::Lazy(lazy) if matches!(***lazy, Lazy::Filter(..)));
            if returned_operand.is_some() && !is_copied {
                stack.replace_source(value, node);
            } else if is_sourced && !is_copied {
                stack.give_source(value, node);
            }
            stack.values.insert(node, value.clone());
        }
        result
    }

    // Whether an expression builds its value in place, from records, tuples, set enumerations,
    // `:>` and `@@` of numbers and strings, so that nothing compared it before.
    fn is_built_here(&self, node: NodeId) -> bool {
        match &self.ir.nodes.arena[node as usize].kind {
            NodeKind::Number(_) | NodeKind::String(_) => true,
            NodeKind::Record(fields) => fields.iter().all(|&(_, value)| self.is_built_here(value)),
            NodeKind::Tuple(items) | NodeKind::SetEnumeration(items) => {
                items.iter().all(|&item| self.is_built_here(item))
            }
            NodeKind::Apply { name, args } => {
                !name.is_local
                    && matches!(self.name(name.text), ":>" | "@@")
                    && args.iter().all(|&arg| self.is_built_here(arg))
            }
            _ => false,
        }
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
                    // TLC calls the method of the operand it can enumerate, or else the right one;
                    // a set enumeration it can't normalize is Reducible as written.
                    "\\cap" | "\\cup" => {
                        let left = self.resolved(args[0]);
                        // A set enumeration is `Reducible`, normalized or not.
                        let is_reducible = self.call_stack.as_ref().is_some_and(|stack| {
                            stack
                                .values
                                .get(&left)
                                .is_some_and(crate::sets::is_reducible)
                        });
                        Some(if is_reducible { args[0] } else { args[1] })
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    // An EXCEPT's `select` of its path (`Value.select(Value[])`) that failed: the value it
    // selects in and, where the `select` of a record or tuple it reached failed, that one, each
    // where it has a source, throw the failure on as a FingerprintException, the inner one's
    // first. The value the EXCEPT selects in is the one it evaluated until a `takeExcept` builds
    // a new one, which has none.
    fn place_except_failure(&mut self, original: &Value, is_taken: bool, selected: &ExceptSelect) {
        let Some(stack) = &mut self.call_stack else {
            return;
        };
        if stack.is_frozen || stack.is_fingerprinted || stack.is_unsourced {
            return;
        }
        let receiver = (!is_taken).then(|| stack.source(original)).flatten();
        let inner = match selected {
            ExceptSelect::Selected(selected)
                if is_taken || address(selected) != address(original) =>
            {
                stack.source(selected)
            }
            _ => None,
        };
        let sources: Vec<NodeId> = receiver.into_iter().chain(inner).collect();
        if !sources.is_empty() {
            stack.is_fingerprinted = true;
            stack.fingerprinted_sources = sources;
        }
        self.is_except_placed = true;
    }

    // Marks the failure as one in a method of a value with a source, where it is.
    fn mark_fingerprinted(&mut self, frame: StackFrame, error: &EvalError) {
        let is_compared_filter = crate::value::take_compared_filter();
        if std::mem::take(&mut self.is_except_placed) {
            return;
        }
        if crate::value::take_unplaced_component() {
            if let Some(stack) = &mut self.call_stack {
                stack.unfollowed = Some(crate::value::UNPLACED_COMPONENT_FAILURE);
            }
            return;
        }
        let reason = error.reason.as_str();
        let StackFrame::Node(node) = frame else {
            return;
        };
        // `toFcnRcd` sizes the domain of a function TLC keeps lazy: Nat, Int, Real or STRING
        // fails in `UserValue.size` with the source a node last gave that shared object, as
        // `{} \cup Nat` gives Nat the union's, which TLC throws on as a FingerprintException
        // that the replay doesn't place.
        // A Java method, as Bags' IsABag, words the failure as its own (2154), with no
        // FingerprintException.
        if (reason == crate::value::BUILT_OVER_OVERRIDDEN
            || reason == crate::value::UNSURE_OVER_OVERRIDDEN)
            && error
                .message
                .as_ref()
                .is_some_and(|message| message.code.is_none())
            && !self.is_assumption
            && let Some(stack) = &mut self.call_stack
            && stack.sources_shared()
        {
            stack.unfollowed.get_or_insert(SHARED_DOMAIN_SOURCED);
        }
        // `toFcnRcd` of a function TLC keeps lazy sizes each domain in turn (`FcnParams.size`):
        // the first domain that fails to count in a method of its own, as `Nat \X Nat` or `SUBSET Nat`,
        // throws the failure on as a FingerprintException where a node gave it a source, which
        // the replay doesn't place for a function it holds lazy.
        if is_sizing_failure(error)
            && !self.is_assumption
            && let NodeKind::Apply { args, .. } = self.kind(node)
        {
            let args: Vec<NodeId> = args.iter().map(|&arg| self.resolved(arg)).collect();
            if let Some(stack) = &mut self.call_stack
                && args.iter().any(|arg| {
                    matches!(stack.values.get(arg), Some(Value::Lambda(lambda))
                    if lambda.domains().into_iter().find(|domain| printed_size(domain).is_err())
                        .is_some_and(|domain| {
                            stack.source(domain).is_some() || stack.is_resourced(domain)
                        }))
                })
            {
                stack.unfollowed.get_or_insert(SOURCED_DOMAIN_SIZED);
            }
        }
        // These checks happen outside the value's methods.
        if reason == APPLIED_NON_BOOLEAN
            || reason == SUBSET_NON_ENUMERABLE
            || reason == ASSIGNED_NON_ENUMERABLE
        {
            return;
        }
        // A bound set TLC fails to sort as it enumerates it (`UNSORTED_BOUND_SOURCED`).
        if error.message.is_some() {
            let sets: Vec<NodeId> = match self.kind(node) {
                NodeKind::Choose { set: Some(set), .. } => vec![*set],
                NodeKind::SetFilter { bound, .. } => vec![bound.set],
                NodeKind::Forall { bounds, .. }
                | NodeKind::Exists { bounds, .. }
                | NodeKind::SetMap { bounds, .. } => bounds.iter().map(|bound| bound.set).collect(),
                _ => Vec::new(),
            };
            let sets: Vec<NodeId> = sets.into_iter().map(|set| self.resolved(set)).collect();
            if let Some(stack) = &mut self.call_stack
                && !stack.is_unsourced
                && let Some(failing) = sets.iter().find_map(|set| {
                    let Some(Value::Unsorted(elements)) = stack.values.get(set) else {
                        return None;
                    };
                    crate::value::normalize_unsorted_failure(elements)
                        .is_some_and(|failure| failure.message == error.message)
                        .then(|| stack.values[set].clone())
                })
            {
                // A set of scalars, which have no source, the replay built with its source fails
                // in its own `normalize` alone.
                let is_scalar = |value: &Value| {
                    matches!(
                        value,
                        Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::Model(_)
                    )
                };
                match (&failing, stack.source(&failing)) {
                    (Value::Unsorted(elements), Some(source))
                        if elements.iter().all(is_scalar) && !stack.is_resourced(&failing) =>
                    {
                        stack.is_fingerprinted = true;
                        stack.fingerprinted_sources = vec![source];
                    }
                    _ => {
                        stack.unfollowed.get_or_insert(UNSORTED_BOUND_SOURCED);
                    }
                }
                return;
            }
        }
        // A set of functions TLC can't enumerate fails in its own method
        // (`SetOfFcnsValue.elements`), wherever TLC enumerates it: as the set of a CHOOSE, a
        // quantifier, a set filter or a set map, or as the base of a filter it keeps lazy, which
        // the method of another value enumerates. That set's source heads the
        // FingerprintException, and the lazy filter has none.
        if reason == "enumerated an infinite set" {
            let sets: Vec<NodeId> = match self.kind(node) {
                NodeKind::Choose { set: Some(set), .. } => vec![*set],
                NodeKind::SetFilter { bound, .. } => vec![bound.set],
                NodeKind::Forall { bounds, .. }
                | NodeKind::Exists { bounds, .. }
                | NodeKind::SetMap { bounds, .. } => bounds.iter().map(|bound| bound.set).collect(),
                _ => self.receiver(node).into_iter().collect(),
            };
            let sets: Vec<NodeId> = sets.into_iter().map(|set| self.resolved(set)).collect();
            if let Some(stack) = &mut self.call_stack
                && let Some(source) = sets.iter().find_map(|set| {
                    stack.source(&crate::sets::unenumerable_function_set(
                        stack.values.get(set)?,
                    )?)
                })
            {
                stack.is_fingerprinted = true;
                stack.fingerprinted_sources = vec![source];
                return;
            }
        }
        // A union of a value that isn't a set fails in its own method (`UnionValue.elements`),
        // wherever TLC enumerates it as the set of a CHOOSE, a quantifier, a set filter or a set
        // map: its source, where it has one, heads the FingerprintException.
        if (reason == UNION_NON_SET || reason == UNION_FIRST_NON_SET) && !self.is_starting {
            let sets: Vec<NodeId> = match self.kind(node) {
                NodeKind::Choose { set: Some(set), .. } => vec![*set],
                NodeKind::SetFilter { bound, .. } => vec![bound.set],
                NodeKind::Forall { bounds, .. }
                | NodeKind::Exists { bounds, .. }
                | NodeKind::SetMap { bounds, .. } => bounds.iter().map(|bound| bound.set).collect(),
                _ => Vec::new(),
            };
            let sets: Vec<NodeId> = sets.into_iter().map(|set| self.resolved(set)).collect();
            if let Some(stack) = &mut self.call_stack
                && let Some(source) = sets.iter().find_map(|set| {
                    let union = stack.values.get(set)?;
                    if is_failing_union(union) {
                        if stack.is_resourced(union) {
                            stack.unfollowed.get_or_insert(UNION_RESOURCED);
                        }
                        stack.source(union)
                    } else {
                        None
                    }
                })
            {
                stack.is_fingerprinted = true;
                stack.fingerprinted_sources = vec![source];
                return;
            }
        }
        // TLC fails to build the enumerator of a set in the `elements` of the values its
        // enumeration passes through, which throw the failure on with their sources.
        // A filter that fails in its own Enumerator as TLC compares two sets built of it, by
        // their parts (`SetOfFcnsValue.equals`), or as it sorts a set enumeration that holds it,
        // which converts it to compare it (`SetEnumValue.compareTo`, `toSetEnum`), isn't
        // enumerated by the set the operator asks: the comparison places it as any other
        // failure.
        let is_sorted_filter = is_own_filter_failure(error)
            && self
                .receiver(node)
                .map(|receiver| self.resolved(receiver))
                .and_then(|receiver| self.call_stack.as_ref()?.values.get(&receiver))
                .is_some_and(holds_unsorted_value);
        if is_enumerator_failure(error)
            && !(is_compared_filter && is_own_filter_failure(error))
            && !is_sorted_filter
            && self.mark_enumerated(node, false)
        {
            return;
        }
        // A power set's enumerator fails as it counts a base TLC can't count, in the `elements`
        // of the values its enumeration passes through, the power sets among them.
        if is_sizing_failure(error) {
            // An interval TLC counts in its own method throws the failure on with a source the
            // replay doesn't give it (`IntervalValue.size`).
            if is_interval_sizing_failure(error)
                && self.holds_sourced_interval()
                && self.leave_enumerated()
            {
                return;
            }
            if is_interval_sizing_failure(error) && self.mark_uncounted_part(node) {
                return;
            }
            if self.mark_enumerated(node, true) {
                return;
            }
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
        // receiver that test their own members, or the value an equality compares with.
        let given = match self.kind(node) {
            NodeKind::Apply { name, args } if !name.is_local && args.len() == 2 => {
                match self.name(name.text) {
                    "\\in" | "\\notin" => Some((true, self.resolved(args[0]))),
                    "=" | "#" => Some((false, self.resolved(args[1]))),
                    _ => None,
                }
            }
            _ => None,
        };
        let applied = match self.kind(node) {
            NodeKind::FunctionApplication { args, .. } if args.len() == 1 => {
                Some(self.resolved(args[0]))
            }
            _ => None,
        };
        // The operands of a union, an intersection or a difference.
        let operands = match self.kind(node) {
            NodeKind::Apply { name, args }
                if !name.is_local && matches!(self.name(name.text), "\\cup" | "\\cap" | "\\") =>
            {
                Some((
                    self.name(name.text) == "\\cup",
                    self.resolved(args[0]),
                    self.resolved(args[1]),
                ))
            }
            _ => None,
        };
        let Some(stack) = &self.call_stack else {
            return;
        };
        let Some(received) = receiver.and_then(|receiver| stack.values.get(&receiver)) else {
            return;
        };
        // `Tool`'s `evalAppl` fails itself where it applies a value that isn't a function, before
        // it calls a method of the value.
        if matches!(self.kind(node), NodeKind::FunctionApplication { .. })
            && !matches!(received, Value::Function(_) | Value::Lambda(_))
        {
            return;
        }
        // `Tool`, which evaluates an assumption, gives the union's value no source.
        if stack.sourced_non_set && !stack.is_unsourced {
            if let Some(stack) = &mut self.call_stack {
                stack.is_source_unfollowed = true;
            }
            return;
        }
        let received = received.clone();
        if let Some((is_union, left, right)) = operands {
            let other = if receiver == Some(left) { right } else { left };
            if let Some(other) = stack.values.get(&other).cloned()
                && let Some((set, element)) = failing_operation(&received, &other, is_union)
            {
                let outer = stack.source(&received);
                let given = element.as_ref().map_or(Given::Nothing, Given::Element);
                self.mark_interval_unplaced(&received, None);
                self.mark_failing_member(outer, &set, given, false);
                return;
            }
        }
        // A function TLC searches key by key fails in the `equals` of a key, given the argument.
        if let (Some(applied), Value::Function(inner)) = (applied, &received)
            && (searches_linearly(inner) || searches_sorted_linearly(inner))
        {
            let Some(argument) = stack.values.get(&applied).cloned() else {
                if let Some(stack) = &mut self.call_stack {
                    stack.unfollowed.get_or_insert(UNPLACED_KEY_SEARCH);
                }
                return;
            };
            self.mark_interval_unplaced(&received, receiver);
            self.mark_failing_member(None, &received, Given::Keyed(&argument), true);
            return;
        }
        let given = given.and_then(|(is_membership, node)| {
            Some((is_membership, stack.values.get(&node)?.clone()))
        });
        let given = match &given {
            Some((true, element)) => Given::Element(element),
            Some((false, other)) => Given::Equated(other),
            None => Given::Nothing,
        };
        let is_given_unsourced = match given {
            Given::Element(value) | Given::Equated(value) => {
                address(value).is_none_or(|_| stack.source(value).is_none())
            }
            _ => true,
        };
        self.mark_interval_unplaced(&received, receiver);
        self.mark_failing_member(None, &received, given, true);
        let is_receiver_sourced = receiver.is_some_and(|node| self.is_sourced(node));
        // An interval a node that gives its value a source returned, as `{} \cup (1..2)` or
        // DOMAIN of a tuple, has that node's source (`CallStackTool.setSource`), which the replay,
        // holding an interval without an address, keeps here: the interval's own method fails,
        // and its source heads those of the values its method passed the failure through.
        if let (Value::Interval(..), Some(node), Some(stack)) =
            (&received, receiver, &mut self.call_stack)
            && stack.unfollowed.is_none()
            && !stack.is_unsourced
            && is_receiver_sourced
        {
            if stack.is_fingerprinted {
                stack.fingerprinted_sources.insert(0, node);
            } else if is_given_unsourced {
                stack.is_fingerprinted = true;
                stack.fingerprinted_sources = vec![node];
            }
        }
    }

    // PrintT of SUBSET S where S isn't a set, as TLC computes it as it starts, where no value has
    // a source: `SubsetValue.toString` asks S's `size`, which fails for a value of no keys
    // (`IntValue.size` and its siblings), and expands it below 7: of no keys to `{{}}`, and
    // otherwise `elementsNormalized` fails as `toSetEnum` gives no set of S. Any other S, a
    // function TLC keeps lazy, or one of 7 keys or more, which TLC prints as written, declines
    // as the SUBSET does.
    fn print_subset_of_non_set(&mut self, value: Value) -> Evaluated<Value> {
        let size = match &value {
            Value::Function(function) => function.domain.len(),
            Value::Int(_) | Value::Bool(_) | Value::Str(_) | Value::Model(_) => {
                return as_java_failure(PRINT_T, printed_size(&value).map(|_| Value::Bool(true)));
            }
            _ => return fail(SUBSET_NON_SET),
        };
        if size >= 7 {
            return fail("PrintT of SUBSET of a function of 7 keys or more");
        }
        if size > 0 {
            return as_java_failure(
                PRINT_T,
                fail_runtime(
                    SUBSET_NON_SET,
                    format!(
                        "Attempted to compute the value of an expression of form\n\
                         SUBSET S, but S is a non-enumerable value:\n{}",
                        format_pretty(&value)
                    ),
                ),
            );
        }
        let subsets = set_of(vec![set_of(Vec::new())?])?;
        self.printed
            .push(crate::OutputEvent::Print(vec![format_printed(&subsets)]));
        Ok(Value::Bool(true))
    }

    // A union of a value that isn't a set, which TLC's `CallStackTool` built with a source,
    // fails as a FingerprintException headed by its own source (`UnionValue.elements`), to
    // which each method of another value with a source it fails in prepends that value's
    // (`FingerprintException.getNewHead`). The replay follows it as the set of a CHOOSE, a
    // quantifier, a set filter or a set map (`mark_fingerprinted`); as `Cardinality`'s argument,
    // whose failure `MethodValue` reports with the nested expressions; and where another value's
    // method failed with a source, as the value the frame's node was given or a part of a value
    // the failure passed through, where only one such union is there to have failed. Elsewhere
    // it declines. TLC's own tool as it starts gives no value a source.
    fn mark_union_unfollowed(&mut self, frame: StackFrame) {
        const UNFOLLOWED: &str = "a union of a value that isn't a set, enumerated by another value";
        let StackFrame::Node(node) = frame else {
            return;
        };
        if self.is_starting {
            return;
        }
        let is_counted = matches!(self.kind(node), NodeKind::Apply { name, .. }
            if !name.is_local
                && matches!(name.resolution, Resolution::Builtin(index)
                    if self.name(self.ir.builtins[index as usize].name) == "Cardinality"));
        let args: Vec<NodeId> = match self.kind(node) {
            NodeKind::Apply { args, .. } => args.iter().map(|&arg| self.resolved(arg)).collect(),
            _ => Vec::new(),
        };
        let Some(stack) = &mut self.call_stack else {
            return;
        };
        if !stack.is_fingerprinted {
            if !is_counted {
                stack.unfollowed.get_or_insert(UNFOLLOWED);
            }
            return;
        }
        let mut candidates: Vec<Value> = args
            .iter()
            .filter_map(|arg| stack.values.get(arg).cloned())
            .collect();
        for &(source, ref value) in stack.sourced.values() {
            if stack.fingerprinted_sources.contains(&source) {
                candidates.push(value.clone());
            }
        }
        let mut unions: Vec<(usize, Option<NodeId>)> = Vec::new();
        for value in &candidates {
            for union in direct_failing_unions(value) {
                let Some(address) = address(&union) else {
                    continue;
                };
                if stack.is_resourced(&union) {
                    stack.unfollowed.get_or_insert(UNION_RESOURCED);
                }
                if !unions.iter().any(|&(seen, _)| seen == address) {
                    unions.push((address, stack.source(&union)));
                }
            }
        }
        let last = stack.fingerprinted_sources.last().copied();
        match unions.as_slice() {
            [(_, Some(source))] if last == Some(*source) => {}
            [(_, Some(source))] => stack.fingerprinted_sources.push(*source),
            _ => {
                stack.unfollowed.get_or_insert(UNFOLLOWED);
            }
        }
    }

    // Marks a failure of TLC's enumerator of a bound set, or of a set an equality enumerates, as
    // a FingerprintException with the sources of the values whose `elements` it passes
    // through, where any has one (`sets::enumeration_chain`). Where the evaluator can't place
    // the failure among those values, it leaves it unfollowed. Whether it marked the failure.
    // A failure counting a power set's base (`is_sizing`) is placed only through a chain that
    // ends at the power set, and one to enumerate only through a chain that doesn't.
    fn mark_enumerated(&mut self, node: NodeId, is_sizing: bool) -> bool {
        let bounds: Vec<NodeId> = match self.kind(node) {
            NodeKind::Choose { set: Some(set), .. } => vec![*set],
            NodeKind::SetFilter { bound, .. } => vec![bound.set],
            NodeKind::Forall { bounds, .. }
            | NodeKind::Exists { bounds, .. }
            | NodeKind::SetMap { bounds, .. } => bounds.iter().map(|bound| bound.set).collect(),
            NodeKind::Apply { name, args }
                if !name.is_local
                    && args.len() == 2
                    && matches!(self.name(name.text), "=" | "#") =>
            {
                return self.mark_equated(args[0], args[1], is_sizing);
            }
            // `x' \in S` enumerates S to assign x' each element (`Tool.getNextStates`), as
            // `x \in S` of a variable does in the initial predicate (`Tool.getInitStates`): a
            // membership test of the variable's value doesn't enumerate S.
            NodeKind::Apply { name, args }
                if !name.is_local
                    && args.len() == 2
                    && self.name(name.text) == "\\in"
                    && (matches!(self.kind(args[0]), NodeKind::Prime(_))
                        || matches!(self.kind(args[0]), NodeKind::Identifier(variable)
                            if matches!(variable.resolution, Resolution::Variable(_)))) =>
            {
                vec![args[1]]
            }
            // `S \subseteq T` calls S's `isSubsetEq` (OPCODE_subseteq), which enumerates S and
            // throws a failure on with S's source, as its `elements` does. A power set's
            // `isSubsetEq` may compare its base instead.
            NodeKind::Apply { name, args }
                if !is_sizing
                    && !name.is_local
                    && args.len() == 2
                    && self.name(name.text) == "\\subseteq" =>
            {
                return self.mark_subset(args[0]);
            }
            // A failure counting a set elsewhere is placed as any other failure is.
            _ if is_sizing => return false,
            _ => return self.leave_enumerated(),
        };
        let bounds: Vec<NodeId> = bounds.into_iter().map(|set| self.resolved(set)).collect();
        let Some(stack) = &self.call_stack else {
            return true;
        };
        // A failure counting a set no bound builds a power set of is placed as any other is.
        if is_sizing
            && !bounds.iter().any(|set| {
                stack
                    .values
                    .get(set)
                    .is_some_and(crate::sets::holds_power_set)
            })
        {
            return false;
        }
        let chains: Vec<Result<Option<Vec<Value>>, ()>> = bounds
            .iter()
            .map(|set| {
                stack
                    .values
                    .get(set)
                    .map_or(Err(()), crate::sets::enumeration_chain)
            })
            .collect();
        // `Tool.contexts` evaluates each bound's set and calls its `elements` in turn, so where
        // the sets before one whose power set fails as it counts its base are enumerations or
        // intervals, which enumerate without failing, the failure is that one's.
        if is_sizing && chains.len() > 1 {
            let failing = bounds.iter().zip(&chains).position(|(set, chain)| {
                !matches!(chain, Ok(None))
                    || !matches!(
                        stack.values.get(set),
                        Some(Value::Set(_) | Value::Interval(..))
                    )
            });
            return match failing.map(|position| &chains[position]) {
                Some(Ok(Some(chain))) if crate::sets::ends_sizing_base(chain) => {
                    let chain = chain.clone();
                    self.fingerprint_chain(&chain, is_sizing, false)
                }
                _ => self.leave_enumerated(),
            };
        }
        // With more than one bound, which set TLC enumerates first isn't placed.
        match chains.as_slice() {
            [Ok(Some(chain))] if crate::sets::ends_sizing_base(chain) != is_sizing => {
                self.leave_enumerated()
            }
            [Ok(Some(chain))] => {
                let chain = chain.clone();
                self.fingerprint_chain(&chain, is_sizing, false)
            }
            // A power set TLC counts the base of otherwise, as it normalizes a set enumeration
            // that holds it, isn't placed.
            [Ok(None)] if is_sizing => self.leave_enumerated(),
            [Ok(None)] => false,
            _ => self.leave_enumerated(),
        }
    }

    // A bound of a CHOOSE, a quantifier or a set map that is a set of functions, records or
    // tuples with an interval part TLC fails to count: `Tool.contexts` evaluates each bound's set
    // and enumerates it in turn, and the `elements` of the first that TLC may fail to count in
    // (`is_counted`) asks whether it is empty (`Value.isEmpty`), which throws the failure
    // on with the sources of the sets it passes through (`uncounted_chain`), as a variable's
    // `\in` does of its one set. Whether it marked the failure.
    fn mark_uncounted_part(&mut self, node: NodeId) -> bool {
        let bounds: Vec<NodeId> = match self.kind(node) {
            NodeKind::Choose { set: Some(set), .. } => vec![*set],
            NodeKind::Forall { bounds, .. }
            | NodeKind::Exists { bounds, .. }
            | NodeKind::SetMap { bounds, .. } => bounds.iter().map(|bound| bound.set).collect(),
            // `x' \in S` and `x \in S` of a variable enumerate S (`mark_enumerated`).
            NodeKind::Apply { name, args }
                if !name.is_local
                    && args.len() == 2
                    && self.name(name.text) == "\\in"
                    && (matches!(self.kind(args[0]), NodeKind::Prime(_))
                        || matches!(self.kind(args[0]), NodeKind::Identifier(variable)
                            if matches!(variable.resolution, Resolution::Variable(_)))) =>
            {
                vec![args[1]]
            }
            _ => return false,
        };
        let bounds: Vec<NodeId> = bounds.into_iter().map(|set| self.resolved(set)).collect();
        let Some(stack) = &self.call_stack else {
            return false;
        };
        let failing = bounds
            .iter()
            .map(|set| stack.values.get(set))
            .find(|value| !value.is_some_and(crate::sets::is_counted));
        let Some(Some(failing)) = failing else {
            return false;
        };
        if !crate::sets::holds_uncounted_part(failing) {
            return false;
        }
        match crate::sets::uncounted_chain(failing) {
            Some(chain) if !chain.iter().any(|value| self.is_resourced(value)) => {
                self.fingerprint_chain(&chain, false, true)
            }
            _ => {
                if let Some(stack) = &mut self.call_stack {
                    stack.unfollowed.get_or_insert(UNPLACED_UNCOUNTED_PART);
                }
                true
            }
        }
    }

    // `left \subseteq right` of a set TLC fails to enumerate: `left`'s `isSubsetEq` and its
    // `elements` throw the failure on with the same source.
    fn mark_subset(&mut self, left: NodeId) -> bool {
        let left = self.resolved(left);
        let Some(stack) = &self.call_stack else {
            return true;
        };
        let chain = match stack.values.get(&left) {
            Some(Value::Lazy(lazy)) if matches!(&***lazy, Lazy::Subset(_)) => Err(()),
            Some(value) => crate::sets::enumeration_chain(value),
            None => Err(()),
        };
        match chain {
            Ok(Some(chain)) if !crate::sets::ends_sizing_base(&chain) => {
                self.fingerprint_chain(&chain, false, true)
            }
            Ok(None) => false,
            _ => self.leave_enumerated(),
        }
    }

    // `left = right` of a set TLC enumerates to compare it: TLC calls `left`'s `equals`, whose
    // source heads the FingerprintException, and which enumerates `left`, or else `right`.
    fn mark_equated(&mut self, left: NodeId, right: NodeId, is_sizing: bool) -> bool {
        let (left, right) = (self.resolved(left), self.resolved(right));
        let Some(stack) = &self.call_stack else {
            return true;
        };
        let (Some(left), Some(right)) = (stack.values.get(&left), stack.values.get(&right)) else {
            return self.leave_enumerated();
        };
        // Neither side is a set, so the equality enumerates neither: the failure is in a set
        // a tuple's, a record's or a function's `equals` compares as a value of it, as
        // `<<{x \in 0 : TRUE}, 1>> = [x \in {1, 2} |-> x]`, which the methods the evaluator
        // follows place.
        // So with a function TLC keeps lazy on either side, which `FcnLambdaValue.equals`
        // converts (`toFcnRcd`) and compares as a function, as the evaluator does: where its
        // domain is what fails, that failure is placed as it converts.
        if !left.is_set() && !right.is_set() {
            return false;
        }
        // The power set of a filter TLC can't enumerate, compared with a set that isn't a power
        // set, converts itself (`SubsetValue.convertAndCache`), whose `toSetEnum` counts it by its
        // base's `size`, which enumerates the filter and fails in the filter's own Enumerator:
        // `CallStackTool` copied the filter without its source, and the power set's `size` and
        // `equals` throw the failure on with its own.
        if !is_sizing
            && let Value::Lazy(lazy) = left
            && let Lazy::Subset(base) = &***lazy
            && crate::sets::is_unenumerable_filter(base)
            && !matches!(right, Value::Lazy(other) if matches!(***other, Lazy::Subset(_)))
        {
            let chain = vec![left.clone()];
            return self.fingerprint_chain(&chain, false, true);
        }
        // A failure counting a set neither side builds a power set of is placed as any other is.
        if is_sizing && !crate::sets::holds_power_set(left) && !crate::sets::holds_power_set(right)
        {
            return false;
        }
        let chain = match crate::sets::enumeration_chain(left) {
            Ok(Some(chain)) => Ok(chain),
            Ok(None) => match crate::sets::enumeration_chain(right) {
                Ok(Some(chain)) => Ok(std::iter::once(left.clone()).chain(chain).collect()),
                Ok(None) if is_sizing => return self.leave_enumerated(),
                Ok(None) => return false,
                Err(()) => Err(()),
            },
            Err(()) => Err(()),
        };
        let Ok(chain) = chain else {
            return self.leave_enumerated();
        };
        if crate::sets::ends_sizing_base(&chain) != is_sizing {
            return self.leave_enumerated();
        }
        // The receiver's `equals` and its `elements` throw the failure on with the same source.
        self.fingerprint_chain(&chain, is_sizing, true)
    }

    // Marks a failure as a FingerprintException with the sources of the values of `chain` that
    // have one, outermost first, the same source once in a row where `is_merged`. TLC's
    // `EvaluatingValue.eval` catches whatever its Java method throws, a FingerprintException too,
    // and fails again with `Assert.fail`: TLC then reports the nested expressions of the call
    // stack the FingerprintException froze (`CallStack.freeze(FingerprintException)`), which
    // holds the sources of its values after the frames it was in.
    fn catch_fingerprint(&mut self) {
        let Some(stack) = &mut self.call_stack else {
            return;
        };
        if !stack.is_fingerprinted {
            return;
        }
        stack.is_fingerprinted = false;
        stack.caught_fingerprint = true;
        stack.is_member_followed = false;
        stack.is_subscript_fingerprinted = false;
        let sources = std::mem::take(&mut stack.fingerprinted_sources);
        // A stack frozen before the FingerprintException was thrown takes none of its sources.
        if !std::mem::take(&mut stack.is_frozen_before_fingerprint) {
            stack
                .frames
                .extend(sources.into_iter().map(StackFrame::Node));
        }
    }

    // `TLCExt.tlcEval2`, an `EvaluatingValue`, of an expression of constant level: the value it
    // cached for the key, which is the expression's where the expression reads nothing that varies
    // and has no effect, and a failure, which TLC never caches, of either, reported as the Java
    // method's.
    fn tlc_cache(&mut self, operands: &[Operand]) -> Evaluated<Value> {
        let key = self.operand(&operands[1]);
        let key = self.evaluating_failure(EVAL2, key)?;
        // TLC reads its cache as the tool object of the expression's node, which for a
        // numeral or a string is the value `SpecProcessor.processConstants` gave it: the
        // cast to a HashMap fails, after the key is evaluated.
        if let Operand::Node(node, _) = &operands[0] {
            let class = match self.kind(*node) {
                NodeKind::Number(_) => Some("IntValue"),
                NodeKind::String(_) => Some("StringValue"),
                _ => None,
            };
            if let Some(class) = class {
                return self.evaluating_failure(
                    EVAL2,
                    fail_runtime(
                        "TLCCache of a literal, whose tool object isn't a cache",
                        format!(
                            "class tlc2.value.impl.{class} cannot be cast to class java.util.HashMap (tlc2.value.impl.{class} is in unnamed module of loader 'app'; java.util.HashMap is in module java.base of loader 'bootstrap')"
                        ),
                    ),
                );
            }
        }
        // TLC hashes the key (`Value.hashCode`, a fingerprint, which normalizes it) as it
        // looks it up in a cache that holds an entry, before it evaluates the expression,
        // and as it puts the value there after: where the hash fails, TLC reports that
        // failure whether or not the expression fails, which the evaluator follows only
        // where the expression doesn't.
        let key_failure = self.key_hash_failure(&key)?;
        let (reads, printed, writes) = (self.reads, self.printed.len(), self.register_writes);
        let random = self.random.as_ref().map(|random| random.state());
        let value = self.operand(&operands[0]);
        if self.reads != reads
            || self.printed.len() != printed
            || self.register_writes != writes
            || self.random.as_ref().map(|random| random.state()) != random
            || value.as_ref().is_ok_and(holds_lazy_part)
        {
            return fail("TLCCache of an expression whose value TLC may cache otherwise");
        }
        // TLC initializes the value it caches (`value.initialize()`), which normalizes
        // and fingerprints it, and fails where it can't.
        if let Ok(value) = &value {
            let mut fingerprints =
                Fingerprints::new(Polynomial::get(self.ir.model.fingerprint_index));
            if crate::fingerprint::state_fingerprint(&mut fingerprints, &[value]).is_none() {
                return fail("TLCCache of a value the evaluator doesn't fingerprint");
            }
        }
        if let Some(failure) = key_failure {
            if value.is_err() {
                return fail("TLCCache of a failing expression with a key TLC can't hash");
            }
            return self.evaluating_failure(EVAL2, Err(failure));
        }
        let value = self.evaluating_failure(EVAL2, value)?;
        // TLC's `CallStackTool` replays a failure after TLC cached the value as it first
        // evaluated it, which has no source, nor has any value within it.
        self.unsource_deep(&value);
        Ok(value)
    }

    // Where `Value.hashCode` of TLCCache's key, its fingerprint, fails: the failure, which the
    // evaluator knows for a set enumeration it can't sort alone (`SetEnumValue.normalize`).
    fn key_hash_failure(&self, key: &Value) -> Evaluated<Option<EvalError>> {
        let mut fingerprints = Fingerprints::new(Polynomial::get(self.ir.model.fingerprint_index));
        if crate::fingerprint::state_fingerprint(&mut fingerprints, &[key]).is_some() {
            return Ok(None);
        }
        if let Value::Unsorted(elements) = key
            && let Some(failure) = crate::value::normalize_unsorted_failure(elements)
            && failure.is_set_normalization
            && failure.message.is_some()
        {
            return Ok(Some(failure));
        }
        fail("TLCCache of a key the evaluator doesn't fingerprint")
    }

    // Takes the source the replay gave a value away, as TLC holds a value it made without one.
    fn unsource(&mut self, value: &Value) {
        if let Some(stack) = &mut self.call_stack
            && let Some(address) = address(value)
        {
            stack.sourced.remove(&address);
            stack.resourced.remove(&address);
        }
    }

    // Takes the sources the replay gave a value and every value within it away, as TLC holds a
    // value its `Tool` made first, before the replay, which gives none of its parts a source:
    // the value `tlcEvalConst` and `tlcEval2` cached.
    fn unsource_deep(&mut self, value: &Value) {
        let Some(stack) = &mut self.call_stack else {
            return;
        };
        if stack.sourced.is_empty() && stack.resourced.is_empty() {
            return;
        }
        let mut pending = vec![value];
        let mut seen = HashSet::new();
        while let Some(value) = pending.pop() {
            let Some(address) = address(value) else {
                continue;
            };
            if !seen.insert(address) {
                continue;
            }
            stack.sourced.remove(&address);
            stack.resourced.remove(&address);
            match value {
                Value::Set(set) | Value::Unsorted(set) => pending.extend(set.iter()),
                Value::Function(function) => {
                    pending.extend(function.domain.iter().chain(&function.range))
                }
                Value::Lazy(lazy) => match &***lazy {
                    Lazy::Subset(base)
                    | Lazy::Seq(base)
                    | Lazy::Union(base)
                    | Lazy::Filter(base, _) => pending.push(base),
                    Lazy::FunctionSet(left, right)
                    | Lazy::Cap(left, right)
                    | Lazy::Cup(left, right)
                    | Lazy::Diff(left, right) => pending.extend([left, right]),
                    Lazy::RecordSet(fields, _) => {
                        pending.extend(fields.iter().map(|(_, value)| value))
                    }
                    Lazy::Product(sets) => pending.extend(sets),
                    _ => {}
                },
                _ => {}
            }
        }
    }

    // The failure of an `EvaluatingValue`'s Java method, which `EvaluatingValue.eval` catches,
    // a FingerprintException too, and fails again with `Assert.fail` (2154). Where what it
    // caught is another's that caught a FingerprintException, TLC never finishes reporting it,
    // which the evaluator doesn't follow.
    fn evaluating_failure<T>(&mut self, signature: &str, result: Evaluated<T>) -> Evaluated<T> {
        if let Err(EvalError {
            message: Some(message),
            ..
        }) = &result
            && message.code == Some(JAVA_METHOD_FAILED)
            && self
                .call_stack
                .as_ref()
                .is_some_and(|stack| stack.caught_fingerprint)
        {
            return fail("a failure within another Java method's caught FingerprintException");
        }
        let result = as_java_failure(signature, result);
        if result.is_err() {
            self.catch_fingerprint();
        }
        result
    }

    // `CallStackTool.setSource` gives a value the source of each node that returns it, the last
    // replacing the first, as `S \cup {}` returns S, where the replay keeps the first: a failure
    // counting a power set's base through a value another such node returned is left unplaced.
    // Whether it marked the failure.
    fn fingerprint_chain(&mut self, chain: &[Value], is_sizing: bool, is_merged: bool) -> bool {
        if is_sizing && chain.iter().any(|value| self.is_resourced(value)) {
            return self.leave_enumerated();
        }
        // A value another node gave its source again, as `{} \cup S` gives S, has that node's
        // source in TLC, which the replay doesn't follow.
        if let Some(stack) = &mut self.call_stack
            && !stack.is_unsourced
            && chain.iter().any(|value| stack.is_resourced(value))
        {
            stack.unfollowed = Some(UNPLACED_ENUMERATOR);
            return true;
        }
        let Some(stack) = &mut self.call_stack else {
            return true;
        };
        let mut sources: Vec<NodeId> = Vec::new();
        for source in chain.iter().filter_map(|value| stack.source(value)) {
            if !is_merged || sources.last() != Some(&source) {
                sources.push(source);
            }
        }
        if !sources.is_empty() {
            stack.is_fingerprinted = true;
            stack.fingerprinted_sources = sources;
        }
        true
    }

    // Whether a node TLC gives a source (`is_sourced`) other than the one the replay gave a value
    // returned it.
    fn is_resourced(&self, value: &Value) -> bool {
        let Some(stack) = &self.call_stack else {
            return false;
        };
        let Some(held) = address(value) else {
            return false;
        };
        let source = stack.source(value);
        stack.values.iter().any(|(&node, other)| {
            Some(node) != source && address(other) == Some(held) && self.is_sourced(node)
        })
    }

    // Whether a node TLC gives a source (`is_sourced`) returned an interval, which the replay,
    // holding an interval without an address, gives none.
    fn holds_sourced_interval(&self) -> bool {
        self.call_stack.as_ref().is_some_and(|stack| {
            stack
                .values
                .iter()
                .any(|(&node, value)| matches!(value, Value::Interval(..)) && self.is_sourced(node))
        })
    }

    // Leaves a failure of TLC's enumerator the evaluator doesn't place unfollowed, where it must
    // place it as TLC does (`is_enumerator_placed`), and otherwise to the methods it follows.
    // Whether it left it.
    fn leave_enumerated(&mut self) -> bool {
        match &mut self.call_stack {
            Some(stack) if self.is_enumerator_placed => {
                stack.unfollowed = Some(UNPLACED_ENUMERATOR);
                true
            }
            _ => false,
        }
    }

    // Marks a failure in a method of an interval that may have a source, which is not one `..`
    // builds at `node`.
    fn mark_interval_unplaced(&mut self, value: &Value, node: Option<NodeId>) {
        let is_range = node.is_some_and(|node| {
            matches!(self.kind(node), NodeKind::Apply { name, .. }
                if !name.is_local && self.name(name.text) == "..")
        });
        if let (Value::Interval(..), false, Some(stack)) = (value, is_range, &mut self.call_stack) {
            stack.is_interval_unplaced = true;
        }
    }

    // Marks a failure in a method of a value with a source as TLC's FingerprintException, after
    // the source of the set whose method asked it, if any, through the sets nested in it that test
    // the element's parts, where an element was tested, and the values with a source whose
    // methods its search, comparison or normalization fails in.
    fn mark_failing_member(
        &mut self,
        outer: Option<NodeId>,
        received: &Value,
        given: Given,
        is_membership: bool,
    ) {
        let Some(stack) = &mut self.call_stack else {
            return;
        };
        if stack.is_fingerprinted {
            return;
        }
        // `SetPredValue.member` asks its base set first, whose FingerprintException passes through
        // a filter `CallStackTool` copied without its source, as though the base were asked.
        if let (Given::Element(element), Value::Lazy(lazy)) = (&given, received)
            && let Lazy::Filter(base, _) = &***lazy
            && stack.source(received).is_none()
            && is_member(element, base).is_err()
        {
            let base = base.clone();
            self.mark_failing_member(outer, &base, given, is_membership);
            return;
        }
        // `UnionValue.member` and `isSubsetEq` enumerate its set (`SetEnumValue.elements`), which
        // normalizes a set enumeration TLC holds unnormalized and fails in the `compareTo` of the
        // element it sorts in: the FingerprintException then holds the sources of the union, its
        // set and that element, which the replay doesn't follow. An equality the replay follows.
        // A union, intersection, difference or filter asks the sets it is built from, a union
        // among them.
        fn reaches_unsorted_union(value: &Value) -> bool {
            let Value::Lazy(lazy) = value else {
                return false;
            };
            match &***lazy {
                Lazy::Union(base) => matches!(base, Value::Unsorted(_)),
                Lazy::Cup(left, right) | Lazy::Cap(left, right) | Lazy::Diff(left, right) => {
                    reaches_unsorted_union(left) || reaches_unsorted_union(right)
                }
                Lazy::Filter(base, _) => reaches_unsorted_union(base),
                _ => false,
            }
        }
        if matches!(given, Given::Element(_) | Given::Nothing) && reaches_unsorted_union(received) {
            stack.is_unsorted_union_member = true;
        }
        // A function set, a record set or a product holding such a set enumeration, as its
        // domain, range, fields' sets or factors, or as theirs.
        fn holds_unsorted_part(value: &Value) -> bool {
            let Value::Lazy(lazy) = value else {
                return false;
            };
            let parts: Vec<&Value> = match &***lazy {
                Lazy::FunctionSet(domain, range) => vec![domain, range],
                Lazy::RecordSet(fields, _) => fields.iter().map(|(_, set)| set).collect(),
                Lazy::Product(factors) => factors.iter().collect(),
                _ => return false,
            };
            parts
                .into_iter()
                .any(|part| matches!(part, Value::Unsorted(_)) || holds_unsorted_part(part))
        }
        fn reaches_held_unsorted(value: &Value) -> bool {
            let Value::Lazy(lazy) = value else {
                return false;
            };
            match &***lazy {
                Lazy::Union(Value::Set(elements) | Value::Unsorted(elements)) => elements
                    .iter()
                    .any(|element| holds_unsorted_part(element) || reaches_held_unsorted(element)),
                Lazy::Cup(left, right) | Lazy::Cap(left, right) | Lazy::Diff(left, right) => {
                    [left, right].into_iter().any(|operand| {
                        holds_unsorted_part(operand) || reaches_held_unsorted(operand)
                    })
                }
                Lazy::Filter(base, _) => reaches_held_unsorted(base),
                _ => false,
            }
        }
        if matches!(given, Given::Element(_) | Given::Nothing) && reaches_held_unsorted(received) {
            stack.is_unsorted_held_member = true;
        }
        let nested = match given {
            Given::Element(element) => crate::sets::failing_sets(element, received),
            _ => None,
        };
        // The search of a set fails in the methods of the values it compares, and an equality in
        // those of the parts it compares (`equals`), which have sources where the evaluation gave
        // them: the set's, which a definition TLC computed as it started has none of, is outside
        // them. A set TLC holds unnormalized normalizes itself in its other methods
        // (`SetEnumValue.normalize`), which fails in the `compareTo` of the element it sorts in.
        // Where a membership's failure passes through nested sets, the search is the innermost set's.
        // A set of functions, of records or of tuples words an element that is no function,
        // record or tuple in its message (`SetOfFcnsValue.member`'s `Assert.fail`), whose
        // `toString` normalizes a set enumeration TLC holds unnormalized and fails in the
        // `compareTo` of the element it sorts in: the FingerprintException holds the element's
        // source, then those of the values compared (`SetEnumValue.toString`). One whose failure
        // is nested deeper in the element the replay doesn't follow.
        let tested = match (&given, &nested) {
            (_, Some((_, inner_element, inner_set))) => Some((inner_element, inner_set)),
            (Given::Element(element), None) => Some((*element, received)),
            _ => None,
        };
        let printed_element = match tested {
            Some((element, Value::Lazy(lazy)))
                if !stack.is_unsourced
                    && matches!(
                        &***lazy,
                        Lazy::FunctionSet(..) | Lazy::RecordSet(..) | Lazy::Product(_)
                    )
                    && !matches!(
                        element,
                        Value::Function(_) | Value::Lambda(_) | Value::Model(_)
                    ) =>
            {
                let written = match element {
                    Value::Unsorted(values) => Some(values.to_vec()),
                    _ => unnormalized(element),
                };
                match written {
                    // TLC gives a value its evaluation built within its call stack a source: one
                    // it can't normalize, which no state or value computed as TLC started holds,
                    // that has none here the replay holds otherwise than TLC.
                    Some(written)
                        if crate::value::normalize_failure(&written).is_some()
                            && stack.source(element).is_none() =>
                    {
                        stack.unfollowed.get_or_insert(NESTED_PRINTED_ELEMENT);
                        return;
                    }
                    Some(written) if crate::value::normalize_failure(&written).is_some() => {
                        let compared = failing_comparisons(|| {
                            crate::value::normalize_failure(&written).map_or(Ok(()), Err)
                        })
                        .err()
                        .unwrap_or_default();
                        Some(std::iter::once(element.clone()).chain(compared).collect())
                    }
                    _ if crate::sets::fails_member_display(element) => {
                        stack.unfollowed.get_or_insert(NESTED_PRINTED_ELEMENT);
                        return;
                    }
                    _ => None,
                }
            }
            _ => None,
        };
        let compared = match (given, received) {
            _ if let Some(printed) = printed_element => printed,
            (Given::Element(element), _) => match &nested {
                Some((_, inner_element, inner_set)) => {
                    crate::sets::failing_search(inner_element, inner_set)
                }
                None => crate::sets::unnormalized_subset_member(element, received)
                    .unwrap_or_else(|| crate::sets::failing_search(element, received)),
            },
            (Given::Equated(other), _)
                if !matches!(received, Value::Lazy(_)) && !matches!(other, Value::Lazy(_)) =>
            {
                failing_comparisons(|| equals(received, other))
                    .err()
                    .unwrap_or_default()
            }
            // Two sets of functions, of records, of tuples or two power sets TLC compares by the
            // sets they are built from (`SetOfFcnsValue.equals`, `SubsetValue.equals`), which
            // fails in the methods of those sets.
            (Given::Equated(other), Value::Lazy(lazy))
                if matches!(other, Value::Lazy(other_lazy)
                    if crate::value::is_same_construction(lazy, other_lazy)) =>
            {
                failing_comparisons(|| equals(received, other))
                    .err()
                    .unwrap_or_default()
            }
            // An equality with a set TLC keeps lazy enumerates it, the receiver first
            // (`convertAndCache`, `toSetEnum`), which may fail in a nested set's `member`, or
            // else in the `normalize` of a set enumeration it is built from, or in the
            // `elements` of the set it enumerates.
            (Given::Equated(other), _) => crate::sets::failing_enumeration(received)
                .or_else(|| crate::sets::failing_enumeration(other))
                .or_else(|| failing_comparisons(|| equals(received, other)).err())
                .unwrap_or_default(),
            (Given::Keyed(argument), _) => failing_comparisons(|| apply_value(received, argument))
                .err()
                .unwrap_or_default(),
            (_, Value::Unsorted(values)) => {
                failing_comparisons(|| crate::value::normalize_failure(values).map_or(Ok(()), Err))
                    .err()
                    .unwrap_or_default()
            }
            _ => Vec::new(),
        };
        let is_interval = |value: &Value| matches!(value, Value::Interval(..));
        if compared.iter().any(is_interval)
            || nested
                .as_ref()
                .is_some_and(|(sets, _, _)| sets.iter().any(is_interval))
        {
            stack.is_interval_unplaced = true;
        }
        let compared: Vec<NodeId> = compared
            .iter()
            .filter_map(|value| stack.source(value))
            .collect();
        let source = stack.source(received);
        if outer.is_none() && source.is_none() && compared.is_empty() {
            return;
        }
        let nested = nested.map(|(sets, _, _)| sets);
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
        let sources: Vec<NodeId> = outer
            .into_iter()
            .chain(source)
            .chain(sources)
            .chain(compared)
            .collect();
        stack.is_fingerprinted = true;
        stack.is_member_followed = is_membership && is_followed;
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
        let is_continued = std::mem::take(&mut self.is_continued_failure);
        // A comparison that failed printing a set TLC holds unnormalized fails in the set's
        // `normalize`, which heads TLC's FingerprintException with the set's source.
        if crate::value::take_unsorted_print_failure()
            && result.is_err()
            && let Some(stack) = &mut self.call_stack
            && !stack.is_frozen
        {
            stack.unfollowed.get_or_insert(UNSORTED_PRINT);
        }
        if let Err(error) = &result
            && !is_continued
            && !matches!(
                error.runtime_exception,
                RuntimeException::ClassCast | RuntimeException::IndexOutOfBounds
            )
            && self
                .call_stack
                .as_ref()
                .is_some_and(|stack| !stack.is_frozen)
        {
            self.mark_fingerprinted(frame, error);
            if error.reason == UNION_NON_SET || error.reason == UNION_FIRST_NON_SET {
                self.mark_union_unfollowed(frame);
            }
        }
        self.is_except_placed = false;
        if result.is_err()
            && let Some(stack) = &mut self.call_stack
            && std::mem::take(&mut stack.is_source_unfollowed)
        {
            stack.is_frozen = true;
            return fail("a failure in a method of a value after a union TLC gave its source");
        }
        if let Some(stack) = &mut self.call_stack {
            let was_frozen = stack.is_frozen;
            stack.is_frozen |= result.as_ref().is_err_and(|error| {
                error.runtime_exception == RuntimeException::Runtime || stack.is_fingerprinted
            });
            if !stack.is_frozen {
                stack.frames.pop();
            } else if !was_frozen {
                self.check_substituted_frames();
            }
        }
        result
    }

    /// TLC's copy of a definition an INSTANCE with substitutions makes has a `SubstInNode` for
    /// its body, which `CallStackTool` pushes as a frame at the INSTANCE where an evaluation
    /// names the copy, and evaluates each substitute where the copy names the declaration, in a
    /// frame of its own; the IR holds the copy with the substitutes put in. A node the copies
    /// share with a definition of the module's own, which the IR writes once, is evaluated
    /// without either frame where an action `Spec.getActions` split out of the copy reaches it
    /// (`SubstInNode` only extends the `Context` there), or within the frames of a copy's name.
    /// A call stack frozen where a frame names such a copy, or in a node only the copies hold,
    /// is printed with the `SubstInNode`'s frames put in (`substitution_frames`) where it can be;
    /// one that can't, as one frozen in a substitute, isn't printed as TLC prints it, though one
    /// TLC doesn't print, as for an invariant or an assumption, still holds.
    pub(crate) fn check_substituted_frames(&mut self) {
        let Some(stack) = &self.call_stack else {
            return;
        };
        if stack.is_substituted || stack.frames.is_empty() {
            return;
        }
        let frames: Vec<NodeId> = stack
            .frames
            .iter()
            .map(|frame| match *frame {
                StackFrame::Node(node)
                | StackFrame::Prefix(node, _)
                | StackFrame::Arguments(node) => node,
            })
            .collect();
        let ir = self.ir;
        let copy_frames = self.get_copy_frames();
        let names_copy = |node: NodeId| match &ir.nodes.arena[node as usize].kind {
            NodeKind::Apply { name, .. }
            | NodeKind::Identifier(name)
            | NodeKind::OperatorReference(name) => match name.resolution {
                Resolution::Definition(index) if copy_frames.copies.contains(&index) => Some(index),
                _ => None,
            },
            _ => None,
        };
        // A copy a LET INSTANCE with substitutions makes of a copy an INSTANCE of the instancee
        // makes: TLC's body is the inner copy's `SubstInNode`, at an INSTANCE the IR doesn't keep.
        let names_nested_local = |node: NodeId| match &ir.nodes.arena[node as usize].kind {
            NodeKind::Apply { name, .. }
            | NodeKind::Identifier(name)
            | NodeKind::OperatorReference(name) => {
                name.is_local && copy_frames.nested_local.contains(&name.text)
            }
            _ => false,
        };
        if frames.iter().any(|&node| names_nested_local(node)) {
            if let Some(stack) = &mut self.call_stack {
                stack.is_substituted = true;
            }
            return;
        }
        let is_within = frames
            .iter()
            .any(|&node| copy_frames.nodes.contains(&node) || names_copy(node).is_some());
        if !is_within {
            return;
        }
        let inserted = (!copy_frames.is_argument)
            .then(|| Self::substitution_frames(ir, copy_frames, &frames))
            .flatten();
        if let Some(stack) = &mut self.call_stack {
            match inserted {
                Some(inserted) => stack.substitution_frames = inserted,
                None => stack.is_substituted = true,
            }
        }
    }

    /// `CallStackTool` pushes a copy's `SubstInNode` as the frame after the one that names the
    /// copy, where the module's own expression names it: where a copy names another, as a
    /// definition of the instancee names one of its own, TLC's copy's body names the instancee's
    /// definition, which has none. None where the frames can't be printed so: in a substitute,
    /// which TLC evaluates in a frame of its own after one of the declaration's name; at a copy
    /// of a copy, whose `SubstInNode` is of an INSTANCE the IR doesn't keep; where the frame
    /// that names the copy is the first, which may be the action `getActions` takes the
    /// `SubstInNode` for; where it is the last, its body not entered; or in a copy no frame names,
    /// as one TLC evaluates itself.
    fn substitution_frames(
        ir: &Ir,
        copy_frames: &CopyFrames,
        frames: &[NodeId],
    ) -> Option<Vec<(usize, tla_ir::SourceRange)>> {
        let contains = |outer: &tla_ir::SourceRange, inner: &tla_ir::SourceRange| {
            outer.module == inner.module
                && (outer.start_line, outer.start_column) <= (inner.start_line, inner.start_column)
                && (inner.end_line, inner.end_column) <= (outer.end_line, outer.end_column)
        };
        let mut inserted = Vec::new();
        // Whether the frames have entered a substitute, all of whose nodes are its own.
        let mut in_substitute = false;
        for (position, &node) in frames.iter().enumerate() {
            let is_copied = copy_frames.nodes.contains(&node);
            // A copy's node outside a frame that names the copy, as where TLC evaluates a
            // `SubstInNode` it holds itself.
            if is_copied && inserted.is_empty() {
                return None;
            }
            let range = ir.nodes.arena[node as usize].range;
            // A substitute is written within its INSTANCE, and is evaluated right after the
            // frame of the declaration's node where the module names it (`Reference` placed
            // there), and in its own frames after that.
            let is_substitute_use = |node: NodeId| {
                let written = &ir.nodes.arena[node as usize];
                matches!(written.kind, NodeKind::Reference(_)) && written.range.is_some()
            };
            if is_copied
                && range.is_some_and(|range| {
                    inserted
                        .iter()
                        .any(|(_, instance)| contains(instance, &range))
                })
                && !in_substitute
            {
                if position > 0 && is_substitute_use(frames[position - 1]) {
                    in_substitute = true;
                } else {
                    return None;
                }
            }
            let (NodeKind::Apply { name, .. } | NodeKind::Identifier(name)) =
                &ir.nodes.arena[node as usize].kind
            else {
                if let NodeKind::OperatorReference(name) = &ir.nodes.arena[node as usize].kind
                    && matches!(name.resolution,
                        Resolution::Definition(index) if copy_frames.copies.contains(&index))
                {
                    return None;
                }
                continue;
            };
            let Resolution::Definition(index) = name.resolution else {
                continue;
            };
            if !copy_frames.copies.contains(&index) {
                continue;
            }
            let definition = &ir.nodes.arena[ir.definitions[index as usize] as usize];
            let NodeKind::Definition(definition) = &definition.kind else {
                return None;
            };
            if definition.flags & Definition::NESTED_SUBSTITUTION != 0 {
                return None;
            }
            if is_copied {
                continue;
            }
            if position == 0 || position + 1 == frames.len() {
                return None;
            }
            // A selection the IR writes as a LET without a range, whose operator it applies at
            // the selector, where SANY's selection through the INSTANCE has the `SubstInNode`
            // first.
            // The selection's LET pushes no frame (`is_selection_let`), but the application of
            // its operator at the selector does.
            let range = |node: NodeId| ir.nodes.arena[node as usize].range;
            let is_selection = |node: NodeId| match &ir.nodes.arena[node as usize].kind {
                NodeKind::Let { .. } => range(node).is_none(),
                NodeKind::Apply { name, .. } => &*ir.texts[name.text as usize] == SELECTION_NAME,
                _ => false,
            };
            if frames[..position].iter().any(|&node| is_selection(node))
                || frames[..position]
                    .windows(2)
                    .any(|pair| range(pair[0]).is_some() && range(pair[0]) == range(pair[1]))
            {
                return None;
            }
            let location = ir
                .model
                .instance_actions
                .iter()
                .find(|action| action.definition == index)
                .and_then(|action| action.location)?;
            inserted.push((position, location));
        }
        Some(inserted)
    }

    // The nodes reachable from some definitions, through the nodes the IR writes once.
    fn reach(ir: &Ir, roots: impl Iterator<Item = NodeId>) -> HashSet<NodeId> {
        let arena = &ir.nodes.arena;
        let mut pending: Vec<NodeId> = roots.collect();
        let mut nodes = HashSet::new();
        while let Some(node) = pending.pop() {
            if !nodes.insert(node) {
                continue;
            }
            let kind = &arena[node as usize].kind;
            match kind {
                NodeKind::Reference(target) => pending.push(*target),
                NodeKind::SetFilter { bound, .. } => pending.push(bound.set),
                _ => {}
            }
            pending.extend(kind.children());
        }
        nodes
    }

    // The nodes the copies reach that no other definition does, the copies' indices, and whether
    // a copy is given as an operator's argument.
    fn get_copy_frames(&mut self) -> &CopyFrames {
        self.copy_frames.get_or_insert_with(|| {
            let ir = self.ir;
            let copies: HashSet<Index> = (0..ir.definitions.len())
                .filter(|&index| {
                    matches!(&ir.nodes.arena[ir.definitions[index] as usize].kind,
                        NodeKind::Definition(definition)
                            if definition.flags & Definition::SUBSTITUTED != 0)
                })
                .map(|index| index as Index)
                .collect();
            let (copied, own): (Vec<_>, Vec<_>) = (ir.definitions.iter().enumerate())
                .partition(|(index, _)| copies.contains(&(*index as Index)));
            let mut nodes = Self::reach(ir, copied.into_iter().map(|(_, &node)| node));
            // A copy given as an operator's argument is entered where the parameter is applied,
            // in no frame that names it: a node it shares counts as its own. A function a copy
            // defines is named where it is applied.
            let is_argument = ir.nodes.arena.iter().any(|node| match &node.kind {
                NodeKind::OperatorReference(name) | NodeKind::Identifier(name) => {
                    matches!(name.resolution, Resolution::Definition(index)
                        if copies.contains(&index)
                            && (matches!(node.kind, NodeKind::OperatorReference(_))
                                || matches!(&ir.nodes.arena[ir.definitions[index as usize] as usize].kind,
                                    NodeKind::Definition(definition)
                                        if matches!(&definition.form,
                                            DefinitionForm::Operator(params) if !params.is_empty()))))
                }
                _ => false,
            });
            if !is_argument {
                let shared = Self::reach(ir, own.into_iter().map(|(_, &node)| node));
                nodes.retain(|node| !shared.contains(node));
            }
            let nested_local = (ir.nodes.arena.iter())
                .filter_map(|node| match &node.kind {
                    NodeKind::Definition(definition)
                        if definition.flags & Definition::NESTED_SUBSTITUTION != 0
                            && definition.flags & Definition::SUBSTITUTED == 0 =>
                    {
                        Some(definition.name)
                    }
                    _ => None,
                })
                .collect();
            CopyFrames {
                nodes,
                copies,
                is_argument,
                nested_local,
            }
        })
    }

    // The nodes of the definitions INSTANCEs with substitutions copy, and of what they reach.
    fn get_substituted_nodes(&mut self) -> &HashSet<NodeId> {
        self.substituted_nodes.get_or_insert_with(|| {
            let ir = self.ir;
            let arena = &ir.nodes.arena;
            let mut pending: Vec<NodeId> = ir
                .definitions
                .iter()
                .enumerate()
                .filter(|&(index, &node)| {
                    matches!(&arena[node as usize].kind,
                        NodeKind::Definition(definition)
                            if definition.flags & Definition::SUBSTITUTED != 0)
                        || ir
                            .model
                            .instance_actions
                            .iter()
                            .any(|action| action.definition as usize == index)
                })
                .map(|(_, &node)| node)
                .collect();
            let mut nodes = HashSet::new();
            while let Some(node) = pending.pop() {
                if !nodes.insert(node) {
                    continue;
                }
                let kind = &arena[node as usize].kind;
                match kind {
                    NodeKind::Reference(target) => pending.push(*target),
                    NodeKind::SetFilter { bound, .. } => pending.push(bound.set),
                    _ => {}
                }
                pending.extend(kind.children());
            }
            nodes
        })
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

    // Whether TLC loads Integers' methods over Naturals', as the flags of an arithmetic builtin
    // the IR holds tell: Integers' + or < is no method of Naturals, and Naturals has no unary
    // minus. None where it holds none of them.
    fn is_integers_loaded(&self) -> Option<bool> {
        self.ir
            .builtins
            .iter()
            .find_map(|builtin| match self.name(builtin.name) {
                "+" | "-" | "*" | "^" | "\\div" | "%" | ".." | "<" | ">" | "<=" => {
                    Some(builtin.flags & Builtin::NATURALS_METHOD == 0)
                }
                ">=" => Some(builtin.flags & Builtin::NATURALS_GEQ == 0),
                "-." => Some(true),
                _ => None,
            })
    }

    // `f[x]` with TLC's message where `x` isn't in the domain of `f`.
    pub(crate) fn apply_checked(&self, function: &Value, key: &Value) -> Evaluated<Value> {
        // `TupleValue.apply` and `RecordValue.apply` fail on a key of another kind before they
        // look it up, printing it.
        if let Value::Function(inner) = function
            && !self.is_174()
            && matches!(inner.class.get(), Class::Tuple | Class::Record)
            && !matches!(key, Value::Int(_) | Value::Str(_))
            && let Some(error) = print_failure(key)
        {
            return Err(error);
        }
        if let Value::Function(inner) = function
            && !self.is_174()
            && match inner.class.get() {
                Class::Tuple => !matches!(key, Value::Int(_)),
                Class::Record => !matches!(key, Value::Str(_)),
                _ => false,
            }
            && let Some(text) = describe_missing(function, inner.class.get(), key)
        {
            return fail_runtime("applied a function outside its domain", text);
        }
        if let Value::Function(inner) = function
            && !self.is_174()
        {
            integer_domain_failure(inner, key)?;
        }
        let class_of = |inner: &crate::value::Function| {
            if inner.class.get() == Class::Lambda
                && inner.java_class.get() == Some(Class::Plain)
                && inner.is_eager_record.get()
            {
                Class::Plain
            } else {
                inner.class.get()
            }
        };
        // `FcnRcdValue.select` of a function built over an interval (`intv`) fails on a key that
        // isn't an integer before it compares it with any.
        if let Value::Function(inner) = function
            && !self.is_174()
            && inner.interval.is_some()
            && class_of(inner) == Class::Plain
            && !matches!(key, Value::Int(_))
            && let Some(text) = describe_missing(function, Class::Plain, key)
        {
            return fail_runtime("applied a function outside its domain", text);
        }
        let result = apply_value(function, key);
        match (&result, function) {
            (Err(error), Value::Function(inner))
                if error.message.is_none()
                    && !self.is_174()
                    && error.reason == "applied a function outside its domain" =>
            {
                let class = class_of(inner);
                match describe_missing(function, class, key) {
                    Some(text) => fail_runtime(&error.reason, text),
                    None => result,
                }
            }
            _ => result,
        }
    }

    // `r.f`, with TLC's messages as `getFieldSelector` words them.
    fn select_field(&mut self, node: NodeId, record: &Value, field: &Value) -> Evaluated<Value> {
        let Value::Str(name) = field else {
            return fail("a field that isn't a string");
        };
        let name = String::from_utf16_lossy(&name.units);
        // `Tool`'s OPCODE_rs takes a function TLC keeps lazy as the value it builds (`toFcnRcd`).
        if let Value::Lambda(lambda) = record {
            return crate::value::lambda_as_function(lambda);
        }
        let Value::Function(inner) = record else {
            if let Some(error) = print_failure(record) {
                return Err(error);
            }
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
                Some(position) => applied_value(inner, position),
                // TLC's NullPointerException printing the record, which isn't an EvalException.
                None if record_null_failure(record).is_some() => {
                    fail("selected a field a record holding a null lacks")
                }
                // TLC prints the record of TLCGet("spec") in the order of the HashMap it built it
                // from (`AbstractChecker.getSpecDescription`), which the evaluator's record,
                // normalized, doesn't keep.
                None if is_spec_description(&format_pretty(record)) => fail(
                    "selected a field TLCGet(\"spec\")'s record lacks, which TLC prints in its own order",
                ),
                None => fail_runtime(
                    "selected a field a record lacks",
                    format!(
                        "Attempted to select nonexistent field \"{name}\" from the record\n{}\n{}",
                        format_pretty(record),
                        self.describe_range(node)
                    ),
                ),
            },
            _ => {
                integer_domain_failure(inner, field)?;
                // A constructor over an interval, built or kept lazy, is a FcnRcdValue over that
                // interval once `toFcnRcd` builds it, whose `select` takes an integer alone.
                if inner.class.get() == Class::Lambda && inner.is_domain_interval.get() {
                    return fail_runtime(
                        "applied a function over an interval to a non-integer",
                        format!(
                            "Attempted to apply function with integer domain to the non-integer argument {}",
                            format_pretty(field)
                        ),
                    );
                }
                match self.selected_key(inner, field, true)? {
                    Some(position) => Ok(inner.range[position].clone()),
                    None => fail_runtime(
                        "applied a function outside its domain",
                        format!(
                            "Attempted to apply function:\n{}\nto argument \"{name}\", which is not in the domain of the function.",
                            format_pretty(record)
                        ),
                    ),
                }
            }
        }
    }

    // Where `r.f`, or an EXCEPT's `Value.select`, finds the key in a function that isn't a
    // record: `FcnRcdValue.select` searches a sorted function of fewer than 32 keys key by key
    // (`selectLinearSearch`), each key asked whether it equals the argument, as it does the
    // FcnRcdValue that `Tool`'s OPCODE_rs converts a function TLC keeps lazy to (`toFcnRcd`,
    // `is_converted`), of the keys its set enumeration gives, sorted. The search is the
    // evaluator's where the order isn't certain.
    fn selected_key(
        &mut self,
        inner: &Rc<Function>,
        field: &Value,
        is_converted: bool,
    ) -> Evaluated<Option<usize>> {
        let is_lazy_over_enumeration = is_converted
            && inner.class.get() == Class::Lambda
            && (inner.domain.len() == 1
                || inner.search.get() == Search::SortedDomain
                || self
                    .held_lazy_domains
                    .get(&(Rc::as_ptr(inner) as usize))
                    .is_some_and(|(held, _)| held.strong_count() > 0));
        // `Tool`'s OPCODE_fc builds a function over Reducible domains where it doesn't keep it
        // lazy, which `toFcnRcd` normalizes.
        let is_built_sorted = inner.class.get() == Class::Lambda
            && inner.java_class.get() == Some(Class::Plain)
            && inner.is_eager_record.get()
            && inner.domain.len() < crate::value::BINARY_SEARCH_KEYS;
        let is_linear = inner.interval.is_none()
            && inner.domain.len() < crate::value::BINARY_SEARCH_KEYS
            && (searches_linearly(inner)
                || searches_sorted_linearly(inner)
                || is_lazy_over_enumeration
                || is_built_sorted);
        if !is_linear {
            return find_key(inner, field);
        }
        for (position, key) in inner.domain.iter().enumerate() {
            match equals(key, field) {
                Ok(true) => return Ok(Some(position)),
                Ok(false) => {}
                // A key that isn't an integer, a boolean or a string may have a source, which
                // heads TLC's FingerprintException.
                Err(error) => {
                    if !matches!(key, Value::Int(_) | Value::Bool(_) | Value::Str(_))
                        && let Some(stack) = &mut self.call_stack
                    {
                        stack.unfollowed.get_or_insert(UNPLACED_KEY_SEARCH);
                    }
                    return Err(error);
                }
            }
        }
        Ok(None)
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

    // `~`, `=>` and `<=>` as `Tool.evalAppl` evaluates them (`OPCODE_lnot`, `OPCODE_implies`,
    // `OPCODE_equiv`), failing with its message, which names the operand's kind
    // (`getKindString`) and where the expression is, on an operand that isn't a boolean: `=>`
    // evaluates Q only where P is true, `<=>` both operands before it tests either.
    fn logical(
        &mut self,
        node: NodeId,
        operator: &str,
        args: &[NodeId],
        context: &Context,
    ) -> Evaluated<Value> {
        let non_boolean = |evaluator: &Self, value: &Value, text: &dyn Fn(&str) -> String| {
            let reason = format!("expected a boolean, not a {}", value.kind_name());
            match kind_string(value) {
                Some(kind) if !evaluator.is_174() => fail_runtime::<()>(
                    reason,
                    format!("{}\n{}", text(kind), evaluator.describe_range(node)),
                ),
                _ => fail(reason),
            }
            .unwrap_err()
        };
        let operand = |evaluator: &mut Self, arg: NodeId| {
            evaluator.operand(&Operand::Node(arg, context.clone()))
        };
        match operator {
            "~" => match operand(self, args[0])? {
                Value::Bool(boolean) => Ok(Value::Bool(!boolean)),
                other => Err(non_boolean(self, &other, &|kind| {
                    format!("Attempted to apply the operator ~ to a non-boolean\n({kind})")
                })),
            },
            "=>" => {
                let check = |evaluator: &Self, value: Value, side: &str| match value {
                    Value::Bool(boolean) => Ok(boolean),
                    other => Err(non_boolean(evaluator, &other, &|kind| {
                        format!(
                            "Attempted to evaluate an expression of form P => Q when {side} was\n{kind}."
                        )
                    })),
                };
                let left = operand(self, args[0])?;
                if !check(self, left, "P")? {
                    return Ok(Value::Bool(true));
                }
                let right = operand(self, args[1])?;
                Ok(Value::Bool(check(self, right, "Q")?))
            }
            _ => {
                let left = operand(self, args[0])?;
                let right = operand(self, args[1])?;
                match (&left, &right) {
                    (Value::Bool(left), Value::Bool(right)) => Ok(Value::Bool(left == right)),
                    _ => {
                        let other = if matches!(left, Value::Bool(_)) {
                            &right
                        } else {
                            &left
                        };
                        let reason = format!("expected a boolean, not a {}", other.kind_name());
                        if self.is_174() {
                            return fail(reason);
                        }
                        fail_runtime(
                            reason,
                            format!(
                                "Attempted to evaluate an expression of form P <=> Q when P or Q was not a boolean.\n{}",
                                self.describe_range(node)
                            ),
                        )
                    }
                }
            }
        }
    }

    fn evaluate_node(&mut self, node: NodeId, context: &Context) -> Evaluated<Value> {
        let kind = self.kind(node);
        match kind {
            NodeKind::Number(int) => Ok(Value::Int(*int)),
            NodeKind::WideNumber(_) => fail("an integer outside 32 bits"),
            NodeKind::Decimal(_) => fail("a real number"),
            // TLC makes a string literal's value once, as the node's tool object, so each
            // evaluation of the node gives the same object (`Tool.evalAppl`'s `StringKind`).
            NodeKind::String(text) => {
                let node = self.node(node).0;
                if let Some(literal) = self.literals.get(&node) {
                    return Ok(Value::Str(Rc::clone(literal)));
                }
                let literal = self.text_of(self.ir.get_text_units(*text).into());
                self.literals.insert(node, Rc::clone(&literal));
                Ok(Value::Str(literal))
            }
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
                    // `Tool`'s OPCODE_domain names its own `expr` once in the message it fails
                    // with, which passes through any enclosing DOMAIN unchanged. The message the
                    // failing application built still ends with the kind it names, `(...)`; one
                    // an inner DOMAIN already placed ends with that DOMAIN's location.
                    self.apply(name, args, context).map_err(|mut error| {
                        if let Some(message) = &mut error.message
                            && error.reason == DOMAIN_OF_NON_FUNCTION
                            && message.text.ends_with(')')
                        {
                            message.text =
                                format!("{}\n{}", message.text, self.describe_range(node));
                        }
                        error
                    })
                }
                // `Tool#evalAppl` fails on a temporal operator (`OPCODE_leadto`, `OPCODE_arrow`)
                // before it evaluates the operands.
                (Resolution::Builtin(_) | Resolution::None, &[_, _])
                    if !self.is_enabling && matches!(self.name(name.text), "~>" | "-+->") =>
                {
                    let operator = if self.name(name.text) == "~>" {
                        "a ~> b"
                    } else {
                        "a -+-> formula"
                    };
                    fail_with(
                        "a temporal formula in a state",
                        TlcMessage {
                            text: format!(
                                "TLC encountered a temporal formula ({operator}) when evaluating a predicate or action.\n{}",
                                self.describe_range(node)
                            ),
                            code: Some(ENCOUNTERED_FORMULA_IN_PREDICATE),
                            is_eval_exception: false,
                            inner: None,
                        },
                    )
                }
                (Resolution::Builtin(index), _)
                    if !name.is_local
                        && matches!(
                            (self.name(self.ir.builtins[index as usize].name), args.len()),
                            ("~", 1) | ("=>" | "<=>" | "\\equiv", 2)
                        ) =>
                {
                    let operator = self.name(self.ir.builtins[index as usize].name);
                    self.logical(node, operator, args, context)
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
                    None => fail_runtime(
                        "no CASE arm holds",
                        format!(
                            "Attempted to evaluate a CASE with no conditions true.\n{}",
                            self.describe_range(node)
                        ),
                    ),
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
                    holds = evaluator.boolean_as(*body, inner, Demand::Quantifier(node))?;
                    Ok(holds)
                })?;
                Ok(Value::Bool(holds))
            }
            NodeKind::Exists { bounds, body } => {
                let mut holds = false;
                self.for_each_binding(bounds, context, &mut |evaluator, inner| {
                    holds = evaluator.boolean_as(*body, inner, Demand::Quantifier(node))?;
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
                if !is_enumerable(&set) {
                    return fail_runtime(
                        "CHOOSE of a value TLC doesn't enumerate",
                        format!(
                            "Attempted to compute the value of an expression of\nform CHOOSE x \\in S: P, but S was not enumerable.\n{}",
                            self.describe_range(node)
                        ),
                    );
                }
                // `OPCODE_bc` normalizes the set before it enumerates it.
                crate::sets::normalize_parts(&set)?;
                let set = self.settle(&set)?;
                crate::sets::check_enumerated_bound(&set)?;
                // `elements(Ordering.NORMALIZED)` builds an interval into a set enumeration
                // (`EnumerableValue.elements`, `IntervalValue.toSetEnum`) whose array it sizes
                // first, which fails past 2^31 - 1 elements (`IntervalValue.size`).
                if let Value::Interval(low, high, _) = &set {
                    crate::value::interval_size(*low, *high)?;
                }
                let elements = elements(&set)?;
                // `OPCODE_bc` stops where the enumeration gives null, an INSTANCE's fact literal
                // TLC did not initialize, as where it gives no more.
                let elements: &[Value] = if is_null_enumeration(&elements)? {
                    &[]
                } else {
                    &elements
                };
                for element in elements.iter() {
                    // `OPCODE_bc` takes each element of a tuple pattern's set as a tuple of as
                    // many elements as the pattern names (`toTuple`).
                    if let Pattern::Tuple(names) = pattern {
                        if matches!(element, Value::Lambda(_) | Value::Lazy(_)) {
                            return fail("CHOOSE of a tuple pattern over a lazy value");
                        }
                        if as_tuple(element).is_none_or(|tuple| tuple.len() != names.len()) {
                            return fail_runtime(
                                TUPLE_MISMATCH,
                                format!(
                                    "Attempted to compute the value of an expression of form\nCHOOSE <<x1, ... , xN>> \\in S: P, but S was not a set\nof N-tuples.\n{}",
                                    self.describe_range(node)
                                ),
                            );
                        }
                    }
                    let inner = self.bind_pattern(pattern, element, context)?;
                    // `OPCODE_bc` names the CHOOSE where its predicate isn't a boolean.
                    if self.boolean_as(*body, &inner, Demand::Quantifier(node))? {
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
            // `OPCODE_ue` and `OPCODE_uf`: nor any quantifier without a bound. Where it computes
            // ENABLED of one as an action, it words the failure apart.
            NodeKind::UnboundedQuantifier {
                is_temporal: false, ..
            } if self.is_enabling => fail("an unbounded quantifier in ENABLED"),
            NodeKind::UnboundedQuantifier {
                is_temporal: false,
                is_forall,
                ..
            } => {
                let symbol = if *is_forall { "\\A" } else { "\\E" };
                fail_runtime(
                    "an unbounded quantifier",
                    format!(
                        "TLC attempted to evaluate an unbounded {symbol}.\nMake sure that the expression is of form {symbol} x \\in S: P(x).\n{}",
                        self.describe_range(node)
                    ),
                )
            }
            NodeKind::SetEnumeration(items) => {
                let values = items
                    .iter()
                    .map(|&item| self.evaluate(item, context))
                    .collect::<Evaluated<Vec<_>>>()?;
                self.held_set(values)
            }
            NodeKind::SetFilter { bound, predicate } => {
                let set = self.evaluate(bound.set, context)?;
                if !self.is_starting && matches!(set, Value::Unsorted(_)) {
                    return fail(UNSORTED_STATE_BOUND);
                }
                let class_is_known = crate::value::set_dispatch_is_known(&set);
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
                    self.captures += 1;
                    let predicate = Predicate {
                        pattern: bound.pattern.clone(),
                        body: *predicate,
                        context: context.clone(),
                        current: self.current.clone(),
                        next: self.next.clone(),
                        level: self.level,
                        text: (
                            format!("{{{names} \\in "),
                            format!(" : <expression {}> }}", self.expression_text(*predicate)?),
                        ),
                        is_untraced: self.is_starting || self.call_stack.is_none(),
                        filtered,
                        converted: RefCell::new(None),
                    };
                    return Ok(Value::lazy_with_class(
                        Lazy::Filter(set, Rc::new(predicate)),
                        class_is_known.then_some(SetClass::Predicate),
                    ));
                }
                let demand = if matches!(
                    java_set_class(&set),
                    Some(SetClass::Enumeration | SetClass::Interval)
                ) {
                    Demand::Filter
                } else {
                    Demand::Unworded
                };
                let mut kept = Vec::new();
                // OPCODE_sso walks the set's elements (`elements()`), an interval's without
                // counting it, as far as the evaluator walks one.
                let walked: Box<dyn Iterator<Item = Value>> = match set {
                    Value::Interval(low, high, _) => {
                        crate::value::check_walk(low, high)?;
                        Box::new(
                            (low..=high)
                                .map(Value::Int)
                                .take(crate::value::MAXIMUM_WALK + 1),
                        )
                    }
                    _ => {
                        let elements = elements(&set)?;
                        // OPCODE_sso stops where the enumeration gives null, an INSTANCE's fact
                        // literal TLC did not initialize.
                        if is_null_enumeration(&elements)? {
                            Box::new(std::iter::empty())
                        } else {
                            Box::new(Rc::unwrap_or_clone(elements).into_iter())
                        }
                    }
                };
                for (index, element) in walked.enumerate() {
                    if index >= crate::value::MAXIMUM_WALK {
                        return fail("an interval too large to build");
                    }
                    let element = &element;
                    self.require_tuple_cast(&bound.pattern, element)?;
                    // OPCODE_sso binds each name of a tuple pattern to the element of the
                    // TupleValue at its index, ignoring those past them.
                    let inner = match &bound.pattern {
                        Pattern::Tuple(names) => {
                            let Some(tuple) = as_tuple(element) else {
                                return fail(TUPLE_MISMATCH);
                            };
                            if tuple.len() < names.len() {
                                return index_out_of_bounds(
                                    TUPLE_MISMATCH,
                                    tuple.len(),
                                    tuple.len(),
                                );
                            }
                            let mut inner = context.clone();
                            for (&name, element) in names.iter().zip(tuple) {
                                inner = inner.bind_value(name, element.clone());
                            }
                            inner
                        }
                        Pattern::Name(_) => self.bind_pattern(&bound.pattern, element, context)?,
                    };
                    if self.boolean_as(*predicate, &inner, demand)? {
                        push_set_element(&mut kept, element.clone())?;
                    }
                }
                Ok(Value::set_with_class(
                    kept,
                    class_is_known.then_some(SetClass::Enumeration),
                ))
            }
            NodeKind::SetMap { expression, bounds } => {
                let mut values = Vec::new();
                self.declines_unsorted_bound = true;
                self.for_each_binding(bounds, context, &mut |evaluator, inner| {
                    let value = evaluator.evaluate(*expression, inner)?;
                    push_set_element(&mut values, value)?;
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
            } => self.construct_in_place(node, bounds, *body, context),
            NodeKind::FunctionSet { domain, range } => {
                let domain = self.evaluate(*domain, context)?;
                let range = self.evaluate(*range, context)?;
                Ok(Value::lazy(Lazy::FunctionSet(domain, range)))
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
                Ok(Value::lazy(Lazy::RecordSet(
                    sets.into_iter().map(|(name, set, _)| (name, set)).collect(),
                    written,
                )))
            }
            NodeKind::Except { function, updates } => {
                // `OPCODE_exc` evaluates the function it updates with its own control: where TLC
                // keeps it lazy, a constructor `held_constructor` follows is the FcnLambdaValue
                // whose `select` evaluates the body at the key and whose `takeExcept` adds the
                // update, unbuilt.
                let held = if self.keeping_lazy > 0 {
                    self.held_constructor(*function, context)?
                } else {
                    None
                };
                let mut value = match held {
                    Some(held) => held,
                    None => self.evaluate(*function, context)?,
                };
                let original = value.clone();
                let mut is_taken = false;
                for (index, update) in updates.iter().enumerate() {
                    let keys = update
                        .path
                        .iter()
                        .map(|step| self.except_key(step, context))
                        .collect::<Evaluated<Vec<_>>>()?;
                    // `Value.select` of the first update's path, on the function as built.
                    if index == 0
                        && let Some(key) = keys.first()
                    {
                        let node = self.resolved(*function);
                        self.lazy_domain_failure(&value, node, key)?;
                    }
                    self.except_selected = None;
                    let excepted = self.except(&value, &keys, update.value, context, *function);
                    if excepted.is_err()
                        && let Some(selected) = self.except_selected.take()
                    {
                        self.place_except_failure(&original, is_taken, &selected);
                    }
                    let excepted = excepted?;
                    // `takeExcept` builds a new value, which has no source; one whose key is
                    // missing is the value as it was (`OPCODE_exc` warns).
                    is_taken |= address(&excepted) != address(&value);
                    value = excepted;
                }
                self.unforced_use(value)
            }
            NodeKind::ExceptAt => match &context.at {
                Some(value) => Ok(value.clone()),
                None => fail("@ outside an EXCEPT"),
            },
            NodeKind::FunctionApplication { function, args } => {
                // `Tool.evalAppl` evaluates the function with `EvalControl.KeepLazy`, so
                // TestRandomSetOfSubsets's constructor stays lazy and draws once, for the key.
                if let NodeKind::Apply { name, args: drawn } = self.kind(*function)
                    && !name.is_local
                    && let Resolution::Builtin(index) = name.resolution
                    && self.name(self.ir.builtins[index as usize].name) == "TestRandomSetOfSubsets"
                    && let [key] = args.as_slice()
                {
                    if self.ir.builtins[index as usize].flags != 0 || drawn.len() != 3 {
                        return fail("TestRandomSetOfSubsets without default Java method origin");
                    }
                    let operands: Vec<Operand> = drawn
                        .iter()
                        .map(|&operand| Operand::Node(operand, context.clone()))
                        .collect();
                    let key = Operand::Node(*key, context.clone());
                    return self.test_random_set_of_subsets(&operands, Some(&key));
                }
                let value = self.apply_function(node, *function, args, context)?;
                self.unforced_use(value)
            }
            NodeKind::FieldAccess { record, field } => {
                // A field of TLCGet("stats") as TLC checks the assumptions other than the time
                // it has run, which the record holds as well.
                if self.is_in_assumptions
                    && self.runtime.is_none()
                    && let Some(value) = self.assumed_statistic(*record, *field)
                {
                    return Ok(value);
                }
                let record = self.evaluate(*record, context)?;
                let key = Value::Str(self.text(*field));
                let value = self.select_field(node, &record, &key)?;
                self.unforced_use(value)
            }
            NodeKind::Product(factors) => {
                let factors = factors
                    .iter()
                    .map(|&factor| self.evaluate(factor, context))
                    .collect::<Evaluated<Vec<_>>>()?;
                Ok(Value::lazy(Lazy::Product(factors)))
            }
            NodeKind::BoxAction { action, subscript } => {
                if self.boolean_as(*action, context, Demand::SquareAction(node))? {
                    return Ok(Value::Bool(true));
                }
                self.unchanged(*subscript, context)
            }
            NodeKind::AngleAction { action, subscript } => {
                if !self.boolean(*action, context)? {
                    return Ok(Value::Bool(false));
                }
                let now = self.evaluate_current_state(*subscript, context)?;
                let then = self.evaluate(*subscript, &context.primed(true))?;
                Ok(Value::Bool(!self.subscript_equals(&now, &then)?))
            }
            NodeKind::Label { body, .. } => self.evaluate(*body, context),
            NodeKind::Enabled(action) if !context.is_primed => self.enabled(*action, context),
            // `Tool#evalAppl` fails on a temporal operator (`OPCODE_box`, `OPCODE_diamond`,
            // `OPCODE_wf`, `OPCODE_sf`); `Tool#enabled` words its own failure, which isn't
            // followed.
            // `OPCODE_te` and `OPCODE_tf` for a temporal quantifier.
            NodeKind::Always(_)
            | NodeKind::Eventually(_)
            | NodeKind::WeakFairness { .. }
            | NodeKind::StrongFairness { .. }
            | NodeKind::UnboundedQuantifier {
                is_temporal: true, ..
            } if !self.is_enabling => {
                let operator = match kind {
                    NodeKind::Always(_) => "[]A",
                    NodeKind::Eventually(_) => "<>A",
                    NodeKind::WeakFairness { .. } => "WF",
                    NodeKind::UnboundedQuantifier {
                        is_forall: true, ..
                    } => "\\AA",
                    NodeKind::UnboundedQuantifier { .. } => "\\EE",
                    _ => "SF",
                };
                fail_with(
                    "a temporal formula in a state",
                    TlcMessage {
                        text: format!(
                            "TLC encountered a temporal formula ({operator}) when evaluating a predicate or action.\n{}",
                            self.describe_range(node)
                        ),
                        code: Some(ENCOUNTERED_FORMULA_IN_PREDICATE),
                        is_eval_exception: false,
                        inner: None,
                    },
                )
            }
            _ => fail(format!("evaluating a {}", describe(kind))),
        }
    }

    // Tool evaluates a state formula with Empty as its successor scope.
    pub(crate) fn evaluate_current_state(
        &mut self,
        node: NodeId,
        context: &Context,
    ) -> Evaluated<Value> {
        let empty = vec![None; self.next.len()];
        let next = std::mem::replace(&mut self.next, empty);
        let result = self.evaluate(node, context);
        self.next = next;
        result
    }

    pub(crate) fn evaluate_next_state(
        &mut self,
        node: NodeId,
        context: &Context,
        primed_control: bool,
    ) -> Evaluated<Value> {
        let empty = vec![None; self.next.len()];
        let next = std::mem::replace(&mut self.next, empty);
        let current = std::mem::replace(&mut self.current, next.clone());
        let enabled = self.is_enabling;
        let primed = self.cache_control_primed;
        self.is_enabling = false;
        self.cache_control_primed = primed_control;
        let result = self.evaluate(node, &context.primed(false));
        self.current = current;
        self.next = next;
        self.is_enabling = enabled;
        self.cache_control_primed = primed;
        result
    }

    /// UNCHANGED e as an expression (`OPCODE_unchanged` of `Tool#evalImpl`, which an action
    /// reaches once every variable has a value): `v0.equals(v1)` of e's values in the two states,
    /// whose failure in the method of a value with a source TLC throws as a FingerprintException.
    pub(crate) fn unchanged(&mut self, subscript: NodeId, context: &Context) -> Evaluated<Value> {
        let now = self.evaluate_current_state(subscript, context)?;
        let then = self.evaluate(subscript, &context.primed(true))?;
        Ok(Value::Bool(self.sourced_equals(&now, &then)?))
    }

    // `now.equals(then)`, marking the replay's failure fingerprinted with the sources of the
    // values whose `equals` failed, as TLC's `CallStackTool` gives the values it builds sources.
    fn sourced_equals(&mut self, now: &Value, then: &Value) -> Evaluated<bool> {
        let result = equals(now, then);
        if result.is_err()
            && let Some(stack) = &mut self.call_stack
            && !stack.is_fingerprinted
            && !stack.is_frozen
        {
            let compared = failing_comparisons(|| equals(now, then))
                .err()
                .unwrap_or_default();
            let sources: Vec<NodeId> = std::iter::once(now)
                .chain(&compared)
                .filter_map(|value| stack.source(value))
                .collect();
            if !sources.is_empty() {
                stack.is_fingerprinted = true;
                stack.fingerprinted_sources = sources;
            }
        }
        result
    }

    /// Whether the subscript of `<<A>>_v` is the same in the current state, `now`, as in the next,
    /// `then`, as TLC compares them with `v1.equals(v2)` (`LNAction.eval`, and `Tool#enabled` for
    /// an ENABLED). TLC's rerun with its `CallStackTool` gives the values the subscript builds
    /// their sources, so a comparison that fails in the method of one with a source throws a
    /// FingerprintException (`TupleValue.equals`), which escapes `Worker#doNextCheckLiveness`
    /// and which `ModelChecker#doNextFailed` reports with no message: the replay marks the
    /// failure fingerprinted with those sources.
    pub(crate) fn subscript_equals(&mut self, now: &Value, then: &Value) -> Evaluated<bool> {
        let was_fingerprinted = self
            .call_stack
            .as_ref()
            .is_some_and(|stack| stack.is_fingerprinted);
        let result = self.sourced_equals(now, then);
        if let Some(stack) = &mut self.call_stack
            && stack.is_fingerprinted
            && !was_fingerprinted
        {
            stack.is_subscript_fingerprinted = true;
        }
        result
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
                    Some(value) => self.configuration_value(value),
                    None => fail(format!(
                        "the constant {}, whose value the IR can't hold",
                        self.name(name.text)
                    )),
                };
            }
            Resolution::Definition(index) => {
                let node = self.ir.definitions[index as usize];
                // TLC evaluates the definition the configuration substitutes for a constant each
                // time it reads the constant (`SpecProcessor.processConstantDefns`).
                if self.definition(node).name != name.text {
                    self.unshared
                        .get_or_insert("of a value a configuration's substitute made again");
                    // The name's lookup finds the substitute's OpDefNode, not the value
                    // `processConstantDefns` computed and deep-normalized for it, and
                    // `Tool.evalAppl` evaluates the body as written: a set it enumerates is a new
                    // SetEnumValue TLC holds unnormalized, with a source.
                    let definition = self.definition(node);
                    if matches!(&definition.form, DefinitionForm::Operator(params) if params.is_empty())
                        && definition.flags & Definition::CONFIGURED_SUBSTITUTE != 0
                        && definition.flags & Definition::LITERAL == 0
                        && !self.failed_startup.contains(&node)
                        && !self.uncomputed_warning_startup.contains(&node)
                        && !self
                            .ir
                            .model
                            .startup
                            .definitions
                            .iter()
                            .any(|&index| self.ir.definitions[index as usize] == node)
                    {
                        let body = definition.body;
                        return self.evaluate_definition(node, body, &context.global());
                    }
                }
                return self.definition_value(node, context);
            }
            Resolution::Builtin(index) if self.ir.builtins[index as usize].arity == 0 => {
                return self.builtin(index, &[], context);
            }
            // A constant declared without parameters that the configuration defines by a table
            // of rows with arguments: `Tool.evalAppl` applies the `OpRcdValue` to no arguments,
            // which fails at its first row.
            Resolution::Builtin(index)
                if self.ir.builtins[index as usize].flags & Builtin::TABLE != 0
                    && !self.ir.builtins[index as usize].table.is_empty() =>
            {
                return self.builtin(index, &[], context);
            }
            _ => {}
        }
        match lookup(&context.env, name.text) {
            Some(frame) => self.binding(&frame, context),
            None => fail(format!("the name {}", self.name(name.text))),
        }
    }

    // A value the frame keeps its later uses read, where TLC's LazyValue reads the one object
    // too; where it doesn't keep it (`Tool` expands a LazyValue directly where the next state is
    // null), both build it again.
    //
    // A thunk whose value is one function TLC keeps lazy, whose body printed, that TLC hasn't
    // forced (`Frame::is_thunk_unforced`), TLC forces again where a print forces a copy of it: the
    // evaluator builds it again, with its body's effects, and nothing else, which it holds as the
    // copy of TLC's one function (`LazyPrint::thunk`), and declines where something forces it in
    // place (`force_lazy_prints`).
    fn binding(&mut self, frame: &Rc<Frame>, context: &Context) -> Evaluated<Value> {
        let is_rebuilt =
            frame.holds_lazy_print.get() && self.cached_binding(frame, context).is_some();
        if is_rebuilt {
            if !frame.is_thunk_unforced.get() {
                return fail(LAZY_BODY_EFFECTS);
            }
            *frame.cached.borrow_mut() = None;
        }
        let first = self.lazy_print_count;
        let before = self.lazy_effects();
        let value = self.binding_value(frame, context);
        if !matches!(frame.binding, Binding::Function { .. }) {
            let built = self.lazy_prints_from(first);
            if built < self.lazy_prints.len() {
                frame.holds_lazy_print.set(true);
                // One function, the thunk's value, whose build had no effect but its body's.
                let now = self.lazy_effects();
                let is_one = matches!(&self.lazy_prints[built..], [lazy]
                    if lazy.start == before
                        && lazy.end == now
                        && matches!(&value, Ok(Value::Function(function)) if Rc::ptr_eq(function, &lazy.function)));
                if is_one {
                    // A thunk whose value is another thunk's (`LET E == C`, or an argument
                    // naming it) holds TLC's same FcnLambdaValue, its LazyValue reading the one
                    // the other's holds: the function stays the innermost thunk's, which a force
                    // through either marks, and the outer one's later uses build the inner one
                    // again or decline with it.
                    let lazy = &mut self.lazy_prints[built];
                    if lazy.thunk.is_none() {
                        lazy.thunk = Some((Rc::downgrade(frame), is_rebuilt));
                    }
                    frame.is_thunk_unforced.set(true);
                } else {
                    frame.is_thunk_unforced.set(false);
                    if is_rebuilt {
                        return fail(LAZY_BODY_EFFECTS);
                    }
                }
            } else if is_rebuilt {
                return fail(LAZY_BODY_EFFECTS);
            }
        }
        value
    }

    // The value a thunk's frame keeps that a use here reads (`LazyValue.getValue`).
    fn cached_binding(&self, frame: &Rc<Frame>, context: &Context) -> Option<Value> {
        let Binding::Thunk {
            context: bound,
            is_self,
            ..
        } = &frame.binding
        else {
            return None;
        };
        let inner =
            own_context(bound, frame, *is_self).primed(context.is_primed || bound.is_primed);
        if inner.is_primed {
            return None;
        }
        frame
            .cached
            .borrow()
            .as_ref()
            .filter(|cached| {
                !matches!(cached.value, Value::Null)
                    && Rc::ptr_eq(&self.identity, &cached.evaluator)
                    && cached.is_primed == self.cache_control_primed
                    && cached.is_enabling == self.is_enabling
                    && state_extends(&self.current, &cached.current)
                    && state_extends(&self.next, &cached.next)
            })
            .map(|cached| cached.value.clone())
    }

    fn binding_value(&mut self, frame: &Rc<Frame>, context: &Context) -> Evaluated<Value> {
        match &frame.binding {
            Binding::Value(value) => Ok(value.clone()),
            Binding::Thunk {
                node,
                context: bound,
                is_self,
            } => {
                let inner = own_context(bound, frame, *is_self)
                    .primed(context.is_primed || bound.is_primed);
                // Tool expands a LazyValue directly when its next state is null.
                if inner.is_primed {
                    return self.evaluate(*node, &inner);
                }
                // LazyValue.getValue treats Cache(null) as a miss, while the write below
                // still replaces an older non-null entry for another state.
                if let Some(cached) = self.cached_thunk(frame) {
                    // The FcnLambdaValue TLC keeps for a constructor applied (`held_constructor`),
                    // which another use may build, by its `toFcnRcd`, or not. Without effects in
                    // its body, over a set TLC can normalize, building it shows only as the
                    // domain normalized, as `toFcnRcd` normalizes it; the evaluator builds it.
                    // Otherwise it doesn't follow which.
                    if let Value::Lambda(lambda) = &cached
                        && is_held_constructor(&cached)
                    {
                        if !lambda.excepts.is_empty()
                            || matches!(lambda.domain, Value::Unsorted(_))
                            || self.has_effect(lambda.body, &lambda.context)
                        {
                            return fail(
                                "a function TLC keeps lazy in an argument, used but applied",
                            );
                        }
                        let (reads, captures) = (self.reads, self.captures);
                        // A build that fails, such as of a body that fails at a key the
                        // application didn't ask, is one TLC doesn't make where the use only
                        // reads the cached function's domain or prints it (`toString` swallows
                        // the failure), which the evaluator doesn't follow.
                        let value = match self.evaluate(*node, &inner) {
                            Ok(value) => value,
                            Err(error) if error.message.is_some() => {
                                return fail(
                                    "a function TLC keeps lazy, applied, then used where its build fails",
                                );
                            }
                            Err(error) => return Err(error),
                        };
                        self.cache_thunk(frame, &value, reads, captures);
                        return Ok(value);
                    }
                    return Ok(cached);
                }
                let (reads, captures) = (self.reads, self.captures);
                let value = self.evaluate(*node, &inner)?;
                self.cache_thunk(frame, &value, reads, captures);
                // TLC keeps the value it computes for a next state, as one object.
                if !matches!(value, Value::Null)
                    && frame.is_evaluated.replace(true)
                    && !is_scalar(&value)
                {
                    self.unshared
                        .get_or_insert("of a value an argument or a LET definition made again");
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
                let is_recursive = definition.flags & Definition::SELF_REFERENTIAL != 0;
                // TLC binds the definition to a LazyValue, which keeps the value its first use
                // computes, whatever the control: one kept lazy, as the function of an
                // application, it reads at every later use, which the evaluator builds again.
                // An application before keeps the FcnLambdaValue unforced (`apply` evaluates the
                // body at the key only), with the domain it evaluated then: a use as a value
                // builds it as the evaluator does where building it has no effect but the body's,
                // whose lines TLC prints where it forces it, or its copy.
                let was_applied =
                    self.keeping_lazy == 0 && frame.is_evaluated.get() && !is_recursive;
                if self.keeping_lazy > 0 {
                    frame.is_evaluated.set(true);
                }
                let effects = self.lazy_effects();
                let first = self.lazy_print_count;
                let function =
                    self.defined_function(bounds, definition.body, &inner, is_recursive)?;
                // A lazy function whose body printed, the domain evaluated without effects, which
                // TLC builds again at each force of its copy or of the function it holds where
                // that is unforced (`FcnLambdaValue`), as the evaluator does.
                let now = self.lazy_effects();
                let is_one = self.lazy_prints_from(first) + 1 == self.lazy_prints.len();
                let lazy = self.lazy_prints.last_mut().filter(|lazy| {
                    is_one && lazy.id >= first && lazy.start == effects && lazy.end == now
                });
                let is_lazy = lazy.is_some();
                if was_applied && !is_lazy && effects != now {
                    return fail(
                        "a function a LET defines, which TLC kept lazy where it first applied it",
                    );
                }
                if let Some(lazy) = lazy {
                    lazy.origin = Some(Rc::downgrade(frame));
                }
                // The LazyValue builds the function once, with its body's prints, TLCSet writes
                // and random draws, and every later use reads that value: the evaluator, building
                // it again, would have them again.
                if frame.is_built.replace(true) {
                    if effects != now && !(is_lazy && frame.is_lazy_unforced.get()) {
                        return fail(BUILT_LET_FUNCTION_EFFECTS);
                    }
                } else {
                    frame.is_lazy_unforced.set(is_lazy);
                }
                Ok(function)
            }
            Binding::Operator(_) => fail("an operator used as a value"),
        }
    }

    // The value a thunk's `LazyValue` keeps for the evaluator's states and control
    // (`LazyValue.getCachedValue`), adding the reads and captures computing it made.
    fn cached_thunk(&mut self, frame: &Rc<Frame>) -> Option<Value> {
        let (value, reads, captures) = self.peek_thunk(frame)?;
        self.reads += reads;
        self.captures += captures;
        Some(value)
    }

    // The value `cached_thunk` gives, with the reads and captures computing it made.
    fn peek_thunk(&self, frame: &Rc<Frame>) -> Option<(Value, u64, u64)> {
        let cached = frame.cached.borrow();
        let cached = cached.as_ref()?;
        if matches!(cached.value, Value::Null)
            || !Rc::ptr_eq(&self.identity, &cached.evaluator)
            || cached.is_primed != self.cache_control_primed
            || cached.is_enabling != self.is_enabling
            || !state_extends(&self.current, &cached.current)
            || !state_extends(&self.next, &cached.next)
        {
            return None;
        }
        Some((cached.value.clone(), cached.reads, cached.captures))
    }

    // Keeps a thunk's value for the evaluator's states and control (`LazyValue.getValue`),
    // computed from `reads` and `captures` on.
    fn cache_thunk(&mut self, frame: &Rc<Frame>, value: &Value, reads: u64, captures: u64) {
        if !frame
            .cached
            .borrow()
            .as_ref()
            .is_some_and(|cached| Rc::ptr_eq(&cached.evaluator, &self.identity))
        {
            if self.cached_frames.len() == self.cached_frames.capacity() {
                self.collect_cached_frames();
                self.cached_frames.retain(|frame| frame.strong_count() > 0);
            }
            self.cached_frames.push(Rc::downgrade(frame));
        }
        FILTER_CONVERSION_JOURNALS.with(|journals| {
            if let Some(journal) = journals.borrow_mut().last_mut() {
                journal.push(SpeculativeChange::Thunk(
                    Rc::downgrade(frame),
                    frame.cached.borrow().clone(),
                    frame.is_evaluated.get(),
                ));
            }
        });
        *frame.cached.borrow_mut() = Some(BoundValue {
            evaluator: Rc::clone(&self.identity),
            value: value.clone(),
            current: self.current.clone(),
            next: self.next.clone(),
            is_primed: self.cache_control_primed,
            is_enabling: self.is_enabling,
            reads: self.reads - reads,
            captures: self.captures - captures,
        });
    }

    /// TestRandomSetOfSubsets(k, n, S), whose definition is
    /// `[i \in 1..5 |-> Cardinality(RandomSetOfSubsets(k, n, S))]`: the five sizes it draws, or,
    /// applied to a key, the one size `FcnLambdaValue.apply` draws for it, after the key. TLC
    /// binds the arguments to `LazyValue`s, which it may evaluate again for each draw, so
    /// arguments with effects, and any failure, which TLC reports in the definition's frames,
    /// aren't followed.
    fn test_random_set_of_subsets(
        &mut self,
        operands: &[Operand],
        key: Option<&Operand>,
    ) -> Evaluated<Value> {
        let effects = self.lazy_effects();
        let unfollowed = |_| EvalError {
            runtime_exception: RuntimeException::Runtime,
            reason: "a failure within TestRandomSetOfSubsets".into(),
            is_set_normalization: false,
            is_set_reduction: false,
            is_followed_comparison: false,
            is_named_normalization: false,
            message: None,
        };
        let key = match key {
            Some(key) => match self.operand(key).map_err(unfollowed)? {
                Value::Int(key) if (1..=5).contains(&key) => Some(key),
                _ => return fail("TestRandomSetOfSubsets applied outside its domain"),
            },
            None => None,
        };
        let values = operands
            .iter()
            .map(|operand| self.operand(operand))
            .collect::<Evaluated<Vec<_>>>()
            .map_err(unfollowed)?;
        if self.lazy_effects() != effects {
            return fail("TestRandomSetOfSubsets of an argument with effects");
        }
        let mut sizes = Vec::with_capacity(5);
        for _ in 0..if key.is_some() { 1 } else { 5 } {
            let drawn = self
                .draw_subset_set("RandomSetOfSubsets", &values)
                .map_err(unfollowed)?;
            sizes.push(Value::Int(cardinality(&drawn).map_err(unfollowed)? as i32));
        }
        if key.is_some() {
            return Ok(sizes.pop().expect("a size"));
        }
        Ok(Value::over_interval(1, sizes, Class::Plain))
    }

    /// `Randomization.RandomSubsetSet` and `Randomization.RandomSetOfSubsets`: their checks of
    /// the arguments, in order, and their draw.
    fn draw_subset_set(&mut self, name: &str, values: &[Value]) -> Evaluated<Value> {
        let shown = if name == "RandomSetOfSubsets" {
            name
        } else {
            "RandomSubsetSetProbability"
        };
        let bad = |position, expected, value: &Value| {
            check_merge_argument_format(value)?;
            module_argument(position, shown, expected, value)
        };
        let Value::Int(count) = values[0] else {
            return bad("first", "nonnegative integer", &values[0]);
        };
        if count < 0 {
            return bad("first", "nonnegative integer", &values[0]);
        }
        let average = if name == "RandomSetOfSubsets" {
            let Value::Int(average) = values[1] else {
                return bad("second", "nonnegative integer", &values[1]);
            };
            if average < 0 {
                return bad("second", "nonnegative integer", &values[1]);
            }
            Some(average)
        } else {
            None
        };
        let probability = if average.is_some() {
            f64::NAN
        } else {
            let Value::Str(probability) = &values[1] else {
                return bad(
                    "second",
                    "string literal representing a probability",
                    &values[1],
                );
            };
            let Some(probability) = tla_values::random::parse_java_double(&probability.units)
                .filter(|probability| !(*probability < 0.0 || *probability > 1.0))
            else {
                return bad(
                    "second",
                    "string literal does not represent a parsable probability",
                    &values[1],
                );
            };
            probability
        };
        let set = &values[2];
        if !is_enumerable(set) || !is_finite(set)? {
            return bad("third", "finite set", set);
        }
        if !crate::random::subset_set_input_is_known(set) {
            return fail("RandomSubsetSet of a value with untracked lazy normalization");
        }
        let size = cardinality(set)?;
        if (32 - (count as u32).leading_zeros()) as usize > size
            && count > 1i32.wrapping_shl(size as u32)
        {
            return module_argument(
                "first",
                shown,
                &format!("nonnegative integer that is smaller than the subset's size of 2^{size}"),
                &values[0],
            );
        }
        let probability = if let Some(average) = average {
            if average as usize > size {
                return bad(
                    "second",
                    "nonnegative integer in range 0..Cardinality(S)",
                    &values[1],
                );
            }
            f64::from(average) / size as f64
        } else {
            probability
        };
        self.reads += 1;
        let Some(random) = self.random.as_mut() else {
            return fail("a random draw where the evaluator doesn't follow TLC's generator");
        };
        random_subset_set(random, count as u32, probability, set)
    }

    /// Computes the model's startup definitions as TLC does when it starts, after the
    /// substitutes, drawing from the generator TLC seeds then, and keeps them as their values.
    pub(crate) fn compute_startup(&mut self) -> Evaluated<()> {
        self.compute_startup_drawing()?;
        self.random = None;
        Ok(())
    }

    /// The texts TLC interns as it computes the startup definitions, the substitutes and then
    /// `definitions` (`processConstantDefns`), past the first `interned` texts the IR ranks, in
    /// order: those Tail, SubSeq, `\o` and ToString make, as `rankString` ranks them, and
    /// RecordValue's field names where it builds its first record.
    pub(crate) fn get_startup_texts(
        ir: &Ir,
        definitions: &[Index],
        interned: usize,
    ) -> Vec<Box<[u16]>> {
        let mut evaluator = Evaluator::new(ir);
        evaluator
            .ranks
            .retain(|_, rank| (*rank as usize) < interned);
        evaluator.start_ranking();
        evaluator.random = Some(JavaRandom::seeded(ir.model.random_seed));
        evaluator.is_processing_constants = true;
        let substitutes = ir.model.startup.substitutes.iter().map(|&(_, index)| index);
        let mut known = HashMap::new();
        for index in substitutes.chain(definitions.iter().copied()) {
            let node = ir.definitions[index as usize];
            // A definition that can neither make a text nor change what a later one computes adds
            // no rank, however long TLC takes to compute it, as the CHOOSE of a ring of nodes.
            if !evaluator.may_rank_texts(node, &mut known) {
                continue;
            }
            // TLC swallows what a constant definition throws, having interned what it made.
            evaluator
                .evaluate(evaluator.definition(node).body, &Context::default())
                .ok();
            evaluator.rank_record_fields();
        }
        evaluator.startup_ranked.take().unwrap_or_default()
    }

    /// Whether evaluating a definition may make a text `made_text` ranks, build a record, or draw
    /// from the generator or set a register that a later startup definition reads: whether it
    /// reaches, as written or through the definitions it names, an operator that does. TLCGet
    /// builds a record for "config", "spec" and "stats". Tail, SubSeq and `\o`
    /// of a tuple written in place make a tuple.
    ///
    /// `known` keeps what each walk learns of the definitions it meets, which reach such an
    /// operator wherever a walk meets them: those on the way to the one it found do, and every
    /// one a walk met that ended without finding one doesn't. So the walks from each definition
    /// of a long chain of them take the chain once in all, not once each.
    fn may_rank_texts(&self, definition: NodeId, known: &mut HashMap<NodeId, bool>) -> bool {
        // Every definition on the path to where the walk found it reaches it.
        fn found(
            known: &mut HashMap<NodeId, bool>,
            met_in: &HashMap<NodeId, Option<NodeId>>,
            mut within: Option<NodeId>,
        ) -> bool {
            while let Some(definition) = within {
                known.insert(definition, true);
                within = met_in[&definition];
            }
            true
        }
        if let Some(&reaches) = known.get(&definition) {
            return reaches;
        }
        let get_operator = |name: &Name| match name.resolution {
            Resolution::Builtin(index) => Some(self.name(self.ir.builtins[index as usize].name)),
            _ => None,
        };
        let is_tuple = |node: &NodeId| matches!(self.kind(*node), NodeKind::Tuple(_));
        let mut visited = HashSet::new();
        // The definition the walk met each definition in, a path from the first to each.
        let mut met_in: HashMap<NodeId, Option<NodeId>> = HashMap::from([(definition, None)]);
        let mut pending = vec![(definition, Some(definition))];
        while let Some((node, within)) = pending.pop() {
            let (node, kind) = self.node(node);
            if !visited.insert(node) {
                continue;
            }
            let name = match kind {
                NodeKind::Identifier(name) | NodeKind::OperatorReference(name) => Some(name),
                NodeKind::Apply { name, args } => {
                    let is_tuple_made = match (get_operator(name), args.as_slice()) {
                        (Some("\\o"), operands) => operands.iter().any(is_tuple),
                        (Some("Tail" | "SubSeq"), [sequence, ..]) => is_tuple(sequence),
                        _ => false,
                    };
                    (!is_tuple_made).then_some(name)
                }
                // A subexpression names what the walk doesn't follow, and TLC interns
                // RecordValue's names as it builds its first record.
                NodeKind::Subexpression(_) | NodeKind::Record(_) | NodeKind::RecordSet(_) => {
                    return found(known, &met_in, within);
                }
                _ => None,
            };
            if let Some(name) = name {
                if let Some(
                    "Tail" | "\\o" | "SubSeq" | "ToString" | "RandomElement" | "RandomSubset"
                    | "TLCSet" | "TLCGet",
                ) = get_operator(name)
                {
                    return found(known, &met_in, within);
                }
                if let Resolution::Definition(index) = name.resolution {
                    let callee = self.ir.definitions[index as usize];
                    match known.get(&callee) {
                        Some(true) => return found(known, &met_in, within),
                        Some(false) => {}
                        None => {
                            if let std::collections::hash_map::Entry::Vacant(entry) =
                                met_in.entry(callee)
                            {
                                entry.insert(within);
                                pending.push((callee, Some(callee)));
                            }
                        }
                    }
                }
            }
            // `children` leaves out the set a filter's bound ranges over.
            if let NodeKind::SetFilter { bound, .. } = kind {
                pending.push((bound.set, within));
            }
            pending.extend(kind.children().into_iter().map(|child| (child, within)));
        }
        for definition in met_in.into_keys() {
            known.insert(definition, false);
        }
        false
    }

    /// Whether the IR shows a model value's fingerprint: TLCFP, or a draw TLC seeds with the
    /// fingerprint of the state it expands.
    fn is_fingerprint_shown(&self) -> bool {
        self.ir.builtins.iter().any(|builtin| {
            matches!(
                self.name(builtin.name),
                "TLCFP"
                    | "RandomElement"
                    | "RandomSubset"
                    | "RandomSetOfSubsets"
                    | "RandomSubsetSet"
                    | "TestRandomSetOfSubsets"
            )
        })
    }

    /// Whether an expression may reach an effect the startup's computation doesn't see run
    /// (`UNSEEN_EFFECTS`).
    pub(crate) fn may_reach_unseen_effects(&mut self, node: NodeId) -> bool {
        self.may_reach(node, UNSEEN_EFFECTS)
    }

    /// The startup, with the generator left where its draws left it, for the assumptions.
    pub(crate) fn compute_startup_drawing(&mut self) -> Evaluated<()> {
        let is_starting = std::mem::replace(&mut self.is_starting, true);
        let is_processing = std::mem::replace(&mut self.is_processing_constants, true);
        let computed = self.compute_startup_definitions();
        self.is_processing_constants = is_processing;
        self.is_starting = is_starting;
        computed
    }

    fn compute_startup_definitions(&mut self) -> Evaluated<()> {
        let ir = self.ir;
        self.random = Some(JavaRandom::seeded(ir.model.random_seed));
        let substitutes = ir.model.startup.substitutes.iter().map(|&(_, index)| index);
        let limit = self
            .startup_limit
            .map(|count| ir.model.startup.substitutes.len() + count);
        for (at, index) in substitutes
            .chain(ir.model.startup.definitions.iter().copied())
            .enumerate()
        {
            if limit.is_some_and(|limit| at >= limit) {
                break;
            }
            let node = ir.definitions[index as usize];
            // `processConstantDefns`: TLC swallows whatever a constant definition throws and keeps
            // it as an operator, evaluated again, and failing again, where it is used: before the
            // same effects, none where it printed, drew and set no register before it failed here.
            // The front end has rejected a substitute TLC checks and finds failing.
            let effects = |evaluator: &Self| {
                (
                    evaluator
                        .printed
                        .iter()
                        .filter(|output| matches!(output, crate::OutputEvent::Print(_)))
                        .count(),
                    evaluator.random.map(|random| random.state()),
                    evaluator.register_writes,
                )
            };
            let before = effects(self);
            let output_start = self.printed.len();
            let definition = self.definition(node).clone();
            let evaluated = match &definition.form {
                DefinitionForm::Function(bounds)
                    if definition.flags & Definition::STARTUP_WARNING_ONLY != 0 =>
                {
                    self.defined_function(
                        bounds,
                        definition.body,
                        &Context::default(),
                        definition.flags & Definition::SELF_REFERENTIAL != 0,
                    )
                }
                _ => self.evaluate(definition.body, &Context::default()),
            };
            let is_searched_failing = self.searched_failing.contains(&node);
            // A print the search couldn't compute is one TLC computes, as PrintT's TRUE, only
            // where the evaluator computes it.
            if self.searched_unworded.contains(&node) && !matches!(evaluated, Ok(Value::Bool(true)))
            {
                return fail("a startup print the search couldn't compute that fails here");
            }
            // The search stopped at a limit of its own before any effect or warning, and evaluates
            // the definition again at each use, which is what TLC does where it computes it
            // quietly, keeping its value, or fails on it before any effect or warning. A warning,
            // a print or an effect TLC has here, or a failure the evaluator can't follow, past
            // which TLC may warn, is one the search didn't have.
            if self.searched_limited.contains(&node) {
                let is_quiet = effects(self) == before
                    && self.printed.len() == output_start
                    && !self.may_reach(definition.body, UNSEEN_EFFECTS);
                if !is_quiet {
                    return fail(
                        "a startup definition the search failed at a limit of that warns or prints here",
                    );
                }
                if let Err(error) = &evaluated
                    && error.message.is_none()
                {
                    return fail(format!(
                        "a startup definition the search failed at a limit of that the evaluator can't follow: {}",
                        error.reason
                    ));
                }
            }
            // The search failed on a warning-only definition before any warning, where TLC may
            // compute it and warn: a warning or a print here is one the search didn't have.
            if self.searched_unwarned.contains(&node)
                && (effects(self) != before || self.printed.len() != output_start)
            {
                return fail(
                    "a warning-only startup definition the search failed on before a warning, that warns or prints here",
                );
            }
            let value = match evaluated {
                // A definition the search found failing that computes here is one the evaluator
                // and the engine disagree on, which TLC may print or compute as either does.
                Ok(_) if is_searched_failing => {
                    return fail("a startup definition the search found failing that computes");
                }
                Ok(value) => value,
                Err(error) => {
                    let warned = self.printed[output_start..]
                        .iter()
                        .any(|output| matches!(output, crate::OutputEvent::Warning(_)));
                    let warning_only = definition.flags & Definition::STARTUP_WARNING_ONLY != 0;
                    if warning_only && !warned {
                        self.uncomputed_warning_startup.insert(node);
                    }
                    // TLC evaluates the definition again where it is used, where it prints and
                    // draws again as it did here before it fails; a register it set here is
                    // none of its checker's.
                    let is_unaffected = effects(self) == before || effects(self).2 == before.2;
                    // The search found it failing before any effect, which only a failure TLC
                    // raises itself, with its message, confirms, before any effect: one the
                    // evaluator can't follow says nothing of what TLC does.
                    // The search stopped where TLC fails only where it printed as much as TLC
                    // did before failing: one that stopped at a limit of its own, as building
                    // `1..100000000` to print it, before TLC's print, is one where TLC prints at
                    // startup what the search didn't.
                    if is_searched_failing
                        && self
                            .searched_printed
                            .get(&node)
                            .is_some_and(|&count| count != effects(self).0 - before.0)
                    {
                        return fail(
                            "a startup definition the search found failing that prints otherwise here",
                        );
                    }
                    if is_searched_failing {
                        match (&error.message, is_unaffected) {
                            (None, _) => {
                                return fail(format!(
                                    "a startup definition the search found failing that the evaluator can't follow: {}",
                                    error.reason
                                ));
                            }
                            (Some(_), false) => {
                                return fail(
                                    "a startup definition the search found failing that fails here after an effect",
                                );
                            }
                            (Some(_), true) => {}
                        }
                        // The search may stop at a value TLC keeps lazy, as an interval too
                        // large to build or `Seq(S)`, which TLC prints before it fails
                        // (`IntervalValue`, `SetOfSeqValue`): TLC prints it again at each use,
                        // where the search fails before it prints.
                        let now = effects(self);
                        let made = (now.0 - before.0, now.1 != before.1);
                        if self
                            .searched_effects
                            .get(&node)
                            .is_some_and(|&searched| searched != made)
                        {
                            return fail(
                                "a startup definition the search found failing that prints or draws here before it fails as the search didn't",
                            );
                        }
                    }
                    if ir.model.startup.definitions.contains(&index)
                        && (!warning_only || warned)
                        && is_unaffected
                        && !self.may_reach(self.definition(node).body, UNSEEN_EFFECTS)
                    {
                        self.failed_startup.insert(node);
                        self.uncomputed_warning_startup.remove(&node);
                    }
                    continue;
                }
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
            // Where the evaluator replays a step of the search, which the search stopped after
            // as TLC does (`ModelChecker.stop`), TLCSet("exit", TRUE) changes no value.
            if text == "exit" && self.level >= 1 && !self.is_in_assumptions {
                return Ok(());
            }
            // `System.setProperty(name, value.toString())`, which every worker reads alike.
            if let Some(name) = text.strip_prefix(JAVA_PROPERTY_PREFIX)
                && is_settable_property(name)
                && self.workers == Some(1)
            {
                if !has_plain_text(&value) {
                    return fail(
                        "TLCSet of a system property to a value whose text depends on how TLC built it",
                    );
                }
                let text = self.text_of(format_units(&value).into());
                let name: Vec<u16> = name.encode_utf16().collect();
                let properties = &mut self.registers.properties;
                match properties.iter_mut().find(|(set, _)| *set == name) {
                    Some(entry) => entry.1 = Value::Str(text),
                    None => properties.push((name, Value::Str(text))),
                }
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

    /// Whether the startup computed the definition at `node`, which it keeps, rather than failed
    /// on it.
    pub(crate) fn is_startup_computed(&self, node: NodeId) -> bool {
        self.cache.contains_key(&(node, false))
    }

    /// Takes the values the search computed at startup for the model's startup definitions,
    /// ids of `store` in their order, as the values of those definitions.
    pub fn set_startup(&mut self, store: &Store, values: &[Id]) -> Result<(), Unsupported> {
        self.set_failed_startup(values);
        for (&index, &id) in self.ir.model.startup.definitions.iter().zip(values) {
            let node = self.ir.definitions[index as usize];
            if id == NO_VALUE {
                continue;
            }
            let value = from_store(store, id)?;
            self.cache.insert((node, false), value.clone());
            self.cache.insert((node, true), value);
        }
        Ok(())
    }

    /// Takes, of the values the search computed at startup, the startup definitions that failed
    /// there, of which the search keeps no value (`NO_VALUE`) and which TLC evaluates again at
    /// each use.
    pub fn set_failed_startup(&mut self, values: &[Id]) {
        self.is_startup_known = values.len() == self.ir.model.startup.definitions.len();
        for (&index, &id) in self.ir.model.startup.definitions.iter().zip(values) {
            if id == NO_VALUE {
                let node = self.ir.definitions[index as usize];
                let definition = self.definition(node);
                if definition.flags & Definition::STARTUP_WARNING_ONLY != 0 {
                    self.uncomputed_warning_startup.insert(node);
                } else if matches!(definition.form, DefinitionForm::Function(_))
                    && definition.flags & (Definition::RECURSIVE | Definition::SELF_REFERENTIAL)
                        != 0
                {
                    // A recursive function TLC keeps lazy as it starts, which the search
                    // applied and converted as TLC does and the evaluator doesn't follow: it
                    // computes none of it. The search keeps no value of a function definition
                    // only there: it evaluates again at each use only a failed definition of no
                    // argument (`is_retried_at_use`), and declines where one of a function fails.
                } else {
                    self.failed_startup.insert(node);
                }
            }
        }
    }

    /// Takes whether the search printed each startup definition, a PrintT, without computing what
    /// it prints (`Prints::unworded`), in the model's order of them.
    pub fn set_searched_unworded(&mut self, unworded: &[bool]) {
        for (&index, &is_unworded) in self.ir.model.startup.definitions.iter().zip(unworded) {
            if is_unworded {
                self.searched_unworded
                    .insert(self.ir.definitions[index as usize]);
            }
        }
    }

    /// Takes whether the search found each startup definition failing as TLC started, in the
    /// model's order of them.
    pub fn set_searched_failing(&mut self, failed: &[bool]) {
        for (&index, &is_failed) in self.ir.model.startup.definitions.iter().zip(failed) {
            if is_failed {
                self.searched_failing
                    .insert(self.ir.definitions[index as usize]);
            }
        }
    }

    /// Takes how many prints the search made of each startup definition before it stopped, in
    /// the model's order of them.
    pub fn set_searched_printed(&mut self, printed: &[usize]) {
        for (&index, &count) in self.ir.model.startup.definitions.iter().zip(printed) {
            self.searched_printed
                .insert(self.ir.definitions[index as usize], count);
        }
    }

    /// Takes how many prints each startup definition made as the search evaluated it, and whether
    /// it drew, in the model's order of them.
    pub fn set_searched_effects(&mut self, effects: &[(usize, bool)]) {
        for (&index, &effect) in self.ir.model.startup.definitions.iter().zip(effects) {
            self.searched_effects
                .insert(self.ir.definitions[index as usize], effect);
        }
    }

    /// Takes which warning-only startup definitions the search failed on before any warning
    /// other than at a limit of its own, in the model's order of them.
    pub fn set_searched_unwarned(&mut self, unwarned: &[bool]) {
        for (&index, &is_unwarned) in self.ir.model.startup.definitions.iter().zip(unwarned) {
            if is_unwarned {
                self.searched_unwarned
                    .insert(self.ir.definitions[index as usize]);
            }
        }
    }

    /// Takes which startup definitions the search failed at a limit of its own before any
    /// effect or warning, in the model's order of them.
    pub fn set_searched_limited(&mut self, limited: &[bool]) {
        for (&index, &is_limited) in self.ir.model.startup.definitions.iter().zip(limited) {
            if is_limited {
                self.searched_limited
                    .insert(self.ir.definitions[index as usize]);
            }
        }
    }

    /// Takes the values the search computed of the constant definitions whose body is a CHOOSE
    /// over a set (`Violation::chosen`), ids of `store` by position in the IR's definitions, for
    /// those whose evaluation has no effect but its value: neither reading the state or TLC's
    /// search, nor printing, drawing or reading or writing a file. Each is the element of the
    /// set TLC computed as it started (`processConstantDefns`), which the rebuild finds without
    /// testing the elements before it.
    pub fn set_chosen(&mut self, store: &Store, values: &[(u32, Id)]) {
        for &(index, id) in values {
            let node = self.ir.definitions[index as usize];
            if self.may_reach(node, EFFECTS) {
                continue;
            }
            if let Ok(value) = from_store(store, id) {
                self.chosen.insert(node, value);
            }
        }
    }

    // A definition's body, or, for a CHOOSE whose value the search computed, the element of its
    // set that is that value, which is the first that satisfies the predicate. TLC evaluates the
    // set, and the predicate of each element up to that one, which only gives its value. An
    // element the walk can't tell from that value, or one that holds a part the predicate may
    // change as TLC evaluates it, leaves the body evaluated as written.
    fn evaluate_definition(
        &mut self,
        node: NodeId,
        body: NodeId,
        context: &Context,
    ) -> Evaluated<Value> {
        if let NodeKind::Choose { set: Some(set), .. } = self.kind(body)
            && let Some(chosen) = self.chosen.get(&node).cloned()
            && let Ok(set) = self.evaluate(*set, context)
            && let Ok(elements) = elements(&set)
        {
            for element in elements.iter() {
                match is_chosen(element, &chosen) {
                    Some(true) => return Ok(element.clone()),
                    Some(false) => {}
                    None => break,
                }
            }
        }
        let printed = self.printed.len();
        // A definition reached again inside its own body, as a RECURSIVE one without parameters
        // that names itself, nests as an operator's call does, so recursion without end stops
        // where TLC's stack would overflow instead of the evaluator's.
        let result = self.nested(|evaluator| evaluator.evaluate(body, context));
        if self.printed.len() != printed
            && result.as_ref().is_err_and(|error| {
                error.reason == "enumerated a filter of a set TLC doesn't enumerate"
            })
            && matches!(&self.definition(node).form, DefinitionForm::Operator(params) if params.is_empty())
            && !self.may_reach_bound(node)
        {
            return fail("a constant definition whose filter enumeration fails after printing");
        }
        result
    }

    /// What `is_unsure_startup_failure` compares, taken before the evaluation: the counts and
    /// the state of the call stack the evaluation then changes.
    pub(crate) fn startup_failure_counts(&mut self) -> StartupFailureCounts {
        let (was_frozen, unsorted_built) = self
            .call_stack
            .as_ref()
            .map_or((true, 0), |stack| (stack.is_frozen, stack.unsorted_built));
        StartupFailureCounts {
            lazy_unions: self.lazy_unions,
            lazy_domains: self.lazy_domains,
            unfollowed_constructions: self.unfollowed_constructions,
            print_normalizations: self.print_normalizations.0,
            was_frozen,
            unsorted_built,
            combination_sort_failures: crate::sets::combination_sort_failures(),
            normalized_print_failure: self.normalized_print_failure.take(),
        }
    }

    /// Whether a failure of a definition TLC computes as it starts, evaluated within the call
    /// stack, may be one TLC's evaluation, which holds values unnormalized or lazy where the
    /// evaluator doesn't always, meets elsewhere or not at all, as `evaluate_failed_startup`
    /// asks: where the evaluation built a set TLC can't normalize or a value TLC may keep lazy,
    /// failed in a function constructor's body or a filter TLC may keep lazy, or failed
    /// comparing, enumerating or testing membership, as `fallback.md` lists. A power set, where
    /// the failure is an enumeration's, is so outside an assumption, where a lazy set TLC gave a
    /// source may fail in its method as a state TLC fails to fingerprint.
    pub(crate) fn is_unsure_startup_failure(
        &mut self,
        error: &EvalError,
        counts: StartupFailureCounts,
    ) -> bool {
        let StartupFailureCounts {
            lazy_unions,
            lazy_domains,
            unfollowed_constructions,
            print_normalizations,
            was_frozen,
            unsorted_built,
            combination_sort_failures,
            normalized_print_failure,
        } = counts;
        // Whether the failure is that of a print whose `deepNormalize` the evaluator followed.
        let is_normalized_print =
            std::mem::replace(&mut self.normalized_print_failure, normalized_print_failure)
                .is_some_and(|failure| &failure == error);
        match &self.call_stack {
            None => true,
            Some(stack) => {
                let lazy: Vec<&Value> = stack
                    .values
                    .values()
                    .filter(|value| may_be_kept_lazy(value))
                    .collect();
                let holds = |is_kind: fn(&Lazy) -> bool| {
                    lazy.iter()
                        .any(|value| matches!(value, Value::Lazy(inner) if is_kind(inner)))
                };
                let reason = error.reason.as_str();
                // The failure is Print's deep normalization, whose walk the evaluator follows.
                let is_print_normalization = self.print_normalizations.0
                    == print_normalizations + 1
                    && self.print_normalizations.1 == reason;
                // A set enumeration TLC can't normalize, written as the operand of `~`, `=>`,
                // `<=>` or DOMAIN, which fails on its kind, as the only one the evaluation built:
                // TLC fails there before anything normalizes it, as its message only names the
                // kind of the set (`getKindString`).
                let is_written_unsorted_operand = !was_frozen
                    && stack.unsorted_built == unsorted_built + 1
                    && (reason == "expected a boolean, not a set"
                        || reason == DOMAIN_OF_NON_FUNCTION)
                    && matches!(stack.frames.last(), Some(StackFrame::Node(failing))
                        if self.fails_on_written_set(*failing));
                (stack.is_unsorted
                    && !error.is_set_normalization
                    && !error.is_named_normalization
                    && !error.is_set_reduction
                    && !is_written_unsorted_operand
                    && !self.is_unsorted_membership(stack, reason)
                    // In an assumption, a failure whose message prints no such set
                    // (`unsorted_prints`): TLC holds the set as written until it compares,
                    // counts, enumerates, fingerprints or prints it, each of which the evaluator
                    // fails in as TLC does, so TLC reaches the same failure first.
                    && !(self.is_assumption && crate::print::unsorted_prints() == 0))
                    // A union of a value that isn't a set TLC's `UnionValue` too holds lazy, and
                    // fails as the evaluator's does, whichever enumeration meets it first; one of
                    // set enumerations all empty but one held sorted is that one set. In an
                    // assumption, which no source wraps, the evaluator streams a union's sets as
                    // `UnionValue.Enumerator` does (`sets::stream`), and normalizes what it
                    // collects of them in that order, as TLC does.
                    || (!self.is_assumption
                        && (self.lazy_unions != lazy_unions
                            || holds(|lazy| matches!(lazy, Lazy::Union(sets)
                                if is_enumerable(sets) && !is_vacuous_union(sets)))))
                    || self.lazy_domains != lazy_domains
                    // `Tool`'s OPCODE_fc evaluates the domains as it meets the constructor, in
                    // order, and the body only as it applies, enumerates or prints the function,
                    // which TLC may keep lazy: a failure in a domain is TLC's wherever it is.
                    // In an assumption, a failure only in the bodies of functions TLC builds as
                    // it meets them (`unfollowed_constructions`) is TLC's.
                    || (stack
                        .frames
                        .iter()
                        .enumerate()
                        .any(|(index, frame)| self.is_in_function_body(&stack.frames, index, frame))
                        && !(self.is_assumption
                            && self.unfollowed_constructions == unfollowed_constructions))
                    // In an assumption, which TLC evaluates with no `CallStackTool`, no set has a
                    // source to fail its `member` with.
                    || (is_unsure_failure(reason) && !self.is_assumption)
                    || (reason.ends_with("of a non-sequence")
                        && lazy.iter().any(|value| matches!(value, Value::Lambda(_)))
                        // In an assumption the evaluator converts such a function as `toTuple`
                        // does, and words its failure so, as probes matched.
                        && !self.is_assumption)
                    // In an assumption the evaluator streams an intersection, a union and a
                    // difference as their Enumerators do (`sets::stream`), up to where TLC stops.
                    || (!self.is_assumption
                        && reason.contains("compare")
                        && !is_print_normalization
                        // An integer's, a string's or a boolean's comparison reads a lazy set it
                        // fails on only as it prints it (`IntValue.equals`).
                        && !error.is_followed_comparison
                        && !is_normalized_print
                        // `UserValue.compareTo` prints the other set, as Print does.
                        && reason != "compared an overridden set with another value"
                        // Where the evaluator failed to sort what an intersection, a union or a
                        // difference enumerates, which TLC streams, with a lazy product or SUBSET
                        // held in another value: TLC may decide before it meets the
                        // incomparable elements, as `({2, 3} \cup SUBSET {1}) \subseteq {7}`.
                        && crate::sets::combination_sort_failures() != combination_sort_failures
                        && lazy.iter().any(|value| {
                            matches!(value, Value::Lazy(inner)
                                if matches!(***inner, Lazy::Product(_) | Lazy::Subset(_)))
                                && stack
                                    .values
                                    .values()
                                    .any(|other| holds_within(other, value))
                        }))
                    || (reason.starts_with("enumerated ")
                        && holds(|lazy| matches!(lazy, Lazy::Subset(_)))
                        // In an assumption TLC walks a power set by size, then in the order of
                        // its base (`SubsetValue.elementsNormalized`), which is the evaluator's
                        // sorted order, as probes of quantifiers, CHOOSE, filters and maps whose
                        // failure depends on the element first met matched.
                        && !self.is_assumption)
                    || ((reason.starts_with("expected ") || reason.ends_with("of a non-sequence"))
                        && holds(|lazy| {
                            matches!(lazy, Lazy::Cap(..) | Lazy::Cup(..) | Lazy::Diff(..))
                        })
                        // In an assumption, where no value has a source, the evaluator words
                        // such a set as its `toString` does (expanded where `toSetEnum`
                        // succeeds, otherwise as written), which probes of 22 operators over 20
                        // lazy unions, intersections and differences matched.
                        && !self.is_assumption)
            }
        }
    }

    // A startup definition that failed as TLC started, which TLC evaluates again where it is used,
    // where it fails again as it did then: the search found it failing before any effect, as TLC
    // reports. A warning TLC prints, or a value here, is a disagreement with the search, and a
    // failure `is_unsure_startup_failure` finds TLC may meet otherwise declines.
    fn evaluate_failed_startup(&mut self, node: NodeId, context: &Context) -> Evaluated<Value> {
        self.failed_startup_uses += 1;
        // In an assumption checked again outside a replay of its failure, the evaluation is
        // followed within a call stack of its own, with no sources, as `checkAssumptions`
        // evaluates: the definition names nothing of the assumption's.
        let is_own_stack = self.is_checking_assumption && self.call_stack.is_none();
        if is_own_stack {
            self.call_stack = Some(CallStack {
                is_unsourced: true,
                ..CallStack::default()
            });
        }
        let counts = self.startup_failure_counts();
        let body = self.definition(node).body;
        let result = self.evaluate_definition(node, body, &context.global());
        let is_unsure = match &result {
            Ok(_) => true,
            Err(error) => self.is_unsure_startup_failure(error, counts),
        };
        if is_own_stack {
            self.call_stack = None;
        }
        let error = match result {
            Ok(_) => {
                return fail("a startup definition that failed there and not where it is used");
            }
            Err(error) => error,
        };
        if is_unsure {
            return fail(format!(
                "a startup definition that failed where TLC may fail otherwise: {}",
                error.reason
            ));
        }
        Err(error)
    }

    // Whether a frame of a failure's call stack is a function constructor the failure is in
    // other than in one of its domains. TLC evaluates every domain as it meets the constructor
    // (`Tool.evalAppl`'s `OPCODE_fc`), lazy or not, so a failure there is TLC's; its body TLC may
    // evaluate later, or in another order, or not at all (`FcnLambdaValue`).
    fn is_in_function_body(&self, frames: &[StackFrame], index: usize, frame: &StackFrame) -> bool {
        let StackFrame::Node(node) = frame else {
            return false;
        };
        let NodeKind::FunctionConstruction { bounds, .. } = self.kind(*node) else {
            return false;
        };
        !matches!(frames.get(index + 1), Some(StackFrame::Node(next))
            if bounds.iter().any(|bound| self.node(bound.set).0 == *next))
    }

    // Whether a node is `~`, `=>`, `<=>` or DOMAIN of a set enumeration written as its operand.
    fn fails_on_written_set(&self, node: NodeId) -> bool {
        let NodeKind::Apply { name, args } = self.kind(node) else {
            return false;
        };
        !name.is_local
            && matches!(name.resolution, Resolution::Builtin(_))
            && matches!(
                self.name(name.text),
                "~" | "=>" | "<=>" | "\\equiv" | "DOMAIN"
            )
            && args
                .iter()
                .any(|&arg| matches!(self.kind(self.resolved(arg)), NodeKind::SetEnumeration(_)))
    }

    // Whether the failure is a comparison in a membership (`\in`, `\notin` or `\subseteq`) in a
    // set enumeration written in place there that TLC fails to normalize, and that is the only
    // such set the evaluation built: `SetEnumValue.member` of a set TLC holds unnormalized asks
    // each element in the order written whether it `equals` the value (`ValueVec.search`), as the
    // evaluator does, and nothing else held the set to normalize it before.
    fn is_unsorted_membership(&self, stack: &CallStack, reason: &str) -> bool {
        if !matches!(
            reason,
            "equality of values TLC can't compare" | "values TLC can't compare"
        ) {
            return false;
        }
        let Some(&StackFrame::Node(node)) = stack.frames.last() else {
            return false;
        };
        let NodeKind::Apply { name, args } = self.kind(node) else {
            return false;
        };
        let [_, set] = args.as_slice() else {
            return false;
        };
        if name.is_local
            || !matches!(name.resolution, Resolution::Builtin(index)
            if matches!(
                self.name(self.ir.builtins[index as usize].name),
                "\\in" | "\\notin" | "\\subseteq"
            ))
            || !matches!(self.kind(*set), NodeKind::SetEnumeration(_))
        {
            return false;
        }
        let Some(Value::Unsorted(held)) = stack.values.get(set) else {
            return false;
        };
        stack.values.iter().all(|(&other, value)| {
            if other == *set {
                return true;
            }
            !holds_unsorted_other_than(value, held)
        }) && held
            .iter()
            .all(|element| !holds_unsorted_other_than(element, held))
    }

    /// Whether TLC keeps a value for a constant definition without parameters as it starts
    /// (`processConstantDefns`): whether it computes it then, in `Context.Empty` with its plain
    /// `Tool`, without a read or a print, to a value it can normalize. One it failed on there
    /// it leaves as the definition, whose body `getInitStates` and `getNextStates` walk.
    pub(crate) fn is_kept_at_startup(
        &mut self,
        node: NodeId,
        context: &Context,
    ) -> Evaluated<bool> {
        if let Some(&kept) = self.kept_at_startup.get(&node) {
            return Ok(kept);
        }
        let body = self.definition(node).body;
        let effects = (
            self.register_writes,
            self.random.as_ref().map(|random| random.state()),
        );
        let (reads, printed, lazy_prints) = (self.reads, self.printed.len(), self.lazy_print_count);
        let call_stack = self.call_stack.take();
        let keeping_lazy = std::mem::take(&mut self.keeping_lazy);
        let empty = Context {
            caller: Held::Empty,
            ..context.global()
        };
        let is_processing = std::mem::replace(&mut self.is_processing_constants, true);
        let computed = self.evaluate_definition(node, body, &empty);
        self.is_processing_constants = is_processing;
        self.keeping_lazy = keeping_lazy;
        self.call_stack = call_stack;
        let kept = computed.is_ok_and(|value| !holds_unsorted(&value))
            && self.reads == reads
            && self.printed.len() == printed;
        self.reads = reads;
        self.printed.truncate(printed);
        self.lazy_prints
            .truncate(self.lazy_prints_from(lazy_prints));
        if effects
            != (
                self.register_writes,
                self.random.as_ref().map(|random| random.state()),
            )
        {
            return fail("a constant definition TLC computed at startup with effects, walked");
        }
        self.kept_at_startup.insert(node, kept);
        Ok(kept)
    }

    pub(crate) fn definition_value(&mut self, node: NodeId, context: &Context) -> Evaluated<Value> {
        let definition = self.definition(node);
        let key = (node, context.is_primed);
        if let Some(value) = self.cache.get(&key) {
            // A set TLC fails to sort that a definition computed before the replay holds is one
            // the replay built, as `held_set` notes: TLC holds it unnormalized, with a source
            // a FingerprintException may trace.
            if let Some(stack) = &mut self.call_stack
                && holds_unsorted(value)
            {
                stack.is_unsorted = true;
            }
            return Ok(value.clone());
        }
        // The value TLC computed at startup, which the search computed and hands on, but for one
        // that failed there, which TLC evaluates again here. One whose only effect is a warning
        // (`STARTUP_WARNING_ONLY`, an EXCEPT) computes here, without a warning, the value TLC
        // computed there without one.
        let is_computed_startup = !self.failed_startup.contains(&node)
            && !self.uncomputed_warning_startup.contains(&node)
            && self
                .ir
                .model
                .startup
                .definitions
                .iter()
                .any(|&index| self.ir.definitions[index as usize] == node);
        let is_warning_only = definition.flags & Definition::STARTUP_WARNING_ONLY != 0;
        if is_computed_startup && !is_warning_only {
            return fail("a value TLC computed at startup with effects");
        }
        if self.failed_startup.contains(&node) {
            return self.evaluate_failed_startup(node, context);
        }
        let (reads, captures) = (self.reads, self.captures);
        let printed = self.printed.len();
        let lazy_prints = self.lazy_print_count;
        // TLC computes a definition of constant level as it starts, with its plain `Tool`, whose
        // values have no source (`processConstantDefns`). One that fails, or that holds a set it
        // can't normalize (`evalConstantDefn`'s `deepNormalize`), it evaluates again where it is
        // used. It computed it without the KeepLazy of an application that names it, so a
        // function constructor over a reducible domain is the `FcnRcdValue` it built.
        let is_kept_lazy_use = self.call_stack.is_none() && self.keeping_lazy > 0;
        if (self.call_stack.is_some() || is_kept_lazy_use)
            && !self.uncomputed_warning_startup.contains(&node)
            && matches!(&definition.form, DefinitionForm::Operator(params) if params.is_empty())
            && self.is_precomputed(node)
        {
            let effects = (
                self.register_writes,
                self.random.as_ref().map(|random| random.state()),
            );
            let call_stack = self.call_stack.take();
            let keeping_lazy = std::mem::take(&mut self.keeping_lazy);
            // `processConstantDefns` evaluates it in `Context.Empty`.
            let empty = Context {
                caller: Held::Empty,
                ..context.global()
            };
            let is_processing = std::mem::replace(&mut self.is_processing_constants, true);
            let computed = self.evaluate_definition(node, definition.body, &empty);
            self.is_processing_constants = is_processing;
            self.keeping_lazy = keeping_lazy;
            self.call_stack = call_stack;
            if let Ok(value) = computed
                && self.reads == reads
                && self.printed.len() == printed
                && !holds_unsorted(&value)
            {
                note_sorted(&value);
                self.cache.insert(key, value.clone());
                return Ok(value);
            }
            self.reads = reads;
            self.printed.truncate(printed);
            self.lazy_prints
                .truncate(self.lazy_prints_from(lazy_prints));
            if is_kept_lazy_use
                && effects
                    != (
                        self.register_writes,
                        self.random.as_ref().map(|random| random.state()),
                    )
            {
                return fail("a constant definition TLC computed at startup with effects, applied");
            }
        }
        let evaluated = (|| -> Evaluated<Value> {
            let value = match &definition.form {
                // TLC evaluates the function constructor SANY makes of the definition, which has the
                // definition's range.
                DefinitionForm::Function(bounds) => {
                    let keeps_lazy =
                        u32::from(definition.flags & Definition::SELF_REFERENTIAL != 0);
                    self.keeping_lazy += keeps_lazy;
                    let value = self.in_frame(StackFrame::Node(node), &mut |evaluator| {
                        evaluator.nested(|evaluator| {
                            evaluator.construct_function(bounds, definition.body, &context.global())
                        })
                    });
                    self.keeping_lazy -= keeps_lazy;
                    value?
                }
                DefinitionForm::Operator(params) if params.is_empty() => {
                    self.evaluate_definition(node, definition.body, &context.global())?
                }
                DefinitionForm::Operator(_) => return fail("an operator used as a value"),
            };
            Ok(value)
        })();
        if evaluated.is_err()
            && self.call_stack.is_some()
            && self.uncomputed_warning_startup.contains(&node)
            && self.printed[printed..]
                .iter()
                .any(|output| matches!(output, crate::OutputEvent::Warning(_)))
        {
            self.failed_startup_uses += 1;
        }
        let value = evaluated?;
        // TLC warned as it computed it at startup, and keeps the value, which it doesn't warn of
        // again here.
        if is_computed_startup && self.printed.len() != printed {
            return fail("a value TLC computed at startup with a warning");
        }
        // A definition that built a lazy value holding the states reads them where it is applied,
        // unless it is one TLC computes as it starts, of constant level and reaching none of what
        // TLC can't read then (`processConstantDefns`), whose value holds no state.
        if self.reads == reads
            && self.printed.len() == printed
            && (self.captures == captures || !self.may_reach_bound(node))
        {
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
        let mut recursive = Vec::new();
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
                    group_env: RefCell::new(Weak::new()),
                })),
            };
            if let Binding::Operator(operator) = &binding
                && operator.is_self
            {
                recursive.push(Rc::clone(operator));
            }
            inner = inner.bind(definition.name, binding);
        }
        // A RECURSIVE operator sees the others its declaration names, defined after it too
        // (`Generator.processRecursive`); SANY rejects any other forward name, and a LET shadows
        // none.
        if let Some(frame) = &inner.env.0 {
            for operator in recursive {
                *operator.group_env.borrow_mut() = Rc::downgrade(frame);
            }
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
                group_env: RefCell::new(Weak::new()),
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
                let node = self.ir.definitions[index as usize];
                let definition = self.definition(node);
                // TLC computes a definition of no parameters at startup where it is a constant
                // (`processConstantDefns`), a literal too, which the walk then takes as a value.
                // One that failed there TLC keeps no value of (`setToolObject` isn't reached), so
                // `getInitStatesAppl`, `getNextStatesAppl` and `enabledAppl` look up its
                // `OpDefNode` and walk its body.
                let is_startup = (self.ir.model.startup.definitions.contains(&index)
                    && !self.failed_startup.contains(&node))
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
                    let base = operator_context(operator, &frame)
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
                // IOUtils's Serialize, which `Json.textSerialize` overrides: TLC's walks of the
                // initial predicate, an action and ENABLED look the name up as the Java method's
                // value (`getNextStatesApplEvalAppl`, `enabledAppl`) and evaluate it as a guard,
                // walking no body.
                if self.is_text_serialized(definition.name, params.len(), definition.body) {
                    return Ok(None);
                }
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
                    group_env: RefCell::new(Weak::new()),
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
                    context: operator_context(operator, &frame),
                    is_self: false,
                    group_env: RefCell::new(Weak::new()),
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
                        group_env: RefCell::new(Weak::new()),
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
                    group_env: RefCell::new(Weak::new()),
                }));
            }
            _ => {}
        }
        fail(format!("the operator argument {}", self.name(name.text)))
    }

    // Whether a RECURSIVE definition's body passes each call of a RECURSIVE definition in it
    // only operators that mean the same at every depth: one of its own operator parameters as it
    // is, a definition of the module, or a LAMBDA that names nothing bound around it. TLC
    // evaluates a LAMBDA's body, and a LET's operator's, in the context it applies it in
    // (`OpLambdaValue.apply`, `Tool.getOpContext`), where a deeper call of the definition has
    // bound its parameters, LETs and bound variables again: one naming them reads the deeper
    // binding, which may be itself, so that TLC overflows its stack.
    fn passes_operators_lexically(&self, body: NodeId, params: &[Param]) -> bool {
        let is_recursive_call = |name: &Name| {
            !name.is_local
                && matches!(name.resolution, Resolution::Definition(index)
                    if self.definition(self.ir.definitions[index as usize]).flags
                        & Definition::RECURSIVE != 0)
        };
        let names_nothing_bound = |lambda_params: &[TextId], lambda_body: NodeId| {
            let mut seen = HashSet::new();
            let mut pending = vec![lambda_body];
            while let Some(at) = pending.pop() {
                if !seen.insert(at) {
                    continue;
                }
                match self.kind(at) {
                    NodeKind::Identifier(name)
                    | NodeKind::OperatorReference(name)
                    | NodeKind::Apply { name, .. }
                        if name.is_local && !lambda_params.contains(&name.text) =>
                    {
                        return false;
                    }
                    NodeKind::Reference(target) => pending.push(*target),
                    kind => pending.extend(kind.children()),
                }
            }
            true
        };
        let mut seen = HashSet::new();
        let mut pending = vec![body];
        while let Some(at) = pending.pop() {
            if !seen.insert(at) {
                continue;
            }
            let kind = self.kind(at);
            if let NodeKind::Apply { name, args } = kind
                && is_recursive_call(name)
                && let Resolution::Definition(index) = name.resolution
                && let DefinitionForm::Operator(callee) =
                    &self.definition(self.ir.definitions[index as usize]).form
            {
                for (param, &argument) in callee.iter().zip(args) {
                    if param.arity == 0 {
                        continue;
                    }
                    let is_lexical = match self.kind(argument) {
                        NodeKind::Identifier(name) | NodeKind::OperatorReference(name) => {
                            !name.is_local
                                || params
                                    .iter()
                                    .any(|own| own.arity > 0 && own.name == name.text)
                        }
                        NodeKind::Lambda {
                            params: lambda_params,
                            body: lambda_body,
                        } => names_nothing_bound(lambda_params, *lambda_body),
                        _ => false,
                    };
                    if !is_lexical {
                        return false;
                    }
                }
            }
            match kind {
                NodeKind::Reference(target) => pending.push(*target),
                kind => pending.extend(kind.children()),
            }
        }
        true
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
                if definition.flags & Definition::RECURSIVE != 0
                    && params.iter().any(|param| param.arity > 0)
                    && !match self.lexical_recursions.get(&definition.body) {
                        Some(&is_lexical) => is_lexical,
                        None => {
                            let is_lexical =
                                self.passes_operators_lexically(definition.body, params);
                            self.lexical_recursions.insert(definition.body, is_lexical);
                            is_lexical
                        }
                    }
                {
                    return fail(
                        "a recursive operator passing a recursive call an operator that names its own bindings",
                    );
                }
                let is_recursive = definition.flags & Definition::RECURSIVE != 0;
                if self.is_text_serialized(definition.name, params.len(), definition.body) {
                    return self.text_serialize(args, context, |evaluator| {
                        let callee =
                            evaluator.bind_arguments(params, args, context, context.global())?;
                        evaluator.nesting(is_recursive, |evaluator| {
                            evaluator.evaluate(definition.body, &callee)
                        })
                    });
                }
                let callee = self.bind_arguments(params, args, context, context.global())?;
                return self.nesting(is_recursive, |evaluator| {
                    evaluator.evaluate(definition.body, &callee)
                });
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
                Value::Null => {
                    return fail_runtime(
                        "Serialize's null options",
                        "Cannot invoke \"tlc2.value.impl.Value.toRcd()\" because \"third\" is null"
                            .into(),
                    );
                }
                _ => {
                    if crate::value::contains_uninitialized(&options) {
                        return fail(
                            "formatting Serialize's non-record options containing an uninitialized literal",
                        );
                    }
                    return module_argument("third", "ndJsonSerialize", "sequence", &options);
                }
            };
            // Value.toRcd makes an empty function the empty record.
            if fields.domain.is_empty() {
                return fail_runtime(
                    "Serialize's options",
                    "Attempted to access nonexistent field 'format' of record\n[]".into(),
                );
            }
            let fields = Rc::clone(fields);
            match self.serialize_option(&options, &fields, "format")? {
                Value::Str(text) if is_text(&text, "NDJSON") => {
                    self.text_serialize_lines(args, context, &options, &fields)
                }
                Value::Str(_) => call(self),
                other => json::string_cast(&other),
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
        let base = operator_context(operator, frame)
            .primed(context.is_primed || operator.context.is_primed);
        match operator.body {
            Body::Node(body) => {
                let callee = self.bind_arguments(&operator.params, args, context, base)?;
                self.nesting(operator.is_self, |evaluator| {
                    evaluator.evaluate(body, &callee)
                })
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

    // Whether an operator's body is a number or a string, whose value TLC takes for the operator
    // where it is an argument (`lookup` finds the body's tool object).
    fn is_literal_body(&self, operator: &Operator) -> bool {
        matches!(operator.body, Body::Node(body) if matches!(
            self.kind(body),
            NodeKind::Number(_) | NodeKind::WideNumber(_) | NodeKind::Decimal(_) | NodeKind::String(_)
        ))
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
                self.nesting(operator.is_self, |evaluator| {
                    evaluator.evaluate(body, &inner)
                })
            }
            Body::Builtin(index) => {
                let operands: Vec<Operand> = values.iter().cloned().map(Operand::Value).collect();
                self.builtin(index, &operands, &operator.context)
            }
        }
    }

    // `TransitiveClosure.Warshall`, which two walks follow: `warshall_enumerated` of the relations
    // whose enumeration and endpoints it proves, and `warshall_followed` of any relation TLC
    // enumerates. Where both answer, they must agree, and the evaluator declines where they
    // don't; where one declines, the other's answer stands.
    fn warshall(&mut self, relation: &Value) -> Evaluated<Value> {
        fn is_answer(result: &Evaluated<Value>) -> bool {
            match result {
                Ok(_) => true,
                Err(error) => error.message.is_some(),
            }
        }
        fn text(result: &Evaluated<Value>) -> Option<String> {
            match result {
                Ok(value) => Some(format_pretty(value)),
                Err(error) => error.message.as_ref().map(|message| message.text.clone()),
            }
        }
        let enumerated = self.warshall_enumerated(relation);
        let followed = self.warshall_followed(relation);
        match (is_answer(&enumerated), is_answer(&followed)) {
            (true, true) if text(&enumerated) != text(&followed) => {
                fail("Warshall of a relation the two walks disagree on")
            }
            (false, true) => followed,
            _ => enumerated,
        }
    }

    // TLC's Warshall (`TransitiveClosure.Warshall`): a relation that isn't `Enumerable` fails;
    // TLC sizes the relation, which normalizes a set enumeration, and enumerates it, converting
    // each element to a tuple (`toTuple`), the first that isn't a pair failing; it tells the
    // endpoints apart by their fingerprints (a `Hashtable`), in the order it meets them, and
    // returns the pairs of the closure in that order, unnormalized.
    fn warshall_enumerated(&mut self, relation: &Value) -> Evaluated<Value> {
        let edges = match relation {
            Value::Set(set) if set.java_class == Some(SetClass::Enumeration) => elements(relation)?,
            // A set enumeration TLC fails to normalize, where the evaluator follows the sort only
            // of elements it holds as TLC does.
            Value::Unsorted(set)
                if set.java_class == Some(SetClass::Enumeration)
                    && set.iter().all(is_plain_value) =>
            {
                elements(relation)?
            }
            Value::Interval(_, _, Some(SetClass::Interval | SetClass::Enumeration)) => {
                elements(relation)?
            }
            // A power set enumerates its subsets the least first, the empty set, which isn't
            // a pair, once TLC sized it by its base (`SubsetValue.size`).
            Value::Lazy(lazy)
                if matches!(&***lazy, Lazy::Subset(base)
                    if matches!(base, Value::Set(set) if set.java_class == Some(SetClass::Enumeration))
                        && elements(base)?.len() < 31) =>
            {
                Rc::new(vec![Value::set(Vec::new())])
            }
            Value::Bool(_)
            | Value::Int(_)
            | Value::Str(_)
            | Value::Model(_)
            | Value::Function(_)
                if is_plain_value(relation) && !holds_unknown_function_order(relation) =>
            {
                return not_enumerable_relation(relation);
            }
            Value::Lazy(lazy) if matches!(&***lazy, Lazy::Nat | Lazy::Int | Lazy::Strings) => {
                return not_enumerable_relation(relation);
            }
            _ => return fail("Warshall of a relation whose enumeration is not proven"),
        };
        let mut nodes: Vec<Value> = Vec::new();
        let mut pairs = Vec::new();
        for edge in edges.iter() {
            if !is_plain_value(edge) || holds_unknown_function_order(edge) {
                return fail("Warshall of an element the evaluator doesn't follow");
            }
            let tuple = match as_tuple(edge) {
                Some(tuple) if tuple.len() == 2 => tuple,
                _ => {
                    return fail_coded(
                        "Warshall of a non-pair",
                        2157,
                        format!(
                            "Attempted to apply TransitiveClosure to a set containing\nthe following value:\n{}",
                            format_pretty(edge)
                        ),
                    );
                }
            };
            let mut pair = [0; 2];
            for (i, value) in tuple.iter().enumerate() {
                let mut position = None;
                for (index, other) in nodes.iter().enumerate() {
                    if is_same_endpoint(value, other)? {
                        position = Some(index);
                        break;
                    }
                }
                pair[i] = match position {
                    Some(position) => position,
                    None => {
                        nodes.push(value.clone());
                        nodes.len() - 1
                    }
                };
            }
            pairs.push(pair);
        }
        let mut matrix = vec![vec![false; nodes.len()]; nodes.len()];
        for [a, b] in pairs {
            matrix[a][b] = true;
        }
        for y in 0..nodes.len() {
            let reachable = matrix[y].clone();
            for row in &mut matrix {
                if row[y] {
                    for (entry, &through) in row.iter_mut().zip(&reachable) {
                        *entry |= through;
                    }
                }
            }
        }
        let mut result = Vec::new();
        for i in 0..nodes.len() {
            for j in 0..nodes.len() {
                if matrix[i][j] {
                    result.push(Value::tuple(vec![nodes[i].clone(), nodes[j].clone()]));
                }
            }
        }
        self.held_set(result)
    }

    // `TransitiveClosure.Warshall` as TLC's Java method follows it: the relation's size, then each
    // element as a pair (`toTuple`), its endpoints numbered as a Hashtable of their fingerprints
    // finds them.
    fn warshall_followed(&mut self, relation: &Value) -> Evaluated<Value> {
        let is_enumerable = match relation {
            Value::Set(_) | Value::Interval(..) | Value::Unsorted(_) => true,
            Value::Lazy(lazy) => match &***lazy {
                // `SubsetValue.size` overflows from 31 elements of its base.
                Lazy::Subset(base) => {
                    if !matches!(base, Value::Set(_) | Value::Interval(..))
                        || cardinality(base)? >= 31
                    {
                        return fail("Warshall of a power set the evaluator doesn't size");
                    }
                    true
                }
                Lazy::Product(factors) => {
                    if !factors
                        .iter()
                        .all(|factor| matches!(factor, Value::Set(_) | Value::Interval(..)))
                        || factors.iter().try_fold(1i64, |size, factor| {
                            Ok::<_, EvalError>(size.saturating_mul(cardinality(factor)? as i64))
                        })? > i64::from(i32::MAX)
                    {
                        return fail("Warshall of a product the evaluator doesn't size");
                    }
                    true
                }
                // Nat and Int are `UserValue`s, which aren't `Enumerable`.
                Lazy::Nat | Lazy::Int => false,
                _ => return fail("Warshall of a lazy set the evaluator doesn't enumerate"),
            },
            Value::Lambda(_) | Value::Null => {
                return fail("Warshall of a value the evaluator doesn't hold as TLC does");
            }
            _ => false,
        };
        if !is_enumerable {
            return fail_coded(
                "Warshall of a non-enumerable value",
                2176,
                format!(
                    "Applying TransitiveClosure to the following value,\nwhich is not an enumerable set:\n{}",
                    format_pretty(relation)
                ),
            );
        }
        let edges = elements(relation)?;
        let mut nodes: Vec<Value> = Vec::new();
        let mut pairs = Vec::new();
        for edge in edges.iter() {
            if matches!(edge, Value::Lambda(_) | Value::Lazy(_) | Value::Null) {
                return fail("Warshall of an element the evaluator doesn't take as a tuple");
            }
            let tuple = as_tuple(edge).filter(|tuple| tuple.len() == 2);
            let Some(tuple) = tuple else {
                return fail_coded(
                    "Warshall of a non-pair",
                    2157,
                    format!(
                        "Attempted to apply TransitiveClosure to a set containing\nthe following value:\n{}",
                        format_pretty(edge)
                    ),
                );
            };
            let mut pair = [0; 2];
            for (i, value) in tuple.iter().enumerate() {
                let mut position = None;
                for (at, other) in nodes.iter().enumerate() {
                    if warshall_node_equals(other, value)? {
                        position = Some(at);
                        break;
                    }
                }
                pair[i] = match position {
                    Some(position) => position,
                    None => {
                        nodes.push(value.clone());
                        nodes.len() - 1
                    }
                };
            }
            pairs.push(pair);
        }
        let mut matrix = vec![vec![false; nodes.len()]; nodes.len()];
        for [a, b] in pairs {
            matrix[a][b] = true;
        }
        for y in 0..nodes.len() {
            let reachable = matrix[y].clone();
            for row in &mut matrix {
                if row[y] {
                    for (entry, &through) in row.iter_mut().zip(&reachable) {
                        *entry |= through;
                    }
                }
            }
        }
        let mut result = Vec::new();
        for i in 0..nodes.len() {
            for j in 0..nodes.len() {
                if matrix[i][j] {
                    result.push(Value::tuple(vec![nodes[i].clone(), nodes[j].clone()]));
                }
            }
        }
        self.held_set(result)
    }

    // Whether an expression applies an operator a scope binds, which may do anything.
    fn applies_local_operator(&self, node: NodeId) -> bool {
        let kind = &self.ir.nodes.arena[node as usize].kind;
        matches!(kind, NodeKind::Apply { name, .. } if name.is_local)
            || kind
                .children()
                .into_iter()
                .any(|child| self.applies_local_operator(child))
    }

    // A Java method of `tlc2.module.Bags` applied to its arguments' values.
    // The NullPointerException a Bags method raises reading the function (`toFcnRcd`) of a value
    // that has none, with the message the jar's helpful NullPointerExceptions give it. A tool
    // value TLC doesn't hold fails otherwise.
    fn bags_null_pointer<T>(&self, reason: String, value: &Value, text: &str) -> Evaluated<T> {
        if self.is_174() || matches!(value, Value::Null) {
            return fail(reason);
        }
        let mut error = fail_runtime::<()>(reason, text.into()).unwrap_err();
        error.runtime_exception = RuntimeException::NullPointer;
        Err(error)
    }

    fn bags(
        &mut self,
        name: &str,
        operator: Option<&Operator>,
        values: &[Value],
    ) -> Evaluated<Value> {
        match (name, values) {
            // Whether a value is a function whose counts are positive integers.
            ("IsABag", [bag]) => Ok(Value::Bool(
                function_entries(bag)?.is_some_and(|entries| is_bag(&entries)),
            )),
            // The copies a bag holds, added in an int, each a positive integer.
            ("BagCardinality", [bag]) => {
                let Some(entries) = function_entries(bag)? else {
                    return wrong_value("BagCardinality", "a function with a finite domain", bag);
                };
                let mut size = 0;
                for (_, count) in entries {
                    match count {
                        Value::Int(count) if count > 0 => size = add_counts(size, count)?,
                        _ => return wrong_value("BagCardinality", "a bag", bag),
                    }
                }
                Ok(Value::Int(size))
            }
            // The elements a bag holds: its domain, an interval where TLC holds one.
            ("BagToSet", [bag]) => {
                if function_entries(bag)?.is_none() {
                    return wrong_value("BagToSet", "a function with a finite domain", bag);
                }
                let Value::Function(function) = bag else {
                    unreachable!("a bag's entries are a function's")
                };
                Ok(match function.interval {
                    Some((low, high)) => Value::interval(low, high),
                    None => Value::set(function.domain.clone()),
                })
            }
            // Each element of a finite set once, whose message names BagToSet.
            ("SetToBag", [set]) => {
                if !is_enumerable(set) {
                    return wrong_value("BagToSet", "a function with a finite domain", set);
                }
                let keys = elements(set)?.to_vec();
                let values = vec![Value::Int(1); keys.len()];
                sorted_function(keys, values, Class::Plain)
            }
            // The sum of a finite set's bags in the set's order: the one element of a set of
            // one, bag or not.
            ("BagUnion", [set]) => {
                if !is_enumerable(set) {
                    return wrong_value("BagUnion", "a finite enumerable set", set);
                }
                let bags = elements(set)?;
                if bags.len() < 2 {
                    return Ok(bags
                        .first()
                        .cloned()
                        .unwrap_or_else(|| Value::function(Vec::new(), Vec::new(), Class::Plain)));
                }
                let not_a_bag = || {
                    fail_coded(
                        "BagUnion of a set whose element isn't a function",
                        BAG_UNION1,
                        format!(
                            "Attempted to apply BagUnion to the following set, whose\nelement is not a bag:\n{}",
                            format_pretty(set)
                        ),
                    )
                };
                let Some(mut counts) = function_entries(&bags[0])? else {
                    return not_a_bag();
                };
                for bag in &bags[1..] {
                    let Some(entries) = function_entries(bag)? else {
                        return not_a_bag();
                    };
                    for (key, count) in entries {
                        add_copies(&mut counts, key, count)?;
                    }
                }
                counted_bag(counts)
            }
            // Whether a bag holds an element, or how many copies: the count at the first key
            // equal to it, which must be an integer.
            ("BagIn" | "CopiesIn", [element, bag]) => {
                // The method reads the function of a value that isn't one, a NullPointerException
                // whose message names a local variable only where TLC was compiled with its
                // names, as tla2tools.jar is.
                let Some(entries) = function_entries(bag)? else {
                    return self.bags_null_pointer(
                        format!("{name} of a value that isn't a function"),
                        bag,
                        "Cannot read field \"values\" because \"fcn\" is null",
                    );
                };
                let mut found = None;
                for (key, count) in entries {
                    if equals(element, &key)? {
                        found = Some(count);
                        break;
                    }
                }
                Ok(match (found, name == "BagIn") {
                    (None, true) => Value::Bool(false),
                    (None, false) => Value::Int(0),
                    (Some(Value::Int(count)), true) => Value::Bool(count > 0),
                    (Some(Value::Int(count)), false) => Value::Int(count),
                    (Some(_), _) => return module_argument("second", name, "bag", bag),
                })
            }
            // The copies of two bags added (`BagCup`): the first's elements, then the second's
            // others. Both must be bags.
            ("\\oplus", [left, right]) => {
                let (left_entries, right_entries) =
                    (function_entries(left)?, function_entries(right)?);
                // `IsABag` reads the function of a value that isn't one, a NullPointerException
                // as BagIn's, which `toFcnRcd` raises calling the method of no value.
                let not_a_function = |evaluator: &Self, value: &Value| {
                    evaluator.bags_null_pointer(
                        "(+) of a value that isn't a function".into(),
                        value,
                        "Cannot invoke \"tlc2.value.impl.Value.toFcnRcd()\" because \"b\" is null",
                    )
                };
                let Some(mut counts) = left_entries else {
                    return not_a_function(self, left);
                };
                if !is_bag(&counts) {
                    return module_argument("first", "(+)", "bag", left);
                }
                let Some(right_entries) = right_entries else {
                    return not_a_function(self, right);
                };
                if !is_bag(&right_entries) {
                    return module_argument("second", "(+)", "bag", right);
                }
                for (key, count) in right_entries {
                    add_copies(&mut counts, key, count)?;
                }
                counted_bag(counts)
            }
            // The first bag's copies less the second's, kept where some remain (`BagDiff`),
            // subtracted in an int.
            ("\\ominus", [left, right]) => {
                let (left_entries, right_entries) =
                    (function_entries(left)?, function_entries(right)?);
                let Some(left_entries) = left_entries else {
                    return module_argument("first", "(-)", "bag", left);
                };
                let Some(right_entries) = right_entries else {
                    return module_argument("second", "(-)", "bag", right);
                };
                let mut keys = Vec::new();
                let mut values = Vec::new();
                for (key, count) in left_entries {
                    let remaining = remaining_copies(&key, &count, &right_entries)?;
                    if remaining > 0 {
                        keys.push(key);
                        values.push(Value::Int(remaining));
                    }
                }
                written_function(keys, values, Class::Plain)
            }
            // Whether no element has more copies in the first bag than in the second
            // (`SqSubseteq`), counted in an int.
            ("\\sqsubseteq", [left, right]) => {
                let (left_entries, right_entries) =
                    (function_entries(left)?, function_entries(right)?);
                let expected = "a function with a finite domain";
                let Some(left_entries) = left_entries else {
                    return wrong_value("\\sqsubseteq", expected, left);
                };
                let Some(right_entries) = right_entries else {
                    return wrong_value("\\sqsubseteq", expected, right);
                };
                for (key, count) in &left_entries {
                    if remaining_copies(key, count, &right_entries)? > 0 {
                        return Ok(Value::Bool(false));
                    }
                }
                Ok(Value::Bool(true))
            }
            // The bag of an operator's images of a bag's elements, each image's copies added.
            ("BagOfAll", [bag]) => {
                let operator = operator.expect("BagOfAll's operator");
                // TLC passes an operator whose body is a number or a string as that literal.
                if let Body::Node(body) = operator.body {
                    let literal = match self.kind(body) {
                        NodeKind::Number(int) => Some(Value::Int(*int)),
                        NodeKind::String(text) => Some(Value::Str(self.text(*text))),
                        _ => None,
                    };
                    if let Some(literal) = literal {
                        return fail_coded(
                            "BagOfAll of a literal",
                            ARGUMENT_ERROR_AN,
                            format!(
                                "The first argument of BagOfAll should be an operator, but instead it is:\n{}",
                                format_pretty(&literal)
                            ),
                        );
                    }
                }
                let Some(entries) = function_entries(bag)? else {
                    return module_argument(
                        "second",
                        "BagOfAll",
                        "function with a finite domain",
                        bag,
                    );
                };
                let mut counts = Vec::new();
                for (key, count) in entries {
                    let image = self.call_with_values(operator, &[key])?;
                    add_copies(&mut counts, image, count)?;
                }
                counted_bag(counts)
            }
            _ => unreachable!("a Bags method of its arity"),
        }
    }

    // Whether the nesting that goes too deep is a recursion TLC never finishes, whose
    // `StackOverflowError` TLC reports as it is, as its evaluation stood when it overflowed: the
    // innermost call is the whole body of the definition it calls, so each call makes the next.
    // An operator's arguments are lazy (`getOpContext`), so a call evaluates nothing before the
    // next. A function's argument is evaluated and tested against the domain at each call
    // (`FcnLambdaValue.apply`), so only `F[x \in S] == F[x + c]` over Nat (c >= 0) or Int, which
    // stays in the domain, counts, where the argument is so far from overflowing an int that no
    // stack reaches that. Every frame around it must be one TLC evaluates in `Tool` and the
    // values it builds, as it does the operators of Naturals and Integers, which evaluate their
    // arguments before their Java method: a Java method that evaluates TLA+ itself, such as one
    // applying an operator argument or TLCEval, catches the error and reports it otherwise
    // (`MethodValue.eval`, `EvaluatingValue.eval`). The replay must follow TLC's call stack.
    fn is_endless_recursion(&self) -> bool {
        let Some(stack) = &self.call_stack else {
            return false;
        };
        if stack.is_frozen || stack.unfollowed.is_some() {
            return false;
        }
        let nodes: Vec<NodeId> = stack
            .frames
            .iter()
            .map(|frame| match frame {
                StackFrame::Node(node)
                | StackFrame::Prefix(node, _)
                | StackFrame::Arguments(node) => self.node(*node).0,
            })
            .collect();
        let Some(&innermost) = nodes.last() else {
            return false;
        };
        nodes.iter().all(|&node| self.is_tool_frame(node)) && self.is_endless_call(innermost, stack)
    }

    // Whether TLC evaluates a frame in `Tool` and the values it builds, without a Java method
    // that evaluates TLA+ itself.
    fn is_tool_frame(&self, node: NodeId) -> bool {
        match self.kind(node) {
            NodeKind::Number(_)
            | NodeKind::String(_)
            | NodeKind::Identifier(_)
            | NodeKind::Definition(_)
            | NodeKind::And(_)
            | NodeKind::Or(_)
            | NodeKind::If { .. }
            | NodeKind::Case { .. }
            | NodeKind::Let { .. }
            | NodeKind::Prime(_)
            | NodeKind::Tuple(_)
            | NodeKind::Record(_)
            | NodeKind::SetEnumeration(_)
            | NodeKind::FunctionApplication { .. } => true,
            NodeKind::Apply { name, .. } if !name.is_local => match name.resolution {
                Resolution::Definition(_) => true,
                Resolution::Builtin(index) => matches!(
                    self.name(self.ir.builtins[index as usize].name),
                    "=" | "#"
                        | "/="
                        | "+"
                        | "-"
                        | "*"
                        | "-."
                        | "\\div"
                        | "%"
                        | "<"
                        | ">"
                        | "<="
                        | "=<"
                        | "\\leq"
                        | ">="
                        | "\\geq"
                        | "~"
                        | "\\lnot"
                        | "\\neg"
                        | "/\\"
                        | "\\land"
                        | "\\/"
                        | "\\lor"
                        | "=>"
                        | "<=>"
                        | "\\equiv"
                        | "\\in"
                        | "\\notin"
                        | ".."
                ),
                _ => false,
            },
            _ => false,
        }
    }

    // Whether a call is the whole body of the definition it calls, which calls it again at once
    // whatever its arguments (`is_endless_recursion`).
    fn is_endless_call(&self, call: NodeId, stack: &CallStack) -> bool {
        // A recursive function's body names it as a binding of its own (`RecursiveFcnSpec`),
        // which SANY resolves to the definition.
        let callee = |name: &Name| match name.resolution {
            Resolution::Definition(index) => {
                let node = self.ir.definitions[index as usize];
                let definition = self.definition(node);
                (self.node(definition.body).0 == call
                    && (!name.is_local
                        || matches!(definition.form, DefinitionForm::Function(_))
                            && definition.name == name.text))
                    .then_some(definition)
            }
            _ => None,
        };
        match self.kind(call) {
            NodeKind::Apply { name, .. } | NodeKind::Identifier(name) => {
                callee(name).is_some_and(|definition| {
                    matches!(definition.form, DefinitionForm::Operator(_))
                        && definition.flags & Definition::RECURSIVE != 0
                })
            }
            NodeKind::FunctionApplication { function, args } => {
                let NodeKind::Identifier(name) = self.kind(*function) else {
                    return false;
                };
                let Some(definition) = callee(name) else {
                    return false;
                };
                let (DefinitionForm::Function(bounds), [argument]) =
                    (&definition.form, args.as_slice())
                else {
                    return false;
                };
                let [bound] = bounds.as_slice() else {
                    return false;
                };
                let Pattern::Name(parameter) = bound.pattern else {
                    return false;
                };
                let is_nat = match self.kind(bound.set) {
                    NodeKind::Identifier(set) if !set.is_local => match set.resolution {
                        Resolution::Builtin(index) => {
                            match self.name(self.ir.builtins[index as usize].name) {
                                "Nat" => true,
                                "Int" => false,
                                _ => return false,
                            }
                        }
                        _ => return false,
                    },
                    _ => return false,
                };
                let is_parameter = |node: NodeId| {
                    matches!(self.kind(node),
                        NodeKind::Identifier(name) if name.is_local && name.text == parameter)
                };
                let step = match self.kind(*argument) {
                    _ if is_parameter(*argument) => 0,
                    NodeKind::Apply { name, args } if !name.is_local => {
                        let operator = match name.resolution {
                            Resolution::Builtin(index) => {
                                self.name(self.ir.builtins[index as usize].name)
                            }
                            _ => return false,
                        };
                        match (operator, args.as_slice()) {
                            ("+", &[left, right]) => match (self.kind(left), self.kind(right)) {
                                (NodeKind::Number(step), _) if is_parameter(right) => *step,
                                (_, NodeKind::Number(step)) if is_parameter(left) => *step,
                                _ => return false,
                            },
                            ("-", &[left, right]) if !is_nat => match self.kind(right) {
                                NodeKind::Number(step) if is_parameter(left) => -*step,
                                _ => return false,
                            },
                            _ => return false,
                        }
                    }
                    _ => return false,
                };
                if is_nat && step < 0 {
                    return false;
                }
                if step == 0 {
                    return true;
                }
                // The argument the innermost call evaluated, from which it steps on.
                let Some(Value::Int(last)) = stack.values.get(&self.node(*argument).0) else {
                    return false;
                };
                let room = if step > 0 {
                    i64::from(i32::MAX) - i64::from(*last)
                } else {
                    i64::from(*last) - i64::from(i32::MIN)
                };
                room / i64::from(step).abs() >= UNREACHABLE_CALLS
            }
            _ => false,
        }
    }

    fn nested<T>(&mut self, work: impl FnOnce(&mut Self) -> Evaluated<T>) -> Evaluated<T> {
        self.nesting(false, work)
    }

    /// Nests an evaluation, which counts toward `MAXIMUM_RECURSION` too where it is a call of a
    /// RECURSIVE operator or a recursive function.
    fn nesting<T>(
        &mut self,
        is_recursive: bool,
        work: impl FnOnce(&mut Self) -> Evaluated<T>,
    ) -> Evaluated<T> {
        let outer = Nesting {
            depth: DEPTH.get(),
            recursions: RECURSIONS.get(),
            base: BASE.get(),
        };
        // How deep the frames are depends on the build, so the stack the nesting uses is bounded
        // too, by its distance from the outermost frame.
        let frame = 0u8;
        let here = std::ptr::addr_of!(frame) as usize;
        if outer.depth == 0 {
            BASE.set(here);
        }
        if TOO_DEEP.get()
            || outer.depth > MAXIMUM_DEPTH
            || (is_recursive && outer.recursions >= MAXIMUM_RECURSION)
            || BASE.get().abs_diff(here) > MAXIMUM_STACK_BYTES
        {
            if !TOO_DEEP.get() {
                ENDLESS.set(self.is_endless_recursion());
            }
            TOO_DEEP.set(true);
            return fail("recursion too deep");
        }
        DEPTH.set(outer.depth + 1);
        RECURSIONS.set(outer.recursions + u32::from(is_recursive));
        work(self)
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
                    return fail(TUPLE_MISMATCH);
                };
                let mut inner = context.clone();
                for (&name, element) in names.iter().zip(tuple) {
                    inner = inner.bind_value(name, element.clone());
                }
                Ok(inner)
            }
        }
    }

    // `ContextEnumerator` and reducible filters cast, rather than convert, a bound element.
    fn require_tuple_class(&self, pattern: &Pattern, value: &Value) -> Evaluated<()> {
        if !matches!(pattern, Pattern::Tuple(_)) {
            return Ok(());
        }
        match value {
            Value::Function(function) => match function.java_class.get() {
                Some(Class::Tuple) => Ok(()),
                Some(_) => fail(TUPLE_MISMATCH),
                None => fail("a tuple pattern whose TLC value class is unknown"),
            },
            _ => fail(TUPLE_MISMATCH),
        }
    }

    fn require_tuple_cast(&self, pattern: &Pattern, value: &Value) -> Evaluated<()> {
        if let Err(error) = self.require_tuple_class(pattern, value) {
            if error.reason != TUPLE_MISMATCH {
                return Err(error);
            }
            let Some(class) = numeric_value_class(value) else {
                return fail("a tuple cast whose TLC value class is unknown");
            };
            // An INSTANCE fact literal TLC did not initialize is null in Java: where the domain
            // of a function constructor holds it, TLC (`FcnLambdaValue`) doesn't cast it as
            // `ContextEnumerator` would (`[<<a, b>> \in {N!A} |-> 1] = <<>>` is false).
            if matches!(value, Value::Null) {
                return fail(
                    "a tuple pattern bound to an INSTANCE fact literal TLC did not initialize",
                );
            }
            return Err(EvalError {
                reason: "a tuple cast of a value that isn't a tuple".into(),
                message: Some(TlcMessage {
                    text: format!(
                        "class tlc2.value.impl.{class} cannot be cast to class tlc2.value.impl.TupleValue (tlc2.value.impl.{class} and tlc2.value.impl.TupleValue are in unnamed module of loader 'app')"
                    ),
                    code: None,
                    is_eval_exception: false,
                    inner: None,
                }),
                runtime_exception: RuntimeException::ClassCast,
                is_set_normalization: false,
                is_set_reduction: false,
                is_followed_comparison: false,
                is_named_normalization: false,
            });
        }
        Ok(())
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
        let declines_unsorted = std::mem::take(&mut self.declines_unsorted_bound);
        let mut sets = Vec::with_capacity(bounds.len());
        let mut is_null = false;
        for bound in bounds {
            let effects = (
                self.printed.len(),
                self.register_writes,
                self.random.as_ref().map(|random| random.state()),
            );
            let set = self.evaluate(bound.set, context)?;
            let is_quiet = effects
                == (
                    self.printed.len(),
                    self.register_writes,
                    self.random.as_ref().map(|random| random.state()),
                );
            if declines_unsorted && !self.is_starting && matches!(set, Value::Unsorted(_)) {
                return fail(UNSORTED_STATE_BOUND);
            }
            self.check_enumerable(&set, bound.set, is_quiet)?;
            let set = self.settle(&set)?;
            // `Tool.contexts` enumerates each bound in normalized order, which an interval gives
            // by building its elements (`EnumerableValue.elements(Ordering)`, `toSetEnum`) after
            // counting them (`IntervalValue.size`), which fails past 2^31 - 1 elements.
            if let Value::Interval(low, high, _) = &set {
                crate::value::interval_size(*low, *high)?;
            }
            crate::sets::check_enumerated_bound(&set)?;
            let set = elements(&set)?;
            // `ContextEnumerator` stops where a bound's enumeration gives null, an INSTANCE's
            // fact literal TLC did not initialize: its first element ends it at once. But
            // `Tool.contexts` evaluates, checks and enumerates every bound before it builds the
            // `ContextEnumerator`, so the later bounds still fail as they would.
            is_null |= is_null_enumeration(&set)?;
            sets.push(set);
        }
        if is_null || sets.iter().any(|set| set.is_empty()) {
            return Ok(true);
        }
        let mut positions = vec![0; bounds.len()];
        loop {
            let mut inner = context.clone();
            for (level, bound) in bounds.iter().enumerate() {
                // `ContextEnumerator` binds a tuple pattern to a tuple of its length alone, and
                // fails with `EC.TLC_ARGUMENT_MISMATCH`, whose `%1` the message keeps.
                let element = &sets[level][positions[level]];
                inner = match self
                    .require_tuple_class(&bound.pattern, element)
                    .and_then(|()| self.bind_pattern(&bound.pattern, element, &inner))
                {
                    Err(error) if error.reason == TUPLE_MISMATCH => {
                        return fail_with(
                            TUPLE_MISMATCH,
                            TlcMessage {
                                text: "Argument mismatch in operator application.%1".into(),
                                code: Some(ARGUMENT_MISMATCH),
                                is_eval_exception: false,
                                inner: None,
                            },
                        );
                    }
                    bound => bound?,
                };
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

    // TLC's failure quantifying over a value it can't enumerate (`Tool.contexts`): one that isn't
    // a set (`Value.getNonEnumerableErrorMsg`), or a set it implements in Java, which it explains
    // for all but STRING since 1.7.4. A function built of a constructor TLC may hold lazy
    // (`FcnLambdaValue`), whose `toString` builds it again (`toFcnRcd`): as the evaluator built
    // it, where the bound is the constructor, which built it here without effect (`is_quiet`).
    fn check_enumerable(&self, set: &Value, node: NodeId, is_quiet: bool) -> Evaluated<()> {
        let is_non_set = match set {
            Value::Function(function) if function.class.get() == Class::Lambda => {
                is_quiet && matches!(self.kind(node), NodeKind::FunctionConstruction { .. })
            }
            _ => is_non_set(set),
        };
        // `FcnLambdaValue.toString` fails to build one over Nat, Int or STRING and prints its
        // parameter, its domain and where its body is.
        let is_non_set = is_non_set
            || matches!(set, Value::Lambda(lambda)
                if matches!(&lambda.domain, Value::Lazy(lazy)
                    if matches!(***lazy, Lazy::Nat | Lazy::Int | Lazy::Strings)));
        if is_non_set && let Some(bound) = self.describe_node(node) {
            return fail_runtime(
                "quantified over a non-set",
                format!(
                    "TLC encountered a non-enumerable quantifier bound\n{}.\n{bound}",
                    format_pretty(set)
                ),
            );
        }
        let Value::Lazy(lazy) = set else {
            return Ok(());
        };
        // Only the sets TLC refuses to quantify over print here: printing a set normalizes the
        // sets it holds, as TLC does only where it prints them.
        if !matches!(
            ***lazy,
            Lazy::Nat | Lazy::Int | Lazy::Real | Lazy::Seq(_) | Lazy::Strings | Lazy::Any
        ) {
            return Ok(());
        }
        let text = format_value(set);
        let quantified = format!(
            "universally (\\A) or existentially (\\E) quantify over {text}, because this would require checking an\ninfinite number of cases."
        );
        let explanation = match ***lazy {
            Lazy::Nat | Lazy::Int | Lazy::Real => format!(
                "The set {text} contains infinitely many elements. As a result, TLC cannot evaluate expressions that\n{quantified} Note that TLC handles set membership like T \\subseteq {text} for any finite set T."
            ),
            Lazy::Seq(_) => format!(
                "In TLA+, Seq(S) represents the set of all finite sequences whose elements come from the set S. Even when S\nis a finite set, the number of possible sequences in Seq(S) is unbounded because sequences can have any\nfinite length (e.g., length 0, 1, 2, and so on). As a result, TLC cannot evaluate expressions that\n{quantified} Note that for a finite set of sequences s, TLC handles s \\subseteq Seq(S).\nSee https://explain.tlapl.us/seq-unenumerable for additional details."
            ),
            Lazy::Strings | Lazy::Any => String::new(),
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
    // TLC keeps a function whose definition reaches itself lazy (SANY's RecursiveFcnSpec, which
    // `Tool`'s OPCODE_rfs never builds), whatever its domain.
    fn defined_function(
        &mut self,
        bounds: &[Bound],
        body: NodeId,
        context: &Context,
        is_recursive: bool,
    ) -> Evaluated<Value> {
        // A function whose definition reaches itself as it is built recurses as an operator does.
        let keeps_lazy = u32::from(is_recursive);
        self.keeping_lazy += keeps_lazy;
        let result = self.nesting(is_recursive, |evaluator| {
            evaluator.construct_function(bounds, body, context)
        });
        self.keeping_lazy -= keeps_lazy;
        if result.is_err()
            && let Some(stack) = &mut self.call_stack
        {
            stack.unfollowed.get_or_insert(BUILT_FUNCTION);
        }
        result
    }

    // Whether a function constructor's domain is a set enumeration TLC fails to sort, which TLC
    // keeps lazy (`FcnLambdaValue`) and applies searching it as written, where the evaluator
    // builds the function sorted: as the function of an application (`is_kept`), or where the
    // sort fails comparing a function or a record, whose consumers the evaluator follows no
    // further. Of an application, `apply_kept_lazy` follows `FcnLambdaValue.apply` over a domain
    // TLC doesn't build (`UNSORTED_LAZY_DOMAIN`), and only a domain TLC builds declines here.
    fn is_unsorted_domain(&self, set: &Value, is_kept: bool) -> bool {
        let Value::Unsorted(elements) = set else {
            return false;
        };
        (is_kept && self.keeping_lazy > 0)
            || unsorted_failure(elements).message.is_some_and(|message| {
                message
                    .text
                    .starts_with("Attempted to compare the function ")
                    || message.text.starts_with("Attempted to compare record:\n")
            })
    }

    // `FcnParams.size` of a function constructor's domains, which it counts in order: the failure
    // of the first that is a set enumeration TLC can't sort (`count_domains`), and otherwise none.
    fn counted_domains_failure(
        &mut self,
        bounds: &[Bound],
        context: &Context,
    ) -> Evaluated<Option<EvalError>> {
        let mut sets = Vec::with_capacity(bounds.len());
        for bound in bounds {
            sets.push(self.evaluate(bound.set, context)?);
        }
        Ok(worded_failure(count_domains(&sets, false, &mut true)))
    }

    // A function constructor over a set enumeration TLC fails to sort, comparing a function or a
    // record, in TLCEval's argument of constant level evaluated again (`builds_unsorted_domains`)
    // or in an assumption, whose failure TLC reports without frames: where nothing keeps the
    // constructor lazy, `Tool`'s OPCODE_fc builds it (`toFcnRcd`), whose `FcnParams.size` fails
    // as the domain's `normalize` does (`count_domains`). Otherwise none, and the evaluator
    // declines.
    fn counted_unsorted_failure(&self, sets: &[Value]) -> Evaluated<Option<EvalError>> {
        // TLC builds the function only where every domain is `Reducible`.
        if !(self.builds_unsorted_domains || self.is_assumption)
            || self.keeping_lazy > 0
            || !sets.iter().all(|set| {
                matches!(
                    java_set_class(set),
                    Some(SetClass::Enumeration | SetClass::Interval)
                )
            })
        {
            return Ok(None);
        }
        Ok(worded_failure(count_domains(sets, false, &mut true)))
    }

    // A function constructor, whose body's prints, where TLC keeps it lazy, wait for an operation
    // that forces it (`force_lazy_prints`).
    // A constructor written in place. Under `EvalControl.KeepLazy`, as the function of an
    // application and what that evaluates, or over a domain that isn't a set enumeration or an
    // interval (`Reducible`), `Tool`'s OPCODE_fc keeps it a FcnLambdaValue, whose body TLC
    // evaluates only at the keys it applies or selects (`FcnLambdaValue.apply`, `select`), in the
    // frames of that application, and `CallStackTool` hands on a copy without a source
    // (`new FcnLambdaValue(value, this)`), whose failures are plain ones. The evaluator builds
    // it, which fails where TLC may not: in a replay, a function of one name whose body has no
    // effects and whose build fails in it is that FcnLambdaValue instead, which the evaluator
    // applies, updates and asks the domain of as TLC does.
    fn construct_in_place(
        &mut self,
        node: NodeId,
        bounds: &[Bound],
        body: NodeId,
        context: &Context,
    ) -> Evaluated<Value> {
        // Only one the application applies directly, or updates by EXCEPT and applies: a name
        // bound to it, a LET definition or an argument, keeps the FcnLambdaValue from its first
        // use (`LazyValue`), which later uses may ask the domain of (`getDomain`), hold in a set
        // or a record, print (`toString` swallows the failure) or build (`toFcnRcd`, failing in
        // the frames of that first use), and a set or a record holding it may be normalized,
        // compared or fingerprinted, none of which the evaluator follows.
        let is_applied_directly = self.in_place_functions.contains(&self.resolved(node));
        let held = match bounds {
            [bound] if is_applied_directly && self.call_stack.is_some() && !self.is_174() => {
                match bound.pattern {
                    Pattern::Name(name)
                        if !self.has_effect(body, context) && !self.may_prime(body, context) =>
                    {
                        Some((bound.set, name))
                    }
                    _ => None,
                }
            }
            _ => None,
        };
        let Some((set_node, name)) = held else {
            return self.construct_function(bounds, body, context);
        };
        let saved = (
            self.call_stack.clone(),
            self.lazy_unions,
            self.lazy_domains,
            self.lazy_body_effects,
            self.unfollowed_constructions,
        );
        let effects = self.lazy_effects();
        self.is_lazy_body_failure_worded = false;
        match self.construct_function(bounds, body, context) {
            Err(error)
                if error.reason == LAZY_BODY_AT_KEY
                    && self.is_lazy_body_failure_worded
                    && self.lazy_effects() == effects =>
            {
                (
                    self.call_stack,
                    self.lazy_unions,
                    self.lazy_domains,
                    self.lazy_body_effects,
                    self.unfollowed_constructions,
                ) = saved;
                // The domain again, which evaluated without effects before.
                let set = self.evaluate(set_node, context)?;
                let is_held = match &set {
                    Value::Set(_) | Value::Interval(..) => self.keeping_lazy > 0,
                    Value::Lazy(lazy) => !lazy.is_overridden(),
                    _ => false,
                };
                if !is_held {
                    if let Some(stack) = &mut self.call_stack {
                        stack.unfollowed.get_or_insert(LAZY_BODY);
                    }
                    return Err(error);
                }
                self.captures += 1;
                self.held_lambda(name, set, body, context, true)
            }
            result => result,
        }
    }

    fn construct_function(
        &mut self,
        bounds: &[Bound],
        body: NodeId,
        context: &Context,
    ) -> Evaluated<Value> {
        let outer = self.lazy_print_start.take();
        let outer_keys = std::mem::take(&mut self.lazy_print_keys);
        let first = self.lazy_print_count;
        let result = self.build_counted(bounds, body, context);
        let start = std::mem::replace(&mut self.lazy_print_start, outer);
        let keys = std::mem::replace(&mut self.lazy_print_keys, outer_keys);
        let (Some(start), Ok(function)) = (start, &result) else {
            return result;
        };
        // TLC prints the body's lines where it forces the FcnLambdaValue (`toFcnRcd`), which
        // the evaluator follows only for an operation it evaluates the function as an argument
        // of, and only for a function whose body holds no other lazy function that printed.
        let Value::Function(function) = function else {
            return fail(LAZY_BODY_EFFECTS);
        };
        if self.forcing.is_none() {
            return fail(LAZY_BODY_EFFECTS);
        }
        // A body that printed only as it built lazy functions of its own: TLC builds those as it
        // forces this one, without printing, and prints them where it forces them in turn, as
        // they wait here, with nothing between them.
        let built = self.lazy_prints_from(first);
        if built < self.lazy_prints.len() {
            let mut at = start;
            for lazy in &self.lazy_prints[built..] {
                if lazy.start != at {
                    return fail(LAZY_BODY_EFFECTS);
                }
                at = lazy.end;
            }
            if at != self.lazy_effects() {
                return fail(LAZY_BODY_EFFECTS);
            }
            return result;
        }
        self.lazy_print_count += 1;
        self.lazy_prints.push(LazyPrint {
            id: first,
            start,
            end: self.lazy_effects(),
            function: Rc::clone(function),
            origin: None,
            is_copied: false,
            thunk: None,
            keys,
        });
        result
    }

    // `construct_function`'s build, counting a failure past its domains the evaluator may meet
    // where TLC doesn't (`unfollowed_constructions`): all but in a function of a single name over
    // a set enumeration or an interval TLC builds as it meets it (`Tool`'s OPCODE_fc calls
    // `toFcnRcd`, which evaluates the body at each element of the normalized domain in order,
    // as the evaluator does).
    fn build_counted(
        &mut self,
        bounds: &[Bound],
        body: NodeId,
        context: &Context,
    ) -> Evaluated<Value> {
        let mut is_followed = None;
        let result = self.build_function(bounds, body, context, &mut is_followed);
        if result.is_err() && is_followed == Some(false) {
            self.unfollowed_constructions += 1;
        }
        result
    }

    // `construct_function`, which sets `is_followed` once it has evaluated the domains.
    fn build_function(
        &mut self,
        bounds: &[Bound],
        body: NodeId,
        context: &Context,
        is_followed: &mut Option<bool>,
    ) -> Evaluated<Value> {
        let preserves = std::mem::take(&mut self.preserves_lazy_domain);
        // A function over an interval keeps it as its domain.
        if let [bound] = bounds
            && let Pattern::Name(name) = bound.pattern
        {
            let set = self.evaluate(bound.set, context)?;
            *is_followed = Some(false);
            if self.is_unsorted_domain(&set, false) {
                if let Some(failure) = self.counted_unsorted_failure(std::slice::from_ref(&set))? {
                    return Err(failure);
                }
                return fail(UNSORTED_DOMAIN);
            }
            // `Tool`'s OPCODE_fc keeps a function lazy unless its domain is reducible, which
            // the evaluator follows where it can't build the function: over a set it can't
            // enumerate, an infinite one, or one whose enumeration fails, which TLC never
            // enumerates to build it.
            if !matches!(set, Value::Set(_) | Value::Interval(..))
                && (!is_enumerable(&set)
                    || !is_finite(&set).unwrap_or(false)
                    || (matches!(set, Value::Lazy(_)) && elements(&set).is_err()))
            {
                let text = (
                    format!("[{} \\in ", self.name(name)),
                    format!(" |-> <expression {}>]", self.expression_text(body)?),
                );
                self.captures += 1;
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
                    params: None,
                    is_in_place: false,
                })));
            }
            // TLC keeps a function over a lazy set lazy (`FcnLambdaValue`) and normalizes that set
            // deeply as it prints or normalizes the function (`deepNormalize`), which fails on a
            // set enumeration it holds that TLC can't sort, which the function the evaluator
            // builds no longer holds.
            if matches!(set, Value::Lazy(_)) && holds_unsorted_deep(&set) {
                return fail("a function TLC keeps lazy over a set that holds one TLC can't sort");
            }
            let is_built = self.is_built(std::slice::from_ref(&set));
            // TLC keeps the function lazy (`FcnLambdaValue`), and never sorts a set enumeration
            // it holds unnormalized as its domain, which the evaluator fails to build it over.
            if !is_built && matches!(set, Value::Unsorted(_)) {
                return fail(UNSORTED_LAZY_DOMAIN);
            }
            if self.is_unsorted_domain(&set, true) {
                return fail(UNSORTED_DOMAIN);
            }
            let is_reducible = matches!(
                java_set_class(&set),
                Some(SetClass::Enumeration | SetClass::Interval)
            );
            *is_followed = Some(is_built && is_reducible);
            // A function TLC keeps lazy asks its domain for the argument it is applied to.
            let is_interval_value = java_set_class(&set) == Some(SetClass::Interval);
            // A set enumeration TLC holds normalized searches the argument as the receiver of
            // each comparison (`ValueVec.search`); one it holds as written is `held_lazy_domains`'.
            let is_sorted_enumeration = matches!(set, Value::Set(_))
                && java_set_class(&set) == Some(SetClass::Enumeration)
                && unnormalized(&set).is_none();
            let lazy_domain = (!is_built
                && (is_interval_value
                    || is_sorted_enumeration
                    || matches!(&set, Value::Lazy(lazy) if !lazy.is_overridden())))
            .then(|| set.clone());
            if let Value::Interval(low, high, _) = set {
                // TLC builds a function over an interval at once (`toFcnRcd`), for its size of
                // values (`IntervalValue.size`), which fails past 2^31 - 1 elements.
                if is_built {
                    crate::value::interval_size(low, high)?;
                }
                // The evaluator builds the function, which TLC may keep lazy and apply at a few
                // arguments only, up to the size it builds an interval to.
                if i64::from(high) - i64::from(low) >= crate::value::MAXIMUM_INTERVAL as i64 {
                    return fail("a function over an interval too large to build");
                }
                let mut values = Vec::new();
                for key in low..=high {
                    let context = context.bind_value(name, Value::Int(key));
                    values.push(self.keyed_function_body(
                        &Value::Int(key),
                        body,
                        &context,
                        is_built,
                    )?);
                }
                let function = Value::over_interval(low, values, Class::Lambda);
                if let Value::Function(inner) = &function {
                    inner.is_domain_interval.set(is_interval_value);
                }
                self.note_kept_lazy(&function, is_built, is_reducible);
                self.hold_lazy_domain(&function, lazy_domain);
                return Ok(function);
            }
            // The elements of the set as TLC holds it, written, before the evaluator enumerates it.
            let held = (!is_built && java_set_class(&set) == Some(SetClass::Enumeration))
                .then(|| unnormalized(&set));
            let mut keys = Vec::new();
            let mut values = Vec::new();
            let domain = if preserves && !is_built {
                held_elements(&set)?
            } else {
                elements(&set)?
            };
            // Over a set that isn't Reducible, TLC keeps the function lazy whatever the control
            // (`FcnLambdaValue`), and evaluates the body only where it applies, selects or
            // builds it (`toFcnRcd`). A body that fails at a key, with TLC's own failure and no
            // effect before it, leaves the function TLC holds: the evaluator holds it so, unbuilt,
            // and fails where TLC builds it. A failure the call stack records is
            // `construct_in_place`'s.
            let is_kept_unbuilt = !is_built
                && self.call_stack.is_none()
                && !self.is_174()
                && matches!(&set, Value::Lazy(lazy) if !lazy.is_overridden());
            let effects = self.lazy_effects();
            self.is_lazy_body_failure_worded = false;
            for element in domain.iter() {
                keys.push(element.clone());
                let inner = context.bind_value(name, element.clone());
                match self.keyed_function_body(element, body, &inner, is_built) {
                    Ok(value) => values.push(value),
                    Err(error)
                        if is_kept_unbuilt
                            && error.reason == LAZY_BODY_AT_KEY
                            && self.is_lazy_body_failure_worded
                            && self.lazy_effects() == effects =>
                    {
                        self.captures += 1;
                        return self.held_lambda(name, set.clone(), body, context, false);
                    }
                    Err(error) => return Err(error),
                }
            }
            let function = sorted_function(keys, values, Class::Lambda)?;
            self.note_kept_lazy(&function, is_built, is_reducible);
            self.hold_lazy_domain(&function, lazy_domain);
            // Applied while TLC keeps it lazy, the function asks its bound's set for the
            // argument, which TLC has sorted where a definition that reads no state names it.
            if let Value::Function(inner) = &function
                && self.is_sorted_constant(bound.set)
            {
                inner.search.set(Search::SortedDomain);
            } else if let Value::Function(inner) = &function
                && let Some(held) = held
            {
                // The entries of functions nothing holds any more go as the map doubles.
                let held_domains = &mut self.held_lazy_domains;
                if held_domains.len() >= 1024 && held_domains.len().is_power_of_two() {
                    held_domains.retain(|_, (function, _)| function.strong_count() > 0);
                }
                held_domains.insert(Rc::as_ptr(inner) as usize, (Rc::downgrade(inner), held));
            }
            return Ok(function);
        }
        // TLC evaluates every domain before it enumerates any (`Tool.evalAppl`'s
        // `OPCODE_fc`), so a later domain fails even when an earlier one is empty.
        let mut sets = Vec::with_capacity(bounds.len());
        for bound in bounds {
            sets.push(self.evaluate(bound.set, context)?);
        }
        *is_followed = Some(false);
        if sets.iter().any(|set| self.is_unsorted_domain(set, false)) {
            if let Some(failure) = self.counted_unsorted_failure(&sets)? {
                return Err(failure);
            }
            return fail(UNSORTED_DOMAIN);
        }
        // TLC keeps such a function lazy too, and applies it without enumerating its domains,
        // which the evaluator doesn't follow for several bounds or a tuple pattern.
        if sets
            .iter()
            .any(|set| !is_enumerable(set) || !is_finite(set).unwrap_or(false))
        {
            if sets.iter().any(|set| self.is_unsorted_domain(set, true)) {
                return fail(UNSORTED_DOMAIN);
            }
            return self.several_lambda(bounds, sets, body, context);
        }
        let is_built = self.is_built(&sets);
        if !is_built && sets.iter().any(|set| matches!(set, Value::Unsorted(_))) {
            return fail(UNSORTED_LAZY_DOMAIN);
        }
        if sets.iter().any(|set| self.is_unsorted_domain(set, true)) {
            return fail(UNSORTED_DOMAIN);
        }
        let is_reducible = sets.iter().all(|set| {
            matches!(
                java_set_class(set),
                Some(SetClass::Enumeration | SetClass::Interval)
            )
        });
        // TLC builds the function (`toFcnRcd`), counting every domain before it enumerates any
        // (`FcnParams.size`): a set enumeration TLC can't sort fails past an empty domain too,
        // which the enumeration below never reaches. Where a call stack traces that failure,
        // outside an assumption, TLC adds the set's own source (`SetEnumValue.size`'s
        // FingerprintException), which the replay follows only where the enumeration meets the
        // set.
        if is_built && is_reducible {
            let mut is_enumerated = true;
            if let Err(error) = count_domains(&sets, true, &mut is_enumerated) {
                if is_enumerated || self.call_stack.is_none() || self.is_assumption {
                    return Err(error);
                }
                return fail(
                    "a function's domain TLC counts, failing, past one its enumeration stops at, \
                     where a call stack traces it",
                );
            }
        } else if sets.iter().enumerate().any(|(index, set)| {
            // TLC keeps the function lazy and counts every domain as a use builds it
            // (`toFcnRcd`), even past one the enumeration below stops at as empty, where one
            // holding a set TLC can't sort fails.
            holds_unsorted_deep(set)
                && sets[..index].iter().any(|before| match before {
                    Value::Set(set) => set.as_slice().is_empty(),
                    Value::Interval(low, high, _) => high < low,
                    Value::Unsorted(_) => false,
                    _ => true,
                })
        }) {
            return fail("a function TLC keeps lazy whose domain past an empty one it can't sort");
        }
        let mut keys = Vec::new();
        let mut values = Vec::new();
        self.for_each_keyed(
            bounds,
            context,
            is_built,
            preserves && !is_built,
            &mut Vec::new(),
            &mut |evaluator, inner, bound| {
                // The key is the element of a single bound, or the tuple of the bounds' elements.
                keys.push(match bound {
                    [element] => element.clone(),
                    _ => Value::tuple(bound.to_vec()),
                });
                let key = keys.last().expect("the key");
                values.push(evaluator.keyed_function_body(key, body, inner, is_built)?);
                Ok(())
            },
        )?;
        let function = sorted_function(keys, values, Class::Lambda)?;
        self.note_kept_lazy(&function, is_built, is_reducible);
        if let ([bound], Value::Function(inner)) = (bounds, &function)
            && self.is_sorted_constant(bound.set)
        {
            inner.search.set(Search::SortedDomain);
        }
        Ok(function)
    }

    // `[x, y \in S, <<a, b>> \in T |-> e]` TLC keeps lazy, as `FcnParams` holds it: SANY's names
    // a domain bounds together, which the IR writes as bounds of one shared set, or a tuple. TLC
    // prints it without enumerating a domain it can't count (`toString` swallows `size`'s
    // failure), and only the first name of each group (`FcnParams.toString`).
    fn several_lambda(
        &mut self,
        bounds: &[Bound],
        sets: Vec<Value>,
        body: NodeId,
        context: &Context,
    ) -> Evaluated<Value> {
        // A finite domain beside an infinite one keeps TLC from counting the function too, but
        // where none is Nat, Int or a product of them the evaluator doesn't say how TLC counts.
        let is_uncountable = |set: &Value| {
            match set {
            Value::Lazy(lazy) => match &***lazy {
                Lazy::Nat | Lazy::Int => true,
                Lazy::Product(factors) => factors.iter().all(
                    |factor| matches!(factor, Value::Lazy(lazy) if matches!(***lazy, Lazy::Nat | Lazy::Int)),
                ),
                _ => false,
            },
            _ => false,
        }
        };
        if !sets.iter().any(is_uncountable) {
            return fail("a function of several bounds or a tuple pattern TLC keeps lazy");
        }
        let mut groups: Vec<ParamGroup> = Vec::new();
        let mut previous: Option<NodeId> = None;
        for (bound, set) in bounds.iter().zip(sets) {
            let node = self.resolved(bound.set);
            match &bound.pattern {
                Pattern::Name(name) => match groups.last_mut() {
                    Some((names, false, _)) if previous == Some(node) => names.push(*name),
                    _ => groups.push((vec![*name], false, set)),
                },
                Pattern::Tuple(names) => groups.push((names.clone(), true, set)),
            }
            previous = Some(node);
        }
        let written = groups
            .iter()
            .map(|(names, is_tuple, domain)| {
                let name = if *is_tuple {
                    format!(
                        "<<{}>>",
                        names
                            .iter()
                            .map(|&name| self.name(name))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                } else {
                    self.name(names[0]).to_string()
                };
                format!("{name} \\in {}", format_value(domain))
            })
            .collect::<Vec<_>>()
            .join(", ");
        let mut domains = Vec::new();
        for (names, is_tuple, domain) in &groups {
            let count = if *is_tuple { 1 } else { names.len() };
            domains.extend(std::iter::repeat_n(domain.clone(), count));
        }
        let domain = match &domains[..] {
            [domain] => domain.clone(),
            _ => Value::lazy(Lazy::Product(domains)),
        };
        let name = groups[0].0[0];
        self.captures += 1;
        Ok(Value::Lambda(Rc::new(Lambda {
            name,
            domain,
            body,
            context: context.clone(),
            current: self.current.clone(),
            next: self.next.clone(),
            level: self.level,
            excepts: Vec::new(),
            text: (
                format!("[{written}"),
                format!(" |-> <expression {}>]", self.expression_text(body)?),
            ),
            params: Some(Rc::new(groups)),
            is_in_place: false,
        })))
    }

    // `FcnLambdaValue.apply` of a function of several parameters or a tuple pattern: the
    // arguments, taken as a tuple, each tested against its domain and bound in turn, and those
    // past the parameters ignored.
    // A test of a lazy function's domain. A domain TLC built of other sets, such as
    // `Nat \X Nat` or a set enumeration, keeps the source `CallStackTool` gives it, and TLC
    // reports a test of it that fails as a value it can't fingerprint
    // (`FingerprintException.getNewHead`), which the replay doesn't word. Nat, Int, STRING and
    // Seq(S) report the failure itself, as any does without the call stack.
    fn member_of_domain(&mut self, element: &Value, domain: &Value) -> Evaluated<bool> {
        let is_member = self.member(element, domain);
        // TLC evaluates an assumption without `CallStackTool`, so that no value has a source,
        // and an assumption checked again has a call stack of its own without them.
        if is_member.is_err()
            && !self.is_assumption
            && self
                .call_stack
                .as_ref()
                .is_some_and(|stack| !stack.is_unsourced)
            && !matches!(domain, Value::Lazy(lazy)
                if matches!(***lazy, Lazy::Nat | Lazy::Int | Lazy::Real | Lazy::Strings | Lazy::Seq(_)))
        {
            return fail("a failing test of a lazy function's domain TLC built from an expression");
        }
        is_member
    }

    fn apply_several(
        &mut self,
        lambda: &Lambda,
        groups: &[ParamGroup],
        key: &Value,
    ) -> Evaluated<Value> {
        let shown = || {
            let (before, after) = lambda.text();
            pretty_print(
                &format!("{before}{after}")
                    .encode_utf16()
                    .collect::<Vec<_>>(),
            )
        };
        let reason = "applied a function outside its domain";
        let mut context = lambda.context.clone();
        let tuple_of = |value: &Value| -> Evaluated<Option<Vec<Value>>> {
            match value {
                Value::Lambda(_) | Value::Lazy(_) => fail("a lazy value taken as a tuple"),
                value => Ok(as_tuple(value).map(<[Value]>::to_vec)),
            }
        };
        if let [(names, true, domain)] = groups {
            if !self.member_of_domain(key, domain)? {
                return fail_runtime(
                    reason,
                    format!(
                        "In applying the function\n{},\nthe first argument is:\n{}\nwhich is not in its domain.\n",
                        shown(),
                        printed_argument(key)?
                    ),
                );
            }
            let Some(elements) = tuple_of(key)? else {
                return fail_runtime(
                    reason,
                    format!(
                        "In applying the function\n{},\nthe first argument is:\n{}\nwhich does not match its formal parameter.\n",
                        shown(),
                        printed_argument(key)?
                    ),
                );
            };
            // `apply` returns null, which its caller doesn't expect.
            if elements.len() != names.len() {
                return fail("a tuple pattern applied to a tuple of another length");
            }
            for (&name, element) in names.iter().zip(elements) {
                context = context.bind_value(name, element);
            }
        } else {
            let Some(elements) = tuple_of(key)? else {
                return fail_runtime(
                    reason,
                    format!(
                        "In applying the function\n{},\nthe argument list is:\n{}\nwhich does not match its formal parameter.\n",
                        shown(),
                        printed_argument(key)?
                    ),
                );
            };
            let mut argument = 0;
            for (names, is_tuple, domain) in groups {
                // `elems[argn]` past the arguments is an ArrayIndexOutOfBoundsException.
                let too_few = || {
                    index_out_of_bounds(
                        "a function of several parameters applied to too few arguments",
                        elements.len(),
                        elements.len(),
                    )
                };
                if *is_tuple {
                    let Some(element) = elements.get(argument) else {
                        return too_few();
                    };
                    argument += 1;
                    if !self.member_of_domain(element, domain)? {
                        return fail_runtime(
                            reason,
                            format!(
                                "In applying the function\n{},\nthe argument number {argument} is:\n{}\nwhich is not in its domain.\n",
                                shown(),
                                printed_argument(element)?
                            ),
                        );
                    }
                    let parts = tuple_of(element)?.filter(|parts| parts.len() == names.len());
                    let Some(parts) = parts else {
                        return fail_runtime(
                            reason,
                            format!(
                                "In applying the function\n{},\nthe argument number {argument} is:\n{}\nwhich does not match its formal parameter.\n",
                                shown(),
                                printed_argument(element)?
                            ),
                        );
                    };
                    for (&name, part) in names.iter().zip(parts) {
                        context = context.bind_value(name, part);
                    }
                } else {
                    for &name in names {
                        let Some(element) = elements.get(argument) else {
                            return too_few();
                        };
                        if !self.member_of_domain(element, domain)? {
                            return fail_runtime(
                                reason,
                                format!(
                                    "In applying the function\n{},\nthe argument number {} is:\n{}\nwhich is not in the function's domain {}.\n",
                                    shown(),
                                    argument + 1,
                                    printed_argument(element)?,
                                    format_value(&lambda.domain)
                                ),
                            );
                        }
                        context = context.bind_value(name, element.clone());
                        argument += 1;
                    }
                }
            }
        }
        let current = std::mem::replace(&mut self.current, lambda.current.clone());
        let next = std::mem::replace(&mut self.next, lambda.next.clone());
        let level = std::mem::replace(&mut self.level, lambda.level);
        let result = self.evaluate(lambda.body, &context);
        self.current = current;
        self.next = next;
        self.level = level;
        result
    }

    // `FcnLambdaValue.apply` and `select` of a constructor written in place that TLC keeps lazy
    // over an interval, a sorted set enumeration or a lazy set ask the set whether it holds the
    // argument, before any
    // EXCEPT's or the body, which fails as the set's `member` does (`IntervalValue.member`,
    // `SubsetValue.member`, ...). Where the set holds it or not, the caller goes on.
    fn lazy_domain_failure(
        &mut self,
        function: &Value,
        function_node: NodeId,
        argument: &Value,
    ) -> Evaluated<()> {
        let Value::Function(inner) = function else {
            return Ok(());
        };
        if self.is_174()
            || matches!(argument, Value::Model(_))
            || !matches!(
                self.kind(function_node),
                NodeKind::FunctionConstruction {
                    is_recursive: false,
                    ..
                }
            )
        {
            return Ok(());
        }
        let Some(set) = self
            .lazy_domain_sets
            .get(&(Rc::as_ptr(inner) as usize))
            .filter(|(held, _)| held.strong_count() > 0)
            .map(|(_, set)| set.clone())
        else {
            return Ok(());
        };
        // A membership with effects, such as a filter's predicate, is one the evaluator asked
        // again as it built the function, so it declines it.
        let before = self.lazy_effects();
        let is_member = self.member(argument, &set);
        if self.lazy_effects() != before {
            return fail("the membership in the domain of a function TLC keeps lazy, with effects");
        }
        // The set a definition of constant level names, which TLC computed as it started with
        // its plain `Tool` and keeps (`processConstantDefns`), has no source, nor has a number,
        // a string or a boolean the search compares with its elements as the receiver
        // (`ValueVec.search`), but one a union returned (`sourced_non_set`): the set's `member`
        // throws the failure as it is, and `CallStackTool` applies a copy of the FcnLambdaValue
        // without one, so TLC reports it with the frames of the application, which the replay
        // follows. An argument that is a set, a tuple or a record has a source, whose `compareTo`
        // throws a FingerprintException.
        let is_unsourced_constant = match self.kind(function_node) {
            NodeKind::FunctionConstruction { bounds, .. } => {
                matches!(&bounds[..], [bound] if self.is_sorted_constant(bound.set))
                    && matches!(&set, Value::Set(_))
                    && matches!(argument, Value::Bool(_) | Value::Int(_) | Value::Str(_))
                    && self.call_stack.as_ref().is_some_and(|stack| {
                        stack.source(&set).is_none()
                            && !stack.is_resourced(&set)
                            && !stack.sourced_non_set
                    })
            }
            _ => false,
        };
        match is_member {
            Err(error) if error.message.is_some() => {
                if let Some(stack) = &mut self.call_stack
                    && !is_unsourced_constant
                {
                    stack.unfollowed.get_or_insert(LAZY_DOMAIN_MEMBER);
                }
                Err(error)
            }
            _ => Ok(()),
        }
    }

    // Records the domain of a function TLC keeps lazy over an interval or a lazy set, which
    // its applications ask for the argument (`lazy_domain_sets`).
    fn hold_lazy_domain(&mut self, function: &Value, domain: Option<Value>) {
        let (Value::Function(inner), Some(domain)) = (function, domain) else {
            return;
        };
        // The entries of functions nothing holds any more go as the map doubles.
        let sets = &mut self.lazy_domain_sets;
        if sets.len() >= 1024 && sets.len().is_power_of_two() {
            sets.retain(|_, (function, _)| function.strong_count() > 0);
        }
        sets.insert(Rc::as_ptr(inner) as usize, (Rc::downgrade(inner), domain));
    }

    // Records, as a failure is evaluated, a function the evaluator built that TLC keeps lazy.
    fn note_kept_lazy(&mut self, function: &Value, is_built: bool, is_reducible: bool) {
        if let Value::Function(function) = function {
            function.is_eager_record.set(is_built && is_reducible);
            function.java_class.set(Some(if is_built {
                Class::Plain
            } else {
                Class::Lambda
            }));
        }
        if !is_built
            && self.call_stack.is_some()
            && let Value::Function(inner) = function
        {
            self.kept_lazy.insert(Rc::as_ptr(inner) as usize);
        }
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

    // Whether `Tool`'s OPCODE_fc builds a function of these domains as it constructs it
    // (`FcnLambdaValue.toFcnRcd`): where each is reducible, a set enumeration or an interval, and
    // TLC doesn't keep the function lazy.
    fn is_built(&self, domains: &[Value]) -> bool {
        self.keeping_lazy == 0
            && domains.iter().all(|domain| {
                matches!(
                    domain,
                    Value::Set(_) | Value::Interval(..) | Value::Unsorted(_)
                )
            })
    }

    /// How many bodies of functions TLC keeps lazy had effects as the evaluator built them.
    pub(crate) fn lazy_body_effects(&self) -> usize {
        self.lazy_body_effects
    }

    // Where the lazy functions numbered from `first` on begin among those held.
    fn lazy_prints_from(&self, first: u64) -> usize {
        self.lazy_prints.partition_point(|lazy| lazy.id < first)
    }

    fn lazy_effects(&self) -> Effects {
        (
            self.printed.len(),
            self.register_reads,
            self.register_writes,
            self.random.as_ref().map(|random| random.state()),
        )
    }

    // TLC applies a FcnLambdaValue (`apply`, `select`) without forcing it, evaluating its body at
    // the key again, and its EXCEPT is a copy (`takeExcept`) that each force builds again, where
    // the evaluator applies or updates the function it built: with a lazy function whose body
    // printed held, the evaluator declines them.
    fn unforced_use(&self, value: Value) -> Evaluated<Value> {
        if !self.lazy_prints.is_empty() {
            return fail(LAZY_BODY_EFFECTS);
        }
        Ok(value)
    }

    // The operation `forcing` names forces lazy functions whose bodies printed as the evaluator
    // built them, after `OpValue.eval` has evaluated every argument. The evaluator printed each
    // body's lines as it built the function, which is TLC's order where nothing else had effects
    // between the building and the force: from each function's build to the next's first body,
    // and from the last's build to the operation.
    //
    // `CombineFcn`, `equals` and the members of a set of functions or a set enumeration call
    // `toFcnRcd` of the arguments `Force::Built` names, in that order, which caches what it builds
    // in the function (`fcnRcd`): any lazy function held so far may be one of them. `Print` and
    // `PrintT` print a copy (`deepCopy`), which builds the lazy functions again where TLC forces
    // the function itself later, so they force only those the arguments built, each held once,
    // and in the order the evaluator built them where TLC's print reaches them in that order
    // (`deepNormalize` sorts sets and keys by comparing them). `ToString` prints the value itself.
    fn force_lazy_prints(&mut self, force: Force<'_>) -> Evaluated<()> {
        let Some(first) = self.forcing.as_ref().map(|forcing| forcing.first) else {
            return Ok(());
        };
        let held = self.lazy_prints_from(first);
        if self.lazy_prints.is_empty() {
            return Ok(());
        }
        let now = self.lazy_effects();
        let forced: Vec<usize> = match force {
            Force::Built(arguments) => {
                let mut forced = Vec::new();
                let mut next = 0;
                for (index, lazy) in self.lazy_prints.iter().enumerate() {
                    let Some(position) = arguments.iter().position(|value| {
                        matches!(value, Value::Function(function) if Rc::ptr_eq(function, &lazy.function))
                    }) else {
                        continue;
                    };
                    // TLC forces the function its copy left unforced again.
                    if position < next || lazy.is_copied {
                        return fail(LAZY_BODY_EFFECTS);
                    }
                    next = position + 1;
                    forced.push(index);
                }
                forced
            }
            Force::Copied(value, returned, _) => {
                let mut reached = Vec::new();
                self.reach_lazy_prints(value, false, &mut reached);
                let mut held_returned = Vec::new();
                if let Some(returned) = returned {
                    self.reach_lazy_prints(returned, false, &mut held_returned);
                }
                // Each the arguments built, and any held before them whose copy no print built,
                // once, and in the order the evaluator built them where there are several.
                let mut forced: Vec<usize> = reached.iter().map(|&(index, _)| index).collect();
                forced.sort_unstable();
                if !held_returned.is_empty()
                    || forced.windows(2).any(|pair| pair[0] == pair[1])
                    || forced
                        .iter()
                        .any(|&index| self.lazy_prints[index].is_copied)
                    || (held..self.lazy_prints.len())
                        .any(|index| !forced.contains(&index) && !self.lazy_prints[index].is_copied)
                    || reached
                        .iter()
                        .enumerate()
                        .any(|(at, &(index, is_unordered))| {
                            reached.len() > 1 && (is_unordered || index != forced[at])
                        })
                {
                    return fail(LAZY_BODY_EFFECTS);
                }
                forced
            }
            // `toString` builds each lazy function once, where it first reaches it.
            Force::Shown(value) => {
                let mut reached = Vec::new();
                self.reach_lazy_prints(value, false, &mut reached);
                let mut first = Vec::new();
                for (index, is_unordered) in reached {
                    if !first.iter().any(|&(seen, _)| seen == index) {
                        first.push((index, is_unordered));
                    }
                }
                let built: Vec<usize> = (held..self.lazy_prints.len())
                    .filter(|&index| !self.lazy_prints[index].is_copied)
                    .collect();
                if first.len() != built.len()
                    || first
                        .iter()
                        .zip(&built)
                        .any(|(&(index, is_unordered), &own)| {
                            index != own || (built.len() > 1 && is_unordered)
                        })
                {
                    return fail(LAZY_BODY_EFFECTS);
                }
                built
            }
        };
        if forced.is_empty() {
            return Ok(());
        }
        // TLC holds one function for the uses of a LET the evaluator built it for: forcing it
        // (`toFcnRcd`) builds it once for them all, and a print of a copy of it once forced
        // builds it no more.
        let is_copy = matches!(force, Force::Copied(..));
        for &index in &forced {
            let Some(origin) = &self.lazy_prints[index].origin else {
                continue;
            };
            let is_shared = self.lazy_prints.iter().enumerate().any(|(other, lazy)| {
                other != index
                    && lazy
                        .origin
                        .as_ref()
                        .is_some_and(|own| Weak::ptr_eq(own, origin))
            });
            // A LET no longer held has no later use.
            let is_unforced = origin
                .upgrade()
                .is_none_or(|frame| frame.is_lazy_unforced.get());
            let is_named = matches!(force, Force::Copied(_, _, true));
            if (!is_copy && is_shared) || (is_copy && (!is_unforced || (is_shared && !is_named))) {
                return fail(LAZY_BODY_EFFECTS);
            }
        }
        let is_followed = forced.iter().enumerate().all(|(at, &index)| {
            self.lazy_prints[index].end
                == forced
                    .get(at + 1)
                    .map_or(now, |&following| self.lazy_prints[following].start)
        });
        if !is_followed {
            return fail(LAZY_BODY_EFFECTS);
        }
        if let Force::Copied(_, _, is_named) = force {
            // TLC prints copies, and still holds the functions unforced: those the arguments
            // built go with the operation, and those held before are copied. A LET's function
            // reached through anything but its name may have been forced on the way, by a
            // comparison that sorts a set (`compareTo`), so its later uses decline.
            for &index in forced.iter().rev() {
                // So may a thunk's function reached through anything but its name.
                if !is_named
                    && let Some((frame, _)) = &self.lazy_prints[index].thunk
                    && let Some(frame) = frame.upgrade()
                {
                    frame.is_thunk_unforced.set(false);
                }
                let origin = if index >= held {
                    self.lazy_prints.remove(index).origin.filter(|_| !is_named)
                } else {
                    self.lazy_prints[index].is_copied = true;
                    self.lazy_prints[index].origin.clone()
                };
                if let Some(frame) = origin.and_then(|origin| origin.upgrade()) {
                    frame.is_lazy_unforced.set(false);
                }
            }
            if let Some(forcing) = &mut self.forcing {
                forcing.printed_at = Some(now);
            }
        } else {
            // TLC forces its one function in place, unforced so far, which the evaluator built
            // again for this use: it prints the body's lines once, as the evaluator's build did,
            // where the evaluator holds no other build of it, which TLC doesn't print again; and
            // the thunk's later uses read it forced.
            let is_built_twice = |at: usize, lazy: &LazyPrint| {
                let Some((frame, is_rebuilt)) = &lazy.thunk else {
                    return false;
                };
                *is_rebuilt
                    && self.lazy_prints.iter().enumerate().any(|(other, held)| {
                        other != at
                            && held
                                .thunk
                                .as_ref()
                                .is_some_and(|(own, _)| Weak::ptr_eq(own, frame))
                    })
            };
            if forced
                .iter()
                .any(|&index| is_built_twice(index, &self.lazy_prints[index]))
            {
                return fail(LAZY_BODY_EFFECTS);
            }
            for &index in forced.iter().rev() {
                let lazy = self.lazy_prints.remove(index);
                if let Some((frame, _)) = &lazy.thunk
                    && let Some(frame) = frame.upgrade()
                {
                    frame.is_thunk_unforced.set(false);
                }
                if let Some(frame) = lazy.origin.and_then(|origin| origin.upgrade()) {
                    frame.is_lazy_unforced.set(false);
                }
            }
        }
        Ok(())
    }

    // Whether an expression is the name of a LET's function, an argument or a LET definition
    // that is one, or a tuple or record of such names and literals, under LETs: nothing but the
    // names reaches the functions TLC holds for them, to force them (`toFcnRcd`) on the way.
    // Whether an expression builds its value afresh at each evaluation: it names no local name
    // but its own binders, no variable, constant or definition, and no builtin but those that
    // read nothing (not TLCGet or TLCGetAndSet, a register).
    fn is_built_afresh(&self, node: NodeId, context: &Context) -> bool {
        let mut pending = vec![node];
        let mut seen = HashSet::new();
        while let Some(node) = pending.pop() {
            if !seen.insert(node) {
                continue;
            }
            let kind = self.kind(node);
            match kind {
                NodeKind::Identifier(name)
                | NodeKind::Apply { name, .. }
                | NodeKind::OperatorReference(name) => {
                    let is_fresh = if name.is_local {
                        lookup(&context.env, name.text).is_none()
                    } else {
                        match name.resolution {
                            Resolution::Builtin(index) => !matches!(
                                self.name(self.ir.builtins[index as usize].name),
                                "TLCGet" | "TLCGetAndSet"
                            ),
                            _ => false,
                        }
                    };
                    if !is_fresh {
                        return false;
                    }
                }
                NodeKind::Prime(_)
                | NodeKind::Unchanged(_)
                | NodeKind::Enabled(_)
                | NodeKind::Subexpression(_)
                | NodeKind::Reference(_) => return false,
                _ => {}
            }
            pending.extend(kind.children());
        }
        true
    }

    fn names_lazy_functions(
        &self,
        node: NodeId,
        context: &Context,
        functions: &mut Vec<TextId>,
        depth: u32,
    ) -> bool {
        if depth == 0 {
            return false;
        }
        let is_named = |evaluator: &Self, element: NodeId, functions: &mut Vec<TextId>| {
            matches!(
                evaluator.kind(element),
                NodeKind::Number(_) | NodeKind::String(_)
            ) || evaluator.names_lazy_functions(element, context, functions, depth - 1)
        };
        match self.kind(node) {
            NodeKind::Identifier(name) if name.is_local => {
                if functions.contains(&name.text) {
                    return true;
                }
                match lookup(&context.env, name.text)
                    .as_deref()
                    .map(|frame| &frame.binding)
                {
                    Some(Binding::Function { .. }) => true,
                    // A thunk of a function constructor holds the one function TLC's
                    // LazyValue keeps (`Frame::is_thunk_unforced`).
                    Some(Binding::Thunk { node, context, .. }) => {
                        matches!(self.kind(*node), NodeKind::FunctionConstruction { .. })
                            || self.names_lazy_functions(*node, context, &mut Vec::new(), depth - 1)
                    }
                    _ => false,
                }
            }
            NodeKind::Tuple(elements) => elements
                .iter()
                .all(|&element| is_named(self, element, functions)),
            NodeKind::Record(fields) => fields
                .iter()
                .all(|&(_, element)| is_named(self, element, functions)),
            // An IF or a CASE returns the value its arm evaluates, the one object a name there
            // reaches (`Tool.evalImpl`'s OPCODE_ite and OPCODE_case); its conditions force
            // what they force as operations of their own.
            NodeKind::If {
                consequent,
                alternative,
                ..
            } => [*consequent, *alternative]
                .iter()
                .all(|&arm| self.names_lazy_functions(arm, context, functions, depth - 1)),
            NodeKind::Case { arms, other } => arms
                .iter()
                .map(|&(_, body)| body)
                .chain(*other)
                .all(|arm| self.names_lazy_functions(arm, context, functions, depth - 1)),
            // A LET whose definitions are functions only.
            NodeKind::Let {
                instances: 0,
                definitions,
                body,
            } => {
                let held = functions.len();
                for &definition in definitions {
                    let definition = self.definition(definition);
                    if !matches!(definition.form, DefinitionForm::Function(_)) {
                        functions.truncate(held);
                        return false;
                    }
                    functions.push(definition.name);
                }
                let is_named = self.names_lazy_functions(*body, context, functions, depth - 1);
                functions.truncate(held);
                is_named
            }
            _ => false,
        }
    }

    // The lazy functions held so far that a value holds, in the order TLC's print reaches them,
    // and whether the print may reach them in another order: in a set, or a function's key,
    // which `deepNormalize` sorts by comparing them, or a function whose written order the
    // evaluator keeps. A lazy set holds none but a SUBSET's of its base.
    fn reach_lazy_prints(
        &self,
        value: &Value,
        is_unordered: bool,
        reached: &mut Vec<(usize, bool)>,
    ) {
        match value {
            Value::Function(function) => {
                if let Some(index) = self
                    .lazy_prints
                    .iter()
                    .position(|lazy| Rc::ptr_eq(&lazy.function, function))
                {
                    reached.push((index, is_unordered));
                    return;
                }
                for key in &function.domain {
                    self.reach_lazy_prints(key, true, reached);
                }
                let is_written = function.written.borrow().is_some();
                for value in &function.range {
                    self.reach_lazy_prints(value, is_unordered || is_written, reached);
                }
            }
            Value::Set(set) | Value::Unsorted(set) => {
                for element in set.iter() {
                    self.reach_lazy_prints(element, true, reached);
                }
            }
            Value::Lazy(lazy) => {
                if let Lazy::Subset(base) = &***lazy {
                    self.reach_lazy_prints(base, true, reached);
                }
            }
            _ => {}
        }
    }

    // A function's value at one key as the evaluator builds the function. TLC builds one it
    // `is_built` in `toFcnRcd` of the FcnLambdaValue that `CallStackTool` gives a source, which
    // throws a failure there on as a FingerprintException (`FingerprintException.getNewHead`).
    // TLC evaluates the body of any other where it applies or fingerprints the function, in
    // frames the replay doesn't record.
    // A function's value at a key, noting the key where a body TLC keeps lazy printed.
    fn keyed_function_body(
        &mut self,
        key: &Value,
        body: NodeId,
        context: &Context,
        is_built: bool,
    ) -> Evaluated<Value> {
        let effects = self.lazy_body_effects;
        let value = self.function_body(body, context, is_built)?;
        if self.lazy_body_effects != effects {
            self.lazy_print_keys.push(key.clone());
        }
        Ok(value)
    }

    fn function_body(
        &mut self,
        body: NodeId,
        context: &Context,
        is_built: bool,
    ) -> Evaluated<Value> {
        let effects = self.lazy_effects();
        let result = self.evaluate(body, context);
        if self.keeping_lazy != 0
            && self.printed[effects.0..]
                .iter()
                .any(|output| matches!(output, crate::OutputEvent::Warning(_)))
        {
            return fail("warning in a function body TLC keeps lazy until application");
        }
        let after = self.lazy_effects();
        if !is_built && effects != after {
            self.lazy_body_effects += 1;
            // TLC holds the function as a FcnLambdaValue (OPCODE_rfs always, OPCODE_fc under
            // `EvalControl.KeepLazy` or over a domain that isn't Reducible), whose body it
            // evaluates only as it uses the value: `apply` and `select` at one key each time,
            // `toFcnRcd` (`compareTo`, `equals`, `fingerPrint`, `toString`) once for the object
            // and cached in `fcnRcd`, and `getDomain` and `deepNormalize` not at all. The
            // evaluator builds the function here, as many times as it reads the definition, so
            // the body's effects come at other points, or more or fewer times, than TLC's. Such a
            // function waits (`construct_function`) for an operation that forces it, with
            // nothing else having effects in between (`force_lazy_prints`).
            if result.is_ok() {
                self.lazy_print_start.get_or_insert(effects);
            }
        }
        if result.is_err()
            && let Some(stack) = &mut self.call_stack
        {
            if !is_built {
                stack.unfollowed.get_or_insert(LAZY_BODY);
            } else if !stack.is_fingerprinted {
                stack.is_fingerprinted = true;
                stack.is_frozen_before_fingerprint = stack.is_frozen;
            }
        }
        // TLC evaluates the body of a function it keeps lazy only at the keys it applies it to
        // (`FcnLambdaValue.apply`), which may not include the one the evaluator failed at.
        if let Err(error) = &result
            && !is_built
        {
            self.is_lazy_body_failure_worded = error.message.is_some();
            return fail(LAZY_BODY_AT_KEY);
        }
        result
    }

    // Each binding of the bounds with the elements bound, the last bound varying fastest.
    fn for_each_keyed(
        &mut self,
        bounds: &[Bound],
        context: &Context,
        is_built: bool,
        preserves: bool,
        bound: &mut Vec<Value>,
        visit: &mut KeyedVisit<'_, 'ir>,
    ) -> Evaluated<()> {
        let Some((first, rest)) = bounds.split_first() else {
            return visit(self, context, bound);
        };
        let set = self.evaluate(first.set, context)?;
        let domain = if preserves {
            held_elements(&set)?
        } else {
            elements(&set)?
        };
        for element in domain.iter() {
            if is_built && let Err(error) = self.require_tuple_cast(&first.pattern, element) {
                if let Some(stack) = &mut self.call_stack
                    && !stack.is_fingerprinted
                {
                    stack.is_fingerprinted = true;
                    stack.is_frozen_before_fingerprint = stack.is_frozen;
                }
                return Err(error);
            }
            let inner = self.bind_pattern(&first.pattern, element, context)?;
            bound.push(element.clone());
            self.for_each_keyed(rest, &inner, is_built, preserves, bound, visit)?;
            bound.pop();
        }
        Ok(())
    }

    // `f[e]`, where TLC, as it starts, applies a constructor of one name written in place, which
    // it keeps lazy (`EvalControl.KeepLazy`), where the evaluator, building it, failed in its body
    // at another key: without effects, the evaluator follows `FcnLambdaValue.apply` instead.
    fn apply_function(
        &mut self,
        node: NodeId,
        function: NodeId,
        args: &[NodeId],
        context: &Context,
    ) -> Evaluated<Value> {
        let lazy = match self.kind(function) {
            NodeKind::FunctionConstruction {
                is_recursive: false,
                bounds,
                body,
            } if !bounds.is_empty()
                && bounds
                    .iter()
                    .all(|bound| matches!(bound.pattern, Pattern::Name(_))) =>
            {
                Some((bounds.clone(), *body, function, context.clone()))
            }
            // A LET's name for a constructor of one name, which TLC keeps lazy as it evaluates
            // the name (`LazyValue`), followed only where the evaluator fails to build it over a
            // set enumeration it can't sort.
            NodeKind::Identifier(name) if name.is_local && args.len() == 1 => {
                self.let_constructor(name.text, context)
            }
            _ => None,
        };
        let Some((bounds, body, constructor, own)) = lazy.filter(|(bounds, ..)| {
            self.is_starting
                && self.asserting == 0
                && !self.is_174()
                && (bounds.len() > 1 || args.len() == 1)
        }) else {
            return self.apply_function_built(node, function, args, context);
        };
        if self.may_reach(constructor, EFFECTS)
            || args.iter().any(|&arg| self.may_reach(arg, EFFECTS))
        {
            return self.apply_function_built(node, function, args, context);
        }
        let saved = (
            self.call_stack.clone(),
            self.lazy_unions,
            self.lazy_domains,
            self.lazy_body_effects,
        );
        let is_let = constructor != function;
        match self.apply_function_built(node, function, args, context) {
            Err(error)
                if error.reason == UNSORTED_LAZY_DOMAIN
                    || (!is_let
                        && (error.reason == LAZY_BODY_AT_KEY
                            || (bounds.len() > 1 && error.message.is_none()))) =>
            {
                (
                    self.call_stack,
                    self.lazy_unions,
                    self.lazy_domains,
                    self.lazy_body_effects,
                ) = saved;
                if let [bound] = &bounds[..] {
                    self.apply_kept_lazy(bound, body, &own, args[0], context)
                } else {
                    self.apply_kept_lazy_several(node, &bounds, body, args, context)
                }
            }
            result => result,
        }
    }

    // `FcnLambdaValue.apply` of a function of several parameters, each of its own bound, over set
    // enumerations or intervals TLC builds as it builds the function: the argument as a tuple
    // (`toTuple`), whose parts it tests in order against the domains, failing on a missing part
    // as Java's array does, then the body. Its message prints the function as `toString` does,
    // and its domain, the set of tuples of the domains.
    fn apply_kept_lazy_several(
        &mut self,
        node: NodeId,
        bounds: &[Bound],
        body: NodeId,
        args: &[NodeId],
        context: &Context,
    ) -> Evaluated<Value> {
        let mut domains = Vec::with_capacity(bounds.len());
        for bound in bounds {
            let set = self.evaluate(bound.set, context)?;
            if !matches!(set, Value::Set(_) | Value::Interval(..)) {
                return fail(LAZY_BODY_AT_KEY);
            }
            domains.push(set);
        }
        let argument = self.evaluate_arguments(node, args, context)?;
        if matches!(argument, Value::Lambda(_)) {
            return fail(LAZY_BODY_AT_KEY);
        }
        let parts = as_tuple(&argument).map(<[Value]>::to_vec);
        let missing = |evaluator: &mut Self, text: String| -> Evaluated<Value> {
            let function = evaluator.printed_lazy_function(bounds, body, &domains, context)?;
            fail_runtime(
                "applied a function outside its domain",
                format!("In applying the function\n{function},\n{text}"),
            )
        };
        let Some(parts) = parts else {
            // TLC prints the function and then the argument (`printed_argument`).
            let function = self.printed_lazy_function(bounds, body, &domains, context)?;
            return fail_runtime(
                "applied a function outside its domain",
                format!(
                    "In applying the function\n{function},\nthe argument list is:\n{}\nwhich does not match its formal parameter.\n",
                    printed_argument(&argument)?
                ),
            );
        };
        let mut inner = context.clone();
        for (index, (bound, domain)) in bounds.iter().zip(&domains).enumerate() {
            let Some(part) = parts.get(index) else {
                return fail_runtime(
                    "applied a function to too few arguments",
                    format!("Index {index} out of bounds for length {}", parts.len()),
                );
            };
            // `SetEnumValue.member` and `IntervalValue.member` fail as a membership does.
            let is_member = match self.member(part, domain) {
                Ok(is_member) => is_member,
                Err(error) if error.message.is_some() => return Err(error),
                Err(_) => return fail(LAZY_BODY_AT_KEY),
            };
            if !is_member {
                let domain = self.lazy_function_domain(&domains)?;
                return missing(
                    self,
                    format!(
                        "the argument number {} is:\n{}\nwhich is not in the function's domain {}.\n",
                        index + 1,
                        format_pretty(part),
                        format_value(&domain)
                    ),
                );
            }
            inner = self.bind_pattern(&bound.pattern, part, &inner)?;
        }
        self.evaluate(body, &inner)
    }

    // The set of tuples of the domains (`SetOfTuplesValue`, or the domain of the function
    // `toFcnRcd` built), which TLC prints normalized.
    fn lazy_function_domain(&self, domains: &[Value]) -> Evaluated<Value> {
        let mut tuples: Vec<Vec<Value>> = vec![Vec::new()];
        for domain in domains {
            let keys = elements(domain)?;
            if tuples.len().saturating_mul(keys.len()) > 1 << 16 {
                return fail(LAZY_BODY_AT_KEY);
            }
            tuples = tuples
                .into_iter()
                .flat_map(|tuple| {
                    keys.iter().map(move |key| {
                        let mut tuple = tuple.clone();
                        tuple.push(key.clone());
                        tuple
                    })
                })
                .collect();
        }
        set_of(tuples.into_iter().map(Value::tuple).collect())
    }

    // `FcnLambdaValue.toString` of a function of several parameters: built (`toFcnRcd`), the body
    // at each tuple of the domains, or, where a body fails, which `toString` swallows, as its
    // parameters, their domains and where its body is (`FcnParams.toString`).
    fn printed_lazy_function(
        &mut self,
        bounds: &[Bound],
        body: NodeId,
        domains: &[Value],
        context: &Context,
    ) -> Evaluated<String> {
        let Some(body_text) = self.describe_node(body) else {
            return fail(LAZY_BODY_AT_KEY);
        };
        let keys = self.lazy_function_domain(domains)?;
        let keys = elements(&keys)?.to_vec();
        let mut values = Vec::with_capacity(keys.len());
        for key in &keys {
            let Some(parts) = as_tuple(key) else {
                return fail(LAZY_BODY_AT_KEY);
            };
            let mut inner = context.clone();
            for (bound, part) in bounds.iter().zip(parts) {
                inner = self.bind_pattern(&bound.pattern, part, &inner)?;
            }
            match self.evaluate(body, &inner) {
                Ok(value) => values.push(value),
                Err(error) if error.message.is_some() => break,
                Err(error) => return Err(error),
            }
        }
        // A value whose text TLC writes otherwise than the evaluator, or fails to write, as a set
        // it can't normalize, which `toString` swallows into another text, declines.
        if values
            .iter()
            .any(|value| holds_unsorted(value) || !crate::value::is_text_known(value))
        {
            return fail(LAZY_BODY_AT_KEY);
        }
        let text = if values.len() == keys.len() {
            format_value(&sorted_function(keys, values, Class::Lambda)?)
        } else {
            // `x, y \in S` is one group of `FcnParams`, whose `toString` names its first only:
            // the bounds of a group share the set written once, at one place.
            let mut params = Vec::with_capacity(bounds.len());
            let mut group = None;
            for (bound, domain) in bounds.iter().zip(domains) {
                let Pattern::Name(name) = bound.pattern else {
                    return fail(LAZY_BODY_AT_KEY);
                };
                let Some(range) = self.ir.nodes.arena[bound.set as usize].range else {
                    return fail(LAZY_BODY_AT_KEY);
                };
                if group == Some(range) {
                    continue;
                }
                group = Some(range);
                params.push(format!("{} \\in {}", self.name(name), format_value(domain)));
            }
            format!("[{} |-> <expression {body_text}>]", params.join(", "))
        };
        Ok(pretty_print(&text.encode_utf16().collect::<Vec<_>>()))
    }

    // `FcnLambdaValue.apply` of a function of one parameter TLC built of a set enumeration or an
    // interval it holds: the body at a key in the domain, and otherwise TLC's message, which
    // prints the function as its `toString` does: built (`toFcnRcd`), or where a key's body fails
    // (which `toString` swallows), as its parameter, its domain and where its body is. As TLC
    // starts no value has a source, so the message has no location.
    fn apply_kept_lazy(
        &mut self,
        bound: &Bound,
        body: NodeId,
        own: &Context,
        arg: NodeId,
        context: &Context,
    ) -> Evaluated<Value> {
        let Pattern::Name(name) = bound.pattern else {
            return fail(LAZY_BODY_AT_KEY);
        };
        let set = self.evaluate(bound.set, own)?;
        let is_unsorted = matches!(set, Value::Unsorted(_));
        if !matches!(set, Value::Set(_) | Value::Interval(..)) && !is_unsorted {
            return fail(LAZY_BODY_AT_KEY);
        }
        let argument = self.evaluate(arg, context)?;
        // `SetEnumValue.member` of a set TLC holds unnormalized asks each element, as written,
        // whether it equals the argument, which fails as that equality does.
        let is_member = match self.member(&argument, &set) {
            Ok(is_member) => is_member,
            Err(error) if is_unsorted && error.message.is_some() => return Err(error),
            Err(_) => return fail(LAZY_BODY_AT_KEY),
        };
        if is_member {
            let inner = self.bind_pattern(&bound.pattern, &argument, own)?;
            return self.evaluate(body, &inner);
        }
        // The message's `FcnLambdaValue.toString` fails to normalize the domain, before it
        // evaluates the body anywhere (`SetEnumValue.Enumerator`), and again printing the
        // bound (`FcnParams.toString`).
        if let Value::Unsorted(elements) = &set {
            return match crate::value::normalize_unsorted_failure_twice(elements) {
                Some(error) => Err(error),
                None => fail(LAZY_BODY_AT_KEY),
            };
        }
        let Some(body_text) = self.describe_node(body) else {
            return fail(LAZY_BODY_AT_KEY);
        };
        let keys = elements(&set)?;
        let mut values = Vec::with_capacity(keys.len());
        for key in keys.iter() {
            let inner = self.bind_pattern(&bound.pattern, key, own)?;
            match self.evaluate(body, &inner) {
                Ok(value) => values.push(value),
                Err(error) if error.message.is_some() => break,
                Err(error) => return Err(error),
            }
        }
        let text = if values.len() == keys.len() {
            format_value(&sorted_function(keys.to_vec(), values, Class::Lambda)?)
        } else {
            format!(
                "[{} \\in {} |-> <expression {body_text}>]",
                self.name(name),
                format_value(&set)
            )
        };
        fail_runtime(
            "applied a function outside its domain",
            format!(
                "In applying the function\n{},\nthe first argument is:\n{}\nwhich is not in its domain.\n",
                pretty_print(&text.encode_utf16().collect::<Vec<_>>()),
                format_pretty(&argument)
            ),
        )
    }

    // `f[e]` of an argument or a LET definition that is a constructor of one name over a set
    // enumeration or an interval, whose body may have effects or whose domain TLC holds
    // unnormalized: TLC's `LazyValue` keeps the FcnLambdaValue `OPCODE_fc` makes with
    // `EvalControl.KeepLazy` (`LazyValue.getValue`), and `FcnLambdaValue.apply` evaluates the
    // body at each key it is applied to, asking the domain as TLC holds it whether it holds the
    // key, without enumerating it. The evaluator keeps it as a lambda, which no other use of the
    // name takes (`binding`).
    fn held_constructor(
        &mut self,
        function: NodeId,
        context: &Context,
    ) -> Evaluated<Option<Value>> {
        // TLC 1.7.4 keeps lazy values by other rules, which the evaluator follows as it did.
        if self.is_174() {
            return Ok(None);
        }
        if let Some(held) = self.held_in_place(function, context)? {
            return Ok(Some(held));
        }
        let mut node = function;
        let mut context = context.clone();
        // The value a thunk of the chain of arguments naming others keeps, which the evaluator
        // gives where it is used, nearest the application.
        let mut kept: Option<(Value, Rc<Frame>)> = None;
        let (frame, inner, bound, body) = loop {
            let NodeKind::Identifier(name) = self.kind(node) else {
                return Ok(None);
            };
            if !name.is_local {
                return Ok(None);
            }
            let Some(frame) = lookup(&context.env, name.text) else {
                return Ok(None);
            };
            let Binding::Thunk {
                node: bound_node,
                context: bound_context,
                is_self,
            } = &frame.binding
            else {
                return Ok(None);
            };
            let inner = own_context(bound_context, &frame, *is_self)
                .primed(context.is_primed || bound_context.is_primed);
            // Tool expands a LazyValue directly when its next state is null.
            if inner.is_primed {
                return Ok(None);
            }
            if kept.is_none() {
                kept = self
                    .peek_thunk(&frame)
                    .map(|(value, ..)| (value, Rc::clone(&frame)));
                // Whatever the argument is written as, one TLC keeps as a FcnLambdaValue.
                if kept
                    .as_ref()
                    .is_some_and(|(value, _)| is_held_constructor(value))
                {
                    return Ok(self.cached_thunk(&frame));
                }
            }
            match self.kind(*bound_node) {
                // An argument that names another passes on its `LazyValue`'s value.
                NodeKind::Identifier(_) => {
                    node = *bound_node;
                    context = inner;
                }
                NodeKind::FunctionConstruction {
                    is_recursive: false,
                    bounds,
                    body,
                } if matches!(&bounds[..], [bound] if matches!(bound.pattern, Pattern::Name(_)))
                    && kept.is_none() =>
                {
                    break (frame, inner, &bounds[0], *body);
                }
                // TLC applies the FcnLambdaValue it keeps again, evaluating the body at the key,
                // where the evaluator would read the function it built before.
                _ => {
                    if kept
                        .as_ref()
                        .is_some_and(|(value, _)| is_kept_lazy_build(value))
                        && self.has_effect(*bound_node, &inner)
                    {
                        // A constructor of one name over a domain TLC can't reduce, which it
                        // keeps a FcnLambdaValue even where a use built it before
                        // (`OPCODE_fc` keeps one over a set that isn't `Reducible`), whose
                        // domain has no effect: `FcnLambdaValue.apply` asks the domain for the
                        // key and evaluates the body at it again. The evaluator applies a lambda
                        // over the domain evaluated again, the same set, and leaves the
                        // function the thunk keeps as it is.
                        if let NodeKind::FunctionConstruction {
                            is_recursive: false,
                            bounds,
                            body,
                        } = self.kind(*bound_node)
                            && let [bound] = &bounds[..]
                            && let Pattern::Name(name) = bound.pattern
                            && !self.has_effect(bound.set, &inner)
                            && !self.may_prime(*body, &inner)
                        {
                            let (reads, captures) = (self.reads, self.captures);
                            let printed = self.printed.len();
                            let set = self.evaluate(bound.set, &inner)?;
                            if self.printed.len() == printed
                                && matches!(&set, Value::Lazy(lazy) if !lazy.is_overridden())
                                && !matches!(
                                    java_set_class(&set),
                                    Some(SetClass::Enumeration | SetClass::Interval)
                                )
                            {
                                self.captures += 1;
                                return Ok(Some(
                                    self.held_lambda(name, set, *body, &inner, false)?,
                                ));
                            }
                            self.reads = reads;
                            self.captures = captures;
                        }
                        return fail(
                            "a function TLC keeps lazy in an argument, with effects, applied again",
                        );
                    }
                    return Ok(None);
                }
            }
        };
        let Pattern::Name(name) = bound.pattern else {
            return Ok(None);
        };
        let is_effected = self.has_effect(body, &inner);
        if let Some((cached, _)) = kept {
            // A function the evaluator built where TLC keeps it lazy, whose body TLC evaluates
            // again as it applies it.
            if is_effected && is_kept_lazy_build(&cached) {
                return fail(
                    "a function TLC keeps lazy in an argument, with effects, applied again",
                );
            }
            return Ok(None);
        }
        if self.has_effect(bound.set, &inner) {
            return Ok(None);
        }
        let (reads, captures) = (self.reads, self.captures);
        let printed = self.printed.len();
        let set = self.evaluate(bound.set, &inner)?;
        // A set enumeration TLC can't normalize, which it searches for the key as it built it.
        let is_held = match &set {
            Value::Set(_) => is_effected || unnormalized(&set).is_some(),
            Value::Interval(..) => is_effected,
            Value::Unsorted(_) => true,
            _ => false,
        };
        if !is_held {
            // The evaluator evaluates the argument as it does any other, which evaluates the
            // domain again: without effects, the same set.
            if self.printed.len() != printed {
                return fail("the domain of a constructor in an argument, printed");
            }
            self.reads = reads;
            self.captures = captures;
            return Ok(None);
        }
        self.captures += 1;
        let lambda = self.held_lambda(name, set, body, &inner, false)?;
        self.cache_thunk(&frame, &lambda, reads, captures);
        frame.is_evaluated.set(true);
        Ok(Some(lambda))
    }

    // A constructor of one name over a set enumeration or an interval, written in place where TLC
    // keeps it lazy, with effects in its body: the FcnLambdaValue `OPCODE_fc` makes under
    // `EvalControl.KeepLazy`, which TLC applies, or updates by EXCEPT, without building it.
    fn held_in_place(&mut self, function: NodeId, context: &Context) -> Evaluated<Option<Value>> {
        if self.is_174() {
            return Ok(None);
        }
        let NodeKind::FunctionConstruction {
            is_recursive: false,
            bounds,
            body,
        } = self.kind(function)
        else {
            return Ok(None);
        };
        let [bound] = &bounds[..] else {
            return Ok(None);
        };
        let Pattern::Name(name) = bound.pattern else {
            return Ok(None);
        };
        if !self.has_effect(*body, context) || self.has_effect(bound.set, context) {
            return Ok(None);
        }
        let (reads, captures) = (self.reads, self.captures);
        // TLC evaluates the domain within the constructor (OPCODE_fc), whose frame
        // `CallStackTool` holds where the domain fails.
        let bound_set = bound.set;
        let set = self.in_frame(StackFrame::Node(function), &mut |evaluator| {
            evaluator.evaluate(bound_set, context)
        })?;
        if !matches!(set, Value::Set(_) | Value::Interval(..)) {
            self.reads = reads;
            self.captures = captures;
            return Ok(None);
        }
        self.captures += 1;
        Ok(Some(self.held_lambda(name, set, *body, context, false)?))
    }

    // Whether evaluating an expression again may show: one of `EFFECTS`, itself or through a
    // definition, an operator argument or a LET definition it names, as `context` binds them, but
    // one TLC evaluates once, a constant definition without parameters. A builtin passed as an
    // operator argument may be one.
    fn has_effect(&self, node: NodeId, context: &Context) -> bool {
        self.may_reach_in(node, context, &|kind, ir| {
            matches!(kind, NodeKind::Identifier(name) | NodeKind::Apply { name, .. }
                if !name.is_local
                    && matches!(name.resolution, Resolution::Builtin(index)
                        if EFFECTS.contains(&&*ir.texts[ir.builtins[index as usize].name as usize])))
        })
    }

    // Whether an expression may be of action level: a prime, UNCHANGED or ENABLED in it, as
    // `has_effect` walks it. TLC evaluates such a body as an action where an action applies the
    // function (`getNextStates`' OPCODE_fa), which the replay of its value doesn't follow.
    fn may_prime(&self, node: NodeId, context: &Context) -> bool {
        self.may_reach_in(node, context, &|kind, _| {
            matches!(
                kind,
                NodeKind::Prime(_) | NodeKind::Unchanged(_) | NodeKind::Enabled(_)
            )
        })
    }

    // Whether an expression, or a definition, an operator argument or a LET definition it names,
    // as `context` binds them, holds a node `is_met` takes, but in a constant definition without
    // parameters TLC evaluates once. A builtin passed as an operator argument may be any.
    fn may_reach_in(
        &self,
        node: NodeId,
        context: &Context,
        is_met: &dyn Fn(&NodeKind, &Ir) -> bool,
    ) -> bool {
        let mut seen = HashSet::new();
        let mut pending = vec![(node, context.clone())];
        while let Some((node, context)) = pending.pop() {
            let scope = context
                .env
                .0
                .as_ref()
                .map_or(0, |frame| Rc::as_ptr(frame) as usize);
            if !seen.insert((node, scope)) {
                continue;
            }
            let kind = &self.ir.nodes.arena[node as usize].kind;
            if is_met(kind, self.ir) {
                return true;
            }
            if let NodeKind::Reference(target) = kind {
                pending.push((*target, context));
                continue;
            }
            if let NodeKind::Identifier(name) | NodeKind::Apply { name, .. } = kind
                && name.is_local
                && let Some(frame) = lookup(&context.env, name.text)
            {
                if let Binding::Operator(operator) = &frame.binding
                    && matches!(operator.body, Body::Builtin(_))
                {
                    return true;
                }
                if let Some(bound) = bound_expression(&context, name.text) {
                    pending.push(bound);
                }
            }
            if let NodeKind::Identifier(name) | NodeKind::Apply { name, .. } = kind
                && !name.is_local
            {
                match name.resolution {
                    Resolution::Builtin(_) => {}
                    Resolution::Definition(index) => {
                        let definition = self.ir.definitions[index as usize];
                        let is_evaluated_once = matches!(&self.definition(definition).form,
                            DefinitionForm::Operator(params) if params.is_empty())
                            && !self
                                .can_read(self.definition(definition).body, &Context::default());
                        if !is_evaluated_once {
                            pending.push((definition, Context::default()));
                        }
                    }
                    _ => {}
                }
            }
            pending.extend(
                kind.children()
                    .into_iter()
                    .map(|child| (child, context.clone())),
            );
        }
        false
    }

    // The lambda `held_constructor` keeps of a constructor of one name over a set it evaluated.
    fn held_lambda(
        &self,
        name: TextId,
        set: Value,
        body: NodeId,
        context: &Context,
        is_in_place: bool,
    ) -> Evaluated<Value> {
        let text = (
            format!("[{} \\in ", self.name(name)),
            format!(" |-> <expression {}>]", self.expression_text(body)?),
        );
        Ok(Value::Lambda(Rc::new(Lambda {
            name,
            domain: set,
            body,
            context: context.clone(),
            current: self.current.clone(),
            next: self.next.clone(),
            level: self.level,
            excepts: Vec::new(),
            text,
            params: None,
            is_in_place,
        })))
    }

    // An application, which forces nothing of the function it applies (`FcnLambdaValue.apply`
    // evaluates its body at the argument), but where TLC's body at the argument prints what the
    // evaluator's did as it built the function (`apply_lazy_prints`).
    fn apply_function_built(
        &mut self,
        node: NodeId,
        function: NodeId,
        args: &[NodeId],
        context: &Context,
    ) -> Evaluated<Value> {
        let outer = self.forcing.replace(Forcing {
            first: self.lazy_print_count,
            printed_at: None,
        });
        let result = self.apply_function_value(node, function, args, context);
        let forcing = std::mem::replace(&mut self.forcing, outer).expect("the application");
        let held = self.lazy_prints_from(forcing.first);
        if self.lazy_prints.len() > held {
            self.lazy_prints.truncate(held);
            return fail(LAZY_BODY_EFFECTS);
        }
        result
    }

    // An application of a lazy function the evaluator built for it, whose body printed at the
    // argument only, with nothing between the build and the application having effects: TLC
    // evaluates that body as it applies it, after evaluating the argument (`evalAppl`), and keeps
    // nothing of it.
    fn apply_lazy_prints(&mut self, function: &Value, argument: &Value) -> Evaluated<()> {
        let Some(first) = self.forcing.as_ref().map(|forcing| forcing.first) else {
            return Ok(());
        };
        let held = self.lazy_prints_from(first);
        let [lazy] = &self.lazy_prints[held..] else {
            return Ok(());
        };
        let is_applied = matches!(function, Value::Function(inner) if Rc::ptr_eq(inner, &lazy.function))
            && !lazy.is_copied
            && lazy.origin.is_none()
            && lazy.end == self.lazy_effects()
            && matches!(&lazy.keys[..], [key] if equals(key, argument)?);
        if is_applied {
            self.lazy_prints.truncate(held);
        }
        Ok(())
    }

    // The argument of a function application: its one argument, or the tuple of several, which
    // TLC evaluates in a frame of its own (`OPCODE_fa` evaluates `args[1]`, SANY's `$Tuple`).
    fn evaluate_arguments(
        &mut self,
        application: NodeId,
        args: &[NodeId],
        context: &Context,
    ) -> Evaluated<Value> {
        if let [arg] = args {
            return self.evaluate(*arg, context);
        }
        self.in_frame(StackFrame::Arguments(application), &mut |evaluator| {
            Ok(Value::tuple(
                args.iter()
                    .map(|&arg| evaluator.evaluate(arg, context))
                    .collect::<Evaluated<_>>()?,
            ))
        })
    }

    fn apply_function_value(
        &mut self,
        node: NodeId,
        function: NodeId,
        args: &[NodeId],
        context: &Context,
    ) -> Evaluated<Value> {
        let argument = |evaluator: &mut Self| evaluator.evaluate_arguments(node, args, context);
        // A function TLC keeps lazy, a definition's or a LET's, is applied without being built.
        // A LET's LazyValue keeps the function its first use computed, with the domain evaluated
        // then: where the evaluator built it before, TLC holds it built (`toFcnRcd`), and
        // `FcnRcdValue.apply` evaluates neither its domain nor its body again, and where TLC kept
        // it lazy, `FcnLambdaValue.apply` evaluates the body only. The prints, TLCSet writes and
        // random draws of what the evaluator evaluates again here aren't TLC's.
        // A lazy function TLC hasn't forced it applies at the key as the evaluator does.
        let (was_evaluated, is_built) = match self.kind(function) {
            NodeKind::Identifier(name) if name.is_local => {
                lookup(&context.env, name.text).map_or((false, false), |frame| {
                    (
                        frame.is_evaluated.get(),
                        frame.is_built.get() && !frame.is_lazy_unforced.get(),
                    )
                })
            }
            _ => (false, false),
        };
        if let NodeKind::Identifier(name) = self.kind(function)
            && let Some((bounds, body, inner)) = self.lazy_function(name, context)?
            && let [bound] = bounds
        {
            let is_recursive = self.is_recursive_function(name, context);
            let effects = |evaluator: &Self| {
                (
                    evaluator.printed.len(),
                    evaluator.register_writes,
                    evaluator.random.as_ref().map(|random| random.state()),
                )
            };
            let before_set = effects(self);
            let set = self.evaluate(bound.set, &inner);
            if (was_evaluated || is_built) && before_set != effects(self) {
                return fail(BUILT_LET_FUNCTION_EFFECTS);
            }
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
            let before_body = effects(self);
            let value = self.nesting(is_recursive, |evaluator| {
                evaluator.evaluate(body, &bound_context)
            })?;
            if is_built && before_body != effects(self) {
                return fail(BUILT_LET_FUNCTION_EFFECTS);
            }
            return Ok(value);
        }
        // `evalAppl` checks that it applies a function before it evaluates the argument.
        let function_node = function;
        // `getInitStates` evaluates the function of the application it walks with
        // `EvalControl.Init`, which builds a function constructor in it.
        let is_init_walked = matches!(
            self.walked_application,
            Some((walked, true)) if walked == self.resolved(node)
        );
        let keeps_lazy = u32::from(!is_init_walked);
        let effects = |evaluator: &Self| {
            (
                evaluator.printed.len(),
                evaluator.register_writes,
                evaluator.random.as_ref().map(|random| random.state()),
            )
        };
        let before_function = effects(self);
        self.keeping_lazy += keeps_lazy;
        let held = if keeps_lazy == 1 {
            self.held_constructor(function, context)
        } else {
            Ok(None)
        };
        // A constructor of one name written in place is a FcnLambdaValue TLC applies and drops,
        // never enumerating its domain, which the evaluator then leaves as TLC holds it.
        self.preserves_lazy_domain = keeps_lazy == 1
            && !self.is_174()
            && matches!(&held, Ok(None))
            && matches!(self.kind(function), NodeKind::FunctionConstruction {
                is_recursive: false,
                bounds,
                ..
            } if bounds.iter().all(|bound| matches!(bound.pattern, Pattern::Name(_))));
        let mut in_place = Vec::new();
        if keeps_lazy == 1 {
            let mut applied = self.resolved(function);
            loop {
                in_place.push(applied);
                match self.kind(applied) {
                    NodeKind::Except { function, .. } => applied = self.resolved(*function),
                    _ => break,
                }
            }
        }
        let outer = std::mem::replace(&mut self.in_place_functions, in_place);
        let function = match held {
            Ok(Some(held)) => Ok(held),
            Ok(None) => self.evaluate(function, context),
            Err(error) => Err(error),
        };
        self.in_place_functions = outer;
        self.preserves_lazy_domain = false;
        self.keeping_lazy -= keeps_lazy;
        let function = function?;
        let after_function = effects(self);
        if let Some(kind) = non_function_kind(&function).or_else(|| {
            java_set_class(&function).map(|class| match class {
                SetClass::Enumeration => "a set of the form {e1, ... ,eN}",
                SetClass::Interval => "a set of the form i..j",
                SetClass::Overridden => "a special set constant",
                SetClass::Subset => "a set of the form SUBSET S",
                SetClass::Functions => "a set of the form [S -> T]",
                SetClass::Records => "a set of the form [d1 : S1, ... , dN : SN]",
                SetClass::Product => "a cartesian product",
                SetClass::Intersection => "a set of the form S \\cap T",
                SetClass::Cup => "a set of the form S \\cup T",
                SetClass::Difference => "a set of the form S \\ T",
                SetClass::Union => "a set of the form UNION  S",
                SetClass::Predicate => "a set of the form {x \\in S : expr}",
            })
        }) {
            let computing = match self.walked_application {
                Some((walked, is_init)) if walked == self.resolved(node) => {
                    format!("In computing {}, a", self.computing(is_init))
                }
                _ => "A".to_string(),
            };
            return fail_runtime(
                "applied a non-function",
                format!(
                    "{computing} non-function ({kind}) was applied as a function.\n{}",
                    self.describe_range(node)
                ),
            );
        }
        // TLC names the set by the class it built it as, which the evaluator doesn't keep.
        if matches!(
            function,
            Value::Set(_) | Value::Interval(..) | Value::Unsorted(_)
        ) {
            return fail(format!(
                "applied a non-function: {}",
                format_value(&function)
            ));
        }
        let argument = argument(self)?;
        self.apply_lazy_prints(&function, &argument)?;
        if let Value::Lambda(lambda) = &function {
            // `FcnLambdaValue.apply` words a key outside a domain of Nat or Int with the function
            // as its `toString` prints it, where `toFcnRcd` can't count the domain: its parameter,
            // its domain and where its body is. `CallStackTool` evaluates the function to a copy
            // without a source, which leaves where it was built out.
            if matches!(&lambda.domain, Value::Lazy(lazy) if matches!(***lazy, Lazy::Nat | Lazy::Int))
                && lambda.params.is_none()
                && !self.is_174()
            {
                let mut is_excepted = false;
                for (excepted, _) in &lambda.excepts {
                    if equals(excepted, &argument)? {
                        is_excepted = true;
                        break;
                    }
                }
                if !is_excepted && !self.member(&argument, &lambda.domain)? {
                    return fail_runtime(
                        "applied a function outside its domain",
                        format!(
                            "In applying the function\n{},\nthe first argument is:\n{}\nwhich is not in its domain.\n",
                            format_pretty(&function),
                            format_pretty(&argument)
                        ),
                    );
                }
            }
            let result = self.apply_lambda(lambda, &argument);
            // TLC evaluates the body of the FcnLambdaValue it keeps in frames the replay
            // doesn't record.
            if let Err(error) = &result
                && error.reason != "applied a function outside its domain"
                && is_held_constructor(&function)
                && !lambda.is_in_place
                && let Some(stack) = &mut self.call_stack
            {
                stack.unfollowed.get_or_insert(LAZY_BODY);
            }
            // `FcnLambdaValue.apply` words a key outside the domain of a constructor written in
            // place, or one a name binds, with the function as its `toString` prints it, built
            // (`toFcnRcd`), which evaluates the body at each key then, after the argument.
            if let Err(error) = &result
                && error.message.is_none()
                && error.reason == "applied a function outside its domain"
                && is_held_constructor(&function)
                && matches!(
                    self.kind(function_node),
                    NodeKind::FunctionConstruction { .. } | NodeKind::Identifier(_)
                )
                && !self.is_174()
            {
                // Over a set enumeration TLC can't normalize, which it holds as written, the
                // message's `toString` builds the function (`toFcnRcd`), whose `FcnParams.size`
                // fails normalizing the domain before it evaluates the body at any key, which it
                // swallows, and prints the domain unbuilt, normalizing it again
                // (`normalize_unsorted_failure_twice`), which an assumption reports without
                // frames.
                if self.is_assumption
                    && lambda.excepts.is_empty()
                    && lambda.params.is_none()
                    && let Value::Unsorted(items) = &lambda.domain
                {
                    return match crate::value::normalize_unsorted_failure_twice(items) {
                        Some(failure) if failure.message.is_some() => Err(failure),
                        _ => result,
                    };
                }
                self.keeping_lazy += 1;
                let built = self.evaluate(function_node, context);
                self.keeping_lazy -= 1;
                let built = built?;
                // A constructor written in place whose build fails in its body
                // (`construct_in_place`): `toString` swallows that failure and prints the function
                // unbuilt. `CallStackTool` freezes its stack where the body failed, which the
                // replay doesn't follow; `Tool`, evaluating an assumption, reports none.
                if let Value::Lambda(_) = &built
                    && matches!(
                        self.kind(function_node),
                        NodeKind::FunctionConstruction { .. }
                    )
                    && let Some(stack) = &mut self.call_stack
                {
                    if !stack.is_unsourced {
                        stack.unfollowed.get_or_insert(LAZY_BODY);
                        return result;
                    }
                    return fail_runtime(
                        "applied a function outside its domain",
                        format!(
                            "In applying the function\n{},\nthe first argument is:\n{}\nwhich is not in its domain.\n",
                            format_pretty(&built),
                            format_pretty(&argument)
                        ),
                    );
                }
                if !matches!(built, Value::Function(_)) {
                    return result;
                }
                // The message's `toString` builds the function (`toFcnRcd`), which forces its
                // body's prints there.
                self.force_lazy_prints(Force::Built(&[&built]))?;
                return fail_runtime(
                    "applied a function outside its domain",
                    format!(
                        "In applying the function\n{},\nthe first argument is:\n{}\nwhich is not in its domain.\n",
                        format_pretty(&built),
                        format_pretty(&argument)
                    ),
                );
            }
            // `FcnLambdaValue.apply` words a key outside the domain with the function as its
            // `toString` prints it, which fails to build one over Nat, Int or STRING
            // (`FcnParams.size`) and prints its parameter, its domain and where its body is,
            // without evaluating the body. Of the domains the membership above doesn't decide
            // (STRING, a function with EXCEPTs or parameters), the evaluator words it only where
            // AssertError compares it or TLC's own tool reports it as it starts.
            return match result {
                Err(error)
                    if error.message.is_none()
                        && error.reason == "applied a function outside its domain"
                        && lambda.excepts.is_empty()
                        && matches!(&lambda.domain, Value::Lazy(lazy)
                            if matches!(***lazy, Lazy::Nat | Lazy::Int | Lazy::Strings))
                        && (self.asserting > 0 || self.is_starting)
                        && !self.is_174() =>
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
                result => result,
            };
        }
        // `FcnLambdaValue.apply` of a function of several arguments TLC keeps lazy, built here,
        // takes the argument as a tuple (`toTuple`), which a value that is no function isn't:
        // TLC fails, wording the function as the FcnRcdValue it builds of it prints, which
        // evaluates its body, and then the argument. The function of one key prints alike in
        // whatever order TLC holds its keys, and a body with effects would have them in another
        // order. TLC reports the failure where the function was built, which the call stack
        // doesn't place.
        if let (
            Value::Function(inner),
            NodeKind::FunctionConstruction {
                is_recursive: false,
                bounds,
                ..
            },
        ) = (&function, self.kind(function_node))
            && bounds.len() >= 2
            && bounds
                .iter()
                .all(|bound| matches!(bound.pattern, Pattern::Name(_)))
            && inner.class.get() == Class::Lambda
            && inner.domain.len() <= 1
            && self.lazy_body_effects == 0
            && !self.is_174()
            && matches!(
                argument,
                Value::Int(_)
                    | Value::Bool(_)
                    | Value::Str(_)
                    | Value::Set(_)
                    | Value::Interval(..)
                    | Value::Lazy(_)
            )
            && inner
                .domain
                .iter()
                .chain(&inner.range)
                .all(crate::value::is_text_known)
            && crate::value::is_text_known(&argument)
        {
            if let Some(stack) = &mut self.call_stack {
                stack.unfollowed.get_or_insert(LAZY_ARGUMENT_LIST);
            }
            return fail_runtime(
                "applied a function of several arguments to a value that isn't a tuple",
                format!(
                    "In applying the function\n{},\nthe argument list is:\n{}\nwhich does not match its formal parameter.\n",
                    format_pretty(&function),
                    format_pretty(&argument)
                ),
            );
        }
        // `FcnLambdaValue.apply` of a function TLC keeps lazy, built here and so not yet built
        // into a FcnRcdValue nor excepted, asks the set enumeration of its one bound whether it
        // holds the argument: element by element, as written, where TLC holds the set so
        // (`SetEnumValue.member`), each asked whether it equals the argument.
        let held_domain = match (&function, self.kind(function_node)) {
            (
                Value::Function(inner),
                NodeKind::FunctionConstruction {
                    is_recursive: false,
                    ..
                },
            ) => self
                .held_lazy_domains
                .get(&(Rc::as_ptr(inner) as usize))
                .filter(|(held, _)| held.strong_count() > 0)
                .and_then(|(_, set)| set.clone()),
            _ => None,
        };
        let is_held_member = |held: &[Value]| -> Evaluated<bool> {
            for element in held {
                if equals(element, &argument)? {
                    return Ok(true);
                }
            }
            Ok(false)
        };
        self.lazy_domain_failure(&function, function_node, &argument)?;
        let result = match held_domain.map(|held| is_held_member(&held)) {
            Some(Ok(false)) => fail("applied a function outside its domain"),
            // The set's `member` throws a failure on as a FingerprintException where the set has
            // a source, whose frames the replay doesn't follow.
            Some(Err(error)) => {
                if let Some(stack) = &mut self.call_stack {
                    stack.unfollowed.get_or_insert(LAZY_DOMAIN_MEMBER);
                }
                Err(error)
            }
            _ => self.apply_checked(&function, &argument),
        };
        // TLC evaluates the function it applies keeping a constructor lazy
        // (`EvalControl.KeepLazy`), and `FcnLambdaValue.apply` words a key outside the domain
        // with the function as its `FcnRcdValue` prints. It reports the failure without where the
        // function was built: `CallStackTool` evaluates the function to a copy without a source.
        // TLC evaluates the body as it prints the function (`toFcnRcd`), after the argument,
        // where the evaluator built it before: the same where either had no effect.
        match (&result, &function) {
            (Err(error), Value::Function(inner))
                if error.message.is_none()
                    && error.reason == "applied a function outside its domain"
                    && inner.class.get() == Class::Lambda
                    && (before_function == after_function || after_function == effects(self))
                    && !self.is_174()
                    && (self.is_kept_lazy(function_node, context)
                        || self.is_kept_lazy_except(function_node, inner, &argument)) =>
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

    // The constructor of one name a LET's name binds, with its bounds, its body and the context
    // the name's binding evaluates it in. Over a set enumeration TLC can't sort, the evaluator
    // never builds it, so never holds it built where TLC holds it lazy (`LazyValue`).
    fn let_constructor(
        &mut self,
        name: TextId,
        context: &Context,
    ) -> Option<(Vec<Bound>, NodeId, NodeId, Context)> {
        let frame = lookup(&context.env, name)?;
        let Binding::Thunk {
            node,
            context: bound,
            is_self,
        } = &frame.binding
        else {
            return None;
        };
        let constructor = self.resolved(*node);
        let NodeKind::FunctionConstruction {
            is_recursive: false,
            bounds,
            body,
        } = self.kind(constructor)
        else {
            return None;
        };
        let (bounds, body) = (bounds.clone(), *body);
        if !matches!(&bounds[..], [bound] if matches!(bound.pattern, Pattern::Name(_))) {
            return None;
        }
        let own = own_context(bound, &frame, *is_self).primed(context.is_primed || bound.is_primed);
        Some((bounds, body, constructor, own))
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

    // Whether the function `f[e]` applies is an EXCEPT, written in place, of a constructor of one
    // name written in place, over an interval, applied at an integer: TLC evaluates both under
    // the application's KeepLazy, so the EXCEPT is a FcnLambdaValue's (`takeExcept` keeps it,
    // over keys of the interval alone, as OPCODE_exc warns of any other), and `apply` compares
    // the integer with those keys, then finds it outside the interval.
    fn is_kept_lazy_except(&self, function: NodeId, built: &Function, argument: &Value) -> bool {
        if !matches!(self.kind(function), NodeKind::Except { .. })
            || built.interval.is_none()
            || !matches!(argument, Value::Int(_))
        {
            return false;
        }
        let mut node = function;
        while let NodeKind::Except { function, .. } = self.kind(node) {
            node = self.resolved(*function);
        }
        matches!(
            self.kind(node),
            NodeKind::FunctionConstruction { is_recursive: false, bounds, .. }
                if matches!(&bounds[..], [bound] if matches!(bound.pattern, Pattern::Name(_)))
        )
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

    // Whether a lazy function's domain is a value that isn't a set and that TLC's replay with the
    // call stack gave a source (`CallStackTool.setSource`), so that a failing test of it is a
    // FingerprintException. Outside that replay TLC gives no value a source.
    fn is_sourced_non_set_domain(&self, domain: &Value) -> bool {
        !domain.is_set()
            && !matches!(domain, Value::Unsorted(_))
            && self
                .call_stack
                .as_ref()
                .is_some_and(|stack| !stack.is_unsourced && stack.source(domain).is_some())
    }

    // Whether a lazy function's domain is one TLC built from an expression, whose failing
    // membership test TLC reports as a value it can't fingerprint (`FingerprintException.getNewHead`)
    // where its replay with the call stack gave it a source, as `apply_lambda` explains.
    fn is_sourced_lazy_domain(&self, domain: &Value) -> bool {
        !self.is_assumption
            && self
                .call_stack
                .as_ref()
                .is_some_and(|stack| !stack.is_unsourced)
            && match domain {
                Value::Lazy(lazy) => !matches!(
                    ***lazy,
                    Lazy::Nat | Lazy::Int | Lazy::Real | Lazy::Strings | Lazy::Seq(_)
                ),
                Value::Set(_) | Value::Unsorted(_) => true,
                _ => false,
            }
    }

    // `exArg.equals(arg)` of `FcnLambdaValue.apply` and `select`, over the keys of its EXCEPTs:
    // a failing comparison whose receiver, the EXCEPT's key, is a tuple, a record, a function or
    // a set, which TLC's replay gives a source where it builds it, the tuple of a key of several
    // arguments too, is a FingerprintException with that value's frames
    // (`FingerprintException.getNewHead`), which the replay doesn't word. A string's or an
    // integer's failure has none.
    fn excepted_equals(&self, excepted: &Value, key: &Value) -> Evaluated<bool> {
        let result = equals(excepted, key);
        if result.is_err()
            && !self.is_assumption
            && (address(excepted).is_some() || matches!(excepted, Value::Lambda(_)))
            && self
                .call_stack
                .as_ref()
                .is_some_and(|stack| !stack.is_unsourced)
        {
            return fail("a failing comparison of a lazy function's EXCEPT key that has a source");
        }
        result
    }

    // `FcnLambdaValue.apply`: the value of the last EXCEPT at the key, or else the body on a key
    // in the domain, in the states the function was built in.
    pub(crate) fn apply_lambda(&mut self, lambda: &Lambda, key: &Value) -> Evaluated<Value> {
        for (except, value) in lambda.excepts.iter().rev() {
            if self.excepted_equals(except, key)? {
                return Ok(value.clone());
            }
        }
        if let Some(groups) = &lambda.params {
            return self.apply_several(lambda, groups, key);
        }
        let is_member = self.member(key, &lambda.domain);
        if is_member.is_err() && self.is_sourced_lazy_domain(&lambda.domain) {
            return fail("a failing test of a lazy function's domain TLC built from an expression");
        }
        // A domain TLC built of other sets, such as `Nat \ {0}` or `Nat \X Nat`, keeps its source,
        // and TLC reports a test of it that fails as a value it can't fingerprint
        // (`FingerprintException.getNewHead`), which the replay doesn't word. Nat, Int, STRING and
        // Seq(S) report the failure itself, as any does where no value has a source: without
        // `CallStackTool`, as TLC starts and in an assumption.
        // A set enumeration the replay built has a source too (`SetEnumValue.member`), as the
        // domain of a constructor TLC keeps lazy where it is applied (`held_constructor`). An
        // interval, which `..`'s Java method builds, has none.
        if is_member.is_err()
            && !self.is_assumption
            && self
                .call_stack
                .as_ref()
                .is_some_and(|stack| !stack.is_unsourced)
            && match &lambda.domain {
                Value::Lazy(lazy) => !matches!(
                    ***lazy,
                    Lazy::Nat | Lazy::Int | Lazy::Real | Lazy::Strings | Lazy::Seq(_)
                ),
                Value::Set(_) | Value::Unsorted(_) => true,
                _ => false,
            }
        {
            return fail("a failing test of a lazy function's domain TLC built from an expression");
        }
        // So does a domain that isn't a set, which TLC keeps as the value it evaluated, such as a
        // tuple or a record its replay gave a source (`TupleValue.member` throws
        // `FingerprintException.getNewHead` where `hasSource`). One TLC built without a source,
        // as Tail, Append, `\o` or an EXCEPT builds it, fails with the test's own message.
        if is_member.is_err() && self.is_sourced_non_set_domain(&lambda.domain) {
            return fail("a failing test of a lazy function's domain that isn't a set");
        }
        if !is_member? {
            return fail("applied a function outside its domain");
        }
        self.apply_lambda_body(lambda, key)
    }

    /// `FcnLambdaValue`'s evaluation of its body at a key its domain holds, which `select` and
    /// `apply` make once they tested the key's membership.
    fn apply_lambda_body(&mut self, lambda: &Lambda, key: &Value) -> Evaluated<Value> {
        let context = lambda.context.bind_value(lambda.name, key.clone());
        let current = std::mem::replace(&mut self.current, lambda.current.clone());
        let next = std::mem::replace(&mut self.next, lambda.next.clone());
        let level = std::mem::replace(&mut self.level, lambda.level);
        // `FcnLambdaValue.apply` evaluates the body with the control it is applied with: where
        // TLC keeps the application lazy, the function of another, a constructor with effects
        // that is the body of one `held_constructor` follows is a FcnLambdaValue too.
        let held = if self.keeping_lazy > 0 && is_held_lambda(lambda) {
            self.held_in_place(lambda.body, &context)
        } else {
            Ok(None)
        };
        let result = match held {
            Ok(Some(held)) => Ok(held),
            Ok(None) => self.evaluate(lambda.body, &context),
            Err(error) => Err(error),
        };
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

    /// `getFcnContext`'s failure where the walk applies a function it keeps lazy, written in
    /// place, outside its domain. TLC prints the function as `FcnLambdaValue.toString` does: built
    /// (`toFcnRcd`), or, where it can't count the domain or the body fails, which leaves that
    /// failure's frames on the call stack, as its parameter, its domain and where its body is.
    pub(crate) fn walked_outside(
        &mut self,
        function: NodeId,
        bound: &Bound,
        body: NodeId,
        base: &Context,
        set: &Value,
        argument: &Value,
    ) -> Evaluated<bool> {
        let reason = "applied a function outside its domain";
        let (
            NodeKind::FunctionConstruction { .. },
            Pattern::Name(name),
            Some(location),
            Some(body_text),
        ) = (
            self.kind(function),
            &bound.pattern,
            self.describe_node(function),
            self.describe_node(body),
        )
        else {
            return fail(reason);
        };
        let unbuilt = |evaluator: &Self| {
            format!(
                "[{} \\in {} |-> <expression {body_text}>]",
                evaluator.name(*name),
                format_value(set)
            )
        };
        let text = match set {
            // `FcnParams.size` fails on a set TLC can't count before it evaluates the body.
            Value::Lazy(lazy) if matches!(***lazy, Lazy::Nat | Lazy::Int) => unbuilt(self),
            Value::Set(_) | Value::Interval(..) => {
                let Ok(keys) = elements(set) else {
                    return fail(reason);
                };
                let effects = |evaluator: &Self| {
                    (
                        evaluator.printed.len(),
                        evaluator.register_writes,
                        evaluator.random.as_ref().map(|random| random.state()),
                        evaluator.call_stack.as_ref().map(|stack| {
                            (
                                stack.is_fingerprinted,
                                stack.fingerprinted_sources.clone(),
                                stack.unfollowed,
                                stack.fingerprint.clone(),
                            )
                        }),
                    )
                };
                let before = effects(self);
                let mut values = Vec::with_capacity(keys.len());
                for key in keys.iter() {
                    let inner = self.bind_pattern(&bound.pattern, key, base)?;
                    match self.evaluate(body, &inner) {
                        Ok(value) => values.push(value),
                        // TLC skips the failure, with its frames left on the frozen call stack.
                        Err(error) if error.message.is_some() => break,
                        Err(error) => return Err(error),
                    }
                }
                if before != effects(self) {
                    return fail("a lazy function TLC prints with effects or a report of its own");
                }
                if values.len() == keys.len() {
                    format_value(&sorted_function(keys.to_vec(), values, Class::Lambda)?)
                } else {
                    unbuilt(self)
                }
            }
            _ => return fail(reason),
        };
        fail_runtime(
            reason,
            format!(
                "In applying the function\n{},\nthe first argument is:\n{}which is not in its domain.\n{location}",
                pretty_print(&text.encode_utf16().collect::<Vec<_>>()),
                format_pretty(argument)
            ),
        )
    }

    // The bounds, body and context of a function definition or LET function a name refers to.
    // Whether the function `lazy_function` finds for a name is a recursive one, whose application
    // counts toward `MAXIMUM_RECURSION`.
    fn is_recursive_function(&self, name: &Name, context: &Context) -> bool {
        if name.is_local
            && let Some(frame) = lookup(&context.env, name.text)
        {
            return match &frame.binding {
                Binding::Function { is_self, .. } => *is_self,
                Binding::Thunk { .. } => true,
                _ => false,
            };
        }
        let Resolution::Definition(index) = name.resolution else {
            return false;
        };
        let definition = self.definition(self.ir.definitions[index as usize]);
        definition.flags & (Definition::RECURSIVE | Definition::SELF_REFERENTIAL) != 0
    }

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
                    // The LazyValue TLC binds it to keeps the function it keeps lazy here.
                    frame.is_evaluated.set(true);
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
                        is_recursive: true, ..
                    } if frame.holds_lazy_print.get() => {
                        return fail(LAZY_BODY_EFFECTS);
                    }
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

    pub(crate) fn emit_warning(&mut self, warning: tla_ir::RuntimeWarning) {
        if self.ir.model.is_warning_enabled {
            self.printed.push(crate::OutputEvent::Warning(warning));
        }
    }

    fn except_key(&mut self, step: &PathStep, context: &Context) -> Evaluated<Value> {
        Ok(match step {
            PathStep::Field(name) => Value::Str(self.text(*name)),
            PathStep::Index(args) if args.len() == 1 => self.evaluate(args[0], context)?,
            PathStep::Index(args) => Value::tuple(
                args.iter()
                    .map(|&arg| self.evaluate(arg, context))
                    .collect::<Evaluated<_>>()?,
            ),
        })
    }

    fn except(
        &mut self,
        value: &Value,
        path: &[Value],
        update: NodeId,
        context: &Context,
        warning_node: NodeId,
    ) -> Evaluated<Value> {
        let Some((step, rest)) = path.split_first() else {
            let inner = Context {
                at: Some(value.clone()),
                ..context.clone()
            };
            return self.evaluate(update, &inner);
        };
        let key = step.clone();
        // `FcnLambdaValue.select`, then `takeExcept`: the EXCEPT is kept, and `@` is the
        // function's value at the key, where an earlier EXCEPT names the key or its domain holds
        // it. Elsewhere TLC leaves the function as it is and warns, as of any other function.
        if let Value::Lambda(lambda) = value {
            if !rest.is_empty() {
                return fail("an EXCEPT of a lazy function past its first key");
            }
            if lambda.params.is_some() {
                return fail(
                    "an EXCEPT of a lazy function of several parameters or a tuple pattern",
                );
            }
            let mut is_excepted = false;
            for (excepted, _) in &lambda.excepts {
                if self.excepted_equals(excepted, &key)? {
                    is_excepted = true;
                    break;
                }
            }
            // A domain that isn't a set fails its test as `apply_lambda` declines it, and so
            // does one TLC built from an expression, which `select` tests as `apply` does.
            let is_member = if is_excepted {
                Ok(true)
            } else {
                self.member(&key, &lambda.domain)
            };
            if is_member.is_err() && self.is_sourced_lazy_domain(&lambda.domain) {
                return fail(
                    "a failing test of a lazy function's domain TLC built from an expression",
                );
            }
            if is_member.is_err() && self.is_sourced_non_set_domain(&lambda.domain) {
                return fail("a failing test of a lazy function's domain that isn't a set");
            }
            if !is_member? {
                self.emit_warning(tla_ir::RuntimeWarning::Except { node: warning_node });
                return Ok(value.clone());
            }
            // `select` tests the key's membership once, as above, and then evaluates the body at
            // it, so a domain whose test has effects, a filter's predicate, shows them once.
            let at = if is_excepted {
                self.apply_lambda(lambda, &key)?
            } else {
                self.apply_lambda_body(lambda, &key)?
            };
            let next = self.except(&at, rest, update, context, warning_node)?;
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
                params: None,
                is_in_place: lambda.is_in_place,
            })));
        }
        // `Value.select` fails at a value that isn't a function, TLC having evaluated every key of
        // the path.
        let Value::Function(function) = value else {
            if let Value::Unsorted(_) = value {
                return fail("EXCEPT on a non-function");
            }
            self.except_selected = Some(ExceptSelect::Path);
            return fail_runtime(
                "EXCEPT on a non-function",
                format!(
                    "Attempted to apply EXCEPT construct to the value {}.",
                    format_pretty(value)
                ),
            );
        };
        if matches!(
            (function.class.get(), &key),
            (Class::Tuple, key) if !matches!(key, Value::Int(_))
        ) || matches!(
            (function.class.get(), &key),
            (Class::Record, key) if !matches!(key, Value::Str(_))
        ) {
            self.except_selected = Some(ExceptSelect::Selected(value.clone()));
        }
        match function.class.get() {
            Class::Tuple if !matches!(key, Value::Int(_)) => {
                check_merge_argument_format(&key)?;
                return fail_runtime(
                    "EXCEPT with a non-integral tuple index",
                    format!(
                        "Attempted to access tuple at a non integral index: {}",
                        format_pretty(&key)
                    ),
                );
            }
            Class::Record if !matches!(key, Value::Str(_)) => {
                check_merge_argument_format(&key)?;
                return fail_runtime(
                    "EXCEPT with a non-string record key",
                    format!(
                        "Attempted to access record by a non-string argument: {}",
                        format_pretty(&key)
                    ),
                );
            }
            _ => {}
        }
        if !self.is_174() {
            integer_domain_failure(function, &key)?;
        }
        // A function over an interval the evaluator doesn't know TLC built: built, TLC fails on a
        // key that isn't an integer (`FcnRcdValue.select`), and kept lazy, it fails testing the
        // key against a nonempty interval or finds it missing from an empty one
        // (`FcnLambdaValue.select`, `IntervalValue.member`).
        if function.interval.is_some() && !matches!(key, Value::Int(_)) {
            // A constructor over an interval TLC built (`Tool`'s OPCODE_fc without KeepLazy) is
            // a FcnRcdValue over that interval, as its EXCEPTs are (`FcnRcdValue.takeExcept`).
            if function.class.get() == Class::Lambda
                && function.java_class.get() == Some(Class::Plain)
                && function.is_domain_interval.get()
                && !self.is_174()
            {
                return fail_runtime(
                    "applied a function over an interval to a non-integer",
                    format!(
                        "Attempted to apply function with integer domain to the non-integer argument {}",
                        format_pretty(&key)
                    ),
                );
            }
            return fail(
                "EXCEPT at a non-integer key of a function over an interval TLC may build",
            );
        }
        // TLC leaves a function as it is where the key isn't in its domain, and warns that the
        // EXCEPT was applied to non-existing fields (`Tool`'s OPCODE_exc), which the evaluator
        // doesn't print. `MP.printWarning` prints nothing under -nowarning.
        let selected = self.selected_key(function, &key, false);
        // A constructor TLC keeps lazy tests the key against its domain (`FcnLambdaValue.select`),
        // where a failing comparison whose receiver is the key, a set, a tuple, a record or a
        // function TLC's replay gave a source, is a FingerprintException with the key's frames
        // (`FingerprintException.getNewHead`), which the replay doesn't word.
        if selected.is_err()
            && function.class.get() == Class::Lambda
            && address(&key).is_some()
            && !self.is_assumption
            && self
                .call_stack
                .as_ref()
                .is_some_and(|stack| !stack.is_unsourced)
        {
            return fail("a failing test of a lazy function's domain at a key that has a source");
        }
        let Some(position) = selected? else {
            self.emit_warning(tla_ir::RuntimeWarning::Except { node: warning_node });
            return Ok(value.clone());
        };
        let next = self.except(
            &function.range[position],
            rest,
            update,
            context,
            warning_node,
        )?;
        let mut range = function.range.clone();
        range[position] = next;
        Ok(Value::Function(Rc::new(Function {
            domain: function.domain.clone(),
            range,
            class: function.class.clone(),
            java_class: Cell::new(match function.java_class.get() {
                Some(Class::Lambda) => None,
                other => other,
            }),
            is_counter_example: std::cell::Cell::new(Some(false)),
            is_eager_record: std::cell::Cell::new(false),
            written: function.written.clone(),
            search: function.search.clone(),
            interval: function.interval,
            is_domain_interval: Cell::new(
                function.is_domain_interval.get()
                    && function.java_class.get() == Some(Class::Plain),
            ),
        })))
    }

    // --- builtins ---

    // A direct difference of freshly constructed finite sets has not been forced by a prior
    // operation. Aliases, operator calls and repeated nodes have no cache-phase proof.
    fn fresh_print_difference(&self, operand: &Operand) -> bool {
        let Operand::Node(root, _) = operand else {
            return false;
        };
        let NodeKind::Apply { name, args } = self.kind(*root) else {
            return false;
        };
        if name.is_local
            || !matches!(name.resolution, Resolution::Builtin(index)
            if self.name(self.ir.builtins[index as usize].name) == "\\")
        {
            return false;
        }
        let [left, right] = args.as_slice() else {
            return false;
        };
        if !matches!(
            self.kind(*left),
            NodeKind::FunctionSet { .. } | NodeKind::RecordSet(_) | NodeKind::Product(_)
        ) {
            return false;
        }
        // The tested set is one the operand builds afresh from literals, whatever the builtin
        // set operations it computes it with: nothing outside it holds it, to force it first.
        if !matches!(self.kind(*right), NodeKind::SetEnumeration(_)) {
            return self.is_fresh_literal(*left, &mut Vec::new(), 0)
                && self.is_fresh_literal(*right, &mut Vec::new(), 0);
        }
        let mut pending = vec![(*root, 0usize)];
        let mut seen = HashSet::new();
        while let Some((node, depth)) = pending.pop() {
            if depth > 64 || !seen.insert(node) {
                return false;
            }
            match self.kind(node) {
                NodeKind::Number(_) | NodeKind::String(_) => {}
                NodeKind::Identifier(name)
                    if !name.is_local
                        && matches!(name.resolution,
                    Resolution::Builtin(index) if matches!(self.name(self.ir.builtins[index as usize].name), "TRUE" | "FALSE")) =>
                    {}
                NodeKind::SetEnumeration(_)
                | NodeKind::Tuple(_)
                | NodeKind::Record(_)
                | NodeKind::FunctionSet { .. }
                | NodeKind::RecordSet(_)
                | NodeKind::Product(_) => {
                    pending.extend(
                        self.kind(node)
                            .children()
                            .into_iter()
                            .map(|child| (child, depth + 1)),
                    );
                }
                NodeKind::Apply { name, args }
                    if node == *root
                        && !name.is_local
                        && matches!(name.resolution,
                    Resolution::Builtin(index) if self.name(self.ir.builtins[index as usize].name) == "\\") =>
                {
                    pending.extend(args.iter().map(|&child| (child, depth + 1)));
                }
                _ => return false,
            }
        }
        true
    }

    // Whether an expression computes its value afresh from literals: numbers, strings, booleans,
    // set enumerations, tuples, records, sets of functions, records and tuples, filters and maps
    // over such sets, naming only what they bind, and the builtin set and integer operations and
    // integer comparisons, which have no effect and build nothing another value holds.
    fn is_fresh_literal(&self, node: NodeId, bound: &mut Vec<TextId>, depth: usize) -> bool {
        if depth > 64 {
            return false;
        }
        let builtin = |name: &tla_ir::Name| -> Option<&str> {
            match name.resolution {
                Resolution::Builtin(index) if !name.is_local => {
                    Some(self.name(self.ir.builtins[index as usize].name))
                }
                _ => None,
            }
        };
        let names = |pattern: &Pattern| match pattern {
            Pattern::Name(name) => vec![*name],
            Pattern::Tuple(names) => names.clone(),
        };
        match self.kind(node) {
            NodeKind::Number(_) | NodeKind::String(_) => true,
            NodeKind::Identifier(name) if name.is_local => bound.contains(&name.text),
            NodeKind::Identifier(name) => {
                matches!(builtin(name), Some("TRUE" | "FALSE" | "BOOLEAN"))
            }
            NodeKind::SetEnumeration(_)
            | NodeKind::Tuple(_)
            | NodeKind::Record(_)
            | NodeKind::FunctionSet { .. }
            | NodeKind::RecordSet(_)
            | NodeKind::Product(_) => self
                .kind(node)
                .children()
                .into_iter()
                .all(|child| self.is_fresh_literal(child, bound, depth + 1)),
            NodeKind::Apply { name, args }
                if matches!(
                    builtin(name),
                    Some(
                        "\\cup"
                            | "\\cap"
                            | "\\"
                            | "UNION"
                            | "SUBSET"
                            | ".."
                            | "+"
                            | "-"
                            | "*"
                            | "<"
                            | ">"
                            | "<="
                            | ">="
                    )
                ) =>
            {
                args.iter()
                    .all(|&arg| self.is_fresh_literal(arg, bound, depth + 1))
            }
            NodeKind::SetFilter {
                bound: filtered,
                predicate,
            } => {
                if !self.is_fresh_literal(filtered.set, bound, depth + 1) {
                    return false;
                }
                let added = names(&filtered.pattern);
                let count = added.len();
                bound.extend(added);
                let is_fresh = self.is_fresh_literal(*predicate, bound, depth + 1);
                bound.truncate(bound.len() - count);
                is_fresh
            }
            NodeKind::SetMap { expression, bounds } => {
                if !bounds
                    .iter()
                    .all(|mapped| self.is_fresh_literal(mapped.set, bound, depth + 1))
                {
                    return false;
                }
                let before = bound.len();
                for mapped in bounds {
                    bound.extend(names(&mapped.pattern));
                }
                let is_fresh = self.is_fresh_literal(*expression, bound, depth + 1);
                bound.truncate(before);
                is_fresh
            }
            _ => false,
        }
    }

    // Only a direct SetPred over SUBSET of a literal enumeration has an unconverted TLC
    // filter and an unforced base here. Its predicate is a boolean or a test of its bound
    // subset against the empty set; no external binding can alias either operand.
    fn fresh_filter_print_difference(&self, operand: &Operand) -> bool {
        let Operand::Node(root, _) = operand else {
            return false;
        };
        let NodeKind::Apply { name, args } = self.kind(*root) else {
            return false;
        };
        if name.is_local
            || !matches!(name.resolution, Resolution::Builtin(index)
            if self.name(self.ir.builtins[index as usize].name) == "\\")
        {
            return false;
        }
        let [left, right] = args.as_slice() else {
            return false;
        };
        let NodeKind::SetFilter { bound, predicate } = self.kind(*left) else {
            return false;
        };
        let Pattern::Name(bound_name) = bound.pattern else {
            return false;
        };
        let NodeKind::Apply { name, args } = self.kind(bound.set) else {
            return false;
        };
        if name.is_local
            || !matches!(name.resolution, Resolution::Builtin(index)
            if self.name(self.ir.builtins[index as usize].name) == "SUBSET")
        {
            return false;
        }
        let [inner] = args.as_slice() else {
            return false;
        };
        if !matches!(self.kind(*inner), NodeKind::SetEnumeration(_))
            || !matches!(self.kind(*right), NodeKind::SetEnumeration(_))
        {
            return false;
        }
        let boolean = |node| {
            matches!(self.kind(node), NodeKind::Identifier(name)
            if !name.is_local && matches!(name.resolution, Resolution::Builtin(index)
                if matches!(self.name(self.ir.builtins[index as usize].name), "TRUE" | "FALSE")))
        };
        let is_bound = |node| {
            matches!(self.kind(node), NodeKind::Identifier(name)
            if name.is_local && name.text == bound_name)
        };
        let empty =
            |node| matches!(self.kind(node), NodeKind::SetEnumeration(items) if items.is_empty());
        let compares_empty = |node| match self.kind(node) {
            NodeKind::Apply { name, args }
                if !name.is_local
                    && matches!(name.resolution,
                Resolution::Builtin(index) if matches!(self.name(self.ir.builtins[index as usize].name), "=" | "#")) =>
            {
                matches!(args.as_slice(), [left, right] if (is_bound(*left) && empty(*right))
                    || (empty(*left) && is_bound(*right)))
            }
            _ => false,
        };
        let predicate_is_safe = boolean(*predicate)
            || compares_empty(*predicate)
            || matches!(self.kind(*predicate), NodeKind::If { condition, consequent, alternative }
                if compares_empty(*condition) && boolean(*consequent) && boolean(*alternative));
        if !predicate_is_safe {
            return false;
        }
        let mut pending = vec![(*inner, 0usize), (*right, 0)];
        let mut seen = HashSet::new();
        while let Some((node, depth)) = pending.pop() {
            if depth > 64 || !seen.insert(node) {
                return false;
            }
            match self.kind(node) {
                NodeKind::Number(_) | NodeKind::String(_) => {}
                NodeKind::Identifier(name)
                    if !name.is_local
                        && matches!(name.resolution,
                    Resolution::Builtin(index) if matches!(self.name(self.ir.builtins[index as usize].name), "TRUE" | "FALSE")) =>
                    {}
                NodeKind::SetEnumeration(items) => {
                    pending.extend(items.iter().map(|&child| (child, depth + 1)))
                }
                _ => return false,
            }
        }
        true
    }

    // Whether the first set with no element a draw of `TLC.RandomElement` from a set written as
    // `node` reaches, part by part as it draws (the range of a set of functions with a domain,
    // the fields of a set of records by name, the factors of a product), is an interval or the
    // empty set written `{}`, both of which fail in TLC's draw; None where it reaches none.
    fn first_empty_draw_is_written(&self, node: NodeId, set: &Value) -> Option<bool> {
        let node = self.resolved(node);
        match (set, self.kind(node)) {
            (Value::Interval(low, high, _), _) => (high < low).then_some(true),
            (Value::Lazy(lazy), kind) => match (&***lazy, kind) {
                (
                    Lazy::FunctionSet(domain, range),
                    NodeKind::FunctionSet { range: written, .. },
                ) => match elements(domain) {
                    Ok(keys) if keys.is_empty() => None,
                    Ok(_) => self.first_empty_draw_is_written(*written, range),
                    Err(_) => Some(false),
                },
                (Lazy::RecordSet(fields, order), NodeKind::RecordSet(written))
                    if written.len() == fields.len() && order.len() == fields.len() =>
                {
                    (0..fields.len()).find_map(|position| {
                        let index = order.iter().position(|&at| at as usize == position)?;
                        self.first_empty_draw_is_written(written[index].1, &fields[position].1)
                    })
                }
                (Lazy::Product(factors), NodeKind::Product(written))
                    if written.len() == factors.len() =>
                {
                    factors.iter().zip(written).find_map(|(factor, &written)| {
                        self.first_empty_draw_is_written(written, factor)
                    })
                }
                (Lazy::FunctionSet(..) | Lazy::RecordSet(..) | Lazy::Product(..), _) => Some(false),
                _ => match elements(set) {
                    Ok(elements) if !elements.is_empty() => None,
                    _ => Some(false),
                },
            },
            (Value::Set(elements), kind) if elements.elements.is_empty() => {
                Some(matches!(kind, NodeKind::SetEnumeration(items) if items.is_empty()))
            }
            _ => match elements(set) {
                Ok(elements) if !elements.is_empty() => None,
                _ => Some(false),
            },
        }
    }

    fn operand_unchecked(&mut self, operand: &Operand) -> Evaluated<Value> {
        match operand {
            Operand::Node(node, context) => self.evaluate(*node, context),
            Operand::Value(value) => Ok(value.clone()),
        }
    }

    fn operand(&mut self, operand: &Operand) -> Evaluated<Value> {
        let value = self.operand_unchecked(operand)?;
        if self.has_uninitialized_literals && crate::value::contains_uninitialized(&value) {
            return fail("a null tool value used by a consumer the replay does not model");
        }
        Ok(value)
    }

    fn sequence_operand(&mut self, operand: &Operand) -> Evaluated<Value> {
        let value = self.operand_unchecked(operand)?;
        if self.has_uninitialized_literals
            && crate::value::contains_uninitialized(&value)
            && !matches!(&value, Value::Function(function) if function.java_class.get() == Some(Class::Tuple))
        {
            return fail("a null tool value in an unproved sequence conversion");
        }
        Ok(value)
    }

    fn operand_boolean(&mut self, operand: &Operand) -> Evaluated<bool> {
        match self.operand(operand)? {
            Value::Bool(boolean) => Ok(boolean),
            other => fail(format!("expected a boolean, not a {}", other.kind_name())),
        }
    }

    fn arithmetic_integer(
        &self,
        value: Option<i64>,
        expression: impl FnOnce() -> String,
    ) -> Evaluated<Value> {
        if let Some(value) = value.and_then(|value| i32::try_from(value).ok()) {
            return Ok(Value::Int(value));
        }
        // Effects from a constructor TLC keeps lazy may have moved ahead of this new error.
        if self.lazy_body_effects != 0 || self.printing_values != 0 {
            return fail("integer overflow");
        }
        fail_coded(
            "integer overflow",
            MODULE_OVERFLOW,
            format!("Overflow when computing {}", expression()),
        )
    }

    // `OpValue.eval` evaluates left to right before the MethodHandle spreader casts right to left.
    fn integer_arguments<const N: usize>(
        &mut self,
        builtin: &Builtin,
        operands: &[Operand],
    ) -> Evaluated<[i64; N]> {
        let mut values = Vec::with_capacity(operands.len());
        for operand in operands {
            match self.operand_unchecked(operand).and_then(|value| {
                if matches!(value, Value::Null) {
                    fail("a null integer argument")
                } else {
                    Ok(value)
                }
            }) {
                Ok(value) => values.push(value),
                Err(mut error) => {
                    if self.lazy_body_effects != 0
                        && values.iter().any(|value| !matches!(value, Value::Int(_)))
                    {
                        error.message = None;
                    }
                    return Err(error);
                }
            }
        }
        let mut integers = [0; N];
        for (position, value) in values.iter().enumerate().rev() {
            match value {
                Value::Int(integer) => integers[position] = i64::from(*integer),
                _ => {
                    let name = self.name(builtin.name);
                    let method = match name {
                        "+" => "Plus",
                        "-" => "Minus",
                        "*" => "Times",
                        "\\div" => "Divide",
                        "%" => "Mod",
                        "^" => "Expt",
                        ".." => "DotDot",
                        "-." => "Neg",
                        _ => unreachable!("a typed integer method"),
                    };
                    let module = if builtin.flags & Builtin::NATURALS_METHOD != 0 {
                        "Naturals"
                    } else {
                        "Integers"
                    };
                    let result = if name == ".." {
                        "IntervalValue"
                    } else {
                        "IntValue"
                    };
                    let signature = format!(
                        "public static tlc2.value.impl.{result} tlc2.module.{module}.{method}({})",
                        vec!["tlc2.value.impl.IntValue"; N].join(",")
                    );
                    let Some(class) = numeric_value_class(value) else {
                        return fail(format!("expected an integer, not a {}", value.kind_name()));
                    };
                    let failure = as_java_runtime_failure(
                        &signature,
                        fail_runtime(
                            "a Java method argument that isn't an integer",
                            format!(
                                "Cannot cast tlc2.value.impl.{} to tlc2.value.impl.IntValue",
                                class
                            ),
                        ),
                    );
                    return failure.map_err(|mut error| {
                        if self.lazy_body_effects != 0 {
                            error.message = None;
                        }
                        error
                    });
                }
            }
        }
        Ok(integers)
    }

    fn operand_operator(&mut self, operand: &Operand) -> Evaluated<Rc<Operator>> {
        match operand {
            Operand::Node(node, context) => self.operator_argument(*node, context),
            Operand::Value(_) => fail("an operator argument"),
        }
    }

    fn written_mixed_scalars(&self, operand: &Operand) -> bool {
        let Operand::Node(node, _) = operand else {
            return false;
        };
        let NodeKind::SetEnumeration(items) = self.kind(*node) else {
            return false;
        };
        let mut kinds = HashSet::new();
        for &item in items {
            let kind = match self.kind(item) {
                NodeKind::Number(_) => 0,
                NodeKind::String(_) => 1,
                NodeKind::Identifier(name)
                    if !name.is_local
                        && matches!(name.resolution, Resolution::Builtin(index)
                    if matches!(self.name(self.ir.builtins[index as usize].name), "TRUE" | "FALSE")) =>
                {
                    2
                }
                _ => return false,
            };
            kinds.insert(kind);
        }
        kinds.len() > 1
    }

    fn direct_named_infinite(&self, operand: &Operand) -> bool {
        let Operand::Node(node, _) = operand else {
            return false;
        };
        matches!(self.kind(*node), NodeKind::Identifier(name)
            if !name.is_local && matches!(name.resolution, Resolution::Builtin(index)
                if matches!(self.name(self.ir.builtins[index as usize].name), "Int" | "Nat" | "STRING")))
    }

    // Whether TLC's member test of a set forces the element (`toFcnRcd`): a set of functions
    // (`SetOfFcnsValue.member`) and of sequences (`Sequences.member`, which prints it as it fails)
    // as they start, a set enumeration of functions, tuples, records, integers, strings or
    // booleans, the set a filter of one leaves, as `ValueVec.search` compares the element with
    // each (`compareTo`, `equals`), and a union of two such (`SetEnumValue.cup`).
    fn forces_member(&self, set: &Operand, combined: &Combined) -> bool {
        let Operand::Node(node, context) = set else {
            return false;
        };
        let node = self.resolved(*node);
        let is_compared = |value: &Value| matches!(value, Value::Set(set) if !set.is_empty() && set.iter().all(forces_compared));
        match (self.kind(node), combined) {
            (NodeKind::FunctionSet { .. }, Combined::Set(_)) => true,
            (NodeKind::SetEnumeration(elements), Combined::Set(value)) => {
                !elements.is_empty() && is_compared(value)
            }
            (NodeKind::SetFilter { bound, .. }, Combined::Set(value)) => {
                matches!(
                    self.kind(self.resolved(bound.set)),
                    NodeKind::SetEnumeration(_)
                ) && is_compared(value)
            }
            (NodeKind::Apply { name, args }, combined) if !name.is_local => {
                let Resolution::Builtin(index) = name.resolution else {
                    return false;
                };
                match (
                    self.name(self.ir.builtins[index as usize].name),
                    &args[..],
                    combined,
                ) {
                    ("Seq", [_], Combined::Set(_)) => true,
                    ("\\cup", [left, right], Combined::Union(left_set, right_set)) => {
                        self.forces_member(&Operand::Node(*left, context.clone()), left_set)
                            && self
                                .forces_member(&Operand::Node(*right, context.clone()), right_set)
                    }
                    _ => false,
                }
            }
            _ => false,
        }
    }

    // Membership in a set, through the operands of a `\\cup`, `\\cap` or `\\`, as TLC's lazy
    // `SetCupValue`, `SetCapValue` and `SetDiffValue` test it, so that an infinite operand such as
    // Nat isn't enumerated.
    //
    // `SetOfFcnsValue.member` forces the element (`toFcnRcd`) before it tests it, and a written
    // set enumeration of functions as it compares them; any other set's member test may not.
    fn is_member_of(&mut self, element: &Value, set: &Operand) -> Evaluated<bool> {
        let combined = self.combined_set(set)?;
        let is_forcing = self.forces_member(set, &combined);
        let forced: &[&Value] = if is_forcing { &[element] } else { &[] };
        self.force_lazy_prints(Force::Built(forced))?;
        let result = combined.has(self, element);
        // TLC's \\cup, \\cap and \\ have a source, so a failure in testing their members is a
        // FingerprintException.
        if result.is_err()
            && matches!(combined, Combined::Union(..))
            && let Some(stack) = &mut self.call_stack
            && !stack.is_frozen
        {
            stack.is_fingerprinted = true;
        }
        result
    }

    // `SetPredValue.member`: the base's membership, then the predicate. TLC turns an
    // EvalException of either into a message of its own ("Cannot decide if element").
    fn filter_member(
        &mut self,
        element: &Value,
        base: &Value,
        predicate: &Predicate,
    ) -> Evaluated<bool> {
        if let Some(elements) = predicate.converted() {
            return is_member(
                element,
                &Value::set_from_rc(elements, Some(SetClass::Enumeration)),
            );
        }
        // `filters` words an EvalException of the predicate itself, so one here is the set's.
        match self.member(element, base) {
            Ok(true) => self.filters(element, base, predicate),
            Ok(false) => Ok(false),
            Err(error)
                if error
                    .message
                    .as_ref()
                    .is_some_and(|message| message.is_eval_exception) =>
            {
                Err(self.undecided_member(element, base, predicate))
            }
            Err(error) => Err(error),
        }
    }

    /// Membership as TLC's lazy sets test it, the predicate of a lazy filter evaluated
    /// (`SetPredValue.member`), through the sets it is combined in.
    pub(crate) fn member(&mut self, element: &Value, set: &Value) -> Evaluated<bool> {
        let was_frozen = self.is_frozen();
        let result = self.member_of(element, set);
        if result.is_err() {
            self.fingerprint_frozen(set, was_frozen);
        }
        result
    }

    fn is_frozen(&self) -> bool {
        self.call_stack
            .as_ref()
            .is_some_and(|stack| stack.is_frozen)
    }

    // A failure that froze the call stack within an evaluation a method of `receiver` made, as of
    // a filter's predicate, passes through that method, which throws it on as a
    // FingerprintException where `receiver` has a source (`getNewHead`). The frozen stack takes
    // none of its sources (`CallStack.freeze(FingerprintException)`).
    // An interval the replay holds without an address has no source in it, where TLC gives one
    // the node that returned it, as DOMAIN does (`setSource(expr, getDomain())`): such a failure
    // is left unfollowed.
    fn fingerprint_frozen(&mut self, receiver: &Value, was_frozen: bool) {
        let is_interval_unplaced =
            matches!(receiver, Value::Interval(..)) && self.holds_sourced_interval();
        if let Some(stack) = &mut self.call_stack
            && !was_frozen
            && stack.is_frozen
            && !stack.is_fingerprinted
            && !stack.is_unsourced
        {
            if stack.source(receiver).is_some() {
                stack.is_fingerprinted = true;
                stack.is_frozen_before_fingerprint = true;
            } else if is_interval_unplaced {
                stack.unfollowed.get_or_insert(LAZY_MEMBER);
            }
        }
    }

    fn member_of(&mut self, element: &Value, set: &Value) -> Evaluated<bool> {
        let closed = self.closed_java_context;
        let Value::Lazy(lazy) = set else {
            return member_filtered(
                element,
                set,
                &mut |_, _, _| fail("a lazy filter's membership outside the evaluator"),
                closed,
            );
        };
        match &***lazy {
            Lazy::Filter(base, predicate) => self.filter_member(element, base, predicate),
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
                let sets = elements(sets)?;
                for inner in sets.iter() {
                    if self.member(element, inner)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            // A set whose parts are lazy filters tests them as the evaluator does.
            _ => member_filtered(element, set, &mut filter_test(self), closed),
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
        if !is_enumerable(&left) {
            return fail_runtime(
                SUBSET_NON_ENUMERABLE,
                format!(
                    "Attempted to evaluate an expression of form S \\subseteq T, but S was not enumerable.\n{}",
                    self.describe_range(node)
                ),
            );
        }
        // `IntervalValue.isSubsetEq`: an interval within another interval is a subset, which TLC
        // decides without enumerating either.
        if let (Value::Interval(low, high, _), Value::Interval(other_low, other_high, _)) =
            (&left, &right)
            && other_low <= low
            && other_high >= high
        {
            return Ok(Value::Bool(true));
        }
        // `isSubsetEq` takes the elements of S from its Enumerator one at a time, as TLC streams
        // them, and stops at the first one T doesn't hold.
        let was_frozen = self.is_frozen();
        let streamed = crate::sets::stream_until(&left.clone(), &mut |element| {
            // `isSubsetEq` of S tests each element in T's own `member`, so a failure there is in
            // a method of T within one of S, which TLC reports as a FingerprintException where
            // either has a source.
            let is_member = self.member(element, &right);
            if is_member.is_err()
                && let Some(stack) = &self.call_stack
                && !stack.is_frozen
            {
                let outer = stack.source(&left);
                self.mark_interval_unplaced(&left, None);
                self.mark_failing_member(outer, &right, Given::Element(element), true);
            } else if is_member.is_err() {
                // A failure the evaluation of T's members met, as in a filter's predicate, is in
                // S's method too.
                self.fingerprint_frozen(&left, was_frozen);
            }
            is_member
        });
        Ok(Value::Bool(streamed?))
    }

    // A lazy filter's predicate on an element of its set, in the states the filter was built in.
    fn filters(&mut self, element: &Value, base: &Value, predicate: &Predicate) -> Evaluated<bool> {
        let context = match &predicate.pattern {
            Pattern::Name(_) => {
                self.bind_pattern(&predicate.pattern, element, &predicate.context)?
            }
            // TLC fails on an element that isn't a tuple of as many (`toTuple`), which converts a
            // function TLC keeps lazy, as the evaluator doesn't.
            Pattern::Tuple(names) => match as_tuple(element) {
                Some(tuple) if tuple.len() == names.len() => {
                    self.bind_pattern(&predicate.pattern, element, &predicate.context)?
                }
                _ if matches!(element, Value::Lazy(_)) => {
                    return fail("a lazy filter's element that isn't a tuple of its names");
                }
                _ => {
                    return fail_runtime(
                        "a lazy filter's element that isn't a tuple of its names",
                        format!(
                            "Attempted to check if the value:\n{}\nis an element of a set of {}-tuples.",
                            format_pretty(element),
                            names.len()
                        ),
                    );
                }
            },
        };
        let current = std::mem::replace(&mut self.current, predicate.current.clone());
        let next = std::mem::replace(&mut self.next, predicate.next.clone());
        let level = std::mem::replace(&mut self.level, predicate.level);
        let result = self.evaluate(predicate.body, &context);
        self.current = current;
        self.next = next;
        self.level = level;
        // A predicate the `Tool` without a call stack evaluates pushes no frames, and its failure
        // freezes none, which the replay doesn't follow.
        if predicate.is_untraced
            && !matches!(result, Ok(Value::Bool(_)))
            && let Some(stack) = &mut self.call_stack
        {
            stack.unfollowed.get_or_insert(LAZY_MEMBER);
        }
        match result {
            Ok(Value::Bool(holds)) => Ok(holds),
            // `Assert.fail` with the filter's source, which a `SetPredValue` never has (see
            // `CallStackTool.evalAppl`), throws a TLCRuntimeException, which the filter doesn't
            // word again. It names the predicate by SANY's `toString`: a numeral by its image.
            Ok(_) => match self.describe_node(predicate.body) {
                Some(written) => fail_runtime(
                    "a lazy filter's predicate that isn't a boolean",
                    format!("The evaluation of predicate {written} yielded non-Boolean value."),
                ),
                None => {
                    fail("a lazy filter's predicate that isn't a boolean, written as a numeral")
                }
            },
            // `SetPredValue.member` words an EvalException as its own failure, after the call
            // stack froze within the predicate.
            Err(error)
                if error
                    .message
                    .as_ref()
                    .is_some_and(|message| message.is_eval_exception) =>
            {
                Err(self.undecided_member(element, base, predicate))
            }
            Err(error) => Err(error),
        }
    }

    // `SetPredValue.member`'s message for an EvalException in the membership of its set or in its
    // predicate, a TLCRuntimeException, as the filter has no source.
    fn undecided_member(&self, element: &Value, base: &Value, predicate: &Predicate) -> EvalError {
        let Err(error) = fail_runtime::<()>(
            "a lazy filter's membership that fails",
            format!(
                "Cannot decide if element:\n{}\n is element of:\n{}\nand satisfies the predicate {}",
                format_pretty(element),
                format_pretty(base),
                self.describe_range(predicate.body)
            ),
        ) else {
            unreachable!("a failure")
        };
        error
    }

    // A set as TLC builds it, both operands of each `\\cup` evaluated, which the replay tests for
    // membership without building the union. TLC builds a union of enumerable sets at once,
    // testing their elements, so a failure replay builds each. It builds an intersection or a
    // difference with a set enumeration or an interval at once too, testing each of its elements
    // in the other operand, which may fail on one the membership doesn't test, so the replay
    // builds those as TLC does.
    // Whether an operand is an application of the builtin of this name.
    fn is_builtin(&self, operand: &Operand, builtin: &str) -> bool {
        matches!(operand, Operand::Node(node, _)
            if matches!(self.kind(*node), NodeKind::Apply { name, .. }
                if !name.is_local
                    && matches!(name.resolution, Resolution::Builtin(index)
                        if self.name(self.ir.builtins[index as usize].name) == builtin)))
    }

    fn combined_set(&mut self, set: &Operand) -> Evaluated<Combined> {
        if let Operand::Node(node, context) = set
            && let NodeKind::Apply { name, args } = self.kind(*node)
            && let [left, right] = args[..]
            && !name.is_local
            && let Resolution::Builtin(index) = name.resolution
            && self.call_stack.is_none()
            && self.name(self.ir.builtins[index as usize].name) == "\\cup"
        {
            let left = self.combined_set(&Operand::Node(left, context.clone()))?;
            let right = self.combined_set(&Operand::Node(right, context.clone()))?;
            let union = Combined::Union(Box::new(left), Box::new(right));
            // `Tool`'s OPCODE_cup evaluates both operands and reduces a union of two Reducible
            // sets at once (`Reducible.cup`), testing the right one's elements in the left one,
            // before anything tests an element of the union or of a union holding it.
            if union.is_reducible() {
                return Ok(Combined::Set(union.reduced()?));
            }
            return Ok(union);
        }
        Ok(Combined::Set(self.operand(set)?))
    }

    // A set enumeration as TLC builds it, of the values as written, which it normalizes only as it
    // uses it: the replay follows that as far as fingerprinting and printing the state, and
    // counting it, and keeps track of the set TLC still holds unnormalized, which it tests for
    // membership element by element. A set TLC fails to sort as it compares a function, a tuple
    // or a record with another value it holds so too: its consumers sort it as `ValueVec.sort`
    // does, each new element the receiver of `compareTo`, or search it element by element as
    // written, each the receiver of `equals`, as TLC does.
    fn held_set(&mut self, values: Vec<Value>) -> Evaluated<Value> {
        // The constructor keeps its written elements even outside a failure replay; an
        // unnormalized membership asks each element as the equality receiver.
        match crate::value::held_set_of(values) {
            Err((error, values)) if error.message.is_some() => {
                if let Some(stack) = &mut self.call_stack {
                    stack.is_unsorted = true;
                    stack.unsorted_built += 1;
                }
                Ok(Value::unsorted(values))
            }
            Err((error, _)) => Err(error),
            Ok(set) => Ok(set),
        }
    }

    // A value whose filters TLC keeps lazy are enumerated, at its top or in the tuples and records
    // it is, as what uses it enumerates them (`SetPredValue.toSetEnum`): the predicate evaluated
    // on each element of the set in turn, where the evaluator didn't filter the set ahead.
    fn settle(&mut self, value: &Value) -> Evaluated<Value> {
        Ok(self.settled(value)?.unwrap_or_else(|| value.clone()))
    }

    // A lazy filter's input is streamed, without materializing an inner filter into a ValueVec.
    fn filter_input(&mut self, set: &Value) -> Evaluated<Rc<Vec<Value>>> {
        if let Value::Lazy(lazy) = set
            && let Lazy::Filter(base, predicate) = &***lazy
            && predicate.filtered().is_none()
            && predicate.converted().is_none()
            && is_enumerable(base)
        {
            let mut kept = Vec::new();
            for element in self.filter_input(base)?.iter() {
                if self.passes(element, predicate)? {
                    kept.push(element.clone());
                }
            }
            return Ok(Rc::new(kept));
        }
        crate::sets::stream(set)
    }

    // `settle`'s value, where it differs.
    fn settled(&mut self, value: &Value) -> Evaluated<Option<Value>> {
        match value {
            Value::Lazy(lazy) => match &***lazy {
                Lazy::Filter(base, predicate)
                    if predicate.filtered().is_none()
                        && predicate.converted().is_none()
                        && is_enumerable(base)
                        && is_finite(base).unwrap_or(false) =>
                {
                    let mut kept = Vec::new();
                    for element in self.filter_input(base)?.iter() {
                        if self.passes(element, predicate)? {
                            push_set_element(&mut kept, element.clone())?;
                        }
                    }
                    Ok(Some(Value::set_with_class(kept, Some(SetClass::Predicate))))
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
                        java_class: function.java_class.clone(),
                        is_counter_example: function.is_counter_example.clone(),
                        is_eager_record: std::cell::Cell::new(false),
                        written: function.written.clone(),
                        search: function.search.clone(),
                        interval: function.interval,
                        is_domain_interval: function.is_domain_interval.clone(),
                    }))
                }))
            }
            _ => Ok(None),
        }
    }

    // Whether an element passes the predicate of a filter, evaluated where the filter was built,
    // as `SetPredValue.Enumerator` tests it: an element that isn't a tuple of as many as a tuple
    // pattern names, or a predicate that isn't a boolean, fails with its own message.
    fn passes(&mut self, element: &Value, predicate: &Predicate) -> Evaluated<bool> {
        let context = self.bind_filtered(element, predicate)?;
        let current = std::mem::replace(&mut self.current, predicate.current.clone());
        let next = std::mem::replace(&mut self.next, predicate.next.clone());
        let level = std::mem::replace(&mut self.level, predicate.level);
        let result = self.evaluate(predicate.body, &context);
        self.current = current;
        self.next = next;
        self.level = level;
        match result? {
            Value::Bool(holds) => Ok(holds),
            other => {
                let reason = format!("expected a boolean, not a {}", other.kind_name());
                // The predicate as SANY's `toString` gives it.
                let Some(written) = self.describe_node(predicate.body) else {
                    return fail(reason);
                };
                fail_runtime(
                    reason,
                    format!("Evaluating predicate {written} yielded non-Boolean value."),
                )
            }
        }
    }

    // The context of a lazy filter's predicate for an element, as `SetPredValue` binds it: a
    // tuple pattern takes an element that is a tuple of as many as it names.
    fn bind_filtered(&mut self, element: &Value, predicate: &Predicate) -> Evaluated<Context> {
        if let Pattern::Tuple(names) = &predicate.pattern
            && as_tuple(element).is_none_or(|tuple| tuple.len() != names.len())
        {
            // A lazy function's `toTuple` builds it first.
            if matches!(element, Value::Lazy(_)) {
                return fail("a lazy value a filter's tuple pattern binds");
            }
            return fail_runtime(
                TUPLE_MISMATCH,
                format!(
                    "Attempted to check if the value:\n{}\nis an element of a set of {}-tuples.",
                    format_pretty(element),
                    names.len()
                ),
            );
        }
        self.bind_pattern(&predicate.pattern, element, &predicate.context)
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
        if let Some(stack) = &mut self.call_stack {
            stack.scalar_state_at_value_failure = Some(false);
        }
        let rollback = rollback_filter_conversions();
        let cache = self.cache.clone();
        let frames = self.cached_frames.clone();
        let unshared = self.unshared;
        let reads = self.reads;
        let captures = self.captures;
        let result = self.filter_ahead_inner(set, pattern, predicate, context);
        if rollback.has_changes() {
            self.cache = cache;
            self.cached_frames = frames;
            self.unshared = unshared;
            self.reads = reads;
            self.captures = captures;
            result.map(|_| None)
        } else {
            rollback.commit();
            result
        }
    }

    fn filter_ahead_inner(
        &mut self,
        set: &Value,
        pattern: &Pattern,
        predicate: NodeId,
        context: &Context,
    ) -> Evaluated<Option<Rc<Vec<Value>>>> {
        // The filter's set as TLC's `SetPredValue.Enumerator` streams it.
        let Ok(elements) = crate::sets::stream(set) else {
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
                Ok(true) if kept.len() >= tla_values::SET_BOUND => {
                    self.call_stack = call_stack;
                    is_failed = true;
                    break;
                }
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

    fn tlc_get(&mut self, operand: &Operand, context: &Context) -> Evaluated<Value> {
        let key = self.operand(operand)?;
        if is_varying_tlc_get_key(&key) {
            self.varying_tlc_gets += 1;
        }
        Ok(match key {
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
            // A simulation has no model checker (`TLCGlobals.mainChecker` is null), whose counts
            // `TLCGetStringValue` then fails to read with a NullPointerException it words as an
            // undefined key. What else a simulation reads of its run isn't followed.
            Value::Str(key) if self.is_simulation && is_simulation_run_key(&key.units) => {
                if matches!(
                    String::from_utf16_lossy(&key.units).as_str(),
                    "generated" | "distinct" | "queue"
                ) {
                    return undefined_register(&Value::Str(key));
                }
                return fail("TLCGet of a key a simulation reads otherwise");
            }
            // `AbstractChecker.createConfig`, as the engine words it: TLC's install is
            // where its jar is, which the native checker has none of.
            Value::Str(key) if *key.units == *"config".encode_utf16().collect::<Vec<_>>() => {
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
                        string(
                            &(Polynomial::get(self.ir.model.fingerprint_index).value() as i64)
                                .to_string(),
                        ),
                    ),
                    (text("install"), string("unknown")),
                ])?
            }
            // A system property TLCSet set, or else the key (`System.getProperty`).
            Value::Str(key)
                if String::from_utf16_lossy(&key.units)
                    .strip_prefix(JAVA_PROPERTY_PREFIX)
                    .is_some_and(is_settable_property) =>
            {
                self.reads += 1;
                self.register_reads += 1;
                let name = &key.units[JAVA_PROPERTY_PREFIX.len()..];
                match self
                    .registers
                    .properties
                    .iter()
                    .find(|(set, _)| set.as_slice() == name)
                {
                    Some((_, value)) => value.clone(),
                    None => Value::Str(key),
                }
            }
            Value::Str(key) if *key.units == *"level".encode_utf16().collect::<Vec<_>>() => {
                self.reads += 1;
                Value::Int(match self.next_level {
                    Some(level) if context.is_primed => level,
                    _ => self.level + i32::from(context.is_primed),
                })
            }
            // `TLCGetSet.TLCGetStringValue` fails on a key it doesn't know.
            Value::Str(key)
                if String::from_utf16(&key.units).is_ok_and(|key| is_unknown_tlc_get_key(&key)) =>
            {
                return undefined_register(&Value::Str(key));
            }
            // As TLC checks the assumptions, its model checker's: no state is counted yet and
            // its trace is at level 1, and the action is unknown (`ModelChecker.getStatesGenerated`,
            // `TLCTrace.getLevel`, `Action.UNKNOWN`). The main thread's TLCSet sets the register
            // of every worker (`AbstractChecker.setAllValues`, `setAllNamedValues`), so TLCGet
            // ("all") and TLCGet("all:named") map each register set so far to the tuple of each
            // worker's value (`getAllValues`, `getAllNamedRegisterValues`).
            Value::Str(key) if self.is_in_assumptions && self.runtime.is_none() => {
                let key = String::from_utf16_lossy(&key.units);
                match key.as_str() {
                    "generated" | "distinct" | "queue" => Value::Int(0),
                    "diameter" => Value::Int(1),
                    // TLCSet on the main thread sets the register of every worker
                    // (`AbstractChecker.setAllValues`, `setAllNamedValues`), so each register
                    // set so far is the tuple of its value once for each worker.
                    "all" | "all:named" => {
                        let set: Vec<(Value, Value)> = if key == "all" {
                            self.registers
                                .numbered
                                .iter()
                                .enumerate()
                                .filter_map(|(index, value)| {
                                    Some((Value::Int(index as i32), value.clone()?))
                                })
                                .collect()
                        } else {
                            self.registers.named.clone()
                        };
                        if !set.is_empty() {
                            self.reads += 1;
                            self.register_reads += 1;
                        }
                        let workers = match self.workers {
                            _ if set.is_empty() => 0,
                            Some(_) if self.is_simulation => {
                                return fail(
                                    "TLCGet of the registers a simulation's assumption set",
                                );
                            }
                            Some(workers) => workers,
                            None => {
                                return fail("TLCGet of the registers without the run's workers");
                            }
                        };
                        let (keys, values) = set
                            .into_iter()
                            .map(|(key, value)| (key, Value::tuple(vec![value; workers])))
                            .unzip();
                        sorted_function(keys, values, Class::Plain)?
                    }
                    "action" => self.unknown_action()?,
                    _ => return fail("TLCGet"),
                }
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
                    // TLCGet("duration") is the seconds since TLC's class was loaded
                    // (`TLCGetSet.startTime`), as `"stats"`'s duration is; the lowering lets a
                    // postcondition read it only where every duration answers alike.
                    "generated" | "distinct" | "queue" | "diameter" | "duration" => {
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
        })
    }

    // TLCGet("action") where TLC's state holds no action, as in its breadth-first search
    // (`new RecordValue(Action.UNKNOWN)`): its name and its location, each field as written.
    fn unknown_action(&mut self) -> Evaluated<Value> {
        let text = |evaluator: &mut Self, text: &str| evaluator.counterexample_field(text, false);
        let mut location = Vec::new();
        for field in ["beginLine", "beginColumn", "endLine", "endColumn"] {
            location.push((text(self, field), Value::Int(0)));
        }
        let module = Value::Str(text(self, "--TLA+ BUILTINS--"));
        location.push((text(self, "module"), module));
        let name = Value::Str(text(self, "UnnamedAction"));
        Value::record(vec![
            (text(self, "name"), name),
            (text(self, "location"), Value::record(location)?),
        ])
    }

    // A field of TLCGet("stats") written as TLCGet("stats").field, as TLC checks the assumptions
    // (`AbstractChecker.getStatistics`): none for the time TLC has run, which only TLC knows, or
    // for a field the record doesn't hold, whose failure prints the record.
    fn assumed_statistic(&mut self, record: NodeId, field: TextId) -> Option<Value> {
        let NodeKind::Apply { name, args } = self.kind(record) else {
            return None;
        };
        let Resolution::Builtin(index) = name.resolution else {
            return None;
        };
        let [key] = args.as_slice() else {
            return None;
        };
        if name.is_local
            || self.name(self.ir.builtins[index as usize].name) != "TLCGet"
            || !matches!(self.kind(*key), NodeKind::String(text) if self.name(*text) == "stats")
        {
            return None;
        }
        self.reads += 1;
        match self.name(field) {
            "queue" | "distinct" | "initial" | "generated" | "worker" => Some(Value::Int(0)),
            "diameter" => Some(Value::Int(1)),
            _ => None,
        }
    }

    // An operator's table as `OpRcdValue.toString` prints it, pretty printed: `{ <0, 1>, <2, 3>}`,
    // each row its arguments and then its value.
    fn table_text(&mut self, table: &[(Option<Index>, Option<Index>)]) -> Evaluated<String> {
        let mut rows = Vec::with_capacity(table.len());
        for &(row, value) in table {
            let (Some(row), Some(value)) = (row, value) else {
                return fail("a value of an operator's table the IR can't hold");
            };
            let mut items: Vec<String> = as_tuple(&self.value(row)?)
                .unwrap_or_default()
                .iter()
                .map(format_value)
                .collect();
            items.push(format_value(&self.value(value)?));
            rows.push(format!("<{}>", items.join(", ")));
        }
        let text = format!("{{ {}}}", rows.join(", "));
        Ok(pretty_print(&text.encode_utf16().collect::<Vec<_>>()))
    }

    // The value of the root module's definition TLCEvalDefinition names (`TLCExt.tlcDefByName`):
    // its body evaluated as written, in the states the evaluation is in.
    fn evaluated_definition(&mut self, operand: &Operand, context: &Context) -> Evaluated<Value> {
        let name = self.operand(operand)?;
        let rejected = |expected: &str, shown: String| {
            fail_coded(
                "TLCEvalDefinition of a name TLC finds no definition without parameters of",
                ONE_ARGUMENT_ERROR,
                format!(
                    "The argument of TLCEvalDefinition should be a {expected}, but instead it is:\n{shown}"
                ),
            )
        };
        let text = match &name {
            Value::Str(text) => text,
            Value::Int(_)
            | Value::Bool(_)
            | Value::Model(_)
            | Value::Set(_)
            | Value::Interval(..)
            | Value::Function(_)
            | Value::Lazy(_) => return rejected("string", format_pretty(&name)),
            _ => return fail("TLCEvalDefinition of a value that isn't a string"),
        };
        // `tool.getSpecProcessor()` is null while the SpecProcessor's constructor computes the
        // constant definitions, so TLCEvalDefinition fails there, which `processConstantDefns`
        // swallows.
        if self.is_processing_constants {
            return fail("TLCEvalDefinition as TLC processes the constant definitions");
        }
        let ir = self.ir;
        let found = ir.model.evaluated_definitions.iter().find(|(written, _)| {
            ir.texts[*written as usize]
                .encode_utf16()
                .eq(text.units.iter().copied())
        });
        match found.map(|(_, found)| *found) {
            Some(EvaluatedDefinition::Body(index)) => {
                let node = ir.definitions[index as usize];
                let body = self.definition(node).body;
                self.evaluate_definition(node, body, &context.global())
            }
            Some(EvaluatedDefinition::Signature(signature)) => rejected(
                "a zero-arity definition",
                ir.texts[signature as usize].to_string(),
            ),
            Some(EvaluatedDefinition::Missing) => rejected(
                "name of a definition reachable from the root module",
                format_pretty(&name),
            ),
            None => fail("TLCEvalDefinition of a name the front end didn't look up"),
        }
    }

    pub(crate) fn builtin(
        &mut self,
        index: Index,
        operands: &[Operand],
        context: &Context,
    ) -> Evaluated<Value> {
        let builtin = &self.ir.builtins[index as usize];
        // The operations that force a lazy function their arguments hold (`force_lazy_prints`).
        // Any other leaves a lazy function whose body printed as the evaluator built it where
        // TLC prints its lines later, or never, and declines.
        if builtin.flags & Builtin::TABLE != 0
            || !matches!(
                self.name(builtin.name),
                "Print" | "PrintT" | "ToString" | "=" | "#" | "\\in" | "\\notin" | "@@"
            )
        {
            return self.builtin_value(index, operands, context);
        }
        let outer = self.forcing.replace(Forcing {
            first: self.lazy_print_count,
            printed_at: None,
        });
        let result = self.builtin_value(index, operands, context);
        let forcing = std::mem::replace(&mut self.forcing, outer).expect("the forcing operation");
        // A failure after a print forced a copy, which TLC may meet before it forces it.
        let held = self.lazy_prints_from(forcing.first);
        // Those the arguments built that a print built a copy of TLC printed then, and never
        // forces again.
        let is_held = self.lazy_prints[held..].iter().any(|lazy| !lazy.is_copied);
        if is_held || (forcing.printed_at.is_some() && result.is_err()) {
            self.lazy_prints.truncate(held);
            return fail(LAZY_BODY_EFFECTS);
        }
        self.lazy_prints.truncate(held);
        result
    }

    fn builtin_value(
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
                if builtin.flags & Builtin::TABLE_PHASE_KNOWN == 0 && value.is_none() {
                    return fail("a value of an operator's table the IR can't hold");
                }
                let Some(row) = row else {
                    return fail("a value of an operator's table the IR can't hold");
                };
                let row = self.value(row)?;
                // `OpRcdValue.eval` tests the number of arguments at each row.
                if as_tuple(&row).map(<[Value]>::len) != Some(operands.len()) {
                    return fail_runtime(
                        "an operator's table applied to the wrong number of arguments",
                        format!(
                            "Attempted to apply the operator {}\nwith wrong number of arguments.",
                            self.table_text(&builtin.table)?
                        ),
                    );
                }
                if equals(&row, &arguments)? {
                    let Some(value) = value else {
                        return fail("a value of an operator's table the IR can't hold");
                    };
                    return self.configuration_value(value);
                }
            }
            return fail_runtime(
                "an operator's table applied outside its rows",
                format!(
                    "Attempted to apply operator:\n{}\nto arguments ({}), which is undefined.",
                    self.table_text(&builtin.table)?,
                    as_tuple(&arguments)
                        .unwrap_or_default()
                        .iter()
                        .map(format_value)
                        .collect::<Vec<_>>()
                        .join(", ")
                ),
            );
        }
        let name = self.name(builtin.name);
        if builtin.flags & Builtin::UNINITIALIZED_LITERAL != 0 {
            return Ok(Value::Null);
        }
        if builtin.flags & Builtin::DECLINED != 0 {
            return fail(format!("the builtin {name}"));
        }
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
            "$Nop" => {
                arity(1)?;
                self.operand(&operands[0])?
            }
            // `TLCExt.tlcNoOp`, whose argument `Tool.evalAppl` evaluates before the Java method
            // returns it.
            "TLCNoOp" if builtin.flags & Builtin::EXTERNAL_CLASS == 0 => {
                arity(1)?;
                self.operand(&operands[0])?
            }
            "TRUE" => Value::Bool(true),
            "FALSE" => Value::Bool(false),
            "BOOLEAN" => Value::set(vec![Value::Bool(false), Value::Bool(true)]),
            "Nat" => Value::lazy(Lazy::Nat),
            "Any" => Value::lazy(Lazy::Any),
            "Int" => Value::lazy(Lazy::Int),
            "Real" => Value::lazy(Lazy::Real),
            "STRING" => Value::lazy(Lazy::Strings),
            "=" | "#" => {
                arity(2)?;
                let left = self.operand_unchecked(&operands[0])?;
                let right = self.operand_unchecked(&operands[1])?;
                // `EQ` is `arg1.equals(arg2)`, which forces the first argument (`toFcnRcd`), and
                // the second where the first is a function, tuple or record, which converts it
                // (`TupleValue.equals`, `FcnRcdValue.equals`), or an integer, string, boolean or
                // record, which prints it as it fails.
                let is_right_forced = forces_compared(&left);
                let forced: &[&Value] = if is_right_forced {
                    &[&left, &right]
                } else {
                    &[&left]
                };
                self.force_lazy_prints(Force::Built(forced))?;
                let null_message = if matches!(left, Value::Null) {
                    Some(r#"Cannot invoke "Object.equals(Object)" because "arg1" is null"#)
                } else if matches!(right, Value::Null) {
                    if matches!(left, Value::Int(_) | Value::Str(_) | Value::Bool(_)) {
                        Some(r#"Cannot invoke "Object.toString()" because "obj" is null"#)
                    } else {
                        return fail("a comparison with a null tool value");
                    }
                } else {
                    None
                };
                if let Some(text) = null_message {
                    if self
                        .ir
                        .model
                        .version
                        .is_some_and(|version| self.name(version) == "1.7.4")
                    {
                        return fail("a null literal comparison under a different TLC version");
                    }
                    let mut error = fail_runtime::<Value>(
                        "a primitive equality with a null tool value",
                        text.into(),
                    )
                    .unwrap_err();
                    error.runtime_exception = crate::value::RuntimeException::NullPointer;
                    return Err(error);
                }
                // The comparison enumerates a filter TLC keeps lazy, the left first. A lazy set
                // on the left converts itself (`convertAndCache`) before it reads the right, but
                // where both are of a class that compares their parts.
                let left = self.settle(&left)?;
                if let (Value::Lazy(own), other) = (&left, &right)
                    && !own.is_overridden()
                    && !matches!(other, Value::Lazy(other)
                        if crate::value::is_same_construction(own, other))
                {
                    elements(&left)?;
                }
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
                let written_left = name != "\\cup"
                    && self.written_mixed_scalars(&operands[0])
                    && self.direct_named_infinite(&operands[1]);
                let written_right = name == "\\cap"
                    && self.direct_named_infinite(&operands[0])
                    && self.written_mixed_scalars(&operands[1]);
                let left = self.operand(&operands[0])?;
                let right = self.operand(&operands[1])?;
                if written_left || written_right {
                    let (written, tested) = if written_left {
                        (&left, &right)
                    } else {
                        (&right, &left)
                    };
                    if let Value::Unsorted(values) = written {
                        for value in values.iter() {
                            self.member(value, tested)?;
                        }
                    }
                    return fail("a mixed scalar set tested against an infinite set");
                }
                // `Reducible.cap` and `diff` test the elements of the reducible operand, the
                // receiver, in the other.
                let was_frozen = self.is_frozen();
                let combined = match name {
                    "\\cup" => union(&left, &right),
                    "\\cap" => intersection(&left, &right, &mut filter_test(self)),
                    _ => difference(&left, &right, &mut filter_test(self)),
                };
                if combined.is_err() {
                    let receiver = if name == "\\cap" && !crate::sets::is_reducible(&left) {
                        &right
                    } else {
                        &left
                    };
                    self.fingerprint_frozen(receiver, was_frozen);
                }
                combined?
            }
            "SUBSET" => {
                arity(1)?;
                let printed_subset = std::mem::take(&mut self.printed_subset);
                let base = self.operand(&operands[0])?;
                if !base.is_set() && !matches!(base, Value::Unsorted(_)) {
                    if printed_subset {
                        self.printed_subset_base = Some(base);
                    }
                    return fail(SUBSET_NON_SET);
                }
                Value::lazy(Lazy::Subset(base))
            }
            // `UnionValue.union`: a set enumeration of set enumerations TLC unions at once, in the
            // order it holds them, keeping an element only where `equals` finds no earlier one
            // equal, and holds the result as a set enumeration it hasn't normalized. Any other
            // UNION it keeps lazy.
            "UNION" => {
                arity(1)?;
                let sets = self.operand(&operands[0])?;
                let class_is_known = crate::value::set_dispatch_is_known(&sets)
                    && match &sets {
                        Value::Set(inner) | Value::Unsorted(inner) => {
                            inner.iter().all(crate::value::set_dispatch_is_known)
                        }
                        _ => true,
                    };
                // `UnionValue.union` combines a set enumeration of set enumerations at once, as
                // they hold their elements, normalized or not, which it doesn't normalize: one
                // TLC fails to normalize is a set enumeration too. TLC tests each set the
                // enumeration holds, duplicates included, as it was written.
                let is_enumeration = |set: &Value| match set {
                    Value::Set(_) => true,
                    Value::Unsorted(_) => crate::value::has_java_set_representation(set),
                    _ => false,
                };
                let as_held = |set: &Value| match set {
                    Value::Unsorted(elements) => Ok(elements.to_vec()),
                    _ => held_order(set),
                };
                let is_combined = match &sets {
                    Value::Set(inner) => unnormalized(&sets)
                        .unwrap_or_else(|| inner.to_vec())
                        .iter()
                        .all(is_enumeration),
                    Value::Unsorted(inner) => {
                        is_enumeration(&sets) && inner.iter().all(is_enumeration)
                    }
                    _ => false,
                };
                let union = match &sets {
                    Value::Set(_) | Value::Unsorted(_) if is_combined => {
                        // Past `TLCGlobals.setBound` elements in all, whether TLC keeps too many
                        // depends on which it finds held, which the evaluator, testing each
                        // against those kept, doesn't follow in time.
                        let held_size = |set: &Value| match set {
                            Value::Set(inner) => {
                                unnormalized(set).map_or(inner.len(), |held| held.len())
                            }
                            Value::Unsorted(elements) => elements.len(),
                            _ => 0,
                        };
                        let total: usize = match &sets {
                            Value::Set(inner) => unnormalized(&sets)
                                .unwrap_or_else(|| inner.to_vec())
                                .iter()
                                .map(held_size)
                                .sum(),
                            Value::Unsorted(inner) => inner.iter().map(held_size).sum(),
                            _ => 0,
                        };
                        if total > tla_values::SET_BOUND {
                            return fail(
                                "a UNION of set enumerations past TLCGlobals.setBound elements",
                            );
                        }
                        let mut kept: Vec<Value> = Vec::new();
                        for set in as_held(&sets)? {
                            for element in as_held(&set)? {
                                let mut is_kept = false;
                                for earlier in &kept {
                                    if equals(earlier, &element)? {
                                        is_kept = true;
                                        break;
                                    }
                                }
                                if !is_kept {
                                    push_set_element(&mut kept, element)?;
                                }
                            }
                        }
                        self.held_set(kept)?
                    }
                    _ => {
                        // Of a value that isn't a set, TLC's `UnionValue` too is lazy, and fails
                        // as the evaluator's does, whichever enumeration meets it first.
                        if is_enumerable(&sets) && !is_vacuous_union(&sets) {
                            self.lazy_unions += 1;
                        }
                        Value::lazy(Lazy::Union(sets))
                    }
                };
                if class_is_known {
                    union
                } else {
                    union.without_set_provenance()
                }
            }
            "DOMAIN" => {
                arity(1)?;
                // `RecordValue.getDomain` and `TupleValue.getDomain` read none of the values, so
                // a record or tuple constructor written in place may hold a null TLC never
                // initialized.
                let function = if matches!(&operands[0], Operand::Node(node, _)
                    if matches!(self.kind(*node), NodeKind::Record(_) | NodeKind::Tuple(_)))
                {
                    let function = self.operand_unchecked(&operands[0])?;
                    if self.has_uninitialized_literals
                        && crate::value::contains_uninitialized(&function)
                        && !matches!(&function, Value::Function(inner)
                        if matches!(inner.java_class.get(), Some(Class::Record | Class::Tuple))
                            && !inner.domain.iter().any(crate::value::contains_uninitialized)
                            && inner.range.iter().all(|value| {
                                matches!(value, Value::Null)
                                    || !crate::value::contains_uninitialized(value)
                            }))
                    {
                        return fail(
                            "a null tool value used by a consumer the replay does not model",
                        );
                    }
                    function
                } else {
                    self.operand(&operands[0])?
                };
                if let Value::Function(inner) = &function
                    && self.kept_lazy.contains(&(Rc::as_ptr(inner) as usize))
                {
                    self.lazy_domains += 1;
                }
                match function {
                    // `FcnLambdaValue.getDomain`: its domain, whatever the EXCEPTs.
                    Value::Lambda(lambda) if lambda.params.is_none() => lambda.domain.clone(),
                    // Of several parameters, a new `SetOfTuplesValue` of the domain of each, but
                    // of a tuple pattern, the domain it bounds, the one parameter's domain.
                    Value::Lambda(lambda) => match &lambda.domain {
                        Value::Lazy(lazy) if let Lazy::Product(domains) = &***lazy => {
                            Value::lazy(Lazy::Product(domains.clone()))
                        }
                        domain => domain.clone(),
                    },
                    Value::Function(function) => {
                        let class_is_known = matches!(
                            function.java_class.get(),
                            Some(Class::Plain | Class::Tuple | Class::Record)
                        );
                        let domain = match function.interval {
                            Some((low, high)) => Value::interval(low, high),
                            // `RecordValue.getDomain` makes a string of each field's name.
                            None if function.class.get() == Class::Record => Value::set(
                                function
                                    .domain
                                    .iter()
                                    .map(|key| match key {
                                        Value::Str(name) => Value::Str(Rc::new(Text {
                                            units: name.units.clone(),
                                            rank: name.rank,
                                        })),
                                        _ => key.clone(),
                                    })
                                    .collect(),
                            ),
                            // A function TLC keeps lazy has the set its constructor bound for
                            // its domain (`FcnLambdaValue.getDomain`), which may be one TLC keeps
                            // lazy and builds past `TLCGlobals.setBound` elements where it
                            // enumerates it; the evaluator holds it built.
                            None if function.domain.len() > tla_values::SET_BOUND => {
                                return fail(
                                    "a DOMAIN of more than TLCGlobals.setBound elements TLC may hold lazy",
                                );
                            }
                            None => Value::set(function.domain.clone()),
                        };
                        // `RecordValue.getDomain` holds the names as the record holds them:
                        // unnormalized, in the order written, where the record is, as one
                        // `Tool`'s OPCODE_rc just built is (`new RecordValue(.., false)`), and a
                        // membership in it then asks each name whether it `equals` the value
                        // (`ValueVec.search`). The evaluator knows that only of a record
                        // constructor written in place there.
                        if function.class.get() == Class::Record
                            && matches!(&operands[0], Operand::Node(node, _)
                                if matches!(self.kind(*node), NodeKind::Record(_)))
                            && let Value::Set(names) = &domain
                        {
                            let written = match &*function.written.borrow() {
                                Some(positions) => positions
                                    .iter()
                                    .map(|&position| names[position as usize].clone())
                                    .collect(),
                                None => names.to_vec(),
                            };
                            crate::value::mark_unnormalized(&domain, written);
                        }
                        if class_is_known {
                            domain
                        } else {
                            domain.without_set_provenance()
                        }
                    }
                    // `Tool`'s OPCODE_domain, whose message the application ends with where it is.
                    value => match kind_string(&value) {
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
                let [low, high] = self.integer_arguments(builtin, operands)?;
                Value::interval(low as i32, high as i32)
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
                        // The method prints the value (`Values.ppr(y.toString())`): of Integers,
                        // whose GT returns a BoolValue, where TLC loads it over Naturals.
                        if let Some(error) = print_failure(value) {
                            // Either module's method fails so; which one TLC loaded names it.
                            let Some(is_integers) = self.is_integers_loaded() else {
                                return fail(
                                    "a comparison's failing print, of Naturals or Integers",
                                );
                            };
                            let method = match name {
                                "<" => "LT",
                                "<=" => "LE",
                                ">=" => "GEQ",
                                _ => "GT",
                            };
                            let (module, result) = match (is_integers, method) {
                                (true, "GT") => ("Integers", "impl.BoolValue"),
                                (true, _) => ("Integers", "IBoolValue"),
                                (false, _) => ("Naturals", "IBoolValue"),
                            };
                            return as_java_failure(
                                &format!(
                                    "public static tlc2.value.{result} tlc2.module.{module}.{method}(tlc2.value.impl.Value,tlc2.value.impl.Value)"
                                ),
                                Err(error),
                            );
                        }
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
                let [left, right] = self.integer_arguments(builtin, operands)?;
                match name {
                    "+" => {
                        self.arithmetic_integer(Some(left + right), || format!("{left}+{right}"))?
                    }
                    "-" => {
                        self.arithmetic_integer(Some(left - right), || format!("{left}-{right}"))?
                    }
                    "*" => {
                        self.arithmetic_integer(Some(left * right), || format!("{left}*{right}"))?
                    }
                    "\\div" => {
                        if right == 0 {
                            return fail_coded(
                                "division by zero",
                                DIVISION_BY_ZERO,
                                "The second argument of \\div is 0.".into(),
                            );
                        }
                        // `Naturals#Divide` floors only a quotient Java truncates below 0, and
                        // lets -2147483648 \\div -1 wrap.
                        if builtin.flags & Builtin::NATURALS_METHOD != 0 {
                            let (left, right) = (left as i32, right as i32);
                            let quotient = left.wrapping_div(right);
                            let is_floored = quotient < 0 && quotient.wrapping_mul(right) != left;
                            Value::Int(quotient - i32::from(is_floored))
                        } else if left == i64::from(i32::MIN) && right == -1 {
                            return fail_coded(
                                "integer overflow",
                                MODULE_OVERFLOW,
                                "Overflow when computing -2147483648 \\div -1".into(),
                            );
                        } else {
                            int(left.div_euclid(right)
                                - i64::from(right < 0 && left.rem_euclid(right) != 0))?
                        }
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
                        let power = u32::try_from(right)
                            .ok()
                            .and_then(|exponent| left.checked_pow(exponent));
                        self.arithmetic_integer(power, || format!("{left}^{right}"))?
                    }
                    _ => unreachable!("an arithmetic operator"),
                }
            }
            "-." => {
                arity(1)?;
                let [integer] = self.integer_arguments(builtin, operands)?;
                self.arithmetic_integer(Some(-integer), || format!("-{integer}"))?
            }
            // `TLCExt.assertError`: whether evaluating the expression fails with this message.
            "AssertError" => {
                arity(2)?;
                // TLC takes only a string written as the message, and says where any other is
                // written as SANY's `toString` gives it.
                match &operands[0] {
                    Operand::Node(node, _) if matches!(self.kind(*node), NodeKind::String(_)) => {}
                    Operand::Node(node, _) => {
                        let written = (self.ir.nodes.arena[self.resolved(*node) as usize].range)
                            .and_then(|_| self.describe_node(*node));
                        let Some(written) = written else {
                            return fail("AssertError of a message that isn't a string");
                        };
                        return as_java_failure(
                            ASSERT_ERROR,
                            fail_runtime(
                                "AssertError of a message that isn't a string",
                                format!(
                                    "In computing AssertError, a non-string expression ({written}) was used as the err of an AssertError(err, exp)."
                                ),
                            ),
                        );
                    }
                    Operand::Value(_) => {
                        return fail("AssertError of a message that isn't a string");
                    }
                }
                let Some(is_tool) = self.is_tool else {
                    return fail("AssertError, whose messages depend on -tool");
                };
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
                let lazy_domains = self.lazy_domains;
                let set = self.operand_unchecked(&operands[0])?;
                if self.has_uninitialized_literals
                    && crate::value::contains_uninitialized(&set)
                    && !set.is_set()
                    && !matches!(set, Value::Unsorted(_))
                {
                    return fail("a null tool value in a cardinality conversion");
                }
                let original_filter = match &set {
                    Value::Lazy(lazy) if lazy.java_class == Some(SetClass::Predicate) => {
                        match &***lazy {
                            Lazy::Filter(_, predicate) if predicate.filtered().is_none() => {
                                Some(Rc::clone(predicate))
                            }
                            _ => None,
                        }
                    }
                    _ => None,
                };
                // TLC counts the domain it holds lazy by its size, which is the evaluator's.
                if self.is_builtin(&operands[0], "DOMAIN") {
                    self.lazy_domains = lazy_domains;
                }
                // `SetPredValue.size` enumerates a filter TLC keeps lazy. A set of functions with a
                // source that fails to enumerate throws a FingerprintException, no EvalException,
                // which `MethodValue` reports as the method's failure.
                let settled = self.settle(&set);
                let is_set_bound = settled.as_ref().is_err_and(|error| {
                    error.runtime_exception == RuntimeException::WrongInvocation
                });
                let set = if is_set_bound
                    || (settled.is_err()
                        && self.call_stack.as_ref().is_some_and(|stack| {
                            crate::sets::unenumerable_function_set(&set)
                                .is_some_and(|functions| stack.source(&functions).is_some())
                        })) {
                    as_java_failure(CARDINALITY, settled)?
                } else {
                    as_java_runtime_failure(CARDINALITY, settled)?
                };
                // `FiniteSets.Cardinality` counts an `Enumerable` value.
                if !is_enumerable(&set) {
                    // TLC words the failure with the value's text, which sorts each set
                    // enumeration it holds and fails, as the method's failure, where it can't sort
                    // one: the evaluator doesn't follow which fails first.
                    if holds_unsortable(&set) {
                        return fail("Cardinality of a non-set holding a set TLC can't sort");
                    }
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
                    && let Some(error) = crate::value::normalize_unsorted_failure(values)
                {
                    return as_java_runtime_failure(CARDINALITY, Err(error));
                }
                let counted = cardinality(&set);
                let counted = match &counted {
                    Err(EvalError {
                        message: Some(message),
                        ..
                    }) if !message.is_eval_exception => as_java_failure(CARDINALITY, counted),
                    _ => counted,
                };
                let counted = counted?;
                if let (Some(predicate), Value::Set(elements)) = (original_filter, &set) {
                    predicate.cache_conversion(Rc::clone(&elements.elements));
                }
                int(counted as i64)?
            }
            // TLC reports what fails, but an EvalException, as the failure of the Java method
            // `FiniteSets.IsFiniteSet` (`MethodValue.eval`).
            "IsFiniteSet" => {
                arity(1)?;
                // A set enumeration written in place where the spec holds a null TLC never
                // initialized: `Tool`'s OPCODE_se evaluates the elements in order into a
                // `SetEnumValue` it doesn't normalize, reading none of them, and
                // `FiniteSets.IsFiniteSet` asks it `isFinite`, which is TRUE whatever they are.
                if self.has_uninitialized_literals
                    && let Operand::Node(node, context) = &operands[0]
                    && let NodeKind::SetEnumeration(items) = self.kind(*node)
                {
                    let (items, context) = (items.clone(), context.clone());
                    for item in items {
                        self.evaluate(item, &context)?;
                    }
                    return Ok(Value::Bool(true));
                }
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
                Value::lazy(Lazy::Seq(self.operand(&operands[0])?))
            }
            // A string is as long as its characters (`Sequences.Len`).
            "Len" => {
                arity(1)?;
                match self.sequence_operand(&operands[0])? {
                    Value::Str(text) => int(text.units.len() as i64)?,
                    sequence => int(argument_sequence("Len", &sequence)?.len() as i64)?,
                }
            }
            "Head" => {
                arity(1)?;
                let sequence = self.sequence_operand(&operands[0])?;
                match argument_sequence("Head", &sequence)?.first() {
                    Some(head) => head.clone(),
                    None => return empty_sequence("Head"),
                }
            }
            "Tail" => {
                arity(1)?;
                let sequence = self.sequence_operand(&operands[0])?;
                // A string's tail is the string of the characters past its first.
                if let Value::Str(text) = &sequence {
                    if text.units.is_empty() {
                        return empty_sequence("Tail");
                    }
                    return Ok(Value::Str(self.made_text(text.units[1..].into())));
                }
                let elements = argument_sequence("Tail", &sequence)?;
                if elements.is_empty() {
                    return empty_sequence("Tail");
                }
                Value::tuple(elements[1..].to_vec())
            }
            "Append" => {
                arity(2)?;
                let sequence = self.sequence_operand(&operands[0])?;
                let was_unsorted = self
                    .call_stack
                    .as_ref()
                    .is_some_and(|stack| stack.is_unsorted);
                let is_literal_set = matches!(&operands[1], Operand::Node(node, _)
                    if matches!(self.kind(*node), NodeKind::SetEnumeration(items)
                        if items.iter().all(|&item| matches!(self.kind(item),
                            NodeKind::Number(_) | NodeKind::String(_)))));
                let element = self.operand_unchecked(&operands[1])?;
                let converted = evaluating_sequence("Append(s, v)", &sequence);
                // SetEnumValue construction doesn't normalize its literals. If conversion of the
                // first argument fails, Append never uses this second set or asks it to normalize.
                if converted.is_err()
                    && is_literal_set
                    && self.ir.builtins.iter().all(|builtin| {
                        builtin.flags & Builtin::EXTERNAL_CLASS == 0
                            && (!matches!(
                                self.name(builtin.name),
                                "Nat" | "Int" | "STRING" | "Seq"
                            ) || builtin.flags == 0)
                    })
                    && matches!(&element, Value::Unsorted(_))
                    && let Some(stack) = &mut self.call_stack
                {
                    stack.is_unsorted = was_unsorted;
                }
                let mut elements = converted?.to_vec();
                elements.push(element);
                Value::tuple(elements)
            }
            "\\o" => {
                arity(2)?;
                let left = self.sequence_operand(&operands[0])?;
                let right = self.sequence_operand(&operands[1])?;
                if let (Value::Str(left), Value::Str(right)) = (&left, &right) {
                    let units: Box<[u16]> = left
                        .units
                        .iter()
                        .chain(right.units.iter())
                        .copied()
                        .collect();
                    return Ok(Value::Str(self.made_text(units)));
                }
                if matches!(left, Value::Str(_)) {
                    return evaluating_wrong("t \\o s", "string", &right);
                }
                let left_elements = evaluating_sequence("s \\o t", &left)?;
                let right_elements = evaluating_sequence("t \\o s", &right)?;
                // `Sequences.Concat` gives one sequence back where the other is empty.
                if left_elements.is_empty() && right.is_tuple_class() {
                    return Ok(right);
                }
                if right_elements.is_empty() && left.is_tuple_class() {
                    return Ok(left);
                }
                let mut elements = left_elements.to_vec();
                elements.extend(right_elements.iter().cloned());
                Value::tuple(elements)
            }
            // `Sequences.SubSeq` tests the sequence, then each bound is an integer, then each is in
            // the sequence's domain, from the first.
            "SubSeq" => {
                arity(3)?;
                let sequence = self.operand(&operands[0])?;
                let from = self.operand(&operands[1])?;
                let to = self.operand(&operands[2])?;
                // A string slices as the sequence of its characters, and stays a string.
                let length = match &sequence {
                    Value::Str(text) => text.units.len(),
                    _ => sequence_argument("SubSeq", "sequence", &sequence)?.len(),
                } as i64;
                let mut bounds = [0; 2];
                for ((bound, value), position) in
                    bounds.iter_mut().zip([&from, &to]).zip(["second", "third"])
                {
                    let Value::Int(int) = value else {
                        return fail_coded(
                            "SubSeq of a bound that isn't an integer",
                            ARGUMENT_ERROR,
                            format!(
                                "The {position} argument of SubSeq should be a natural number, but instead it is:\n{}",
                                format_pretty(value)
                            ),
                        );
                    };
                    *bound = i64::from(*int);
                }
                let [from, to] = bounds;
                // `EC.TLC_MODULE_ARGUMENT_NOT_IN_DOMAIN`.
                let outside = |position: &str, bound: i64| {
                    fail_coded(
                        "SubSeq outside the sequence's domain",
                        ARGUMENT_NOT_IN_DOMAIN,
                        format!(
                            "The {position} argument of SubSeq must be in the domain of its first argument:\n{}\n, but instead it is\n{bound}",
                            format_pretty(&sequence)
                        ),
                    )
                };
                let range = if from > to {
                    0..0
                } else if from < 1 || from > length {
                    return outside("second", from);
                } else if to > length {
                    return outside("third", to);
                } else {
                    from as usize - 1..to as usize
                };
                match &sequence {
                    Value::Str(text) => Value::Str(self.made_text(text.units[range].into())),
                    _ if from > to => Value::empty_tuple(),
                    _ => Value::tuple(sequence_of(&sequence)?[range].to_vec()),
                }
            }
            "SelectSeq" => {
                arity(2)?;
                let sequence = self.operand(&operands[0])?;
                let test = self.operand_operator(&operands[1])?;
                if sequence_argument("SelectSeq", "sequence", &sequence)?.is_empty() {
                    return Ok(Value::empty_tuple());
                }
                let mut kept = Vec::new();
                for element in sequence_argument("SelectSeq", "sequence", &sequence)? {
                    let tested = self.call_with_values(&test, std::slice::from_ref(element));
                    match as_java_runtime_failure(SELECT_SEQ, tested)? {
                        Value::Bool(true) => kept.push(element.clone()),
                        Value::Bool(false) => {}
                        value => {
                            // `lookup` finds an operator whose body is a number or a string as the
                            // value `processConstants` gave the body, which isn't an `OpValue`.
                            if let Body::Node(body) = test.body
                                && matches!(
                                    self.kind(body),
                                    NodeKind::Number(_) | NodeKind::String(_)
                                )
                            {
                                return fail_coded(
                                    "a SelectSeq test that isn't an operator",
                                    ARGUMENT_ERROR,
                                    format!(
                                        "The second argument of SelectSeq should be a operator, but instead it is:\n{}",
                                        format_pretty(&value)
                                    ),
                                );
                            }
                            // TLC holds a LAMBDA or a definition as an `OpLambdaValue`, which
                            // prints as its name.
                            let name = match &operands[1] {
                                Operand::Node(node, _) => match self.kind(*node) {
                                    NodeKind::Lambda { .. } => Some("LAMBDA".to_string()),
                                    NodeKind::Identifier(name)
                                    | NodeKind::OperatorReference(name)
                                        if !name.is_local =>
                                    {
                                        match name.resolution {
                                            Resolution::Definition(index)
                                                if self
                                                    .definition(self.ir.definitions[index as usize])
                                                    .name
                                                    == name.text =>
                                            {
                                                Some(self.name(name.text).to_string())
                                            }
                                            _ => None,
                                        }
                                    }
                                    _ => None,
                                },
                                Operand::Value(_) => None,
                            };
                            let Some(name) = name.filter(|_| !self.is_literal_body(&test)) else {
                                return fail("a SelectSeq test that isn't a boolean");
                            };
                            return fail_coded(
                                "a SelectSeq test that isn't a boolean",
                                ARGUMENT_ERROR,
                                format!(
                                    "The second argument of SelectSeq should be a boolean-valued operator, but instead it is:\n<Operator {name}>"
                                ),
                            );
                        }
                    }
                }
                Value::tuple(kept)
            }
            // `TLC.SortSeq`: an insertion sort, which moves each element before those it is less
            // than, `Op(element, other)`, from the last sorted on.
            "SortSeq" => {
                arity(2)?;
                let sequence = self.operand(&operands[0])?;
                let less = self.operand_operator(&operands[1])?;
                let elements = sequence_argument("SortSeq", "natural number", &sequence)?;
                // TLC passes an operator whose body is a number or a string as that literal, which
                // isn't an OpValue.
                if let Body::Node(body) = less.body {
                    let literal = match self.kind(body) {
                        NodeKind::Number(int) => Some(Value::Int(*int)),
                        NodeKind::String(text) => Some(Value::Str(self.text(*text))),
                        _ => None,
                    };
                    if let Some(literal) = literal {
                        return fail_coded(
                            "SortSeq of a literal",
                            ARGUMENT_ERROR,
                            format!(
                                "The second argument of SortSeq should be a operator, but instead it is:\n{}",
                                format_pretty(&literal)
                            ),
                        );
                    }
                }
                if self.is_literal_body(&less) {
                    return fail("SortSeq of an operator TLC takes for its body's value");
                }
                let mut sorted: Vec<Value> = Vec::with_capacity(elements.len());
                for element in elements {
                    let mut position = sorted.len();
                    while position > 0 {
                        let pair = [element.clone(), sorted[position - 1].clone()];
                        let compared = self.call_with_values(&less, &pair);
                        match as_java_runtime_failure(SORT_SEQ, compared)? {
                            Value::Bool(true) => position -= 1,
                            Value::Bool(false) => break,
                            other => {
                                return fail_coded(
                                    "a SortSeq comparison that isn't a boolean",
                                    ARGUMENT_ERROR,
                                    format!(
                                        "The second argument of SortSeq should be a boolean function, but instead it is:\n{}",
                                        format_pretty(&other)
                                    ),
                                );
                            }
                        }
                    }
                    sorted.insert(position, element.clone());
                }
                Value::tuple(sorted)
            }
            ":>" => {
                arity(2)?;
                let key = self.operand(&operands[0])?;
                let value = self.operand(&operands[1])?;
                Value::function(vec![key], vec![value], Class::Plain)
            }
            "@@" => {
                arity(2)?;
                let lazy_body_effects_before = self.lazy_body_effects;
                let left_value = self.operand(&operands[0])?;
                let right_value = self.operand(&operands[1])?;
                self.force_lazy_prints(Force::Built(&[&left_value, &right_value]))?;
                let is_order_known = [&left_value, &right_value].iter().all(|value| match value {
                    Value::Function(function) => function_order_is_known(function),
                    _ => true,
                });
                let mut combined = (|| {
                    let left = function_entries(&left_value)?;
                    let right = function_entries(&right_value)?;
                    let Some(left) = left else {
                        if holds_unknown_function_order(&left_value) {
                            return fail(
                                "@@ argument containing a function whose written key order isn't retained",
                            );
                        }
                        check_merge_argument_format(&left_value)?;
                        return module_argument("first", "@@", "function", &left_value);
                    };
                    let Some(right) = right else {
                        if holds_unknown_function_order(&right_value) {
                            return fail(
                                "@@ argument containing a function whose written key order isn't retained",
                            );
                        }
                        check_merge_argument_format(&right_value)?;
                        return module_argument("second", "@@", "function", &right_value);
                    };
                    let mut keys: Vec<Value> = left.iter().map(|(key, _)| key.clone()).collect();
                    let mut values: Vec<Value> = left.into_iter().map(|(_, value)| value).collect();
                    let left_length = keys.len();
                    'right: for (key, value) in right {
                        for own_key in &keys[..left_length] {
                            let is_equal = equals(&key, own_key).map_err(|mut error| {
                                if !is_order_known
                                    || holds_unknown_function_order(&key)
                                    || holds_unknown_function_order(own_key)
                                    || holds_unsorted(&key)
                                    || holds_unsorted(own_key)
                                {
                                    error.message = None;
                                }
                                error
                            })?;
                            if is_equal {
                                continue 'right;
                            }
                        }
                        keys.push(key);
                        values.push(value);
                    }
                    Ok((keys, values))
                })();
                if self.lazy_body_effects != lazy_body_effects_before
                    && let Err(error) = &mut combined
                {
                    error.message = None;
                }
                let (keys, values) = as_java_runtime_failure(COMBINE_FCN, combined)?;
                // TLC keeps the written order of a function of strings, which prints as a record.
                if keys.iter().all(|key| matches!(key, Value::Str(_))) {
                    written_function(keys, values, Class::Plain)?
                } else {
                    // `CombineFcn` builds an unnormalized FcnRcdValue, which `select` searches key
                    // by key in the order it holds them (`selectLinearSearch`): where that order
                    // is the sorted one, as the search of one TLC sorted below 32 keys.
                    let held = keys.clone();
                    let function = sorted_function(keys, values, Class::Plain)?;
                    if let Value::Function(inner) = &function {
                        let is_held_sorted = inner.domain.len() == held.len()
                            && inner
                                .domain
                                .iter()
                                .zip(&held)
                                .all(|(own, key)| equals(own, key).unwrap_or(false));
                        if is_order_known
                            && is_held_sorted
                            && inner.domain.len() < crate::value::BINARY_SEARCH_KEYS
                            && inner.interval.is_none()
                            && inner.search.get() == Search::Unknown
                        {
                            inner.search.set(Search::Sorted);
                        }
                    }
                    function
                }
            }
            // TLC evaluates both arguments, as it does any Java method's, then tests the first.
            "Assert" => {
                arity(2)?;
                // `TLC.Assert` holds only of TRUE: any other value fails as FALSE does.
                let holds = matches!(self.operand(&operands[0])?, Value::Bool(true));
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
                let fresh: Vec<(bool, bool)> = operands
                    .iter()
                    .map(|operand| {
                        (
                            self.fresh_print_difference(operand),
                            self.fresh_filter_print_difference(operand),
                        )
                    })
                    .collect();
                let mut values = Vec::with_capacity(operands.len());
                for operand in operands {
                    let is_subset = name == "PrintT"
                        && operands.len() == 1
                        && self.is_starting
                        && self.is_builtin(operand, "SUBSET");
                    self.printed_subset_base = None;
                    let printed_subset = std::mem::replace(&mut self.printed_subset, is_subset);
                    let value = self.operand(operand);
                    self.printed_subset = printed_subset;
                    match value {
                        Err(error) if is_subset && error.reason == SUBSET_NON_SET => {
                            let Some(base) = self.printed_subset_base.take() else {
                                return Err(error);
                            };
                            return self.print_subset_of_non_set(base);
                        }
                        value => values.push(value?),
                    }
                }
                let expected = if name == "Print" { 2 } else { 1 };
                if values.len() != expected {
                    return fail("an operator applied to the wrong number of arguments");
                }
                if values.iter().any(crate::print::holds_any_expansion) {
                    return fail(ANY_EXPANSION_PRINT);
                }
                // A print evaluated with KeepLazy (as the function of an application, `Tool`'s
                // OPCODE_fa), or a function TLC kept lazy as an operator's argument, holds a
                // `FcnLambdaValue` whose values `deepNormalize` doesn't reach, and whose `apply`
                // builds each value anew: a record among them prints its fields as written, where
                // the evaluator holds them as TLC sorts them, or as an earlier use sorted them.
                // A function constructor written in place, naming nothing but its own binders and
                // builtins, outside KeepLazy, is one TLC builds at this print and prints with each
                // value built anew, as the evaluator holds it (`[v \in SUBSET {0} |-> [a |-> 1,
                // b |-> 2]]` prints its record as written).
                let is_fresh_constructor = self.keeping_lazy == 0
                    && operands.iter().all(|operand| {
                        matches!(operand, Operand::Node(node, context)
                            if matches!(self.kind(*node), NodeKind::FunctionConstruction { .. })
                                && self.is_built_afresh(*node, context))
                    });
                if !is_fresh_constructor
                    && values
                        .iter()
                        .any(|value| holds_inner_record(value, self.keeping_lazy > 0, false))
                {
                    return fail(
                        "printing records in a function TLC may keep lazy, evaluated as the function of an application",
                    );
                }
                // Print returns its second argument, whose lazy functions it prints a copy of too.
                let is_named = matches!(&operands[0], Operand::Node(node, context)
                    if self.names_lazy_functions(*node, context, &mut Vec::new(), 16));
                self.force_lazy_prints(Force::Copied(&values[0], values.get(1), is_named))?;
                let returned = if name == "Print" {
                    Some(values[1].clone())
                } else {
                    None
                };
                let signature = if name == "Print" { PRINT } else { PRINT_T };
                // `deepNormalize` walks a function's values in the order TLC holds its keys,
                // which `CombineFcn` leaves as its operands give them: where two values fail to
                // normalize, the evaluator doesn't know which TLC reaches first.
                if values.iter().any(crate::value::holds_values_out_of_order) {
                    return fail(
                        "printing a function TLC may hold out of order, two of whose values hold sets TLC can't normalize",
                    );
                }
                // TLC deep-normalizes a copy of each value before it prints any (`deepNormalize`),
                // in place, failing at the first set enumeration it can't normalize, before it
                // enumerates a filter or expands a lazy set. Three walks follow it.
                // `print_normalize` follows it where every set's Java class is known, normalizing
                // each set and restoring them after; `deep_normalize` claims the failure of a set
                // TLC can't normalize where it knows the order TLC walks the values in, and
                // nothing from a value it doesn't on; `deep_normalize_print` sorts each set
                // enumeration TLC holds unnormalized that the walk reaches, which TLC's later
                // searches find sorted, and declines where it can't follow the walk. A failure
                // one of the first two claims is TLC's where the other claims the same or nothing;
                // where it claims to have followed every value without one, they disagree, and
                // the print declines. Where `deep_normalize` claims nothing, a failure of
                // `deep_normalize_print` is TLC's only where printing the values fails so too,
                // and its decline where the values hold a set TLC can't normalize leaves the
                // printing to fail as it does.
                let as_print_failure = |error: EvalError| match &error.message {
                    Some(message) if !message.is_eval_exception => {
                        as_java_failure(signature, Err::<(), _>(error)).unwrap_err()
                    }
                    _ => error,
                };
                let normalized: Evaluated<bool> =
                    crate::value::preserving_set_normalization(|| {
                        values.iter().try_fold(true, |is_known, value| {
                            Ok(is_known && crate::value::print_normalize(value)?)
                        })
                    });
                let walked = deep_normalize(&values);
                let disagreement = "a print whose deep normalization the walks disagree on";
                let is_walk_known = match (normalized.clone(), walked) {
                    (Err(normalizing), Err(walking)) => {
                        if normalizing.message != walking.message {
                            return fail(disagreement);
                        }
                        self.print_normalizations.0 += 1;
                        self.print_normalizations.1 = walking.reason.clone();
                        let failed = as_print_failure(normalizing);
                        self.normalized_print_failure = Some(failed.clone());
                        return Err(failed);
                    }
                    (Err(normalizing), Ok(false)) => {
                        let failed = as_print_failure(normalizing);
                        self.normalized_print_failure = Some(failed.clone());
                        return Err(failed);
                    }
                    (Ok(false), Err(walking)) => {
                        self.print_normalizations.0 += 1;
                        self.print_normalizations.1 = walking.reason.clone();
                        return Err(as_print_failure(walking));
                    }
                    (Err(_), Ok(true)) | (Ok(true), Err(_)) => return fail(disagreement),
                    (Ok(_), Ok(is_known)) => is_known,
                };
                let is_normalized = normalized.unwrap_or(false);
                let mut unclaimed_failure = None;
                for value in &values {
                    match deep_normalize_print(value) {
                        Ok(()) => {}
                        Err(error) if !is_walk_known && error.reason == UNFOLLOWED_PRINT => {
                            self.unfollowed_print_normalizations += 1;
                            break;
                        }
                        Err(error) if !is_walk_known => {
                            unclaimed_failure = Some(error);
                            break;
                        }
                        Err(error) => return as_java_failure(signature, Err(error)),
                    }
                }
                let unsettled = values.clone();
                // Print's Java method enumerates a filter TLC keeps lazy as it prints it.
                for (value, fresh) in values.iter_mut().zip(&fresh) {
                    let _settlement_diagnostics =
                        suppress_new_function_diagnostic(!(fresh.0 || fresh.1));
                    self.printing_values += 1;
                    let settled = self.settle(value);
                    self.printing_values -= 1;
                    if settled.is_err() && unclaimed_failure.is_some() {
                        return fail("a printed value whose deep normalization may fail elsewhere");
                    }
                    *value = as_java_runtime_failure(signature, settled)?;
                }
                // PrintT normalizes its argument's copy before it prints it. Print normalizes each
                // of two, which the evaluator settles before, so it is left as it was.
                if name == "PrintT" {
                    as_java_runtime_failure(signature, normalize_printed_parts(&values[0]))?;
                }
                let proven = values.iter().zip(&fresh).all(|(value, fresh)| {
                    (fresh.0 && normalize_simple_print_difference(value))
                        || (fresh.1 && normalize_fresh_filter_difference(value))
                        || crate::value::is_known_cup_print(value)
                });
                let _runtime_diagnostics = suppress_new_function_diagnostic(!proven);
                // TLC prints each value with `toStringUnchecked`, which fails where a lazy set's
                // expansion fails.
                // Of the expansions that fail after `deepNormalize`, the evaluator follows
                // TLC's order only of a union of sets it enumerates without testing membership,
                // and of a set of tuples, records or functions or a SUBSET of such sets
                // (`SetCupValue.toSetEnum`, which collects both enumerations and then normalizes
                // them); a difference or an intersection tests each element of its left side, as
                // TLC streams it, in the other, which the evaluator follows only of a difference
                // of a written set of functions, records or tuples and a written set
                // enumeration, whose deep normalization it proved above (`SetDiffValue`'s
                // Enumerator asks the normalized right side of each element of the left in turn).
                let is_followed_print =
                    is_normalized && (proven || unsettled.iter().all(is_followed_expansion));
                let checked = if is_normalized {
                    crate::value::preserving_set_normalization(|| {
                        for value in &unsettled {
                            if !crate::value::print_normalize(value)? {
                                return fail("a print whose normalization changed as it settled");
                            }
                        }
                        values.iter().try_for_each(check_unchecked)
                    })
                } else {
                    values.iter().try_for_each(check_unchecked)
                };
                if let Some(unclaimed) = unclaimed_failure {
                    let is_same = match &checked {
                        Err(error) => {
                            error.message.as_ref().map(|message| &message.text)
                                == unclaimed.message.as_ref().map(|message| &message.text)
                        }
                        Ok(()) => false,
                    };
                    if !is_same {
                        return fail("a printed value whose deep normalization may fail elsewhere");
                    }
                    self.print_normalizations.0 += 1;
                    self.print_normalizations.1 = unclaimed.reason.clone();
                    return as_java_failure(signature, Err(unclaimed));
                }
                if let Err(EvalError {
                    message: Some(message),
                    ..
                }) = &checked
                    && !message.is_eval_exception
                {
                    let is_followed = proven
                        && name == "PrintT"
                        && values.iter().all(crate::value::is_known_cup_print);
                    let failed = as_java_failure(signature, checked.map(|()| Value::Bool(true)))
                        .map_err(|mut error| {
                            error.is_followed_comparison = is_followed;
                            error
                        });
                    if is_followed_print && let Err(error) = &failed {
                        self.normalized_print_failure = Some(error.clone());
                    }
                    return failed;
                }
                if is_followed_print && let Err(error) = &checked {
                    self.normalized_print_failure = Some(error.clone());
                }
                checked?;
                if self.is_install_read && values.iter().any(holds_install) {
                    return fail("printing TLC's install, where its jar is");
                }
                if values.iter().any(holds_unknown_key) {
                    return fail("printing a key whose letters Unicode's categories decide");
                }
                if let Some(printed_at) =
                    self.forcing.as_ref().and_then(|forcing| forcing.printed_at)
                    && printed_at != self.lazy_effects()
                {
                    return fail(LAZY_BODY_EFFECTS);
                }
                // A record inside a function that prints its fields as written, not as TLC sorts
                // them: the evaluator takes the function for one TLC holds lazily, whose values
                // `deepNormalize` doesn't reach, which it can't tell from one TLC built and
                // normalized, as of an operator's argument printed before it is applied.
                if !is_fresh_constructor && values.iter().any(holds_inner_written_record) {
                    return fail(
                        "printing records in a function TLC may keep lazy, evaluated as the function of an application",
                    );
                }
                self.printed.push(crate::OutputEvent::Print(
                    values.iter().map(format_printed).collect(),
                ));
                returned.unwrap_or(Value::Bool(true))
            }
            // TLCExt's AssertEq, whose TLA+ definition TLC evaluates: where the arguments differ,
            // PrintT("Assertion failed") /\ PrintT(a) /\ PrintT(b) /\ a = b. TLC reports a failure
            // at the positions of that definition, which the IR doesn't hold.
            "AssertEq" => {
                arity(2)?;
                let unfollowed = |_| EvalError {
                    runtime_exception: RuntimeException::Runtime,
                    reason: "a failure within TLCExt's AssertEq".into(),
                    is_set_normalization: false,
                    is_set_reduction: false,
                    is_followed_comparison: false,
                    is_named_normalization: false,
                    message: None,
                };
                // `a # b` evaluates the arguments, which TLC passes lazily, in turn, and then
                // `equals`. Where TLC prints no call stack, in an assumption (`checkAssumptions`
                // evaluates with its plain `Tool`) or a constant definition it swallows the failure
                // of as it starts, a failure there is the one it reports.
                let is_unplaced =
                    self.is_assumption || (self.is_starting && self.call_stack.is_none());
                let placed = |error: EvalError| {
                    if is_unplaced && error.message.is_some() {
                        error
                    } else {
                        unfollowed(error)
                    }
                };
                let left = self.operand(&operands[0]).map_err(placed)?;
                let right = self.operand(&operands[1]).map_err(placed)?;
                if equals(&left, &right).map_err(placed)? {
                    return Ok(Value::Bool(true));
                }
                let message = Value::Str(self.text_of("Assertion failed".encode_utf16().collect()));
                for value in [message, left, right] {
                    let value = self.settle(&value).map_err(unfollowed)?;
                    check_unchecked(&value).map_err(unfollowed)?;
                    if self.is_install_read && holds_install(&value) {
                        return fail("printing TLC's install, where its jar is");
                    }
                    if holds_unknown_key(&value) {
                        return fail("printing a key whose letters Unicode's categories decide");
                    }
                    self.printed
                        .push(crate::OutputEvent::Print(vec![format_printed(&value)]));
                }
                Value::Bool(false)
            }
            // Randomization's TestRandomSetOfSubsets, a definition TLC evaluates as written:
            // where it isn't applied, TLC builds its function, drawing five times
            // (`FcnLambdaValue.toFcnRcd`) from the arguments it evaluates once.
            "TestRandomSetOfSubsets" => {
                arity(3)?;
                if builtin.flags != 0 {
                    return fail("TestRandomSetOfSubsets without default Java method origin");
                }
                if self.ir.may_keep_test_draws_lazy() {
                    return fail("TestRandomSetOfSubsets where TLC may keep its function lazy");
                }
                return self.test_random_set_of_subsets(operands, None);
            }
            "RandomSubsetSet" | "RandomSetOfSubsets" => {
                if name == "RandomSetOfSubsets" && builtin.flags != 0 {
                    return fail("RandomSetOfSubsets without default Java method origin");
                }
                arity(3)?;
                let values = operands
                    .iter()
                    .map(|operand| self.operand(operand))
                    .collect::<Evaluated<Vec<_>>>();
                if self.lazy_body_effects > 0 {
                    return fail("RandomSubsetSet after effects in a function TLC keeps lazy");
                }
                let values = values?;
                let result = self.draw_subset_set(name, &values);
                as_java_runtime_failure(
                    if name == "RandomSetOfSubsets" {
                        RANDOM_SET_OF_SUBSETS
                    } else {
                        RANDOM_SUBSET_SET
                    },
                    result,
                )?
            }
            "RandomElement" | "RandomSubset" => {
                let values = operands
                    .iter()
                    .map(|operand| self.operand(operand))
                    .collect::<Evaluated<Vec<_>>>()?;
                let default_method = builtin.flags == 0;
                // TLC reports what fails in the Java method, but an EvalException, as the method's
                // failure (`MethodValue.eval`), as where its argument's text, or its draw, sorts a
                // set enumeration it can't sort.
                #[allow(clippy::redundant_closure_call)]
                let drawn = (|| -> Evaluated<Value> {
                    if let ("RandomElement", [set]) = (name, values.as_slice()) {
                        crate::random::check_random_element_argument(set)?;
                        if default_method {
                            crate::random::validate_random_element(set)?;
                        }
                    }
                    // `Randomization.RandomSubset` checks its arguments before it draws: a count
                    // that isn't an integer, and a set that isn't a finite `EnumerableValue`, fail.
                    // TLC evaluates a constant definition as it starts and again where it is used
                    // (`processConstantDefns`), which shows what printed before the failure twice,
                    // where the evaluator shows it once: the draw declines there.
                    if let ("RandomSubset", [count, set]) = (name, values.as_slice())
                        && builtin.flags & tla_ir::Builtin::EXTERNAL_CLASS == 0
                        && !self.is_174()
                        && self.printed.is_empty()
                    {
                        let bad = |position, expected, value: &Value| {
                            check_merge_argument_format(value)?;
                            module_argument(position, name, expected, value)
                        };
                        if !matches!(count, Value::Int(_)) {
                            return bad("first", "nonnegative integer", count);
                        }
                        if !is_enumerable(set)
                            || !as_java_runtime_failure(RANDOM_SUBSET, is_finite(set))?
                        {
                            return bad("second", "a finite set", set);
                        }
                    }
                    // A draw is never the same twice, so what reads one isn't cached.
                    self.reads += 1;
                    let is_174 = self.is_174();
                    // `SetEnumValue.getRandomSubset` and `IntervalValue.getRandomSubset` make room
                    // for the subset first, which Java refuses for a negative count, before they draw.
                    if let (
                        "RandomSubset",
                        [Value::Int(count), Value::Set(_) | Value::Interval(..)],
                    ) = (name, values.as_slice())
                        && *count < 0
                        && !is_174
                    {
                        return as_java_failure(
                            RANDOM_SUBSET,
                            fail_runtime("RandomSubset of a negative count", count.to_string()),
                        );
                    }
                    // A draw from an interval with no element fails whatever the generator gives
                    // (`IntervalValue.randomElement` checks its bounds), and so does one from the
                    // empty set written `{}`: `SetEnumValue.randomElement` indexes its vector, which
                    // checks no bound (`ValueVec.elementAt`) but has no room there. A set with no
                    // element TLC builds in a vector with room (`SetPredValue.toSetEnum`) gives
                    // null rather than failing, which fails later or not at all, so a draw whose
                    // first set with no element, of the parts of a set of functions, records or
                    // tuples in the order `TLC.RandomElement` draws them, is any other declines.
                    // Where the evaluator doesn't follow TLC's generator, any generator shows those
                    // failures; a draw that gives an element it doesn't know declines.
                    let is_written_empty = match (values.as_slice(), operands) {
                        ([set], [Operand::Node(node, _)]) => {
                            self.first_empty_draw_is_written(*node, set) == Some(true)
                        }
                        _ => false,
                    };
                    let mut unfollowed = None;
                    if self.random.is_none() && name == "RandomElement" {
                        unfollowed = Some(JavaRandom::seeded(0));
                    }
                    let Some(random) = self.random.as_mut().or(unfollowed.as_mut()) else {
                        return fail(
                            "a random draw where the evaluator doesn't follow TLC's generator",
                        );
                    };
                    Ok(match (name, values.as_slice()) {
                        ("RandomElement", [set]) => {
                            let result = random_element(random, set, default_method);
                            // Whatever the generator, TLC draws null from an empty set it built
                            // with room.
                            if matches!(&result, Err(error)
                                if error.reason == "RandomElement of the empty set" && !is_written_empty)
                            {
                                return fail(
                                    "RandomElement of an empty set TLC may draw null from",
                                );
                            }
                            if unfollowed.is_some() && result.is_ok() {
                                return fail(
                                    "a random draw where the evaluator doesn't follow TLC's generator",
                                );
                            }
                            if default_method {
                                as_java_runtime_failure(RANDOM_ELEMENT, result)?
                            } else {
                                result?
                            }
                        }
                        // TLC 1.7.4 draws a subset's indices another way.
                        ("RandomSubset", [Value::Int(count), set]) if *count >= 0 && !is_174 => {
                            random_subset(random, *count as u64, set)?
                        }
                        _ => return fail(name.to_string()),
                    })
                })();
                let is_174 = self.is_174();
                match &drawn {
                    Err(EvalError {
                        message: Some(message),
                        ..
                    }) if default_method
                        && !is_174
                        && message.code != Some(JAVA_METHOD_FAILED)
                        && !message.is_eval_exception =>
                    {
                        let signature = if name == "RandomElement" {
                            RANDOM_ELEMENT
                        } else {
                            RANDOM_SUBSET
                        };
                        return as_java_failure(signature, drawn);
                    }
                    _ => drawn?,
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
            // _Possible.tla's `_PrintCounts == PrintT(_Counts)`.
            "_PrintCounts" if self.runtime.is_some() => {
                arity(0)?;
                self.reads += 1;
                let counts = &self.runtime.as_ref().expect("the runtime").possible_counts;
                let text = format_printed(counts);
                self.printed.push(crate::OutputEvent::Print(vec![text]));
                Value::Bool(true)
            }
            // _Possible.tla's `_CheckName(name) == LET counts == _Counts IN (name \notin DOMAIN
            // counts \/ counts[name] = 0) => (PrintT(counts) /\ FALSE)`, of a name that is a
            // string, which compares with the counts' names without failing.
            "_CheckName" if self.runtime.is_some() => {
                arity(1)?;
                let name = self.operand(&operands[0])?;
                let Value::Str(name) = name else {
                    return fail("_CheckName of a name that isn't a string");
                };
                self.reads += 1;
                let counts = self
                    .runtime
                    .as_ref()
                    .expect("the runtime")
                    .possible_counts
                    .clone();
                let Some(function) = counts.as_function() else {
                    return fail("_CheckName of counts that aren't a function");
                };
                let count = function
                    .domain
                    .iter()
                    .position(|key| matches!(key, Value::Str(key) if key.units == name.units))
                    .map(|position| &function.range[position]);
                let is_unwitnessed = match count {
                    None => true,
                    Some(Value::Int(count)) => *count == 0,
                    Some(_) => return fail("_CheckName of a count that isn't an integer"),
                };
                if is_unwitnessed {
                    let text = format_printed(&counts);
                    self.printed.push(crate::OutputEvent::Print(vec![text]));
                }
                Value::Bool(!is_unwitnessed)
            }
            "Trace" if self.trace.is_some() => {
                arity(0)?;
                self.reads += 1;
                let prefix = self.trace.as_ref().expect("the trace");
                if !matches!(prefix.context, TraceContext::Printed(_))
                    && builtin.flags & Builtin::EXTERNAL_CLASS != 0
                {
                    return fail("Trace with an unproven Java method origin");
                }
                match prefix.context {
                    TraceContext::Printed(length) | TraceContext::WorkerPrefix(length) => {
                        Value::tuple(prefix.records[..length].to_vec())
                    }
                    TraceContext::WorkerUnrecorded { workers } => {
                        return fail_with(
                            "Trace of a worker state without a trace record",
                            TlcMessage {
                                text: format!(
                                    "Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.impl.TupleValue tlc2.module.TLCExt.getTrace(tlc2.tool.impl.Tool,tla2sany.semantic.ExprOrOpArgNode[],tlc2.util.Context,tlc2.tool.TLCState,tlc2.tool.TLCState,int,tlc2.tool.coverage.CostModel) throws java.io.IOException,\nbut it produced the following error:\nIndex 32767 out of bounds for length {workers}"
                                ),
                                code: Some(JAVA_METHOD_FAILED),
                                is_eval_exception: true,
                                inner: None,
                            },
                        );
                    }
                    TraceContext::Unfollowed => {
                        return fail("Trace reconstructs a worker prefix with unfollowed effects");
                    }
                }
            }
            // TLCExt's Trace in the initial predicate, and in an assumption and a POSTCONDITION,
            // which TLC evaluates in a state whose variables are all unassigned: TLC fails where
            // a variable is unassigned, before it reads the checker, and gives the state's record
            // otherwise.
            "Trace"
                if self.is_initial_walk
                    || self.is_assumption
                    || (self.runtime.is_some() && !self.ir.variables.is_empty()) =>
            {
                arity(0)?;
                self.reads += 1;
                let mut names: Vec<&str> = (0..self.ir.variables.len())
                    .filter(|&variable| !self.is_initial_walk || self.current[variable].is_none())
                    .map(|variable| &*self.ir.texts[self.ir.variables[variable] as usize])
                    .collect();
                if names.is_empty() {
                    let fields = self
                        .ir
                        .tlc_order
                        .iter()
                        .map(|&variable| {
                            let name =
                                &self.ir.texts[self.ir.variables[variable as usize] as usize];
                            (
                                self.text_of(name.encode_utf16().collect()),
                                self.current[variable as usize]
                                    .clone()
                                    .expect("an assigned variable"),
                            )
                        })
                        .collect();
                    return Ok(Value::tuple(vec![Value::record(fields)?]));
                }
                names.sort_unstable();
                let inner = TlcMessage {
                    text: format!(
                        "In evaluating TLCExt!Trace, the state is not completely specified yet (variable{} {} undefined).",
                        if names.len() > 1 { "s" } else { "" },
                        names.join(", ")
                    ),
                    code: Some(1000),
                    is_eval_exception: false,
                    inner: None,
                };
                return fail_with(
                    "Trace in a state whose variables are unassigned",
                    TlcMessage {
                        text: format!(
                            "Attempted to apply the operator overridden by the Java method\npublic static tlc2.value.impl.TupleValue tlc2.module.TLCExt.getTrace(tlc2.tool.impl.Tool,tla2sany.semantic.ExprOrOpArgNode[],tlc2.util.Context,tlc2.tool.TLCState,tlc2.tool.TLCState,int,tlc2.tool.coverage.CostModel) throws java.io.IOException,\nbut it produced the following error:\n{}",
                            inner.text
                        ),
                        code: Some(JAVA_METHOD_FAILED),
                        is_eval_exception: false,
                        inner: Some(Box::new(inner)),
                    },
                );
            }
            "CounterExample" => {
                arity(0)?;
                self.reads += 1;
                match &self.runtime {
                    Some(runtime) => runtime.counter_example.clone(),
                    None => Value::counter_example(
                        ["action", "state"]
                            .into_iter()
                            .map(|name| {
                                (self.counterexample_field(name, false), Value::empty_set())
                            })
                            .collect(),
                    )?,
                }
            }
            // The states of a CounterExample as a sequence, each at its number
            // (`CounterExample.toTrace`).
            "ToTrace" => {
                arity(1)?;
                let counter_example = self.operand(&operands[0])?;
                let key = Value::Str(self.text_of("state".encode_utf16().collect()));
                let states = match &counter_example {
                    Value::Function(record) if record.is_counter_example.get() == Some(true) => {
                        match find_key(record, &key)? {
                            Some(position) => record.range[position].clone(),
                            None => return fail("ToTrace of a CounterExample without states"),
                        }
                    }
                    Value::Function(record) if record.is_counter_example.get().is_none() => {
                        return fail(
                            "ToTrace of a value whose CounterExample origin was not retained",
                        );
                    }
                    value => return to_trace_argument_error(value),
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
            "ToJson" | "ToJsonArray" | "ToJsonObject" => {
                arity(1)?;
                if builtin.flags & Builtin::PINNED_STANDARD_SOURCES == 0 {
                    return fail("a Json conversion without a proved standard source prefix");
                }
                if builtin.flags & Builtin::EXTERNAL_CLASS != 0 {
                    return fail("a Json conversion without its packaged Java implementation");
                }
                let value = self.operand_unchecked(&operands[0])?;
                self.json_conversion(name, &value)?
            }
            // The Json module's Java methods, whose arguments TLC evaluates first, as their failure
            // shows; reading and writing the files is the engine's, and the replay words only
            // the failures it finds.
            "JsonSerialize" | "ndJsonSerialize" | "JsonDeserialize" | "ndJsonDeserialize" => {
                arity(if name.ends_with("Serialize") { 2 } else { 1 })?;
                let mut values = Vec::with_capacity(operands.len());
                for operand in operands {
                    values.push(self.operand(operand)?);
                }
                if builtin.flags & (Builtin::TABLE | Builtin::DECLINED | Builtin::EXTERNAL_CLASS)
                    != 0
                {
                    return fail(format!("{name} without its packaged Java implementation"));
                }
                self.json_file_failure(name, &values)?;
                return fail(format!(
                    "{name}, whose file the replay doesn't read or write"
                ));
            }
            // TLC's TLCEval is an @Evaluation method that evaluates its argument itself, and
            // reports its failure as its own, which TLC 1.7.4's Java override didn't.
            "TLCEval" => {
                arity(1)?;
                // TLCEval's `convert` builds a function constructor written as its argument
                // (`FcnLambdaValue.toFcnRcd`), as `Tool` does unless it keeps it lazy, which first
                // counts its domains in order (`FcnParams.size`): a set enumeration TLC can't sort
                // fails there, as its `normalize` does. In an assumption, whose failure TLC
                // reports without frames, the evaluator, which declines such a function over a
                // set it can't sort (`UNSORTED_LAZY_DOMAIN`, `UNSORTED_DOMAIN`), counts the
                // domains instead; elsewhere TLC's FingerprintException of the function's source
                // isn't followed. An argument of constant level in an empty `Context`
                // (`tlcEvalConst`) TLC evaluates without the control of TLCEval's application
                // (`EvalControl.KeepLazy`), so it builds each function constructor in it as well:
                // the evaluator evaluates it again so, keeping none lazy.
                let retried = match &operands[0] {
                    Operand::Node(node, inner)
                        if self.is_assumption
                            && !crate::split::may_have_effect(self, *node, &mut HashSet::new()) =>
                    {
                        let bounds = match self.kind(*node) {
                            NodeKind::FunctionConstruction {
                                is_recursive: false,
                                bounds,
                                ..
                            } => Some(bounds.clone()),
                            _ => None,
                        };
                        let is_constant = inner.held() == Held::Empty
                            && !self.can_read(*node, inner)
                            && !self.get_substituted_nodes().contains(node);
                        (bounds.is_some() || is_constant)
                            .then(|| (bounds, *node, inner.clone(), self.call_stack.clone()))
                    }
                    _ => None,
                };
                let value = match self.operand(&operands[0]) {
                    Err(error)
                        if error.reason == UNSORTED_LAZY_DOMAIN
                            || error.reason == UNSORTED_DOMAIN =>
                    {
                        match retried {
                            Some((Some(bounds), _, inner, call_stack)) => {
                                self.call_stack = call_stack;
                                match self.counted_domains_failure(&bounds, &inner)? {
                                    Some(failure) => Err(failure),
                                    None => Err(error),
                                }
                            }
                            Some((None, node, inner, call_stack))
                                if (error.reason == UNSORTED_LAZY_DOMAIN
                                    && self.keeping_lazy > 0)
                                    || error.reason == UNSORTED_DOMAIN =>
                            {
                                self.call_stack = call_stack;
                                let keeping_lazy = std::mem::take(&mut self.keeping_lazy);
                                let builds =
                                    std::mem::replace(&mut self.builds_unsorted_domains, true);
                                let value = self.operand(&Operand::Node(node, inner));
                                self.builds_unsorted_domains = builds;
                                self.keeping_lazy = keeping_lazy;
                                value
                            }
                            _ => Err(error),
                        }
                    }
                    value => value,
                };
                let value = value.and_then(|value| {
                    // TLCEval.convert calls RecordValue.toFcnRcd, which does not retain
                    // the Java CounterExample subclass.
                    if let Value::Function(function) = &value
                        && function.is_counter_example.get() == Some(true)
                    {
                        return sorted_function(
                            function.domain.clone(),
                            function.range.clone(),
                            Class::Plain,
                        );
                    }
                    Ok(value)
                });
                if self.is_174() && value.as_ref().is_ok_and(holds_unsorted_deep) {
                    return fail("TLCEval of a value holding a set TLC can't normalize, in 1.7.4");
                }
                if self.is_174() {
                    value?
                } else {
                    // `TLCEval.convert` enumerates a set TLC keeps lazy (`toSetEnum`), which fails
                    // where TLC can't enumerate it, as the Java method's failure. Where the
                    // enumeration is TLC's, the evaluator keeps the lazy set, which answers as it
                    // does; an operand that may have an effect isn't enumerated twice.
                    let is_enumerated = match &operands[0] {
                        Operand::Node(node, _) => {
                            !crate::split::may_have_effect(self, *node, &mut HashSet::new())
                        }
                        Operand::Value(_) => false,
                    };
                    let is_operand_evaluated = value.is_ok();
                    let converted = value.and_then(|value| {
                        if matches!(value, Value::Interval(low, high, _) if i64::from(high) - i64::from(low) < crate::value::MAXIMUM_INTERVAL as i64) {
                            return Ok(Value::set(elements(&value)?.as_ref().clone()));
                        }
                        if is_enumerated
                            && matches!(&value, Value::Lazy(lazy) if !lazy.is_overridden())
                            && let Err(error) = elements(&value)
                            && error.message.is_some()
                        {
                            return Err(error);
                        }
                        // One whose operand may have an effect, as TLCEvalDefinition's, TLC
                        // enumerates there all the same, failing as the Java method
                        // (`TLCEval(TLCEvalDefinition("D"))` of `D == {1} \cup 2`), where the
                        // evaluator keeps the set lazy.
                        if !is_enumerated
                            && matches!(&value, Value::Lazy(lazy) if !lazy.is_overridden())
                        {
                            return fail(
                                "TLCEval of a set TLC keeps lazy whose operand may have an effect",
                            );
                        }
                        // A function TLC keeps lazy has no set enumeration, and `convert` builds
                        // it (`toFcnRcd`), which fails over a domain TLC can't count.
                        if let Value::Lambda(lambda) = &value {
                            return crate::value::lambda_as_function(lambda);
                        }
                        Ok(value)
                    });
                    // `TLCEval.tlcEval` deep-normalizes the value it converted (`deepNormalize`)
                    // only for an argument of constant level in an empty `Context`
                    // (`tlcEvalConst`): under a bound name, an operator's parameter or a LET
                    // definition it converts the value alone, which fails later, where it is
                    // used. The deep normalization fails at the first set enumeration TLC can't
                    // normalize, as the Java method's failure: the evaluator claims that failure
                    // where `deep_normalize` knows the order TLC walks the value in, and
                    // otherwise declines, as it does where it doesn't know whether TLC's
                    // `Context` is empty.
                    // A copy an INSTANCE with substitutions makes evaluates in the `Context` its
                    // `SubstInNode` conses the substitutes onto, which isn't empty.
                    let held = match &operands[0] {
                        Operand::Node(node, inner) => match inner.held() {
                            Held::Bound => Held::Bound,
                            _ if self.can_read(*node, inner) => Held::Unknown,
                            _ if self.get_substituted_nodes().contains(node) => Held::Unknown,
                            held => held,
                        },
                        Operand::Value(_) => Held::Unknown,
                    };
                    let converted = converted.and_then(|value| {
                        if held == Held::Bound || !holds_unsorted_deep(&value) {
                            Ok(value)
                        } else if held == Held::Unknown {
                            fail(
                                "TLCEval of a value holding a set TLC can't normalize, where TLC \
                                 may or may not normalize it",
                            )
                        } else if deep_normalize(std::slice::from_ref(&value))? {
                            Ok(value)
                        } else {
                            fail(
                                "TLCEval of a value holding a set TLC can't normalize, in an order \
                                 the evaluator doesn't know",
                            )
                        }
                    });
                    // `convert` and `deepNormalize` fail in a method of the value the argument
                    // evaluated to, which has a source in TLC's `CallStackTool` (a constant
                    // definition's too), as a FingerprintException that adds no frames, as it
                    // passes no frame of the call stack.
                    if is_operand_evaluated
                        && converted.is_err()
                        && let Some(stack) = &mut self.call_stack
                        && !stack.is_unsourced
                    {
                        stack.caught_fingerprint = true;
                    }
                    // `EvaluatingValue.eval` of a TLCEval whose argument fails in another
                    // TLCEval fails again on that one's `Assert.fail` (2154 nested in 2154). Where
                    // the inner one caught a FingerprintException, in the initial predicate, a
                    // step, an invariant or a property, TLC reports the error and then never
                    // prints the nested expressions nor exits (`TLCEval(TLCEval(<<1>>[2]))`,
                    // `TLCEval(TLCEval({1, "a"} = {2}))`, `TLCEval(TLCEval({1} \cup 2))`), as
                    // where the inner one is a TLCEvalDefinition, which catches and fails again
                    // alike (`TLCEval(TLCEvalDefinition("D"))` of `D == <<1>>[2]`); one of
                    // a failure without a source (`TLCEval(TLCEval(1 \div 0))`,
                    // `TLCEval(TLCEval(Head(<<>>)))`) it reports as any other.
                    if !self.is_assumption
                        && self
                            .call_stack
                            .as_ref()
                            .is_some_and(|stack| stack.caught_fingerprint)
                        && let Err(EvalError {
                            message: Some(message),
                            ..
                        }) = &converted
                        && message.code == Some(JAVA_METHOD_FAILED)
                        && (message.text.contains(TLC_EVAL) || message.text.contains(DEF_BY_NAME))
                    {
                        return fail(
                            "a TLCEval failing in another TLCEval's caught FingerprintException, \
                             which TLC hangs reporting",
                        );
                    }
                    let result = as_java_failure(TLC_EVAL, converted);
                    if result.is_err() {
                        self.catch_fingerprint();
                    }
                    let value = result?;
                    // `convert` makes a record or a tuple a new `FcnRcdValue` (`toFcnRcd`), which
                    // TLC's `CallStackTool` never gives a source, nor the value `tlcEvalConst`
                    // cached as TLC first evaluated it, before any failure it replays.
                    let value = match &value {
                        Value::Function(function)
                            if function.java_class.get() == Some(Class::Record) =>
                        {
                            sorted_function(
                                function.domain.clone(),
                                function.range.clone(),
                                Class::Plain,
                            )?
                        }
                        _ => value,
                    };
                    let is_tuple = matches!(&value, Value::Function(function)
                        if function.java_class.get() == Some(Class::Tuple));
                    // The value `tlcEvalConst` cached has no source within it either; the
                    // parts of one `convert` made anew keep theirs.
                    if held == Held::Empty {
                        self.unsource_deep(&value);
                    } else if is_tuple {
                        self.unsource(&value);
                    }
                    value
                }
            }
            // `TLC.ToString` prints with `toStringUnchecked`, where what the expansion of a lazy
            // set fails with fails, reported, but an EvalException, as its Java method's.
            "ToString" => {
                arity(1)?;
                let value = self.operand(&operands[0])?;
                let value = if matches!(&value, Value::Lazy(lazy)
                    if lazy.java_class == Some(SetClass::Predicate)
                        && matches!(&***lazy, Lazy::Filter(_, predicate)
                        if predicate.filtered().is_none() && predicate.converted().is_none()))
                {
                    as_java_runtime_failure(TO_STRING, self.settle(&value))?
                } else {
                    value
                };
                if crate::print::holds_any_expansion(&value) {
                    return fail(ANY_EXPANSION_PRINT);
                }
                self.force_lazy_prints(Force::Shown(&value))?;
                // TLC sorts a record's fields in place wherever it compares the record, and
                // shares a LET definition's value and a constant definition's, which it sorts as
                // it starts, between their uses, which the evaluator doesn't follow: a record
                // ToString reaches through one prints as written only where that is its sorted
                // order.
                let is_built_here = match &operands[0] {
                    Operand::Node(node, _) => self.is_built_here(*node),
                    Operand::Value(_) => false,
                };
                if !is_built_here && holds_record_out_of_order(&value) {
                    return fail("ToString of a record TLC may have sorted");
                }
                if self.is_install_read && holds_install(&value) {
                    return fail("ToString of TLC's install, where its jar is");
                }
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
                // TLC's string is the Java text, where a lone surrogate stays one.
                let units: Box<[u16]> = format_units(&value).into();
                Value::Str(self.made_text(units))
            }
            // TLC's empty bag is the empty function (`Bags.EmptyBag`), of a user's module named
            // Bags too.
            "EmptyBag" | "EmptyBag@Bags" => {
                arity(0)?;
                Value::function(Vec::new(), Vec::new(), Class::Plain)
            }
            // The Java methods of `tlc2.module.Bags`, which TLC applies to its arguments' values,
            // BagOfAll's first an operator. What fails in a method but an EvalException fails as
            // the method's failure (`MethodValue.eval`).
            "Warshall" | "Warshall@TransitiveClosure" => {
                arity(1)?;
                // TLC forces what a relation holds lazy as Warshall converts its elements and
                // fingerprints their endpoints, which may print or draw where the evaluator
                // evaluated it before.
                let Operand::Node(node, _) = &operands[0] else {
                    return fail("Warshall of a relation whose evaluation is not proven");
                };
                if crate::split::may_have_effect(self, *node, &mut HashSet::new())
                    || self.applies_local_operator(*node)
                {
                    return fail("Warshall of a relation whose evaluation is not proven");
                }
                let relation = self.operand(&operands[0])?;
                // What fails in the method but an EvalException fails as the method's failure
                // (`MethodValue.eval`), as normalizing the relation does.
                as_method_failure(WARSHALL, self.warshall(&relation))?
            }
            "IsABag" | "BagCardinality" | "BagToSet" | "SetToBag" | "BagUnion" | "BagIn"
            | "CopiesIn" | "\\oplus" | "\\ominus" | "\\sqsubseteq" | "BagOfAll" => {
                let (method, result) = bags_method(name);
                let is_binary = !matches!(
                    name,
                    "IsABag" | "BagCardinality" | "BagToSet" | "SetToBag" | "BagUnion"
                );
                arity(if is_binary { 2 } else { 1 })?;
                let operator = if name == "BagOfAll" {
                    Some(self.operand_operator(&operands[0])?)
                } else {
                    None
                };
                let values = operands[usize::from(operator.is_some())..]
                    .iter()
                    .map(|operand| self.operand(operand))
                    .collect::<Evaluated<Vec<_>>>()?;
                let signature = format!(
                    "public static {result} tlc2.module.Bags.{method}({})",
                    vec!["tlc2.value.impl.Value"; operands.len()].join(",")
                );
                let applied = self.bags(name, operator.as_deref(), &values);
                as_method_failure(&signature, applied)?
            }
            // TLC evaluates SubBag as Bags.tla defines it: every bag of at most a bag's copies of
            // each element (`RSB[B]`), where Biggest's CHOOSE first compares the least count with
            // itself by `>=`.
            "SubBag" => {
                arity(1)?;
                let bag = self.operand(&operands[0])?;
                // The DOMAIN that fails names where Bags.tla applies it, in RSB's domain, which TLC
                // evaluates first: `SUBSET DOMAIN B`.
                let Value::Function(function) = &bag else {
                    let reason = "SubBag of a value that isn't a function";
                    return match kind_string(&bag) {
                        Some(kind) if !matches!(bag, Value::Lambda(_)) && !self.is_174() => {
                            // TLC's call stack holds the frames of Bags.tla's definition.
                            if let Some(stack) = &mut self.call_stack {
                                stack.unfollowed.get_or_insert(STANDARD_MODULE);
                            }
                            fail_runtime(
                                reason,
                                format!(
                                    "Attempted to apply the operator DOMAIN to a non-function\n({kind})\nline 106, col 58 to line 106, col 65 of module Bags"
                                ),
                            )
                        }
                        _ => fail(reason),
                    };
                };
                let Ok(range) = set_of(function.range.clone()) else {
                    return fail("SubBag of a bag whose counts don't compare");
                };
                let range = elements(&range)?;
                if let Some(least) = range.first()
                    && !matches!(least, Value::Int(_))
                {
                    // The >= of Naturals names itself >, and Integers replaces it where TLC loads
                    // Integers, which the IR says only of a >= the spec applies.
                    let Some(geq) = self
                        .ir
                        .builtins
                        .iter()
                        .find(|builtin| self.name(builtin.name) == ">=")
                    else {
                        return fail("SubBag's >=, which may be Naturals' or Integers'");
                    };
                    let shown = if geq.flags & Builtin::NATURALS_GEQ != 0 {
                        ">"
                    } else {
                        ">="
                    };
                    return fail_coded(
                        "expected an integer",
                        ARGUMENT_ERROR_AN,
                        format!(
                            "The first argument of {shown} should be an integer, but instead it is:\n{}",
                            format_pretty(least)
                        ),
                    );
                }
                let mut counts = Vec::with_capacity(function.domain.len());
                for (key, count) in function.domain.iter().zip(&function.range) {
                    let Value::Int(count) = count else {
                        return fail("SubBag of a bag whose counts aren't all integers");
                    };
                    counts.push((key.clone(), *count));
                }
                let Some(biggest) = counts.iter().map(|&(_, count)| count).max() else {
                    return Ok(Value::set(vec![Value::tuple(Vec::new())]));
                };
                if biggest > 0 && counts.iter().all(|&(_, count)| count > 0) {
                    return sub_bags(&counts);
                }
                // A count that isn't positive leaves the bag outside the domain of RSB, the bags
                // of DOMAIN B's subsets with counts in 1..Biggest, which `FcnLambdaValue.apply`
                // prints as a function: each bag's sub-bags of at most B's copies.
                let bounds: Vec<_> = counts
                    .iter()
                    .map(|(key, _)| (key.clone(), biggest))
                    .collect();
                let domain = sub_bags(&bounds)?;
                let domain = elements(&domain)?;
                let mut keys = Vec::with_capacity(domain.len());
                let mut values = Vec::with_capacity(domain.len());
                for point in domain.iter() {
                    let Value::Function(point_function) = point else {
                        return fail("a sub-bag that isn't a function");
                    };
                    let mut point_bounds = Vec::with_capacity(point_function.domain.len());
                    for key in &point_function.domain {
                        for (inner_key, count) in &counts {
                            if equals(key, inner_key)? {
                                point_bounds.push((key.clone(), *count));
                            }
                        }
                    }
                    keys.push(point.clone());
                    values.push(sub_bags(&point_bounds)?);
                }
                return fail_runtime(
                    "SubBag of a bag with a count that isn't positive",
                    format!(
                        "In applying the function\n{},\nthe first argument is:\n{}\nwhich is not in its domain.\n",
                        format_pretty(&sorted_function(keys, values, Class::Lambda)?),
                        format_pretty(&bag)
                    ),
                );
            }
            // The model value of a name (`TLCExt.tlcModelValue`), which compares by the name's
            // rank, as TLC ranks it.
            "TLCModelValue" => {
                arity(1)?;
                match self.operand(&operands[0])? {
                    // TLC fingerprints a model value by the intern number of its name
                    // (`UniqueString.tok`), which TLCFP shows and which seeds a state's draws:
                    // the IR numbers as TLC does only the texts TLC interns first, those of the
                    // configuration's values and those it interns as it starts, up to "@".
                    Value::Str(name)
                        if name.rank >= 0
                            && self.is_fingerprint_shown()
                            && name.rank >= self.ir.get_numbered_rank_count() =>
                    {
                        return fail(
                            "TLCModelValue of a name whose number TLC fingerprints the evaluator doesn't know",
                        );
                    }
                    Value::Str(name) if name.rank >= 0 => Value::Model(name),
                    Value::Str(_) => return fail("TLCModelValue of a name TLC ranks as it runs"),
                    name @ (Value::Int(_)
                    | Value::Bool(_)
                    | Value::Model(_)
                    | Value::Set(_)
                    | Value::Interval(..)
                    | Value::Function(_)
                    | Value::Lazy(_)) => {
                        return fail_coded(
                            "TLCModelValue of a value that isn't a string",
                            ONE_ARGUMENT_ERROR,
                            format!(
                                "The argument of ModelValue should be a string, but instead it is:\n{}",
                                format_pretty(&name)
                            ),
                        );
                    }
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
            // `TLCExt.pickSuccessor`, which fingerprints the successor first: where the state isn't
            // complete, as in an invariant, TLCStateMut.fingerPrint dereferences a variable's
            // missing value. Where it is, TLC asks whether it has seen the state, which the
            // evaluator doesn't know. Under a VIEW or symmetry TLC fingerprints otherwise.
            "PickSuccessor" => {
                arity(1)?;
                let model = &self.ir.model;
                if self.next.iter().all(Option::is_some)
                    || model.view.is_some()
                    || model.startup.symmetry.is_some()
                {
                    return fail("PickSuccessor of a successor TLC fingerprints");
                }
                return as_java_failure(
                    PICK_SUCCESSOR,
                    fail_runtime(
                        "PickSuccessor of a successor TLC fingerprints incomplete",
                        "Cannot invoke \"tlc2.value.IValue.fingerPrint(long)\" because \"minVals[i]\" is null".into(),
                    ),
                );
            }
            // `TLCExt.tlcGetOrDefault`: the register's value, or the default where the key names
            // none or none is set. TLCGetAndSet, TLA+ in TLCExt, then sets the register to
            // Op(oldVal, val) and is oldVal. TLC reports a failure within TLCGetAndSet at the
            // positions of its definition, which the IR doesn't hold.
            "TLCGetOrDefault" | "TLCGetAndSet" => {
                let is_set = name == "TLCGetAndSet";
                arity(if is_set { 4 } else { 2 })?;
                let unfollowed = |error| {
                    if is_set {
                        EvalError {
                            runtime_exception: RuntimeException::Runtime,
                            reason: "a failure within TLCExt's TLCGetAndSet".into(),
                            is_set_normalization: false,
                            is_set_reduction: false,
                            is_followed_comparison: false,
                            is_named_normalization: false,
                            message: None,
                        }
                    } else {
                        error
                    }
                };
                let key = self.operand(&operands[0]).map_err(unfollowed)?;
                let default = self
                    .operand(&operands[operands.len() - 1])
                    .map_err(unfollowed)?;
                self.reads += 1;
                self.register_reads += 1;
                // As TLC processes the spec, before it has made its checker, TLCExt's
                // `tlcGetOrDefault` finds no register for any key, and gives the default.
                let old = match &key {
                    _ if self.is_processing_constants && !is_set => None,
                    Value::Int(index) if *index >= 0 => self
                        .registers
                        .numbered
                        .get(*index as usize)
                        .cloned()
                        .flatten(),
                    Value::Int(_) => return fail("TLCGetOrDefault of a negative number"),
                    key if is_register_name(key) => self.get_named_register(key)?,
                    _ => None,
                }
                .unwrap_or(default);
                // Whether TLC's call stack gives the value a source, which words a failure that
                // compares it, isn't followed.
                if self.call_stack.is_some() && address(&old).is_some() {
                    return fail("a value of TLCGetOrDefault a failure may name the source of");
                }
                if is_set {
                    let operator = self.operand_operator(&operands[1]).map_err(unfollowed)?;
                    let value = self.operand(&operands[2]).map_err(unfollowed)?;
                    let new = self
                        .call_with_values(&operator, &[old.clone(), value])
                        .map_err(unfollowed)?;
                    // TLCSet's own failure, of a key it rejects, after it evaluated Op: TLC words
                    // it as TLCSet does, and an assumption prints no call stack, which would hold
                    // TLCExt's frames.
                    match self.set_register(key, new) {
                        Err(error) if self.is_assumption && error.message.is_some() => {
                            return Err(error);
                        }
                        set => set.map_err(unfollowed)?,
                    }
                }
                old
            }
            // `TLCExt.tlcFingerprint`: TLC's fingerprint of the value, as an int.
            "TLCFP" => {
                arity(1)?;
                let value = self.operand(&operands[0])?;
                // Nat, Int, Real and STRING are `UserValue`s, which inherit `Value.fingerPrint`:
                // it fails naming the value, which has no source here.
                if let Value::Lazy(lazy) = &value
                    && let Some(name) = match &***lazy {
                        Lazy::Nat => Some("Nat"),
                        Lazy::Int => Some("Int"),
                        Lazy::Real => Some("Real"),
                        Lazy::Strings => Some("STRING"),
                        _ => None,
                    }
                {
                    return as_java_failure(
                        FINGERPRINT,
                        fail_runtime(
                            "TLCFP of a value TLC doesn't fingerprint",
                            format!(
                                "TLC has found a state in which the value of a variable contains {name}"
                            ),
                        ),
                    );
                }
                let mut fingerprints =
                    Fingerprints::new(Polynomial::get(self.ir.model.fingerprint_index));
                match crate::fingerprint::state_fingerprint(&mut fingerprints, &[&value]) {
                    Some(fingerprint) => Value::Int(fingerprint as i32),
                    None => return fail("TLCFP of a value the evaluator doesn't fingerprint"),
                }
            }
            // `TLCExt.tlcDefByName`, an `EvaluatingValue`: TLC reports any failure within it,
            // the body's included, as the failure of the Java method.
            "TLCEvalDefinition" => {
                arity(1)?;
                let value = self.evaluated_definition(&operands[0], context);
                self.evaluating_failure(DEF_BY_NAME, value)?
            }
            // `TLCExt.tlcEval2` (`tlc_cache`).
            "TLCCache" => {
                arity(2)?;
                // TLC computes a constant definition as it starts, swallows its failure, and
                // computes it again where it is used (`processConstantDefns`): what printed before
                // a TLCCache that fails then shows twice, where the evaluator shows it once.
                let has_printed = !self.printed.is_empty();
                let cached = self.tlc_cache(operands);
                if has_printed
                    && matches!(
                        &cached,
                        Err(EvalError {
                            message: Some(_),
                            ..
                        })
                    )
                {
                    return fail("a TLCCache failing after a print TLC may show twice");
                }
                cached?
            }
            // `TLCExt.tlcDefer`: TLC's breadth-first search never runs the deferred expression.
            "TLCDefer" => {
                arity(1)?;
                Value::Bool(true)
            }
            // `TLCGetSet.TLCGetEval`, an `EvaluatingValue`: TLC reports any failure within it,
            // its argument's included, as the failure of the Java method.
            "TLCGet" => {
                arity(1)?;
                as_java_failure(TLC_GET_EVAL, self.tlc_get(&operands[0], context))?
            }
            "Permutations" => {
                arity(1)?;
                let set = self.operand(&operands[0])?;
                // `UserValue` inherits Value.toSetEnum, which returns null, as every function
                // does, one TLC keeps lazy too, whose `toString` builds it where it can.
                let is_function = matches!(set, Value::Function(_) | Value::Lambda(_));
                if is_function {
                    self.force_lazy_prints(Force::Shown(&set))?;
                    // The message prints the function, which fails where it holds a set TLC
                    // can't normalize, at a comparison the evaluator doesn't place.
                    if holds_unsorted_deep(&set) {
                        return fail("Permutations of a function holding a set TLC can't print");
                    }
                }
                if is_function
                    || is_non_set(&set)
                    || java_set_class(&set) == Some(SetClass::Overridden)
                {
                    return fail_coded(
                        "Permutations of a value that isn't a set",
                        APPLYING_TO_WRONG_VALUE,
                        format!(
                            "Applying Permutations to the following value,\nwhich is not a finite set:\n{}",
                            format_pretty(&set)
                        ),
                    );
                }
                let elements = as_java_runtime_failure(
                    "public static tlc2.value.impl.Value tlc2.module.TLC.Permutations(tlc2.value.impl.Value)",
                    elements(&set),
                )?;
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

// A lazy filter's test of an element, through its base, as the evaluator makes it
// (`SetPredValue.member`).
fn filter_test<'a, 'ir>(
    evaluator: &'a mut Evaluator<'ir>,
) -> impl FnMut(&Value, &Value, &Predicate) -> Evaluated<bool> + 'a {
    move |element, base, predicate| evaluator.filter_member(element, base, predicate)
}

enum Combined {
    Set(Value),
    Union(Box<Combined>, Box<Combined>),
}

impl Combined {
    // Membership, testing the second operand only where the first one doesn't decide it. TLC
    // combines a union through its set enumeration or interval operand (`Tool`'s OPCODE_cup), so
    // that one is first.
    fn has(&self, evaluator: &mut Evaluator<'_>, element: &Value) -> Evaluated<bool> {
        match self {
            Combined::Set(set) => evaluator.member(element, set),
            Combined::Union(left, right) => {
                // TLC builds the union of two Reducible sets, testing each element of the right
                // one in the left one, and tests the element in the result, which it holds
                // unnormalized (`Reducible.cup`, `SetEnumValue.member`): the union the evaluator
                // builds as TLC holds it.
                if left.is_reducible() && right.is_reducible() {
                    let set = self.reduced()?;
                    return evaluator.member(element, &set);
                }
                let (first, second) = if !left.is_reducible() && right.is_reducible() {
                    (right, left)
                } else {
                    (left, right)
                };
                Ok(first.has(evaluator, element)? || second.has(evaluator, element)?)
            }
        }
    }

    // The union of Reducible sets, as `Tool`'s OPCODE_cup builds it.
    fn reduced(&self) -> Evaluated<Value> {
        match self {
            Combined::Set(set) => Ok(set.clone()),
            Combined::Union(left, right) => union(&left.reduced()?, &right.reduced()?),
        }
    }

    // Whether TLC holds the set as a set enumeration or an interval (`Reducible`), as it holds
    // the union of two.
    fn is_reducible(&self) -> bool {
        match self {
            // A set enumeration TLC fails to normalize is one all the same.
            Combined::Set(set) => is_reducible(set) || matches!(set, Value::Unsorted(_)),
            Combined::Union(left, right) => left.is_reducible() && right.is_reducible(),
        }
    }
}

/// An argument of a builtin: an expression as written, or a value an operator argument is
/// applied to.
pub(crate) enum Operand {
    Node(NodeId, Context),
    Value(Value),
}

// Whether a set (or a function, which the engine counts as a finite set) is finite, without
// enumerating it: a lazy set is when its parts are.
// `isFinite` of TLC's set values: a set of functions, records or tuples is finite where one of
// its finite parts is empty, and `Seq(S)` where S is.
fn is_finite(value: &Value) -> Evaluated<bool> {
    Ok(match value {
        Value::Lazy(lazy) => match &***lazy {
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
                let sets = elements(sets)?;
                for set in sets.iter() {
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
        // `FcnLambdaValue.isFinite`, of a function TLC keeps lazy, built or not.
        Value::Lambda(_) => {
            return fail_runtime(
                "IsFiniteSet of a function",
                format!(
                    "Attempted to check if the function:\n{}\nis a finite set.",
                    format_pretty(value)
                ),
            );
        }
        // A function TLC built (`FcnRcdValue`, `TupleValue`, `RecordValue`) is finite.
        Value::Function(function)
            if function.class.get() == Class::Lambda && function.java_class.get().is_none() =>
        {
            return fail("IsFiniteSet of a function the evaluator doesn't know TLC built");
        }
        Value::Function(function) if function.java_class.get() == Some(Class::Lambda) => {
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
        // `intv.size() == 0`, which fails for an interval of more than 2^31 - 1 elements.
        Value::Interval(low, high, _) => crate::value::interval_size(*low, *high)? == 0,
        Value::Lazy(lazy) => match &***lazy {
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
                let sets = elements(sets)?;
                for (index, inner) in sets.iter().enumerate() {
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

// A value that isn't a set, which TLC prints as the evaluator does: not a `FcnLambdaValue`, which
// TLC prints by building it again.
pub(crate) fn is_non_set(value: &Value) -> bool {
    match value {
        Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::Model(_) => true,
        Value::Function(function) => function.class.get() != Class::Lambda,
        _ => false,
    }
}

// TLC's `getKindString` of a value that isn't a function, whose class the evaluator knows: a
// scalar or a lazy set, but not a set enumeration, which TLC may hold as another class.
fn non_function_kind(value: &Value) -> Option<&'static str> {
    match value {
        Value::Bool(_) => Some("a Boolean value"),
        Value::Int(_) => Some("an integer"),
        Value::Str(_) => Some("a string"),
        Value::Model(_) => Some("a model value"),
        Value::Lazy(lazy) => match &***lazy {
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
pub(crate) fn kind_string(value: &Value) -> Option<&'static str> {
    if value.is_set() || matches!(value, Value::Unsorted(_)) {
        return java_set_class(value).map(|class| match class {
            SetClass::Enumeration => "a set of the form {e1, ... ,eN}",
            SetClass::Interval => "a set of the form i..j",
            SetClass::Overridden => "a special set constant",
            SetClass::Subset => "a set of the form SUBSET S",
            SetClass::Functions => "a set of the form [S -> T]",
            SetClass::Records => "a set of the form [d1 : S1, ... , dN : SN]",
            SetClass::Product => "a cartesian product",
            SetClass::Intersection => "a set of the form S \\cap T",
            SetClass::Cup => "a set of the form S \\cup T",
            SetClass::Difference => "a set of the form S \\ T",
            SetClass::Union => "a set of the form UNION  S",
            SetClass::Predicate => "a set of the form {x \\in S : expr}",
        });
    }
    match value {
        Value::Lambda(_) => Some("a function of the form  [x \\in S |-> expr]"),
        Value::Function(function) => match function.java_class.get() {
            Some(Class::Tuple) => Some("a tuple"),
            Some(Class::Record) => Some("a record"),
            Some(Class::Plain) if function.is_eager_record.get() => {
                Some("a function  of the form (d1 :> e1 @@ ... @@ dN :> eN)")
            }
            _ => None,
        },
        _ => non_function_kind(value),
    }
}

// The text of an argument `FcnLambdaValue.apply` names in its failure, after the function's
// (`Values.ppr(args.toString())`): `SetEnumValue.toString` normalizes a set enumeration first,
// so one TLC fails to normalize fails there, and the evaluator declines one holding such a set
// deeper.
fn printed_argument(value: &Value) -> Evaluated<String> {
    if let Some(error) = print_failure(value) {
        return Err(error);
    }
    if crate::value::holds_unnormalizable_part(value) {
        return fail("a function's argument holding a set TLC fails to normalize");
    }
    Ok(format_pretty(value))
}

// The sequence the argument of Len, Head or Tail must be (`EC.TLC_MODULE_ONE_ARGUMENT_ERROR`).
fn argument_sequence<'v>(name: &str, value: &'v Value) -> Evaluated<&'v [Value]> {
    if let Value::Lambda(lambda) = value {
        let result_type = if name == "Len" { "IntValue" } else { "Value" };
        let signature = format!(
            "public static tlc2.value.impl.{result_type} tlc2.module.Sequences.{name}(tlc2.value.impl.Value)"
        );
        return as_java_runtime_failure(&signature, lambda_as_tuple(lambda));
    }
    match as_tuple(value) {
        Some(elements) => Ok(elements),
        None if let Some(error) = print_failure(value) => {
            let result_type = if name == "Len" { "IntValue" } else { "Value" };
            as_java_failure(
                &format!(
                    "public static tlc2.value.impl.{result_type} tlc2.module.Sequences.{name}(tlc2.value.impl.Value)"
                ),
                Err(error),
            )
        }
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

// A sequence argument of an operator TLC overrides (`EC.TLC_MODULE_ARGUMENT_ERROR`), which
// SortSeq names a natural number. TLC fails otherwise to make a sequence of a function it keeps
// lazy (`FcnLambdaValue.toTuple`).
fn sequence_argument<'v>(name: &str, expected: &str, value: &'v Value) -> Evaluated<&'v [Value]> {
    let signature = || {
        let (module, arguments) = match name {
            "SubSeq" => ("Sequences", 3),
            "SelectSeq" => ("Sequences", 2),
            _ => ("TLC", 2),
        };
        format!(
            "public static tlc2.value.impl.Value tlc2.module.{module}.{name}({})",
            vec!["tlc2.value.impl.Value"; arguments].join(",")
        )
    };
    match (as_tuple(value), value) {
        (Some(elements), _) => Ok(elements),
        // The method's first step is `toTuple`, which fails on a function over a set TLC
        // overrides (`FcnLambdaValue.toTuple`); the evaluator declines any other.
        (None, Value::Lambda(lambda)) => {
            as_java_runtime_failure(&signature(), lambda_as_tuple(lambda)).map_err(|mut error| {
                if error.message.is_none() {
                    error.reason = format!("{name} of a function TLC keeps lazy");
                }
                error
            })
        }
        (None, _) if let Some(error) = print_failure(value) => {
            as_java_failure(&signature(), Err(error))
        }
        (None, _) => fail_coded(
            format!("{name} of a non-sequence"),
            ARGUMENT_ERROR,
            format!(
                "The first argument of {name} should be a {expected}, but instead it is:\n{}",
                format_pretty(value)
            ),
        ),
    }
}

// `EC.TLC_MODULE_APPLY_EMPTY_SEQ`.
fn empty_sequence<T>(name: &str) -> Evaluated<T> {
    fail_coded(
        format!("{name} of the empty sequence"),
        APPLY_EMPTY_SEQ,
        format!("Attempted to apply {name} to the empty sequence."),
    )
}

// `Sequences.Append` and `Sequences.Concat` convert operands in their Java method.
fn evaluating_sequence<'v>(form: &str, value: &'v Value) -> Evaluated<&'v [Value]> {
    match (as_tuple(value), value) {
        (Some(elements), _) => Ok(elements),
        (None, Value::Lambda(lambda)) => {
            as_java_runtime_failure(sequence_method(form), lambda_as_tuple(lambda))
        }
        (None, _) => evaluating_wrong(form, "sequence", value),
    }
}

fn sequence_method(form: &str) -> &'static str {
    if form == "Append(s, v)" {
        "public static tlc2.value.impl.Value tlc2.module.Sequences.Append(tlc2.value.impl.Value,tlc2.value.impl.Value)"
    } else {
        "public static tlc2.value.impl.Value tlc2.module.Sequences.Concat(tlc2.value.impl.Value,tlc2.value.impl.Value)"
    }
}

fn evaluating_wrong<T>(form: &str, expected: &str, value: &Value) -> Evaluated<T> {
    as_java_runtime_failure(sequence_method(form), check_merge_argument_format(value))?;
    fail_coded(
        format!("{form} of a value that isn't a {expected}"),
        MODULE_EVALUATING,
        format!(
            "Evaluating an expression of the form {form} when s is not a {expected}:\n{}",
            format_pretty(value)
        ),
    )
}

// A value a dumped trace writes as it is, without an object of its own to refer back to.
fn is_scalar(value: &Value) -> bool {
    matches!(
        value,
        Value::Bool(_) | Value::Int(_) | Value::Model(_) | Value::Interval(..)
    )
}

fn sequence_of(value: &Value) -> Evaluated<&[Value]> {
    match as_tuple(value) {
        Some(elements) => Ok(elements),
        None => fail(format!("expected a sequence, not {}", format_value(value))),
    }
}

/// `f[x]`: a function applied to a key in its domain.
/// `FcnRcdValue.selectLinearSearch`: a FcnRcdValue of fewer than 32 keys asks each of its keys,
/// in the order it holds them, whether it equals the argument. The order of one key is certain,
/// wherever the evaluator doesn't know TLC's order of more.
fn searches_sorted_linearly(inner: &Function) -> bool {
    inner.search.get() == Search::Sorted
        && inner.interval.is_none()
        && matches!(inner.class.get(), Class::Plain | Class::Lambda)
        && inner.domain.len() < crate::value::BINARY_SEARCH_KEYS
}

fn searches_linearly(inner: &Function) -> bool {
    inner.domain.len() == 1
        && inner.interval.is_none()
        && inner.java_class.get() == Some(Class::Plain)
        && inner.is_eager_record.get()
        && matches!(inner.class.get(), Class::Plain | Class::Lambda)
}

pub fn apply_value(function: &Value, key: &Value) -> Evaluated<Value> {
    let Value::Function(inner) = function else {
        return fail(format!(
            "applied a non-function: {}",
            format_value(function)
        ));
    };
    if searches_linearly(inner) {
        return if equals(&inner.domain[0], key)? {
            applied_value(inner, 0)
        } else {
            fail("applied a function outside its domain")
        };
    }
    match find_key(inner, key)? {
        Some(position) => applied_value(inner, position),
        None => fail("applied a function outside its domain"),
    }
}

// The value a function holds at a key. Where TLC never initialized it, `RecordValue.lookup` gives
// null, which the record takes for a field it lacks, and fails printing itself; a tuple or another
// function passes the null on.
fn applied_value(function: &Function, position: usize) -> Evaluated<Value> {
    let value = &function.range[position];
    if matches!(value, Value::Null) && function.class.get() == Class::Record {
        return fail("applied a record at a field TLC never initialized");
    }
    Ok(value.clone())
}

// `FcnRcdValue.select` of a function TLC holds over an interval (`intv`) fails on a key that isn't
// an integer before it looks it up.
fn integer_domain_failure(function: &Function, key: &Value) -> Evaluated<()> {
    if function.class.get() == Class::Plain
        && function.java_class.get() == Some(Class::Plain)
        && function.interval.is_some()
        && !matches!(key, Value::Int(_))
    {
        return fail_runtime(
            "applied a function over an interval to a non-integer",
            format!(
                "Attempted to apply function with integer domain to the non-integer argument {}",
                format_pretty(key)
            ),
        );
    }
    Ok(())
}

// What `RecordValue.toString` throws printing a record that holds a value TLC never initialized
// (a THEOREM or an ASSUME of an INSTANCE, whose value is null): the NullPointerException of its
// first such field, `r.values[0]` or, past it, `r.values[i]`. `None` for a record without one;
// `Some(None)` where a field before it holds one deeper, whose own `toString` throws otherwise.
pub(super) fn record_null_failure(record: &Value) -> Option<Option<String>> {
    let Value::Function(inner) = record else {
        return None;
    };
    if !crate::value::contains_uninitialized(record) {
        return None;
    }
    // The fields in the order the record holds them unsorted, as it prints.
    let Some(index) = crate::print::print_order(inner, false)
        .into_iter()
        .position(|position| crate::value::contains_uninitialized(&inner.range[position]))
    else {
        return Some(None);
    };
    let position = crate::print::print_order(inner, false)[index];
    Some(matches!(inner.range[position], Value::Null).then(|| {
        format!(
            "Cannot invoke \"tlc2.value.impl.Value.toString(StringBuffer, int, boolean)\" because \"r.values[{}]\" is null",
            if index == 0 { "0" } else { "i" }
        )
    }))
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
        // A record holding a null fails to print, which the caller words where TLC's message is
        // that NullPointerException's.
        (Class::Record, Value::Str(_)) if record_null_failure(function).is_some() => return None,
        (Class::Record, Value::Str(field)) => format!(
            "Attempted to access nonexistent field '{}' of record\n{shown}",
            String::from_utf16_lossy(&field.units)
        ),
        (Class::Record, _) => {
            format!("Attempted to access record by a non-string argument: {shown_key}")
        }
        // `FcnRcdValue.select` of a function TLC built over an interval (`intv`) takes an
        // integer alone.
        (Class::Plain, key)
            if !matches!(key, Value::Int(_))
                && matches!(function, Value::Function(inner) if inner.interval.is_some()) =>
        {
            format!(
                "Attempted to apply function with integer domain to the non-integer argument {shown_key}"
            )
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

/// `EC.TLC_ENCOUNTERED_FORMULA_IN_PREDICATE`.
const ENCOUNTERED_FORMULA_IN_PREDICATE: u32 = 2261;

/// `EC.TLC_MODULE_BAG_UNION1`.
const BAG_UNION1: u32 = 2177;
/// The most sub-bags SubBag builds.
const MAXIMUM_SUB_BAGS: usize = 1 << 20;

// The Java method of a Bags operator, and the class it returns.
fn bags_method(name: &str) -> (&str, &'static str) {
    match name {
        "IsABag" | "BagIn" => (name, "tlc2.value.IBoolValue"),
        "\\sqsubseteq" => ("SqSubseteq", "tlc2.value.IBoolValue"),
        "BagCardinality" | "CopiesIn" => (name, "tlc2.value.impl.IntValue"),
        "\\oplus" => ("BagCup", "tlc2.value.impl.Value"),
        "\\ominus" => ("BagDiff", "tlc2.value.impl.Value"),
        _ => (name, "tlc2.value.impl.Value"),
    }
}

// `MethodValue.eval`: what fails in a Java method, but an EvalException, fails as the method's
// failure.
// `EC.TLC_MODULE_APPLYING_TO_WRONG_VALUE` of Warshall's relation.
fn not_enumerable_relation<T>(relation: &Value) -> Evaluated<T> {
    fail_coded(
        "Warshall of a value that isn't an enumerable set",
        APPLYING_TO_WRONG_VALUE,
        format!(
            "Applying TransitiveClosure to the following value,\nwhich is not an enumerable set:\n{}",
            format_pretty(relation)
        ),
    )
}

// Whether a value is one TLC holds as the evaluator does, at every depth: no set TLC keeps lazy
// or fails to normalize, no function it keeps lazy.
fn is_plain_value(value: &Value) -> bool {
    match value {
        Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::Model(_) | Value::Interval(..) => {
            true
        }
        Value::Set(set) => set.iter().all(is_plain_value),
        Value::Function(function) => {
            function.domain.iter().all(is_plain_value) && function.range.iter().all(is_plain_value)
        }
        Value::Null | Value::Unsorted(_) | Value::Lazy(_) | Value::Lambda(_) => false,
    }
}

// Whether two endpoints of Warshall's are the same node: TLC's `Hashtable` compares two only
// where their fingerprints agree, which values of different kinds' don't.
fn is_same_endpoint(left: &Value, right: &Value) -> Evaluated<bool> {
    let kind = |value: &Value| match value {
        Value::Bool(_) => 0,
        Value::Int(_) => 1,
        Value::Str(_) => 2,
        Value::Model(_) => 3,
        Value::Function(_) => 4,
        _ => 5,
    };
    if kind(left) != kind(right) {
        return Ok(false);
    }
    match equals(left, right) {
        Ok(is_same) => Ok(is_same),
        Err(_) => fail("Warshall of endpoints the evaluator can't tell apart"),
    }
}

fn as_method_failure<T>(signature: &str, result: Evaluated<T>) -> Evaluated<T> {
    match &result {
        Err(EvalError {
            message: Some(message),
            ..
        }) if !message.is_eval_exception => as_java_failure(signature, result),
        _ => result,
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

// `EC.TLC_MODULE_APPLYING_TO_WRONG_VALUE` of a Bags method.
fn wrong_value<T>(name: &str, expected: &str, value: &Value) -> Evaluated<T> {
    // The caller reports it as the method's failure (`as_java_runtime_failure`).
    if matches!(name, "BagCardinality" | "BagToSet")
        && let Some(error) = print_failure(value)
    {
        return Err(error);
    }
    fail_coded(
        format!("{name} of a value that isn't {expected}"),
        APPLYING_TO_WRONG_VALUE,
        format!(
            "Applying {name} to the following value,\nwhich is not {expected}:\n{}",
            format_pretty(value)
        ),
    )
}

// `EC.TLC_MODULE_ARGUMENT_ERROR` of a Java method.
fn module_argument<T>(position: &str, name: &str, expected: &str, value: &Value) -> Evaluated<T> {
    fail_coded(
        format!("{name} of a value that isn't a {expected}"),
        ARGUMENT_ERROR,
        format!(
            "The {position} argument of {name} should be a {expected}, but instead it is:\n{}",
            format_pretty(value)
        ),
    )
}

fn to_trace_argument_error<T>(value: &Value) -> Evaluated<T> {
    as_java_runtime_failure(TO_TRACE, check_merge_argument_format(value))?;
    fail_coded(
        "ToTrace of a value that isn't a CounterExample",
        ONE_ARGUMENT_ERROR,
        format!(
            "The argument of ToTrace should be a CounterExample, but instead it is:\n{}",
            format_pretty(value)
        ),
    )
}

pub(crate) fn check_merge_argument_format(value: &Value) -> Evaluated<()> {
    match value {
        Value::Unsorted(elements) => {
            if elements
                .iter()
                .any(|element| check_merge_argument_format(element).is_err())
            {
                return fail("normalizing an @@ argument whose elements may fail to print");
            }
            Err(unsorted_failure(elements))
        }
        Value::Set(elements) => elements.iter().try_for_each(check_merge_argument_format),
        Value::Function(function) => {
            let integer_keys = function
                .domain
                .iter()
                .all(|key| matches!(key, Value::Int(_)));
            let record_keys = function
                .domain
                .iter()
                .all(|key| matches!(key, Value::Str(_)));
            if holds_unknown_key(value)
                || (!integer_keys && !record_keys && function.written.borrow().is_some())
            {
                return fail("the default formatting of an @@ argument's function keys");
            }
            for position in crate::print::print_order(function, integer_keys) {
                if !integer_keys && !record_keys {
                    check_merge_argument_format(&function.domain[position])?;
                }
                check_merge_argument_format(&function.range[position])?;
            }
            Ok(())
        }
        Value::Lazy(lazy) => match &***lazy {
            Lazy::Nat | Lazy::Int | Lazy::Real | Lazy::Strings | Lazy::Any => Ok(()),
            Lazy::Seq(base) => check_merge_argument_format(base),
            Lazy::Subset(base) => check_finite_argument_format(value, std::iter::once(base)),
            Lazy::Product(factors) => check_finite_argument_format(value, factors),
            Lazy::RecordSet(fields, _) => {
                check_finite_argument_format(value, fields.iter().map(|(_, field)| field))
            }
            // `SetOfFcnsValue.toString` swallows what counting its parts throws, and Nat, Int,
            // Real and STRING throw as they are counted, after an empty domain is ruled out: it
            // writes the parts as they are written.
            Lazy::FunctionSet(domain, range)
                if [domain, range].into_iter().any(is_counted_overridden)
                    && !is_empty(domain).unwrap_or(false) =>
            {
                check_merge_argument_format(domain)?;
                check_merge_argument_format(range)
            }
            Lazy::FunctionSet(domain, range) => {
                check_finite_argument_format(value, [domain, range])
            }
            Lazy::Cup(left, right) if !is_enumerable(left) || !is_enumerable(right) => {
                check_merge_argument_format(left)?;
                check_merge_argument_format(right)
            }
            Lazy::Diff(left, right) if !is_enumerable(left) => {
                check_merge_argument_format(left)?;
                check_merge_argument_format(right)
            }
            Lazy::Cap(left, right) if !is_enumerable(left) && !is_enumerable(right) => {
                check_merge_argument_format(left)?;
                check_merge_argument_format(right)
            }
            _ => fail("the default formatting of a lazy @@ argument"),
        },
        // `FcnLambdaValue.toString` builds the function first (`toFcnRcd`), which fails sizing a
        // domain TLC's module overrides (`FcnParams.size`) before it evaluates the body anywhere:
        // it swallows that and prints the function unbuilt, as the evaluator does.
        Value::Lambda(lambda) if lambda.is_unbuildable() => Ok(()),
        Value::Lambda(_) => fail("the default formatting of a lazy @@ argument"),
        _ => Ok(()),
    }
}

// Nat, Int, Real and STRING, whose `size` fails ("the number of elements in the overridden
// value").
fn is_counted_overridden(value: &Value) -> bool {
    matches!(value, Value::Lazy(lazy) if matches!(&***lazy, Lazy::Nat | Lazy::Int | Lazy::Real | Lazy::Strings))
}

fn check_finite_argument_format<'v>(
    value: &Value,
    parts: impl IntoIterator<Item = &'v Value>,
) -> Evaluated<()> {
    let parts: Vec<&Value> = parts.into_iter().collect();
    if parts
        .iter()
        .any(|part| check_merge_argument_format(part).is_err())
    {
        return fail("the default formatting of a lazy @@ argument");
    }
    // Successful unchecked formatting proves the default expansion without relying on which
    // failures each lazy value swallows before falling back to its symbolic form.
    if check_unchecked(value).is_err() && !is_sized_unexpanded(&parts) {
        return fail("the default formatting of a lazy @@ argument");
    }
    Ok(())
}

// Whether the `toString` of a set of functions, records or tuples, sizing its parts before it
// expands itself (`SetOfFcnsValue.toString` and its siblings), meets a part TLC overrides and
// can't count (`UserValue.size`), every part before it a set enumeration or an interval it sizes
// without effects: it swallows that failure and prints the set unexpanded, its parts as written.
fn is_sized_unexpanded(parts: &[&Value]) -> bool {
    let is_overridden = |part: &Value| {
        matches!(part, Value::Lazy(lazy)
            if matches!(***lazy, Lazy::Nat | Lazy::Int | Lazy::Real | Lazy::Strings))
    };
    parts.iter().any(|part| is_overridden(part))
        && parts
            .iter()
            .all(|part| is_overridden(part) || matches!(part, Value::Set(_) | Value::Interval(..)))
}

// A plain function may already have lost nonstring keys' written order in `sorted_function`.
fn function_order_is_known(function: &Function) -> bool {
    function.class.get() != Class::Plain
        || function.domain.len() < 2
        || function.written.borrow().is_some()
        || function.search.get() == Search::Sorted
        || function.interval.is_some()
}

pub(crate) fn holds_unknown_function_order(value: &Value) -> bool {
    match value {
        Value::Set(_) | Value::Unsorted(_) => value
            .set_items()
            .expect("an enumeration")
            .iter()
            .any(holds_unknown_function_order),
        Value::Function(function) => {
            (!function_order_is_known(function)
                && !function
                    .domain
                    .iter()
                    .all(|key| matches!(key, Value::Int(_))))
                || function.domain.iter().any(holds_unknown_function_order)
                || function.range.iter().any(holds_unknown_function_order)
        }
        Value::Lambda(lambda) => holds_unknown_function_order(lambda.domain()),
        Value::Lazy(lazy) => match &***lazy {
            Lazy::Subset(base) | Lazy::Seq(base) | Lazy::Union(base) | Lazy::Filter(base, _) => {
                holds_unknown_function_order(base)
            }
            Lazy::FunctionSet(left, right)
            | Lazy::Cap(left, right)
            | Lazy::Cup(left, right)
            | Lazy::Diff(left, right) => {
                holds_unknown_function_order(left) || holds_unknown_function_order(right)
            }
            Lazy::Product(factors) => factors.iter().any(holds_unknown_function_order),
            Lazy::RecordSet(fields, _) => fields
                .iter()
                .any(|(_, field)| holds_unknown_function_order(field)),
            _ => false,
        },
        _ => false,
    }
}

// `Value.toFcnRcd`: a function's keys and values in retained written order, or sorted order
// where that isn't retained; `None` for a value that isn't a function. `RecordValue.toFcnRcd` sorts the record, and
// `FcnLambdaValue.toFcnRcd` fails to size a domain TLC overrides.
fn function_entries(value: &Value) -> Evaluated<Option<Vec<(Value, Value)>>> {
    let function = match value {
        Value::Function(function) => function,
        Value::Lambda(lambda) => return lambda_as_function(lambda),
        _ => return Ok(None),
    };
    if function.class.get() == Class::Record {
        function.written.borrow_mut().take();
    }
    let order: Vec<usize> = match &*function.written.borrow() {
        Some(written) => written.iter().map(|&position| position as usize).collect(),
        None => (0..function.domain.len()).collect(),
    };
    Ok(Some(
        order
            .into_iter()
            .map(|position| {
                (
                    function.domain[position].clone(),
                    function.range[position].clone(),
                )
            })
            .collect(),
    ))
}

// Whether each count is a positive integer (`Bags.IsABag`).
fn is_bag(entries: &[(Value, Value)]) -> bool {
    entries
        .iter()
        .all(|(_, count)| matches!(count, Value::Int(count) if *count > 0))
}

// Whether a value holds a set enumeration TLC fails to sort (`SetEnumValue.normalize`).
fn holds_unsortable(value: &Value) -> bool {
    match value {
        Value::Unsorted(elements) => {
            crate::value::normalize_failure(elements).is_some()
                || elements.iter().any(holds_unsortable)
        }
        Value::Set(elements) => elements.iter().any(holds_unsortable),
        Value::Function(function) => function
            .domain
            .iter()
            .chain(&function.range)
            .any(holds_unsortable),
        Value::Lambda(lambda) => {
            holds_unsortable(&lambda.domain)
                || lambda
                    .excepts
                    .iter()
                    .any(|(key, value)| holds_unsortable(key) || holds_unsortable(value))
        }
        Value::Lazy(lazy) => match &***lazy {
            Lazy::Subset(base) | Lazy::Union(base) | Lazy::Filter(base, _) | Lazy::Seq(base) => {
                holds_unsortable(base)
            }
            Lazy::FunctionSet(left, right)
            | Lazy::Cap(left, right)
            | Lazy::Cup(left, right)
            | Lazy::Diff(left, right) => holds_unsortable(left) || holds_unsortable(right),
            Lazy::RecordSet(fields, _) => fields.iter().any(|(_, set)| holds_unsortable(set)),
            Lazy::Product(sets) => sets.iter().any(holds_unsortable),
            Lazy::Nat | Lazy::Int | Lazy::Real | Lazy::Strings | Lazy::Any => false,
        },
        _ => false,
    }
}

// `(IntValue) count` in a Bags method: a count that isn't an integer fails with Java's
// ClassCastException.
fn cast_count(count: &Value) -> Evaluated<i32> {
    if let Value::Int(count) = count {
        return Ok(*count);
    }
    let class = java_value_class(count);
    fail_runtime(
        "a bag's count that isn't an integer",
        format!(
            "class tlc2.value.impl.{class} cannot be cast to class tlc2.value.impl.IntValue (tlc2.value.impl.{class} and tlc2.value.impl.IntValue are in unnamed module of loader 'app')"
        ),
    )
}

// Legacy transfers retain presentation classes; a numeric cast needs proven runtime provenance.
fn numeric_value_class(value: &Value) -> Option<&'static str> {
    if value.is_set() || matches!(value, Value::Unsorted(_)) {
        return java_set_class(value).map(SetClass::java_name);
    }
    if let Value::Function(function) = value {
        return function.java_class.get().map(|class| match class {
            Class::Plain => "FcnRcdValue",
            Class::Lambda => "FcnLambdaValue",
            Class::Tuple => "TupleValue",
            Class::Record => "RecordValue",
        });
    }
    Some(java_value_class(value))
}

// TLC's concrete Java class, retained even where values are mathematically equal.
fn java_value_class(value: &Value) -> &'static str {
    match value {
        Value::Null => "null",
        Value::Int(_) => "IntValue",
        Value::Bool(_) => "BoolValue",
        Value::Str(_) => "StringValue",
        Value::Model(_) => "ModelValue",
        Value::Set(_) | Value::Unsorted(_) => "SetEnumValue",
        Value::Interval(..) => "IntervalValue",
        Value::Lambda(_) => "FcnLambdaValue",
        Value::Function(function) => match function.class.get() {
            Class::Plain => "FcnRcdValue",
            Class::Lambda => "FcnLambdaValue",
            Class::Tuple => "TupleValue",
            Class::Record => "RecordValue",
        },
        Value::Lazy(lazy) => match &***lazy {
            lazy if lazy.is_overridden() => "UserValue",
            Lazy::Subset(_) => "SubsetValue",
            Lazy::FunctionSet(..) => "SetOfFcnsValue",
            Lazy::RecordSet(..) => "SetOfRcdsValue",
            Lazy::Product(_) => "SetOfTuplesValue",
            Lazy::Cap(..) => "SetCapValue",
            Lazy::Cup(..) => "SetCupValue",
            Lazy::Diff(..) => "SetDiffValue",
            Lazy::Union(_) => "UnionValue",
            Lazy::Filter(..) => "SetPredValue",
            _ => unreachable!("an overridden set"),
        },
    }
}

// Adds an element's copies to the counts gathered, as `Bags.BagCup`, `Bags.BagUnion` and
// `Bags.BagOfAll` do: to the count of the first element it equals, both cast to an int, or
// after them.
fn add_copies(counts: &mut Vec<(Value, Value)>, element: Value, copies: Value) -> Evaluated<()> {
    for (key, count) in counts.iter_mut() {
        if equals(&element, key)? {
            let held = cast_count(count)?;
            *count = Value::Int(add_counts(held, cast_count(&copies)?)?);
            return Ok(());
        }
    }
    counts.push((element, copies));
    Ok(())
}

// An element's copies in a bag less those in another, subtracted in an int, as `Bags.BagDiff`
// and `Bags.SqSubseteq` do.
fn remaining_copies(key: &Value, count: &Value, other: &[(Value, Value)]) -> Evaluated<i32> {
    let count = cast_count(count)?;
    for (other_key, removed) in other {
        if equals(key, other_key)? {
            return Ok(count.wrapping_sub(cast_count(removed)?));
        }
    }
    Ok(count)
}

// The bag of the counts gathered, in their order, as TLC builds it before it normalizes it.
fn counted_bag(counts: Vec<(Value, Value)>) -> Evaluated<Value> {
    let (keys, values) = counts.into_iter().unzip();
    written_function(keys, values, Class::Plain)
}

// The bags of at most each element's copies, counts of 1 or more: `<< >>`, and the functions
// Bags.tla's Combine builds.
fn sub_bags(bounds: &[(Value, i32)]) -> Evaluated<Value> {
    let size = bounds.iter().fold(1usize, |size, &(_, count)| {
        size.saturating_mul(count.max(0) as usize + 1)
    });
    if size > MAXIMUM_SUB_BAGS {
        return fail("SubBag of a bag with too many sub-bags to build");
    }
    let mut sub_bags: Vec<Vec<(Value, i32)>> = vec![Vec::new()];
    for (key, count) in bounds {
        let mut grown = Vec::new();
        for sub_bag in &sub_bags {
            for copies in 1..=*count {
                let mut inner_sub_bag = sub_bag.clone();
                inner_sub_bag.push((key.clone(), copies));
                grown.push(inner_sub_bag);
            }
        }
        sub_bags.extend(grown);
    }
    let mut values = Vec::with_capacity(sub_bags.len());
    for sub_bag in sub_bags {
        values.push(if sub_bag.is_empty() {
            Value::tuple(Vec::new())
        } else {
            let (keys, copies) = sub_bag
                .into_iter()
                .map(|(key, copies)| (key, Value::Int(copies)))
                .unzip();
            sorted_function(keys, copies, Class::Lambda)?
        });
    }
    set_of(values)
}

/// The builtins whose evaluation has an effect besides its value, or reads what TLC's search
/// sets: a constant definition that may reach one takes no value from the search's.
const EFFECTS: &[&str] = &[
    "TLCGet",
    "TLCSet",
    "CounterExample",
    "_Counts",
    "_CheckName",
    "_PrintCounts",
    "_Track",
    "Print",
    "PrintT",
    "RandomElement",
    "RandomSubset",
    "RandomSubsetSet",
    "RandomSetOfSubsets",
    "TestRandomSetOfSubsets",
    "JavaTime",
    "JsonSerialize",
    "ndJsonSerialize",
    "JsonDeserialize",
    "ndJsonDeserialize",
    "Serialize",
    "Deserialize",
    "IOExec",
    "IOEnvExec",
    "IOExecTemplate",
    "IOEnvExecTemplate",
    "IOEnv",
];

/// The builtins of `EFFECTS` but those whose effect the startup sees run: Print, PrintT,
/// RandomElement, RandomSubset and TLCSet.
const UNSEEN_EFFECTS: &[&str] = &[
    "TLCGet",
    "CounterExample",
    "_Counts",
    "_CheckName",
    "_PrintCounts",
    "_Track",
    "JavaTime",
    "JsonSerialize",
    "ndJsonSerialize",
    "JsonDeserialize",
    "ndJsonDeserialize",
    "Serialize",
    "Deserialize",
    "IOExec",
    "IOEnvExec",
    "IOExecTemplate",
    "IOEnvExecTemplate",
    "IOEnv",
];

// Whether an element of a set is the value the search chose, by a walk that changes neither:
// `None` where the walk can't tell, or where the element is that value but holds a part that
// evaluating the predicate may change, such as a function's written order or a function TLC
// keeps lazy, which TLC's normalizing of what it computes at startup leaves as it is. A
// function's domain and a set are in TLC's order in both.
fn is_chosen(element: &Value, chosen: &Value) -> Option<bool> {
    let are_chosen = |elements: &[Value], chosen: &[Value]| {
        if elements.len() != chosen.len() {
            return Some(false);
        }
        for (element, chosen) in elements.iter().zip(chosen) {
            if !is_chosen(element, chosen)? {
                return Some(false);
            }
        }
        Some(true)
    };
    match (element, chosen) {
        (Value::Bool(element), Value::Bool(chosen)) => Some(element == chosen),
        (Value::Int(element), Value::Int(chosen)) => Some(element == chosen),
        (Value::Str(element), Value::Str(chosen))
        | (Value::Model(element), Value::Model(chosen)) => Some(element.units == chosen.units),
        (Value::Set(element), Value::Set(chosen)) => are_chosen(element, chosen),
        (Value::Function(element), Value::Function(chosen)) => {
            let is_same = are_chosen(&element.domain, &chosen.domain)?
                && are_chosen(&element.range, &chosen.range)?;
            let is_settled =
                element.written.borrow().is_none() && element.class.get() != Class::Lambda;
            (!is_same || is_settled).then_some(is_same)
        }
        _ => None,
    }
}

// The failures the evaluator words otherwise than TLC wherever they arise: a function TLC keeps
// lazy over a set it doesn't enumerate tested for membership in a set of functions or records,
// which TLC may fail in the set's method (`lambda_as_function_unsure`). Compared or tested for
// equality, it fails as TLC builds it, or makes a tuple of it, as the class of the receiver
// decides (`lambda_as_operand`); where TLC takes `toFcnRcd` itself (`@@`, Bags, a field), it
// fails so. A
// tuple pattern that doesn't match fails in `ContextEnumerator.nextElement` as the walk of the
// set, normalized (`Enumerable.Ordering.NORMALIZED`), reaches it, which the evaluator follows.
fn is_unsure_failure(reason: &str) -> bool {
    reason == crate::value::UNSURE_OVER_OVERRIDDEN
}

// The elements of a set enumeration in the order TLC holds them: as built where it holds the set
// unnormalized, and otherwise normalized.
// A UNION TLC keeps lazy of a set enumeration whose sets, as written, are all set enumerations or
// intervals, all empty but at most one, which TLC holds sorted, as `UNION {{}, 2..1, {1, 2}}`: it
// enumerates as that one set, in its order, without duplicates (`UnionValue.Enumerator`), sizes and
// prints as it, so holding it lazy leaves nothing for TLC's evaluation to do otherwise.
fn is_vacuous_union(sets: &Value) -> bool {
    let Value::Set(inner) = sets else {
        return false;
    };
    let mut nonempty = 0;
    unnormalized(sets)
        .unwrap_or_else(|| inner.to_vec())
        .iter()
        .all(|set| match set {
            Value::Set(elements) if elements.is_empty() => true,
            Value::Interval(low, high, _) if low > high => true,
            Value::Set(_) | Value::Interval(..) => {
                nonempty += 1;
                nonempty == 1 && unnormalized(set).is_none()
            }
            _ => false,
        })
}

fn held_order(set: &Value) -> Evaluated<Vec<Value>> {
    match unnormalized(set) {
        Some(written) => Ok(written),
        None => Ok(elements(set)?.to_vec()),
    }
}

// Whether a thunk's value is the lambda `held_constructor` keeps: the only one over a set
// enumeration or an interval.
fn is_held_constructor(value: &Value) -> bool {
    matches!(value, Value::Lambda(lambda) if is_held_lambda(lambda))
}

// Whether a value holds, below itself, a record of more than one field: anywhere where `is_kept`,
// and otherwise inside a function the evaluator built of a constructor TLC keeps lazy.
fn holds_inner_record(value: &Value, is_kept: bool, is_inner: bool) -> bool {
    match value {
        Value::Function(function) => {
            if is_inner
                && is_kept
                && function.class.get() == Class::Record
                && function.domain.len() > 1
            {
                return true;
            }
            let is_kept = is_kept || is_kept_lazy_build(value);
            function
                .domain
                .iter()
                .chain(&function.range)
                .any(|inner| holds_inner_record(inner, is_kept, true))
        }
        Value::Set(elements) | Value::Unsorted(elements) => elements
            .iter()
            .any(|inner| holds_inner_record(inner, is_kept, true)),
        _ => false,
    }
}

// Whether a value holds, inside a function other than a tuple, a record of more than one field that
// prints its fields as written in an order other than TLC's sorted one (`print_order`).
fn holds_inner_written_record(value: &Value) -> bool {
    fn walk(value: &Value, in_function: bool, depth: u32) -> bool {
        if depth > 64 {
            return true;
        }
        match value {
            Value::Function(function) => {
                let is_record = function.class.get() == Class::Record;
                if in_function
                    && is_record
                    && function.domain.len() > 1
                    && function.written.borrow().as_ref().is_some_and(|written| {
                        written
                            .iter()
                            .enumerate()
                            .any(|(index, &position)| position as usize != index)
                    })
                {
                    return true;
                }
                // A `TupleValue` TLC built as such (a tuple, or what TLC itself builds, as its
                // counterexample) is no function TLC keeps lazy.
                let in_function =
                    in_function || (!is_record && function.java_class.get() != Some(Class::Tuple));
                function
                    .domain
                    .iter()
                    .chain(&function.range)
                    .any(|inner| walk(inner, in_function, depth + 1))
            }
            Value::Set(elements) | Value::Unsorted(elements) => elements
                .iter()
                .any(|inner| walk(inner, in_function, depth + 1)),
            _ => false,
        }
    }
    walk(value, false, 0)
}

fn is_held_lambda(lambda: &Lambda) -> bool {
    lambda.params.is_none()
        && matches!(
            lambda.domain,
            Value::Set(_) | Value::Interval(..) | Value::Unsorted(_)
        )
}

// Whether a value is a function the evaluator built of a constructor TLC keeps lazy
// (`note_kept_lazy`), not yet built into a FcnRcdValue there.
fn is_kept_lazy_build(value: &Value) -> bool {
    matches!(value, Value::Function(function) if function.java_class.get() == Some(Class::Lambda))
}

// The elements of the domain of a function TLC keeps lazy and applies, which it never enumerates:
// a set enumeration it holds unnormalized stays so, and one it would fail to normalize leaves the
// evaluator unable to build the function.
fn held_elements(set: &Value) -> Evaluated<Rc<Vec<Value>>> {
    match crate::value::preserving_set_normalization(|| elements(set)) {
        Err(error) if error.message.is_some() => {
            fail("a function TLC keeps lazy over a set it can't normalize")
        }
        result => result,
    }
}

// Whether a value holds, anywhere within it, a set or a function TLC may keep lazy, which may read
// what it reads only once applied or enumerated.
fn holds_lazy_part(value: &Value) -> bool {
    match value {
        Value::Lambda(_) | Value::Lazy(_) | Value::Null => true,
        Value::Set(set) | Value::Unsorted(set) => set.iter().any(holds_lazy_part),
        Value::Function(function) => {
            function.domain.iter().any(holds_lazy_part)
                || function.range.iter().any(holds_lazy_part)
        }
        Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::Model(_) | Value::Interval(..) => {
            false
        }
    }
}

// Whether TLC may hold a value lazy: a function it builds by its constructor, or a set but Nat,
// Int, Real, STRING and Any.
fn may_be_kept_lazy(value: &Value) -> bool {
    match value {
        Value::Lambda(_) => true,
        Value::Lazy(lazy) => !matches!(
            ***lazy,
            Lazy::Nat | Lazy::Int | Lazy::Real | Lazy::Strings | Lazy::Any
        ),
        _ => false,
    }
}

// Why the replay can't place a union TLC fails to enumerate at once that an operator returned as
// it was, which TLC gave that operator's source (`Tool.setSource`).
const UNION_RESOURCED: &str =
    "a union of a value that isn't a set, given a source again by an operator returning it";

// The unions `UnionValue.elements` fails on at once that a value is, or holds as an element or an
// operand, one level down.
fn direct_failing_unions(value: &Value) -> Vec<Value> {
    if is_failing_union(value) {
        return vec![value.clone()];
    }
    let parts: Vec<&Value> = match value {
        Value::Set(set) | Value::Unsorted(set) => set.iter().collect(),
        Value::Function(function) => function.range.iter().collect(),
        Value::Lazy(lazy) => match &***lazy {
            Lazy::Subset(inner) | Lazy::Seq(inner) | Lazy::Filter(inner, _) => vec![inner],
            Lazy::Union(sets) => match sets {
                Value::Set(set) | Value::Unsorted(set) => set.iter().chain([sets]).collect(),
                _ => vec![sets],
            },
            Lazy::FunctionSet(left, right)
            | Lazy::Cap(left, right)
            | Lazy::Cup(left, right)
            | Lazy::Diff(left, right) => vec![left, right],
            Lazy::Product(sets) => sets.iter().collect(),
            Lazy::RecordSet(fields, _) => fields.iter().map(|(_, set)| set).collect(),
            Lazy::Nat | Lazy::Int | Lazy::Real | Lazy::Strings | Lazy::Any => Vec::new(),
        },
        _ => Vec::new(),
    };
    parts
        .into_iter()
        .filter(|part| is_failing_union(part))
        .cloned()
        .collect()
}

// Whether `container` holds the lazy set `held` (the same value, not an equal one) inside it: as
// an operand of a lazy set, an element of a set or a part of a function, at any depth.
fn holds_within(container: &Value, held: &Value) -> bool {
    let Value::Lazy(held) = held else {
        return false;
    };
    let mut pending: Vec<&Value> = Vec::new();
    let mut seen = HashSet::new();
    pending.push(container);
    let mut is_root = true;
    while let Some(value) = pending.pop() {
        if !is_root && matches!(value, Value::Lazy(lazy) if Rc::ptr_eq(lazy, held)) {
            return true;
        }
        is_root = false;
        match value {
            Value::Set(set) | Value::Unsorted(set) => {
                if seen.insert(Rc::as_ptr(set) as usize) {
                    pending.extend(set.iter());
                }
            }
            Value::Function(function) => {
                if seen.insert(Rc::as_ptr(function) as usize) {
                    pending.extend(function.domain.iter().chain(&function.range));
                }
            }
            Value::Lambda(lambda) => pending.push(lambda.domain()),
            Value::Lazy(lazy) => {
                if !seen.insert(Rc::as_ptr(lazy) as usize) {
                    continue;
                }
                match &***lazy {
                    Lazy::Subset(base)
                    | Lazy::Seq(base)
                    | Lazy::Union(base)
                    | Lazy::Filter(base, _) => pending.push(base),
                    Lazy::FunctionSet(left, right)
                    | Lazy::Cap(left, right)
                    | Lazy::Cup(left, right)
                    | Lazy::Diff(left, right) => pending.extend([left, right]),
                    Lazy::RecordSet(fields, _) => {
                        pending.extend(fields.iter().map(|(_, value)| value))
                    }
                    Lazy::Product(sets) => pending.extend(sets),
                    Lazy::Nat | Lazy::Int | Lazy::Real | Lazy::Strings | Lazy::Any => {}
                }
            }
            _ => {}
        }
    }
    false
}

// Whether a value is or holds, at any depth, a set enumeration TLC fails to normalize other than
// `held`.
fn holds_unsorted_other_than(value: &Value, held: &Rc<crate::value::Set>) -> bool {
    let mut pending = vec![value];
    let mut seen = HashSet::new();
    while let Some(value) = pending.pop() {
        match value {
            Value::Unsorted(set) if Rc::ptr_eq(set, held) => {}
            Value::Unsorted(_) => return true,
            Value::Set(set) => {
                if seen.insert(Rc::as_ptr(set) as usize) {
                    pending.extend(set.iter());
                }
            }
            Value::Function(function) => {
                if seen.insert(Rc::as_ptr(function) as usize) {
                    pending.extend(function.domain.iter().chain(&function.range));
                }
            }
            Value::Lambda(lambda) => pending.push(lambda.domain()),
            Value::Lazy(lazy) => {
                if !seen.insert(Rc::as_ptr(lazy) as usize) {
                    continue;
                }
                match &***lazy {
                    Lazy::Subset(base)
                    | Lazy::Seq(base)
                    | Lazy::Union(base)
                    | Lazy::Filter(base, _) => pending.push(base),
                    Lazy::FunctionSet(left, right)
                    | Lazy::Cap(left, right)
                    | Lazy::Cup(left, right)
                    | Lazy::Diff(left, right) => pending.extend([left, right]),
                    Lazy::RecordSet(fields, _) => {
                        pending.extend(fields.iter().map(|(_, value)| value))
                    }
                    Lazy::Product(sets) => pending.extend(sets),
                    Lazy::Nat | Lazy::Int | Lazy::Real | Lazy::Strings | Lazy::Any => {}
                }
            }
            _ => {}
        }
    }
    false
}

// Whether a value holds a set TLC can't normalize.
fn holds_unsorted(value: &Value) -> bool {
    match value {
        Value::Unsorted(_) => true,
        Value::Set(elements) => elements.iter().any(holds_unsorted),
        Value::Function(function) => function
            .domain
            .iter()
            .chain(&function.range)
            .any(holds_unsorted),
        _ => false,
    }
}

/// Whether TLC's enumeration of a set enumeration's elements gives null at once: the set holds
/// only an INSTANCE's THEOREM or ASSUME literal TLC did not initialize (`Value::Null`), which
/// `SetEnumValue.Enumerator.nextElement` returns as it is, and which every loop of `Tool`
/// takes for the enumeration's end (`while ((elem = Enum.nextElement()) != null)`). A larger
/// set holding one TLC fails to sort, comparing it, where the evaluator may not: that declines.
fn is_null_enumeration(elements: &[Value]) -> Evaluated<bool> {
    if !elements
        .iter()
        .any(|element| matches!(element, Value::Null))
    {
        return Ok(false);
    }
    if elements.len() > 1 {
        return fail(
            "an enumeration of a set holding an INSTANCE fact literal TLC did not initialize, with other elements",
        );
    }
    Ok(true)
}

#[cfg(test)]
mod tests {
    use super::*;

    // A value the replay gave a source and then dropped keeps its address, so the next value the
    // allocator makes can't take its source, whichever allocator it is.
    #[test]
    fn keeps_the_values_it_gives_a_source() {
        let mut stack = CallStack::default();
        let Value::Set(elements) = Value::set(vec![Value::Int(1)]) else {
            unreachable!("a set enumeration")
        };
        let kept = Rc::downgrade(&elements);
        stack.give_source(&Value::Set(elements), 7);
        assert!(
            kept.upgrade().is_some(),
            "the call stack keeps the value it gave a source"
        );
        let other = Value::set(vec![Value::Int(2)]);
        assert_eq!(stack.source(&other), None);
        assert_eq!(
            stack.source(&Value::Set(kept.upgrade().expect("kept"))),
            Some(7)
        );
    }

    fn lazy(lazy: Lazy) -> Value {
        Value::lazy(lazy)
    }

    // `SetOfTuplesValue.toString` and its siblings size each part, which fails on a value that
    // isn't a set but a function, a tuple or a record, and enumerate the set, which first asks
    // each part whether it is empty, which fails on any value that isn't a set.
    #[test]
    fn fails_to_print_a_set_of_a_non_set_as_tlc_does() {
        let message = |value: Value| {
            check_unchecked(&value)
                .err()
                .and_then(|error| error.message)
                .map(|message| message.text)
        };
        let set = || Value::set(vec![Value::Int(1), Value::Int(2)]);
        let tuple = Value::function(vec![Value::Int(1)], vec![Value::Int(2)], Class::Tuple);
        assert_eq!(
            message(lazy(Lazy::Product(vec![set(), Value::Int(0)]))).as_deref(),
            Some("Attempted to compute the number of elements in the integer 0.")
        );
        assert_eq!(
            message(lazy(Lazy::Product(vec![set(), Value::Bool(false)]))).as_deref(),
            Some("Attempted to compute the number of elements in the boolean FALSE.")
        );
        assert_eq!(
            message(lazy(Lazy::Product(vec![set(), tuple.clone()]))).as_deref(),
            Some("Shouldn't call isEmpty() on value <<2>>")
        );
        assert_eq!(
            message(lazy(Lazy::FunctionSet(set(), tuple))).as_deref(),
            Some("Shouldn't call isEmpty() on value <<2>>")
        );
        assert_eq!(
            message(lazy(Lazy::Product(vec![
                Value::set(Vec::new()),
                Value::Int(0)
            ]))),
            None
        );
    }

    #[test]
    fn finds_a_set_finite_as_tlc_does() {
        let nat = || lazy(Lazy::Nat);
        let empty = || Value::set(Vec::new());
        let one = || Value::interval(0, 0);
        // [Nat -> {}] and [Nat -> {0}] are finite, [Nat -> 0..1] isn't.
        assert!(is_finite(&lazy(Lazy::FunctionSet(nat(), empty()))).expect("finite"));
        assert!(is_finite(&lazy(Lazy::FunctionSet(nat(), one()))).expect("finite"));
        assert!(
            !is_finite(&lazy(Lazy::FunctionSet(nat(), Value::interval(0, 1)))).expect("infinite")
        );
        // Nat \X {} and Seq({}) are finite, Seq({1}) isn't.
        assert!(is_finite(&lazy(Lazy::Product(vec![nat(), empty()]))).expect("finite"));
        assert!(is_finite(&lazy(Lazy::Seq(empty()))).expect("finite"));
        assert!(!is_finite(&lazy(Lazy::Seq(one()))).expect("infinite"));
    }

    #[test]
    fn caches_lazy_bindings_only_in_compatible_evaluations() {
        let bytes = std::fs::read(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../../tests/conformance/ir/tlc/tlatools/org.lamport.tlatools/test-model/suite/etest14.ir"
        ))
        .expect("a golden IR");
        let mut ir = tla_ir::decode(&bytes).expect("an IR that decodes");
        let variable = ir.texts.len() as u32;
        ir.texts.push("x".into());
        let print = ir.texts.len() as u32;
        ir.texts.push("Print".into());
        ir.variables = vec![variable];
        let builtin = ir.builtins.len() as u32;
        ir.builtins.push(Builtin {
            name: print,
            arity: 2,
            flags: 0,
            table: Vec::new(),
        });
        let mut push = |kind| {
            let index = ir.nodes.arena.len() as u32;
            ir.nodes.arena.push(tla_ir::Node {
                line: 1,
                column: 1,
                range: None,
                kind,
            });
            index
        };
        let zero = push(NodeKind::Number(0));
        let read = push(NodeKind::Identifier(Name {
            text: variable,
            resolution: Resolution::Variable(0),
            is_local: false,
        }));
        let printed = push(NodeKind::Apply {
            name: Name {
                text: print,
                resolution: Resolution::Builtin(builtin),
                is_local: false,
            },
            args: vec![zero, read],
        });
        let context = Context::default().bind(
            variable,
            Binding::Thunk {
                node: printed,
                context: Context::default(),
                is_self: false,
            },
        );
        let frame = lookup(&context.env, variable).expect("a lazy binding");
        let mut evaluator = Evaluator::new(&ir);
        assert!(evaluator.binding(&frame, &context).is_err());
        evaluator.current[0] = Some(Value::Int(1));
        for _ in 0..2 {
            assert!(matches!(
                evaluator.binding(&frame, &context),
                Ok(Value::Int(1))
            ));
        }
        assert_eq!(evaluator.printed.len(), 1);
        evaluator.current[0] = Some(Value::Int(2));
        assert!(matches!(
            evaluator.binding(&frame, &context),
            Ok(Value::Int(2))
        ));
        assert_eq!(evaluator.printed.len(), 2);
        evaluator.next[0] = Some(Value::Int(3));
        assert!(matches!(
            evaluator.binding(&frame, &context.primed(true)),
            Ok(Value::Int(3))
        ));
        assert_eq!(evaluator.printed.len(), 3);
        evaluator.is_enabling = true;
        assert!(matches!(
            evaluator.binding(&frame, &context.primed(true)),
            Ok(Value::Int(3))
        ));
        assert_eq!(evaluator.printed.len(), 4);
        let mut other = Evaluator::new(&ir);
        other.current[0] = Some(Value::Int(4));
        assert!(matches!(other.binding(&frame, &context), Ok(Value::Int(4))));
        assert_eq!(other.printed.len(), 1);
    }

    #[test]
    fn a_null_lazy_result_misses_but_evicts_and_primed_expansion_keeps_the_old_cache() {
        let bytes = std::fs::read(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../../tests/conformance/ir/tlc/tlatools/org.lamport.tlatools/test-model/suite/etest14.ir"
        ))
        .expect("a golden IR");
        let mut ir = tla_ir::decode(&bytes).expect("an IR that decodes");
        let variable = ir.texts.len() as u32;
        ir.texts.extend([
            "x".into(),
            "PrintT".into(),
            "=".into(),
            "$UninitializedLiteral".into(),
        ]);
        ir.variables = vec![variable];
        let first_builtin = ir.builtins.len() as u32;
        for (name, arity, flags) in [
            (variable + 1, 1, 0),
            (variable + 2, 2, 0),
            (
                variable + 3,
                0,
                Builtin::UNINITIALIZED_LITERAL | Builtin::DECLINED,
            ),
        ] {
            ir.builtins.push(Builtin {
                name,
                arity,
                flags,
                table: Vec::new(),
            });
        }
        let mut push = |kind| {
            let index = ir.nodes.arena.len() as u32;
            ir.nodes.arena.push(tla_ir::Node {
                line: 1,
                column: 1,
                range: None,
                kind,
            });
            index
        };
        let zero = push(NodeKind::Number(0));
        let one = push(NodeKind::Number(1));
        let read = push(NodeKind::Identifier(Name {
            text: variable,
            resolution: Resolution::Variable(0),
            is_local: false,
        }));
        let printed = push(NodeKind::Apply {
            name: Name {
                text: variable + 1,
                resolution: Resolution::Builtin(first_builtin),
                is_local: false,
            },
            args: vec![read],
        });
        let condition = push(NodeKind::Apply {
            name: Name {
                text: variable + 2,
                resolution: Resolution::Builtin(first_builtin + 1),
                is_local: false,
            },
            args: vec![read, zero],
        });
        let null = push(NodeKind::Identifier(Name {
            text: variable + 3,
            resolution: Resolution::Builtin(first_builtin + 2),
            is_local: false,
        }));
        let selected = push(NodeKind::If {
            condition,
            consequent: one,
            alternative: null,
        });
        let body = push(NodeKind::If {
            condition: printed,
            consequent: selected,
            alternative: zero,
        });
        let tuple = push(NodeKind::Tuple(vec![null]));
        let carrier_body = push(NodeKind::If {
            condition: printed,
            consequent: tuple,
            alternative: zero,
        });
        let context = Context::default().bind(
            variable,
            Binding::Thunk {
                node: body,
                context: Context::default(),
                is_self: false,
            },
        );
        let frame = lookup(&context.env, variable).expect("a lazy argument");
        let mut evaluator = Evaluator::new(&ir);
        evaluator.current[0] = Some(Value::Int(0));
        evaluator.next[0] = Some(Value::Int(1));
        assert!(matches!(
            evaluator.binding(&frame, &context),
            Ok(Value::Int(1))
        ));
        assert_eq!(evaluator.printed.len(), 1);
        // Tool's explicit-prime/null-s1 path expands the expression without getValue,
        // so a null there must not overwrite the ordinary current-state cache.
        assert!(matches!(
            evaluator.binding(&frame, &context.primed(true)),
            Ok(Value::Null)
        ));
        assert!(matches!(
            frame.cached.borrow().as_ref().map(|value| &value.value),
            Some(Value::Int(1))
        ));
        assert!(matches!(
            evaluator.binding(&frame, &context),
            Ok(Value::Int(1))
        ));
        assert_eq!(evaluator.printed.len(), 2);
        // Ordinary getValue replaces the previous entry with Cache(null). That
        // entry always misses, including after returning to the old state.
        evaluator.current[0] = Some(Value::Int(1));
        for expected_prints in [3, 4] {
            assert!(matches!(
                evaluator.binding(&frame, &context),
                Ok(Value::Null)
            ));
            assert!(matches!(
                frame.cached.borrow().as_ref().map(|value| &value.value),
                Some(Value::Null)
            ));
            assert_eq!(evaluator.printed.len(), expected_prints);
        }
        evaluator.current[0] = Some(Value::Int(0));
        assert!(matches!(
            evaluator.binding(&frame, &context),
            Ok(Value::Int(1))
        ));
        assert_eq!(evaluator.printed.len(), 5);
        assert!(evaluator.unshared.is_none());
        // A non-null Java container holding null is an ordinary cached object.
        let carrier_context = Context::default().bind(
            variable,
            Binding::Thunk {
                node: carrier_body,
                context: Context::default(),
                is_self: false,
            },
        );
        let carrier = lookup(&carrier_context.env, variable).expect("a container argument");
        for _ in 0..2 {
            let value = evaluator
                .binding(&carrier, &carrier_context)
                .expect("a cached tuple");
            assert!(matches!(value, Value::Function(_)));
            assert!(crate::value::contains_uninitialized(&value));
        }
        assert_eq!(evaluator.printed.len(), 6);
    }

    #[test]
    fn distinguishes_configuration_literals_from_equal_transferred_values() {
        let bytes = std::fs::read(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../../tests/conformance/ir/tlc/tlatools/org.lamport.tlatools/test-model/suite/etest14.ir"
        )).expect("a golden IR");
        let mut ir = tla_ir::decode(&bytes).expect("an IR that decodes");
        let set = tla_ir::Value::Set(vec![tla_ir::Value::Int(1)]);
        ir.values.list = vec![
            set.clone(),
            tla_ir::Value::Function {
                class: 0,
                domain: vec![tla_ir::Value::Int(1)],
                range: vec![set],
            },
        ];
        let mut evaluator = Evaluator::new(&ir);
        assert_eq!(
            java_set_class(&evaluator.value(0).expect("a transferred set")),
            None
        );
        let first = evaluator
            .configuration_value(0)
            .expect("a configuration set");
        assert_eq!(java_set_class(&first), Some(SetClass::Enumeration));
        let repeated = evaluator
            .configuration_value(0)
            .expect("the same configuration set");
        assert!(
            matches!((&first, &repeated), (Value::Set(first), Value::Set(repeated)) if Rc::ptr_eq(first, repeated))
        );
        assert_eq!(
            java_set_class(&evaluator.value(0).expect("still a transfer")),
            None
        );
        let function = evaluator
            .configuration_value(1)
            .expect("an unproven transfer");
        assert_eq!(numeric_value_class(&function), None);
        assert_eq!(
            java_set_class(&function.as_function().expect("a function").range[0]),
            None
        );
    }

    #[test]
    fn speculative_filter_conversion_restores_nested_scopes() {
        let predicate = Rc::new(Predicate {
            pattern: Pattern::Name(0),
            body: 0,
            context: Context::default(),
            current: Vec::new(),
            next: Vec::new(),
            level: 0,
            text: (String::new(), String::new()),
            is_untraced: false,
            filtered: None,
            converted: RefCell::new(None),
        });
        {
            let _outer = rollback_filter_conversions();
            let first = Rc::new(vec![Value::Int(1)]);
            predicate.cache_conversion(Rc::clone(&first));
            {
                let _inner = rollback_filter_conversions();
                predicate.cache_conversion(Rc::new(vec![Value::Int(2)]));
            }
            assert!(Rc::ptr_eq(predicate.converted().as_ref().unwrap(), &first));
        }
        assert!(predicate.converted().is_none());
    }

    #[test]
    fn cached_state_identity_precedes_potentially_failing_equality() {
        let unnormalized = Value::unsorted(vec![Value::Int(1), Value::Bool(true)]);
        assert!(equals(&unnormalized, &unnormalized).is_err());
        assert!(state_extends(
            &[Some(unnormalized.clone())],
            &[Some(unnormalized)]
        ));
        let predicate = Predicate {
            pattern: Pattern::Name(0),
            body: 0,
            context: Context::default(),
            current: Vec::new(),
            next: Vec::new(),
            level: 0,
            text: ("{x in ".into(), " : PrintT(x)}".into()),
            is_untraced: false,
            filtered: None,
            converted: RefCell::new(None),
        };
        let filter = Value::lazy(Lazy::Filter(Value::lazy(Lazy::Nat), Rc::new(predicate)));
        assert!(equals(&filter, &filter).is_err());
        assert!(state_extends(&[Some(filter.clone())], &[Some(filter)]));
        assert!(!state_extends(
            &[Some(Value::set(Vec::new()))],
            &[Some(Value::Int(1))]
        ));
    }

    #[test]
    fn cached_bindings_keep_physical_values_across_partial_state_extensions() {
        let bytes = std::fs::read(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../../tests/conformance/ir/tlc/tlatools/org.lamport.tlatools/test-model/suite/etest14.ir"
        ))
        .expect("a golden IR");
        let mut ir = tla_ir::decode(&bytes).expect("an IR that decodes");
        let variable = ir.texts.len() as u32;
        ir.texts.push("x".into());
        let print = ir.texts.len() as u32;
        ir.texts.push("Print".into());
        ir.variables = vec![variable];
        let builtin = ir.builtins.len() as u32;
        ir.builtins.push(Builtin {
            name: print,
            arity: 2,
            flags: 0,
            table: Vec::new(),
        });
        let mut push = |kind| {
            let index = ir.nodes.arena.len() as u32;
            ir.nodes.arena.push(tla_ir::Node {
                line: 1,
                column: 1,
                range: None,
                kind,
            });
            index
        };
        let zero = push(NodeKind::Number(0));
        let read = push(NodeKind::Identifier(Name {
            text: variable,
            resolution: Resolution::Variable(0),
            is_local: false,
        }));
        let printed = push(NodeKind::Apply {
            name: Name {
                text: print,
                resolution: Resolution::Builtin(builtin),
                is_local: false,
            },
            args: vec![zero, read],
        });
        let context = Context::default().bind(
            variable,
            Binding::Thunk {
                node: printed,
                context: Context::default(),
                is_self: false,
            },
        );
        let frame = lookup(&context.env, variable).expect("a lazy binding");
        let mut evaluator = Evaluator::new(&ir);
        evaluator.current.clear();
        assert!(evaluator.binding(&frame, &context).is_err());
        let values = [
            Value::Int(1),
            Value::set(vec![Value::Int(1)]),
            Value::function(vec![Value::Int(1)], vec![Value::Int(2)], Class::Plain),
            Value::tuple(vec![Value::Int(2)]),
            lazy(Lazy::Subset(Value::set(vec![Value::Int(1)]))),
            Value::set_with_class(vec![Value::Int(3)], None),
        ];
        let classes = [
            Some("IntValue"),
            Some("SetEnumValue"),
            Some("FcnRcdValue"),
            Some("FcnRcdValue"),
            Some("SubsetValue"),
            None,
        ];
        for (index, value) in values.into_iter().enumerate() {
            evaluator.current = vec![Some(value.clone()), None];
            let returned = evaluator
                .binding(&frame, &context)
                .expect("an assigned value");
            assert_eq!(numeric_value_class(&returned), classes[index]);
            assert_eq!(evaluator.printed.len(), [1, 2, 3, 3, 4, 5][index]);
            evaluator.current[1] = Some(Value::Bool(true));
            let returned = evaluator
                .binding(&frame, &context)
                .expect("a state extension");
            assert_eq!(numeric_value_class(&returned), classes[index]);
            assert_eq!(evaluator.printed.len(), [1, 2, 3, 3, 4, 5][index]);
        }
    }

    #[test]
    fn releases_cached_closures_that_capture_their_binding() {
        let bytes = std::fs::read(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../../tests/conformance/ir/tlc/tlatools/org.lamport.tlatools/test-model/suite/etest14.ir"
        ))
        .expect("a golden IR");
        let mut ir = tla_ir::decode(&bytes).expect("an IR that decodes");
        let name = ir.texts.len() as u32;
        ir.texts.push("Alias".into());
        let domain = ir.texts.len() as u32;
        ir.texts.push("Domain".into());
        let parameter = ir.texts.len() as u32;
        ir.texts.push("k".into());
        let mut push = |kind| {
            let index = ir.nodes.arena.len() as u32;
            ir.nodes.arena.push(tla_ir::Node {
                line: 1,
                column: 1,
                range: None,
                kind,
            });
            index
        };
        let zero = push(NodeKind::Number(0));
        let set = push(NodeKind::Identifier(Name {
            text: domain,
            resolution: Resolution::None,
            is_local: true,
        }));
        let function = push(NodeKind::FunctionConstruction {
            is_recursive: false,
            bounds: vec![Bound {
                pattern: Pattern::Name(parameter),
                set,
            }],
            body: zero,
        });
        let nested = push(NodeKind::Tuple(vec![function]));
        for node in [function, nested] {
            let mut evaluator = Evaluator::new(&ir);
            let mut weak_frames = Vec::new();
            let mut escaped = Vec::new();
            for iteration in 0..256 {
                let bound = Context::default().bind_value(domain, lazy(Lazy::Nat));
                let context = bound.bind(
                    name,
                    Binding::Thunk {
                        node,
                        context: Context::default(),
                        is_self: true,
                    },
                );
                let frame = lookup(&context.env, name).expect("a self-closing instance binding");
                weak_frames.push(Rc::downgrade(&frame));
                let value = evaluator
                    .binding(&frame, &context)
                    .expect("a captured function");
                let repeated = evaluator
                    .binding(&frame, &context)
                    .expect("the same captured function");
                match (&value, &repeated) {
                    (Value::Lambda(first), Value::Lambda(second)) => {
                        assert!(Rc::ptr_eq(first, second))
                    }
                    (Value::Function(first), Value::Function(second)) => {
                        assert!(Rc::ptr_eq(first, second))
                    }
                    _ => panic!("a function or a tuple containing it"),
                }
                if iteration % 64 == 0 {
                    escaped.push(value);
                }
            }
            assert!(
                evaluator.cached_frames.len() <= 16,
                "unreachable cycles are swept during one evaluation session"
            );
            evaluator.collect_cached_frames();
            for (iteration, frame) in weak_frames.iter().enumerate() {
                assert_eq!(
                    frame.upgrade().is_some(),
                    iteration % 64 == 0,
                    "only externally retained closures keep their contexts between evaluations"
                );
            }
            drop(evaluator);
            assert!(
                weak_frames[0].upgrade().is_some(),
                "a returned closure survives its evaluator"
            );
            let mut later = Evaluator::new(&ir);
            for value in &escaped {
                let lambda = match value {
                    Value::Lambda(lambda) => lambda,
                    Value::Function(function) => match &function.range[0] {
                        Value::Lambda(lambda) => lambda,
                        _ => panic!("a tuple containing a lazy function"),
                    },
                    _ => panic!("a returned function"),
                };
                assert!(matches!(
                    later.apply_lambda(lambda, &Value::Int(3)),
                    Ok(Value::Int(0))
                ));
            }
            drop(escaped);
            assert!(
                weak_frames.iter().all(|frame| frame.upgrade().is_none()),
                "the caches must not retain their own frames"
            );
            let bound = Context::default().bind_value(domain, lazy(Lazy::Nat));
            let context = bound.bind(
                name,
                Binding::Thunk {
                    node: function,
                    context: Context::default(),
                    is_self: true,
                },
            );
            let frame = lookup(&context.env, name).expect("a self-closing binding");
            let mut evaluator = Evaluator::new(&ir);
            let value = evaluator
                .binding(&frame, &context)
                .expect("a captured function");
            let values = Rc::new(vec![value]);
            let first = Value::set_from_rc(Rc::clone(&values), Some(SetClass::Enumeration));
            let second = Value::set_from_rc(Rc::clone(&values), None);
            let escaped = first.clone();
            frame
                .cached
                .borrow_mut()
                .as_mut()
                .expect("a cached value")
                .value = Value::tuple(vec![first.clone(), first, second]);
            let weak = Rc::downgrade(&frame);
            drop(frame);
            drop(context);
            evaluator.collect_cached_frames();
            assert!(
                weak.upgrade()
                    .expect("an escaped wrapper")
                    .cached
                    .borrow()
                    .is_some()
            );
            assert_eq!(java_set_class(&escaped), Some(SetClass::Enumeration));
            drop(escaped);
            evaluator.collect_cached_frames();
            assert!(
                weak.upgrade()
                    .expect("escaped shared contents")
                    .cached
                    .borrow()
                    .is_some()
            );
            drop(values);
            evaluator.collect_cached_frames();
            assert!(
                weak.upgrade().is_none(),
                "shared wrappers must not hide an unreachable cycle"
            );
            let context = Context::default().bind_value(domain, lazy(Lazy::Nat)).bind(
                name,
                Binding::Thunk {
                    node: function,
                    context: Context::default(),
                    is_self: true,
                },
            );
            let frame = lookup(&context.env, name).expect("a self-closing binding");
            let value = evaluator
                .binding(&frame, &context)
                .expect("a captured function");
            let converted = Rc::new(vec![value]);
            let predicate = Predicate {
                pattern: Pattern::Name(name),
                body: zero,
                context: Context::default(),
                current: Vec::new(),
                next: Vec::new(),
                level: 0,
                text: ("{v in ".into(), " : TRUE}".into()),
                is_untraced: false,
                filtered: None,
                converted: RefCell::new(Some(Rc::clone(&converted))),
            };
            frame
                .cached
                .borrow_mut()
                .as_mut()
                .expect("a cached value")
                .value = lazy(Lazy::Filter(lazy(Lazy::Nat), Rc::new(predicate)));
            let weak = Rc::downgrade(&frame);
            drop(frame);
            drop(context);
            evaluator.collect_cached_frames();
            assert!(
                weak.upgrade().is_some(),
                "converted elements are an external root"
            );
            drop(converted);
            evaluator.collect_cached_frames();
            assert!(
                weak.upgrade().is_none(),
                "converted filter elements must not hide a cycle"
            );
        }
    }

    #[test]
    fn restores_the_nesting_after_a_caught_panic() {
        let bytes = std::fs::read(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../../tests/conformance/ir/tlc/tlatools/org.lamport.tlatools/test-model/suite/etest14.ir"
        ))
        .expect("a golden IR");
        let ir = tla_ir::decode(&bytes).expect("an IR that decodes");
        let mut evaluator = Evaluator::new(&ir);
        let outside = (DEPTH.get(), BASE.get());
        let caught = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            evaluator.nested(|evaluator| {
                evaluator.nested(|_| -> Evaluated<()> { panic!("a panic in a nesting") })
            })
        }));
        assert!(caught.is_err());
        assert_eq!((DEPTH.get(), BASE.get()), outside);
    }
}
