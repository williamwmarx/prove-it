//! The evaluator's values: trees that keep what TLC's `Value` classes keep and the store forgets,
//! as the TypeScript `Value` of `values.ts` does: a record's written order until TLC sorts it, the
//! function classes, intervals, and the lazy sets TLC keeps. Values are ordered as the store
//! orders them, rule for rule, so a set's elements are in TLC's order and a value matches the
//! store's id of it ([`matches`]).

use std::cell::{Cell, RefCell};
use std::cmp::Ordering;
use std::collections::HashMap;
use std::rc::{Rc, Weak};

use tla_values::Store;

use crate::Unsupported;
use crate::print::format_pretty;
use tla_values::store::{
    INT, KIND_ANY, KIND_BOOL, KIND_FUNCTION, KIND_INFINITE_SET, KIND_INT, KIND_MODEL, KIND_SET,
    KIND_STRING, KIND_TUPLE, NAT, STRINGS, TRUE,
};

/// Why an evaluation failed, as TLC would have, or where the evaluator can't follow it: the
/// evaluator's reason, and TLC's message where the failure gives TLC's text.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EvalError {
    pub reason: String,
    pub message: Option<TlcMessage>,
    pub runtime_exception: RuntimeException,
    /// A modeled normalization failure of a proven set enumeration.
    pub is_set_normalization: bool,
    /// A modeled Reducible operation iterating a concrete set in its written order.
    pub is_set_reduction: bool,
    /// A failed comparison the evaluator follows as TLC makes it, whatever lazy sets the
    /// evaluation holds: one whose receiver is an integer, a string, a boolean or a function
    /// and whose argument is a lazy set, which its `equals` and `compareTo` read only to print, where that
    /// text is known, or the sort of a union `PrintT` prints (`is_known_cup_print`).
    pub is_followed_comparison: bool,
    /// A modeled normalization failure of a proven set enumeration that TLC meets as it words
    /// another failure with the set's `toString`, whose `getNewHead` adds the set's source to a
    /// fingerprint stack, which the evaluator, holding no source of the set, can't add.
    pub is_named_normalization: bool,
}

/// Runtime exception classes with different reporting or CallStackTool unwinding.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum RuntimeException {
    #[default]
    Runtime,
    WrongInvocation,
    ClassCast,
    NullPointer,
    /// An ArrayIndexOutOfBoundsException, which TLC reports as it reports a ClassCastException.
    IndexOutOfBounds,
}

impl RuntimeException {
    pub fn class_name(self) -> &'static str {
        match self {
            Self::Runtime => "java.lang.RuntimeException",
            Self::WrongInvocation => "util.WrongInvocationException",
            Self::ClassCast => "java.lang.ClassCastException",
            Self::NullPointer => "java.lang.NullPointerException",
            Self::IndexOutOfBounds => "java.lang.ArrayIndexOutOfBoundsException",
        }
    }
}

/// TLC's message for an error: its text, the code of TLC's message it is where it is one of
/// `tlc2.output.MP`'s, and whether TLC raises it as an EvalException rather than a
/// RuntimeException.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TlcMessage {
    pub text: String,
    pub code: Option<u32>,
    pub is_eval_exception: bool,
    /// The message of the error this one reports, which its text ends with, as a Java method's
    /// failure reports the error the method produced (`MP.getMessage`'s nested message).
    pub inner: Option<Box<TlcMessage>>,
}

pub type Evaluated<T> = Result<T, EvalError>;

pub fn fail<T>(reason: impl Into<String>) -> Evaluated<T> {
    Err(EvalError {
        reason: reason.into(),
        message: None,
        runtime_exception: RuntimeException::Runtime,
        is_set_normalization: false,
        is_set_reduction: false,
        is_followed_comparison: false,
        is_named_normalization: false,
    })
}

/// A failure TLC raises as a RuntimeException with a message of no code.
pub fn fail_runtime<T>(reason: impl Into<String>, text: String) -> Evaluated<T> {
    Err(EvalError {
        reason: reason.into(),
        message: Some(TlcMessage {
            text,
            code: None,
            is_eval_exception: false,
            inner: None,
        }),
        runtime_exception: RuntimeException::Runtime,
        is_set_normalization: false,
        is_set_reduction: false,
        is_followed_comparison: false,
        is_named_normalization: false,
    })
}

/// A failure with TLC's message for it.
pub fn fail_with<T>(reason: impl Into<String>, message: TlcMessage) -> Evaluated<T> {
    Err(EvalError {
        reason: reason.into(),
        message: Some(message),
        runtime_exception: RuntimeException::Runtime,
        is_set_normalization: false,
        is_set_reduction: false,
        is_followed_comparison: false,
        is_named_normalization: false,
    })
}

/// A failure TLC raises as an EvalException with the message of this code.
pub fn fail_coded<T>(reason: impl Into<String>, code: u32, text: String) -> Evaluated<T> {
    Err(EvalError {
        reason: reason.into(),
        message: Some(TlcMessage {
            text,
            code: Some(code),
            is_eval_exception: true,
            inner: None,
        }),
        runtime_exception: RuntimeException::Runtime,
        is_set_normalization: false,
        is_set_reduction: false,
        is_followed_comparison: false,
        is_named_normalization: false,
    })
}

/// Java's ArrayIndexOutOfBoundsException of an index into an array of a length.
pub fn index_out_of_bounds<T>(
    reason: impl Into<String>,
    index: usize,
    length: usize,
) -> Evaluated<T> {
    Err(EvalError {
        reason: reason.into(),
        message: Some(TlcMessage {
            text: format!("Index {index} out of bounds for length {length}"),
            code: None,
            is_eval_exception: false,
            inner: None,
        }),
        runtime_exception: RuntimeException::IndexOutOfBounds,
        is_set_normalization: false,
        is_set_reduction: false,
        is_followed_comparison: false,
        is_named_normalization: false,
    })
}

/// ValueVec.addElement fails after evaluating the element, before insertion or normalization.
pub fn push_set_element(elements: &mut Vec<Value>, value: Value) -> Evaluated<()> {
    check_set_bound(elements.len())?;
    elements.push(value);
    Ok(())
}

/// Whether a `ValueVec` that holds `length` elements takes another, which fails past
/// `TLCGlobals.setBound` (`ensureCapacity`).
pub(crate) fn check_set_bound(length: usize) -> Evaluated<()> {
    tla_values::check_set_insertion(length).map_err(|_| set_bound_exceeded())
}

/// `ValueVec.ensureCapacity`'s failure, given an element past `TLCGlobals.setBound`.
pub(crate) fn set_bound_exceeded() -> EvalError {
    EvalError {
        reason: tla_values::SET_BOUND_EXCEEDED.0.into(),
        message: Some(TlcMessage {
            text: format!(
                "Attempted to construct a set with too many elements (>{}).",
                tla_values::SET_BOUND
            ),
            code: None,
            is_eval_exception: false,
            inner: None,
        }),
        runtime_exception: RuntimeException::WrongInvocation,
        is_set_normalization: false,
        is_set_reduction: false,
        is_followed_comparison: false,
        is_named_normalization: false,
    }
}

/// A string or a model value's name, with TLC's rank of it: the order TLC interned the text in,
/// or -1 for a text the evaluator doesn't rank, which TLC made as it searched.
#[derive(Debug, PartialEq, Eq)]
pub struct Text {
    pub units: Box<[u16]>,
    pub rank: i32,
}

impl Text {
    /// A model value's type: the letter before `_` in a name such as `A_x`, or 0.
    pub fn model_type(&self) -> u16 {
        if self.units.len() > 2 && self.units[1] == u16::from(b'_') {
            self.units[0]
        } else {
            0
        }
    }
}

/// TLC's class of a function, which decides how it prints and how its errors are worded.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Class {
    /// A `FcnRcdValue`.
    Plain,
    /// A `FcnLambdaValue`: `[x \in S |-> e]`, until TLC fingerprints it.
    Lambda,
    /// A `TupleValue`.
    Tuple,
    /// A `RecordValue`.
    Record,
}

/// A function: its domain in TLC's order, the value at each key, its class, and, until TLC sorts
/// it, the positions of its keys in the order they were written.
#[derive(Debug)]
pub struct Function {
    pub domain: Vec<Value>,
    pub range: Vec<Value>,
    pub class: Cell<Class>,
    /// The concrete Java class, independent of printing and fingerprint normalization.
    /// None means evaluation or transfer did not retain enough provenance for a typed cast.
    pub java_class: Cell<Option<Class>>,
    /// The CounterExample record subtype; None where transfer erased its origin.
    pub is_counter_example: Cell<Option<bool>>,
    /// Proven FcnRcdValue, directly built or eagerly built over TLC Reducible domains.
    pub is_eager_record: Cell<bool>,
    pub written: RefCell<Option<Vec<u32>>>,
    /// How TLC searches the function's keys, where the evaluator knows.
    pub search: Cell<Search>,
    /// The interval the function was built over, which DOMAIN gives back, as TLC keeps a
    /// tuple's or a function's over `a..b` (`getDomainInterval`); `None` for any other domain.
    pub interval: Option<(i32, i32)>,
    /// Whether TLC builds the function over the `IntervalValue` its constructor's bound gave
    /// (`toFcnRcd` keeps it as `FcnRcdValue.intv`), whose `select` takes an integer alone.
    pub is_domain_interval: Cell<bool>,
}

/// How TLC searches a function's keys for an argument, which decides its message where two
/// can't compare.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Search {
    /// TLC holds the keys in the order it built them, which the evaluator doesn't keep.
    Unknown,
    /// A function TLC built and sorted (`FcnRcdValue.select` with `isNorm`), as it sorts a
    /// constant definition's value as it starts and a state's as it fingerprints it.
    Sorted,
    /// A function TLC keeps lazy, over a set it has sorted: `SetEnumValue.member`.
    SortedDomain,
}

/// A set's physical Java class, independent of an enumeration cached for its contents.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SetClass {
    Enumeration,
    Interval,
    Overridden,
    Subset,
    Functions,
    Records,
    Product,
    Intersection,
    Cup,
    Difference,
    Union,
    Predicate,
}

impl SetClass {
    pub fn java_name(self) -> &'static str {
        match self {
            Self::Enumeration => "SetEnumValue",
            Self::Interval => "IntervalValue",
            Self::Overridden => "UserValue",
            Self::Subset => "SubsetValue",
            Self::Functions => "SetOfFcnsValue",
            Self::Records => "SetOfRcdsValue",
            Self::Product => "SetOfTuplesValue",
            Self::Intersection => "SetCapValue",
            Self::Cup => "SetCupValue",
            Self::Difference => "SetDiffValue",
            Self::Union => "UnionValue",
            Self::Predicate => "SetPredValue",
        }
    }
}

/// Enumerated contents and the original physical class, when evaluation retained it.
#[derive(Debug)]
pub struct Set {
    pub elements: Rc<Vec<Value>>,
    pub java_class: Option<SetClass>,
    /// The elements as TLC built it of a set TLC holds unnormalized (`SetEnumValue` with
    /// `isNorm` false), which `elements` holds sorted, with the replay that built it: see
    /// `mark_unnormalized`.
    written: RefCell<Option<Hold>>,
}

impl std::ops::Deref for Set {
    type Target = Vec<Value>;

    fn deref(&self) -> &Self::Target {
        &self.elements
    }
}

/// The sets TLC keeps lazily, and the infinite ones.
#[derive(Clone, Debug)]
pub enum Lazy {
    Nat,
    Int,
    Real,
    Strings,
    Subset(Value),
    FunctionSet(Value, Value),
    /// The fields in TLC's order, then the order written.
    RecordSet(Vec<(Rc<Text>, Value)>, Vec<u32>),
    Product(Vec<Value>),
    Seq(Value),
    /// `S \cap T`, `S \cup T` and `S \ T` where TLC keeps them lazy (`SetCapValue`,
    /// `SetCupValue`, `SetDiffValue`): neither operand is a set enumeration or an interval, or
    /// for `\cup` one is and the other isn't, which TLC puts first.
    Cap(Value, Value),
    Cup(Value, Value),
    Diff(Value, Value),
    /// `TLC!Any`, the `UserValue` of `AnySet`: every value is in it, and TLC can't say whether
    /// it is empty.
    Any,
    /// `UNION S` where some element of S isn't a set enumeration (`UnionValue`).
    Union(Value),
    /// `{x \in S : P}` of an S TLC can't enumerate, or an infinite one (`SetPredValue`): the
    /// evaluator tests its members, and TLC fails to enumerate it as it fails S.
    Filter(Value, Rc<crate::eval::Predicate>),
}

impl Lazy {
    /// Whether TLC holds the set as a `UserValue` its module overrides (Nat, Int, Real, STRING,
    /// Seq(S)), which isn't `Enumerable` and compares only with another.
    pub fn is_overridden(&self) -> bool {
        matches!(
            self,
            Lazy::Nat | Lazy::Int | Lazy::Real | Lazy::Strings | Lazy::Seq(_) | Lazy::Any
        )
    }
}

/// A lazy set's construction and its physical class, when evaluation retained it.
#[derive(Clone, Debug)]
pub struct LazySet {
    pub construction: Lazy,
    pub java_class: Option<SetClass>,
}

impl std::ops::Deref for LazySet {
    type Target = Lazy;

    fn deref(&self) -> &Self::Target {
        &self.construction
    }
}

impl Lazy {
    fn java_class(&self) -> SetClass {
        match self {
            Lazy::Nat | Lazy::Int | Lazy::Real | Lazy::Strings | Lazy::Seq(_) | Lazy::Any => {
                SetClass::Overridden
            }
            Lazy::Subset(_) => SetClass::Subset,
            Lazy::FunctionSet(..) => SetClass::Functions,
            Lazy::RecordSet(..) => SetClass::Records,
            Lazy::Product(_) => SetClass::Product,
            Lazy::Cap(..) => SetClass::Intersection,
            Lazy::Cup(..) => SetClass::Cup,
            Lazy::Diff(..) => SetClass::Difference,
            Lazy::Union(_) => SetClass::Union,
            Lazy::Filter(..) => SetClass::Predicate,
        }
    }
}

/// The proven physical Java class of a set, or None if evaluation or transfer lost it.
pub fn java_set_class(value: &Value) -> Option<SetClass> {
    match value {
        Value::Set(set) | Value::Unsorted(set) => set.java_class,
        Value::Interval(_, _, class) => *class,
        Value::Lazy(lazy) => lazy.java_class,
        _ => None,
    }
}

pub(crate) fn has_java_set_representation(value: &Value) -> bool {
    match value {
        Value::Set(set) | Value::Unsorted(set) => set.java_class == Some(SetClass::Enumeration),
        Value::Interval(_, _, class) => *class == Some(SetClass::Interval),
        Value::Lazy(lazy) => lazy.java_class == Some(lazy.construction.java_class()),
        _ => false,
    }
}

// A scalar or function is certainly not Reducible, even when its concrete subtype is unknown.
pub(crate) fn set_dispatch_is_known(value: &Value) -> bool {
    match value {
        Value::Null => false,
        Value::Bool(_)
        | Value::Int(_)
        | Value::Str(_)
        | Value::Model(_)
        | Value::Function(_)
        | Value::Lambda(_) => true,
        Value::Set(_) | Value::Unsorted(_) | Value::Interval(..) | Value::Lazy(_) => {
            has_java_set_representation(value)
        }
    }
}

/// Whether TLC's value of a set is `Enumerable`, which it may try to enumerate, even where the
/// set is infinite.
pub fn is_enumerable(value: &Value) -> bool {
    match value {
        Value::Lazy(lazy) => !lazy.is_overridden(),
        _ => value.is_set() || matches!(value, Value::Unsorted(_)),
    }
}

#[derive(Clone, Debug)]
pub enum Value {
    /// A literal semantic node whose TLC tool value was never initialized.
    Null,
    Bool(bool),
    Int(i32),
    Str(Rc<Text>),
    Model(Rc<Text>),
    /// A set enumeration, its elements distinct and in TLC's order.
    Set(Rc<Set>),
    /// A set enumeration TLC fails to normalize, its elements as written: TLC keeps it as it is
    /// until it fingerprints or prints it, which then fails.
    Unsorted(Rc<Set>),
    /// `low..high`, an `IntervalValue`.
    Interval(i32, i32, Option<SetClass>),
    Function(Rc<Function>),
    Lazy(Rc<LazySet>),
    /// `[x \in S |-> e]` over an S TLC can't enumerate or an infinite one, which TLC keeps lazy
    /// (`FcnLambdaValue`): the evaluator applies it.
    Lambda(Rc<crate::eval::Lambda>),
}

/// Whether an initialized value carries an unavailable literal in its observable data.
pub(crate) fn contains_uninitialized(value: &Value) -> bool {
    let mut pending = vec![value];
    let mut seen = std::collections::HashSet::new();
    while let Some(value) = pending.pop() {
        match value {
            Value::Null => return true,
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
            Value::Lazy(lazy) => match &***lazy {
                Lazy::Subset(base)
                | Lazy::Seq(base)
                | Lazy::Union(base)
                | Lazy::Filter(base, _) => pending.push(base),
                Lazy::FunctionSet(left, right)
                | Lazy::Cap(left, right)
                | Lazy::Cup(left, right)
                | Lazy::Diff(left, right) => pending.extend([left, right]),
                Lazy::RecordSet(fields, _) => pending.extend(fields.iter().map(|(_, value)| value)),
                Lazy::Product(sets) => pending.extend(sets),
                _ => {}
            },
            _ => {}
        }
    }
    false
}

/// The field names tlc2.value.impl.RecordValue interns as it initializes, in the order it declares
/// them.
pub const RECORD_VALUE_FIELDS: [&str; 10] = [
    "beginLine",
    "beginColumn",
    "endLine",
    "endColumn",
    "module",
    "name",
    "location",
    "context",
    "parameters",
    "_action",
];

thread_local! {
    // Whether the evaluator has built a record since `take_is_record_built` last asked: TLC
    // initializes RecordValue, which interns its field names, as it builds its first record.
    static IS_RECORD_BUILT: Cell<bool> = const { Cell::new(false) };
}

fn new_class(class: Class) -> Cell<Class> {
    if class == Class::Record {
        IS_RECORD_BUILT.set(true);
    }
    Cell::new(class)
}

/// Whether the evaluator has built a record since the last call.
pub(crate) fn take_is_record_built() -> bool {
    IS_RECORD_BUILT.replace(false)
}

impl Value {
    pub fn interval(low: i32, high: i32) -> Value {
        Value::Interval(low, high, Some(SetClass::Interval))
    }

    pub fn lazy(construction: Lazy) -> Value {
        let class = construction.java_class();
        Self::lazy_with_class(construction, Some(class))
    }

    pub fn lazy_with_class(construction: Lazy, java_class: Option<SetClass>) -> Value {
        if matches!(construction, Lazy::Any) && java_class == Some(SetClass::Overridden) {
            thread_local! {
                static ANY: Rc<LazySet> = Rc::new(LazySet {
                    construction: Lazy::Any,
                    java_class: Some(SetClass::Overridden),
                });
            }
            return Value::Lazy(ANY.with(Rc::clone));
        }
        Value::Lazy(Rc::new(LazySet {
            construction,
            java_class,
        }))
    }

    pub fn unsorted(elements: Vec<Value>) -> Value {
        Value::Unsorted(Rc::new(Set {
            elements: Rc::new(elements),
            java_class: Some(SetClass::Enumeration),
            written: RefCell::new(None),
        }))
    }

    pub(crate) fn without_set_provenance(self) -> Value {
        match self {
            Value::Set(set) if set.java_class.is_some() => {
                let original = Value::Set(set);
                let written = unnormalized(&original);
                let Value::Set(set) = original else {
                    unreachable!("a set enumeration")
                };
                let result = Value::set_from_rc(Rc::clone(&set.elements), None);
                if let Some(written) = written {
                    mark_unnormalized(&result, written);
                }
                result
            }
            Value::Unsorted(set) if set.java_class.is_some() => Value::Unsorted(Rc::new(Set {
                elements: Rc::clone(&set.elements),
                java_class: None,
                written: RefCell::new(None),
            })),
            Value::Interval(low, high, _) => Value::Interval(low, high, None),
            Value::Lazy(lazy) if lazy.java_class.is_some() => {
                Value::lazy_with_class(lazy.construction.clone(), None)
            }
            other => other,
        }
    }

    pub(crate) fn set_items(&self) -> Option<&[Value]> {
        match self {
            Value::Set(set) => Some(set.as_slice()),
            Value::Unsorted(items) => Some(items.as_slice()),
            _ => None,
        }
    }

    pub fn set(elements: Vec<Value>) -> Value {
        Self::set_with_class(elements, Some(SetClass::Enumeration))
    }

    pub fn set_with_class(elements: Vec<Value>, java_class: Option<SetClass>) -> Value {
        Self::set_from_rc(Rc::new(elements), java_class)
    }

    pub fn set_from_rc(elements: Rc<Vec<Value>>, java_class: Option<SetClass>) -> Value {
        Value::Set(Rc::new(Set {
            elements,
            java_class,
            written: RefCell::new(None),
        }))
    }

    pub fn empty_set() -> Value {
        Value::set(Vec::new())
    }

    pub fn function(domain: Vec<Value>, range: Vec<Value>, class: Class) -> Value {
        Value::Function(Rc::new(Function {
            domain,
            range,
            class: new_class(class),
            java_class: Cell::new(match class {
                Class::Lambda => None,
                other => Some(other),
            }),
            is_counter_example: std::cell::Cell::new(Some(false)),
            is_eager_record: std::cell::Cell::new(class == Class::Plain),
            written: RefCell::new(None),
            search: Cell::new(Search::Unknown),
            interval: None,
            is_domain_interval: Cell::new(false),
        }))
    }

    /// A function over `low..low + range.len() - 1`, built over that interval.
    pub fn over_interval(low: i32, range: Vec<Value>, class: Class) -> Value {
        let (low, high) = if range.is_empty() && low == i32::MIN {
            (1, 0)
        } else {
            (low, (i64::from(low) + range.len() as i64 - 1) as i32)
        };
        Value::Function(Rc::new(Function {
            domain: (low..=high).map(Value::Int).collect(),
            range,
            class: new_class(class),
            java_class: Cell::new(match class {
                Class::Lambda => None,
                other => Some(other),
            }),
            is_counter_example: std::cell::Cell::new(Some(false)),
            is_eager_record: std::cell::Cell::new(class == Class::Plain),
            written: RefCell::new(None),
            search: Cell::new(Search::Unknown),
            interval: Some((low, high)),
            is_domain_interval: Cell::new(false),
        }))
    }

    pub fn tuple(elements: Vec<Value>) -> Value {
        Value::over_interval(1, elements, Class::Tuple)
    }

    /// `TupleValue.EmptyTuple`, the one empty sequence of TLC's that SubSeq and SelectSeq give,
    /// which a dumped trace writes once.
    pub fn empty_tuple() -> Value {
        thread_local! {
            static EMPTY: Value = Value::tuple(Vec::new());
        }
        EMPTY.with(Value::clone)
    }

    /// Whether the value is a `TupleValue`, as opposed to a function TLC converts to one.
    pub fn is_tuple_class(&self) -> bool {
        matches!(self, Value::Function(function) if function.class.get() == Class::Tuple)
    }

    /// A record of fields as written: sorted into TLC's order, keeping the written order where it
    /// differs.
    pub fn record(fields: Vec<(Rc<Text>, Value)>) -> Evaluated<Value> {
        let keys: Vec<Value> = fields
            .iter()
            .map(|(name, _)| Value::Str(Rc::clone(name)))
            .collect();
        let values = fields.into_iter().map(|(_, value)| value).collect();
        written_function(keys, values, Class::Record)
    }

    pub(crate) fn counter_example(fields: Vec<(Rc<Text>, Value)>) -> Evaluated<Value> {
        let value = Self::record(fields)?;
        if let Value::Function(record) = &value {
            record.is_counter_example.set(Some(true));
        }
        Ok(value)
    }

    pub fn as_function(&self) -> Option<&Rc<Function>> {
        match self {
            Value::Function(function) => Some(function),
            _ => None,
        }
    }

    pub fn is_set(&self) -> bool {
        matches!(self, Value::Set(_) | Value::Interval(..) | Value::Lazy(_))
    }

    pub fn kind_name(&self) -> &'static str {
        match self {
            Value::Null => "null tool value",
            Value::Bool(_) => "boolean",
            Value::Int(_) => "integer",
            Value::Str(_) => "string",
            Value::Model(_) => "model value",
            Value::Function(_) | Value::Lambda(_) => "function",
            _ => "set",
        }
    }
}

/// A function of keys and values as written: sorted into TLC's order, keeping the written order
/// where it differs. A key written twice keeps its last value, as `@@` and a record do not
/// allow; the caller checks that.
pub fn written_function(keys: Vec<Value>, values: Vec<Value>, class: Class) -> Evaluated<Value> {
    let mut order: Vec<u32> = (0..keys.len() as u32).collect();
    let mut failure = None;
    order.sort_by(|&left, &right| {
        compare(&keys[left as usize], &keys[right as usize]).unwrap_or_else(|error| {
            failure.get_or_insert(error);
            Ordering::Equal
        })
    });
    if let Some(error) = failure {
        return Err(error);
    }
    let is_sorted = order
        .iter()
        .enumerate()
        .all(|(at, &index)| at as u32 == index);
    // The written order, as positions in the sorted domain.
    let written = (!is_sorted).then(|| {
        let mut positions = vec![0; order.len()];
        for (at, &index) in order.iter().enumerate() {
            positions[index as usize] = at as u32;
        }
        positions
    });
    let mut domain = Vec::with_capacity(keys.len());
    let mut range = Vec::with_capacity(keys.len());
    for &index in &order {
        domain.push(keys[index as usize].clone());
        range.push(values[index as usize].clone());
    }
    Ok(Value::Function(Rc::new(Function {
        domain,
        range,
        class: new_class(class),
        java_class: Cell::new(match class {
            Class::Lambda => None,
            other => Some(other),
        }),
        is_counter_example: std::cell::Cell::new(Some(false)),
        is_eager_record: std::cell::Cell::new(class == Class::Plain),
        written: RefCell::new(written),
        search: Cell::new(Search::Unknown),
        interval: None,
        is_domain_interval: Cell::new(false),
    })))
}

/// A function of keys and values in any order, sorted into TLC's order, as TLC holds one it
/// builds normalized.
pub fn sorted_function(keys: Vec<Value>, values: Vec<Value>, class: Class) -> Evaluated<Value> {
    let function = written_function(keys, values, class)?;
    if let Value::Function(inner) = &function {
        sort(inner);
    }
    Ok(function)
}

// --- TLC's order, as the store's `compare` ---

// TLC interns a text it makes after it starts as it makes it, after every text it interned as it
// started: two such texts the evaluator didn't rank compare in an order it can't know.
fn compare_texts(left: &Text, right: &Text) -> Evaluated<Ordering> {
    // TLC interns a text once, so the same text compares equal however each was made.
    if left.units == right.units {
        return Ok(Ordering::Equal);
    }
    match (left.rank, right.rank) {
        (-1, -1) => fail("an order of strings TLC made as it searched"),
        (_, -1) => Ok(Ordering::Less),
        (-1, _) => Ok(Ordering::Greater),
        (left, right) => Ok(left.cmp(&right)),
    }
}

fn check_model_types(left: &Value, right: &Value, is_equality: bool) -> Evaluated<()> {
    let (Value::Model(left_text), Value::Model(right_text)) = (left, right) else {
        return Ok(());
    };
    let (left_type, right_type) = (left_text.model_type(), right_text.model_type());
    if left_type != 0 && right_type != 0 && left_type != right_type {
        return typed_model_failure(left, right, is_equality);
    }
    Ok(())
}

// TLC's error for a typed model value compared with a value of another type, as
// `checkModelValueTypes` in `src/values.ts` words it.
fn typed_model_failure<T>(left: &Value, right: &Value, is_equality: bool) -> Evaluated<T> {
    let action = if is_equality {
        "check equality of"
    } else {
        "compare"
    };
    let (reason, text) = match (left, right) {
        (Value::Model(_), Value::Model(_)) => (
            "differently typed model values",
            format!(
                "Attempted to {action} the differently-typed model values {} and {}",
                format_pretty(left),
                format_pretty(right)
            ),
        ),
        (Value::Model(_), _) => (
            "typed model value",
            format!(
                "Attempted to {action}{} typed model value {} and non-model value\n{}",
                if is_equality { "" } else { " the" },
                format_pretty(left),
                format_pretty(right)
            ),
        ),
        _ => (
            "typed model value",
            format!(
                "Attempted to {action} the typed model value {} and the non-model value\n{}",
                format_pretty(right),
                format_pretty(left)
            ),
        ),
    };
    fail_runtime(reason, text)
}

thread_local! {
    // Which replay's sets TLC holds unnormalized: a set holds its elements in the order TLC
    // built it (`Set::written`) for the replay that built it, and `clear_unnormalized` starts
    // another.
    static REPLAY: Cell<u64> = const { Cell::new(0) };
    // How many times a set built before others TLC held unnormalized again, which may change how
    // the elements of those others sort (`Hold::sorting`).
    static REHELD: Cell<u64> = const { Cell::new(0) };
}

// A set TLC holds unnormalized: the replay that built it, its elements as TLC built it, and how
// those sort (`sorts_without_effects`) as TLC built it, with `REHELD` then. That holds while no
// set within them is held unnormalized again, as only a set built before them can be; one that
// TLC normalized since sorts no worse (`Sorting::Nested` normalizes nothing more of sets
// normalized already).
#[derive(Debug)]
struct Hold {
    replay: u64,
    written: Written,
    sorting: Option<(u64, Sorting)>,
}

// The elements as TLC built a set it holds unnormalized.
#[derive(Debug)]
enum Written {
    // The set's own elements, in their order: TLC built it in order, each element once.
    Held,
    Values(Vec<Value>),
}

// A set TLC held unnormalized, with its elements as TLC built it.
type Unnormalized = (Weak<Set>, Written);

// The elements as TLC built a set it holds unnormalized in this replay, borrowed.
enum WrittenRef<'a> {
    Held(&'a [Value]),
    Values(std::cell::Ref<'a, Vec<Value>>),
}

impl std::ops::Deref for WrittenRef<'_> {
    type Target = [Value];

    fn deref(&self) -> &[Value] {
        match self {
            WrittenRef::Held(values) => values,
            WrittenRef::Values(values) => values,
        }
    }
}

// The elements as TLC built them of a set TLC holds unnormalized in this replay.
fn written_of(set: &Set) -> Option<WrittenRef<'_>> {
    let hold = set.written.borrow();
    match &*hold {
        Some(Hold {
            replay,
            written: Written::Held,
            ..
        }) if *replay == REPLAY.get() => Some(WrittenRef::Held(&set.elements)),
        Some(Hold {
            replay,
            written: Written::Values(_),
            ..
        }) if *replay == REPLAY.get() => std::cell::Ref::filter_map(hold, |hold| match hold {
            Some(Hold {
                written: Written::Values(values),
                ..
            }) => Some(values),
            _ => None,
        })
        .ok()
        .map(WrittenRef::Values),
        _ => None,
    }
}

// Puts back the elements as TLC built them of a set TLC holds unnormalized again.
fn hold_unnormalized(set: &Set, written: Written) {
    REHELD.set(REHELD.get() + 1);
    hold_built(set, written, None);
}

// Holds a set TLC built unnormalized, with how its elements as written sort, where known.
fn hold_built(set: &Set, written: Written, sorting: Option<Sorting>) {
    *set.written.borrow_mut() = Some(Hold {
        replay: REPLAY.get(),
        written,
        sorting: sorting.map(|sorting| (REHELD.get(), sorting)),
    });
}

// Takes out the elements as TLC built them of a set TLC holds unnormalized, as it normalizes it,
// with how they sort where that is known still.
fn take_unnormalized(set: &Set) -> Option<(Written, Option<Sorting>)> {
    let hold = set.written.borrow_mut().take()?;
    (hold.replay == REPLAY.get()).then(|| {
        let sorting = hold
            .sorting
            .filter(|(reheld, _)| *reheld == REHELD.get())
            .map(|(_, sorting)| sorting);
        (hold.written, sorting)
    })
}

/// Records a set a replay built as TLC holds it unnormalized (`SetEnumValue` with `isNorm`
/// false), with its elements as TLC built it.
pub(crate) fn mark_unnormalized(set: &Value, written: Vec<Value>) {
    if let Value::Set(elements) = set {
        // A set nothing else holds yet is within no other.
        if Rc::strong_count(elements) == 1 {
            hold_built(elements, Written::Values(written), None);
        } else {
            hold_unnormalized(elements, Written::Values(written));
        }
    }
}

/// A set enumeration as TLC builds it of these elements, which it holds unnormalized
/// (`mark_unnormalized`), sorted as `set_of` sorts them but leaving each set's normalization as
/// it was (`preserving_set_normalization`). Where TLC fails to sort them, the failure, and the
/// elements back.
pub(crate) fn held_set_of(elements: Vec<Value>) -> Result<Value, (EvalError, Vec<Value>)> {
    // One element or none sorts without a comparison, and elements in order without duplicates
    // are the set's own. Where no comparison of them fails, what the sort normalizes is put back,
    // so it sorts them without normalizing.
    let sorting = is_sorted_without_effects(&elements);
    let set = match sorting {
        Some((sorting, true)) => {
            let set = Value::set(elements);
            if let Value::Set(held) = &set {
                hold_built(held, Written::Held, Some(sorting));
            }
            return Ok(set);
        }
        Some((_, false)) => {
            let mut distinct = elements.clone();
            distinct.sort_by(compare_without_effects);
            distinct
                .dedup_by(|later, kept| compare_without_effects(later, kept) == Ordering::Equal);
            Ok(Value::set(distinct))
        }
        None => preserving_set_normalization(|| set_of(elements.clone())),
    };
    match set {
        Ok(set) => {
            if let Value::Set(held) = &set {
                hold_built(
                    held,
                    Written::Values(elements),
                    sorting.map(|(sorting, _)| sorting),
                );
            }
            Ok(set)
        }
        Err(error) => Err((error, elements)),
    }
}

/// The elements of a set TLC holds unnormalized, as TLC built it.
pub(crate) fn unnormalized(set: &Value) -> Option<Vec<Value>> {
    let Value::Set(elements) = set else {
        return None;
    };
    written_of(elements).map(|written| written.to_vec())
}

thread_local! {
    static NORMALIZATION_JOURNALS: RefCell<Vec<Vec<Unnormalized>>> = const { RefCell::new(Vec::new()) };
    // Whether a `preserving_set_normalization` is in progress, which spares each normalization
    // outside one a look at the journals.
    static IS_JOURNALING: Cell<bool> = const { Cell::new(false) };
}

pub(crate) fn preserving_set_normalization<T>(run: impl FnOnce() -> T) -> T {
    struct Restore;
    impl Drop for Restore {
        fn drop(&mut self) {
            let changes = NORMALIZATION_JOURNALS.with(|journals| {
                let mut journals = journals.borrow_mut();
                let changes = journals.pop().expect("normalization journal");
                IS_JOURNALING.set(!journals.is_empty());
                changes
            });
            for (set, written) in changes.into_iter().rev() {
                if let Some(set) = set.upgrade() {
                    hold_unnormalized(&set, written);
                }
            }
        }
    }
    NORMALIZATION_JOURNALS.with(|journals| journals.borrow_mut().push(Vec::new()));
    IS_JOURNALING.set(true);
    let _restore = Restore;
    run()
}

// Notes a set TLC normalized, which a `preserving_set_normalization` in progress puts back.
fn journal_normalized(set: &Rc<Set>, written: Written) {
    if IS_JOURNALING.get() {
        NORMALIZATION_JOURNALS.with(|journals| {
            if let Some(journal) = journals.borrow_mut().last_mut() {
                journal.push((Rc::downgrade(set), written));
            }
        });
    }
}

/// Forgets the sets the last replay built.
pub(crate) fn clear_unnormalized() {
    REPLAY.set(REPLAY.get() + 1);
}

// TLC normalizes a set to enumerate, compare or print it.
pub(crate) fn normalize(value: &Value) {
    if let Value::Set(elements) = value
        && let Some((written, _)) = take_unnormalized(elements)
    {
        journal_normalized(elements, written);
    }
}

/// TLC's `deepNormalize` of a value Print or PrintT prints, which normalizes, in place, each set
/// enumeration it reaches: a set enumeration's elements and then the set (`SetEnumValue`), a
/// tuple's elements, a record's or a function's values and then its domain (`RecordValue`,
/// `FcnRcdValue`), and the operands of a lazy set, in TLC's order of them. `Ok(false)` where the
/// walk reaches a value whose Java class the evaluator doesn't know, or one it doesn't follow,
/// before any failure; a failure is the first set enumeration TLC fails to normalize.
pub(crate) fn print_normalize(value: &Value) -> Evaluated<bool> {
    let mut seen = std::collections::HashSet::new();
    print_normalize_inner(value, &mut seen)
}

fn print_normalize_inner(
    value: &Value,
    seen: &mut std::collections::HashSet<usize>,
) -> Evaluated<bool> {
    let all = |values: &mut dyn Iterator<Item = &Value>,
               seen: &mut std::collections::HashSet<usize>| {
        for value in values {
            if !print_normalize_inner(value, seen)? {
                return Ok(false);
            }
        }
        Ok(true)
    };
    match value {
        Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::Model(_) => Ok(true),
        Value::Interval(..) => Ok(has_java_set_representation(value)),
        Value::Null | Value::Lambda(_) => Ok(false),
        Value::Set(set) => {
            if !has_java_set_representation(value) {
                return Ok(false);
            }
            if !seen.insert(Rc::as_ptr(set) as usize) {
                return Ok(true);
            }
            let written = unnormalized(value);
            let elements = written.as_deref().unwrap_or(set.elements.as_slice());
            if !all(&mut elements.iter(), seen)? {
                return Ok(false);
            }
            normalize_enumeration(value)?;
            Ok(true)
        }
        Value::Unsorted(set) => {
            if !has_java_set_representation(value) {
                return Ok(false);
            }
            if !all(&mut set.iter(), seen)? {
                return Ok(false);
            }
            Err(unsorted_failure(set))
        }
        Value::Function(function) => {
            if !seen.insert(Rc::as_ptr(function) as usize) {
                return Ok(true);
            }
            match function.java_class.get() {
                Some(Class::Tuple) => all(&mut function.range.iter(), seen),
                Some(Class::Record | Class::Plain) => {
                    let written = function.written.borrow().clone();
                    let in_order = match &written {
                        Some(order) => order
                            .iter()
                            .map(|&index| function.range.get(index as usize))
                            .collect::<Option<Vec<_>>>(),
                        None => Some(function.range.iter().collect()),
                    };
                    let Some(in_order) = in_order else {
                        return Ok(false);
                    };
                    if !all(&mut in_order.into_iter(), seen)? {
                        return Ok(false);
                    }
                    // `normalize` sorts the domain, which fails only on keys TLC can't compare.
                    let is_comparable = function.domain.len() <= 1
                        || function
                            .domain
                            .iter()
                            .all(|key| matches!(key, Value::Int(_)))
                        || function
                            .domain
                            .iter()
                            .all(|key| matches!(key, Value::Str(_)))
                        || function
                            .domain
                            .iter()
                            .all(|key| matches!(key, Value::Bool(_)));
                    Ok(is_comparable)
                }
                Some(Class::Lambda) | None => Ok(false),
            }
        }
        Value::Lazy(lazy) => {
            if !has_java_set_representation(value) || lazy.is_overridden() {
                return Ok(false);
            }
            if !seen.insert(Rc::as_ptr(lazy) as usize) {
                return Ok(true);
            }
            match &***lazy {
                Lazy::Subset(base) | Lazy::Union(base) | Lazy::Filter(base, _) => {
                    print_normalize_inner(base, seen)
                }
                Lazy::FunctionSet(left, right)
                | Lazy::Cap(left, right)
                | Lazy::Cup(left, right)
                | Lazy::Diff(left, right) => all(&mut [left, right].into_iter(), seen),
                Lazy::RecordSet(fields, _) => all(&mut fields.iter().map(|(_, set)| set), seen),
                Lazy::Product(factors) => all(&mut factors.iter(), seen),
                Lazy::Nat | Lazy::Int | Lazy::Real | Lazy::Strings | Lazy::Seq(_) | Lazy::Any => {
                    Ok(false)
                }
            }
        }
    }
}

/// `IntervalValue.size`: an interval of more than 2^31 - 1 elements has no int size.
pub fn interval_size(low: i32, high: i32) -> Evaluated<usize> {
    let size = (i64::from(high) - i64::from(low) + 1).max(0);
    if size > i64::from(i32::MAX) {
        return fail_runtime(
            "an interval too large to size",
            format!(
                "Size of interval value exceeds the maximum representable size (32bits): {}.",
                format_pretty(&Value::interval(low, high))
            ),
        );
    }
    Ok(size as usize)
}

/// The most elements of an interval the evaluator builds.
pub(crate) const MAXIMUM_INTERVAL: usize = 1 << 24;

/// The most elements of an interval the evaluator walks without building it, as TLC's
/// `IntervalValue.Enumerator` does, where TLC collects what it keeps of them, up to its bound
/// (`ValueVec.addElement`), or may walk billions.
pub(crate) const MAXIMUM_WALK: usize = 4 * tla_values::SET_BOUND;

fn normalize_enumeration(value: &Value) -> Evaluated<()> {
    let Value::Set(set) = value else {
        return Ok(());
    };
    // The set's elements as written, taken out while they sort (which compares only them), and
    // put back where they fail to, which leaves the set unnormalized.
    let Some((written, sorting)) = take_unnormalized(set) else {
        return Ok(());
    };
    let as_written = match &written {
        Written::Held => &set.elements[..],
        Written::Values(values) => &values[..],
    };
    if has_java_set_representation(value)
        && let Err(error) = normalize_written(set, as_written, sorting)
    {
        hold_unnormalized(set, written);
        return Err(error);
    }
    journal_normalized(set, written);
    Ok(())
}

/// The elements of a set TLC can enumerate, in TLC's order.
pub fn elements(value: &Value) -> Evaluated<Rc<Vec<Value>>> {
    normalize_enumeration(value)?;
    match value {
        Value::Set(elements) => Ok(Rc::clone(&elements.elements)),
        // An interval TLC walks without building it or computing its size
        // (`IntervalValue.elements`), which the evaluator builds, up to a size.
        Value::Interval(low, high, _)
            if i64::from(*high) - i64::from(*low) >= MAXIMUM_INTERVAL as i64 =>
        {
            if WALKS_DECLINED.with(Cell::get) {
                return fail(WALKED_INTERVAL);
            }
            fail("an interval too large to build")
        }
        Value::Interval(low, high, _) => Ok(Rc::new((*low..=*high).map(Value::Int).collect())),
        Value::Lazy(lazy) => {
            if let Lazy::Filter(_, predicate) = &***lazy
                && let Some(elements) = predicate.converted()
            {
                return Ok(elements);
            }
            // TLC finds a set its parts empty to be empty before it enumerates any of them.
            // The set's own `elements` enumerates it, where TLC's exception passes.
            if crate::sets::is_empty_by_argument(value) {
                Ok(Rc::new(Vec::new()))
            } else {
                comparing(value, || crate::sets::enumerate(lazy).map(Rc::new))
            }
        }
        // `SetEnumValue.Enumerator` normalizes the set first, which fails in the set's own
        // `elements` (or `normalize`, where a constructor asks it), whose FingerprintException
        // has the set's source.
        Value::Unsorted(values) => comparing(value, || Err(unsorted_failure(values))),
        _ => fail(format!("expected a set, not a {}", value.kind_name())),
    }
}

fn is_record(function: &Function) -> bool {
    function
        .domain
        .iter()
        .all(|key| matches!(key, Value::Str(_)))
}

/// Whether a value holds a record whose fields are written in an order other than their sorted
/// one, which TLC prints otherwise once it sorts the record.
pub fn holds_record_out_of_order(value: &Value) -> bool {
    match value {
        Value::Set(_) | Value::Unsorted(_) => value
            .set_items()
            .expect("an enumeration")
            .iter()
            .any(holds_record_out_of_order),
        Value::Function(function) => {
            let is_out_of_order = function
                .written
                .borrow()
                .as_ref()
                .is_some_and(|written| !written.is_sorted());
            is_out_of_order
                || function.domain.iter().any(holds_record_out_of_order)
                || function.range.iter().any(holds_record_out_of_order)
        }
        _ => false,
    }
}

/// Forgets the written order of a function TLC sorts to compare it.
fn sort(function: &Function) {
    function.written.borrow_mut().take();
}

thread_local! {
    // While `failing_comparisons` runs, the left operands of the comparisons in progress,
    // `compareTo` and `equals`, outermost first, which a failure leaves in place: the values in
    // whose methods TLC's exception passes as it unwinds. `None` otherwise, so that no other
    // comparison keeps values.
    static COMPARING: RefCell<Option<Vec<Value>>> = const { RefCell::new(None) };
}

// Runs a comparison of `left`, which a failure leaves among those in progress.
pub(crate) fn comparing<T>(left: &Value, run: impl FnOnce() -> Evaluated<T>) -> Evaluated<T> {
    COMPARING.with_borrow_mut(|comparing| {
        if let Some(comparing) = comparing {
            comparing.push(left.clone());
        }
    });
    let compared = run();
    if compared.is_ok() {
        COMPARING.with_borrow_mut(|comparing| {
            if let Some(comparing) = comparing {
                comparing.pop();
            }
        });
    }
    compared
}

/// The elements of a set as TLC's `toSetEnum` makes them, which counts an interval first
/// (`IntervalValue.size`): one of more than 2^31 - 1 elements fails there.
pub(crate) fn counted(set: &Value) -> Evaluated<Rc<Vec<Value>>> {
    if let Value::Interval(low, high, _) = set {
        interval_size(*low, *high)?;
    }
    elements(set)
}

/// The elements of a set as the receiver of `equals` or `compareTo` holds them: a lazy set
/// converts itself (`convertAndCache`), which deep-normalizes the set enumeration it makes, and
/// fails to sort a set TLC holds unnormalized anywhere in it as TLC does; one whose deep
/// normalization the evaluator doesn't follow declines.
pub(crate) fn converted(set: &Value) -> Evaluated<Rc<Vec<Value>>> {
    let elements = counted(set)?;
    if matches!(set, Value::Lazy(lazy) if !lazy.is_overridden())
        && !crate::eval::deep_normalize(&elements)?
    {
        return fail(
            "a lazy set whose conversion's deep normalization the evaluator doesn't follow",
        );
    }
    Ok(elements)
}

/// TLC's `compareTo`, as the store's `compare`: an error where TLC can't compare the two.
pub fn compare(left: &Value, right: &Value) -> Evaluated<Ordering> {
    if matches!(left, Value::Null) || matches!(right, Value::Null) {
        return fail("a comparison involving a null tool value");
    }
    comparing(left, || compare_values(left, right))
}

// A set a comparison enumerates (`toSetEnum`), which fails where it is a power set whose base TLC
// can't count, in `SubsetValue.size` and in that of each power set nested in it: those join the
// comparisons in progress after the left operand, which is in progress already.
fn counted_power_set<T>(set: &Value, is_left: bool, enumerated: Evaluated<T>) -> Evaluated<T> {
    if let Err(error) = &enumerated
        && error
            .message
            .as_ref()
            .is_some_and(|message| message.code.is_none())
        && let Some(chain) = crate::sets::power_set_sizing_chain(set)
    {
        COMPARING.with_borrow_mut(|comparing| {
            if let Some(comparing) = comparing {
                comparing.extend(chain.into_iter().skip(usize::from(is_left)));
            }
        });
    }
    enumerated
}

/// What `run` gives, or where it fails, the values in whose `compareTo` or `equals` it fails,
/// outermost first.
pub fn failing_comparisons<T>(run: impl FnOnce() -> Evaluated<T>) -> Result<T, Vec<Value>> {
    let _rollback = crate::eval::rollback_filter_conversions();
    COMPARING.set(Some(Vec::new()));
    let compared = run();
    let comparing = COMPARING.take().unwrap_or_default();
    compared.map_err(|_| comparing)
}

// SetEnumValue delegates to an untyped ModelValue before it normalizes either set.
fn comparison_normalizes(left: &Value, right: &Value) -> bool {
    ![left, right]
        .into_iter()
        .any(|value| matches!(value, Value::Model(model) if model.model_type() == 0))
}

fn compare_values(left: &Value, right: &Value) -> Evaluated<Ordering> {
    if comparison_normalizes(left, right) {
        normalize_enumeration(left)?;
        normalize_enumeration(right)?;
    }
    match (left, right) {
        (Value::Int(left), Value::Int(right)) => Ok(left.cmp(right)),
        (Value::Bool(left), Value::Bool(right)) => Ok(left.cmp(right)),
        (Value::Str(left), Value::Str(right)) => compare_texts(left, right),
        (Value::Model(left_text), Value::Model(right_text)) => {
            check_model_types(left, right, false)?;
            compare_texts(left_text, right_text)
        }
        // `FcnLambdaValue.compareTo` builds the function first (`toFcnRcd`).
        (Value::Lambda(lambda), Value::Model(_)) => lambda_as_function(lambda),
        (Value::Model(model), _) => {
            if model.model_type() == 0 {
                Ok(Ordering::Less)
            } else {
                typed_model_failure(left, right, false)
            }
        }
        // `UserValue.compareTo` puts any model value first.
        (Value::Lazy(lazy), Value::Model(_)) if lazy.is_overridden() => Ok(Ordering::Greater),
        (_, Value::Model(model)) => {
            if model.model_type() == 0 {
                Ok(Ordering::Greater)
            } else {
                typed_model_failure(left, right, false)
            }
        }
        (Value::Function(left), Value::Function(right)) => compare_functions(left, right),
        (Value::Function(function), Value::Lambda(lambda)) => lambda_as_operand(function, lambda),
        (Value::Lambda(lambda), _) => lambda_as_function(lambda),
        (Value::Lazy(lazy), _) if lazy.is_overridden() => compare_overridden(left, lazy, right),
        // `SubsetValue.compareTo`: by the sets.
        (Value::Lazy(left_lazy), Value::Lazy(right_lazy))
            if matches!(
                (&***left_lazy, &***right_lazy),
                (Lazy::Subset(_), Lazy::Subset(_))
            ) =>
        {
            let (Lazy::Subset(base), Lazy::Subset(other_base)) = (&***left_lazy, &***right_lazy)
            else {
                unreachable!("two power sets")
            };
            compare(base, other_base)
        }
        (_, Value::Lazy(lazy)) if lazy.is_overridden() && left.is_set() => {
            incomparable(left, right, false)
        }
        _ if left.is_set() && right.is_set() => {
            // A set TLC keeps lazy compares as its set enumeration (`convertAndCache`).
            crate::sets::check_enumerated_bound(left)?;
            let left = counted_power_set(left, true, converted(left))?;
            crate::sets::check_enumerated_bound(right)?;
            let right = counted_power_set(right, false, counted(right))?;
            if left.len() != right.len() {
                return Ok(left.len().cmp(&right.len()));
            }
            for (left, right) in left.iter().zip(right.iter()) {
                let comparison = compare(left, right)?;
                if comparison != Ordering::Equal {
                    return Ok(comparison);
                }
            }
            Ok(Ordering::Equal)
        }
        _ => incomparable(left, right, false),
    }
}

fn compare_functions(left: &Rc<Function>, right: &Rc<Function>) -> Evaluated<Ordering> {
    sort(left);
    sort(right);
    match left.class.get() {
        // `RecordValue.compareTo`: the other as a record, by its fields' names, then their values.
        Class::Record if !is_record_like(right) => non_record(
            &Value::Function(Rc::clone(left)),
            &Value::Function(Rc::clone(right)),
            false,
        ),
        // `TupleValue.compareTo`: the other as a tuple, by its elements.
        Class::Tuple if is_tuple_like(right) => {
            let size = left.range.len();
            if size != right.range.len() {
                return Ok(size.cmp(&right.range.len()));
            }
            compare_all(&left.range, &right.range)
        }
        Class::Record => {
            let size = left.domain.len();
            if size != right.domain.len() {
                return Ok(size.cmp(&right.domain.len()));
            }
            match compare_all(&left.domain, &right.domain)? {
                Ordering::Equal => compare_all(&left.range, &right.range),
                comparison => Ok(comparison),
            }
        }
        _ => compare_function_records(left, right),
    }
}

// `FcnRcdValue.compareTo`, the other as a function: their sizes, then the keys of one over an
// interval as integers against the other's (`compareToInterval`, `compareOtherInterval`), then
// their values.
fn compare_function_records(left: &Function, right: &Function) -> Evaluated<Ordering> {
    let size = left.range.len();
    if size != right.range.len() {
        return Ok(size.cmp(&right.range.len()));
    }
    let integer_key = |key: &Value, separator: &str| match key {
        Value::Int(int) => Ok(i64::from(*int)),
        _ => fail_runtime(
            "a function over an interval compared with one over other keys",
            format!(
                "Attempted to compare integer with non-integer{separator}\n{}.",
                format_pretty(key)
            ),
        ),
    };
    let keys = match (function_interval(left), function_interval(right)) {
        (Some(_), _) if size == 0 => return Ok(Ordering::Equal),
        (Some(low), Some(other)) => low.cmp(&other),
        (Some(low), None) => {
            let mut comparison = Ordering::Equal;
            for (index, key) in right.domain.iter().enumerate() {
                comparison = (i64::from(low) + index as i64).cmp(&integer_key(key, ":")?);
                if comparison != Ordering::Equal {
                    break;
                }
            }
            comparison
        }
        (None, Some(other)) => {
            let mut comparison = Ordering::Equal;
            for (index, key) in left.domain.iter().enumerate() {
                comparison = integer_key(key, "")?.cmp(&(i64::from(other) + index as i64));
                if comparison != Ordering::Equal {
                    break;
                }
            }
            comparison
        }
        (None, None) => compare_all(&left.domain, &right.domain)?,
    };
    match keys {
        Ordering::Equal => compare_all(&left.range, &right.range),
        comparison => Ok(comparison),
    }
}

// The first of the comparisons of two lists of values, element by element, that isn't equal.
fn compare_all(left: &[Value], right: &[Value]) -> Evaluated<Ordering> {
    for (left, right) in left.iter().zip(right) {
        let comparison = compare(left, right)?;
        if comparison != Ordering::Equal {
            return Ok(comparison);
        }
    }
    Ok(Ordering::Equal)
}

// The low end of the interval TLC holds a function over, as `toFcnRcd` makes it: a tuple's 1..n.
fn function_interval(function: &Function) -> Option<i32> {
    match function.class.get() {
        Class::Tuple => Some(1),
        _ => function.interval.map(|(low, _)| low),
    }
}

// Whether `toRcd` gives a record of a function: a record, the empty tuple, and a function over
// strings TLC holds without an interval.
fn is_record_like(function: &Function) -> bool {
    match function.class.get() {
        Class::Record => true,
        Class::Tuple => function.domain.is_empty(),
        _ => function.interval.is_none() && is_record(function),
    }
}

// Whether `toTuple` gives a tuple of a function: a tuple, the empty record, and a function over
// 1..n.
fn is_tuple_like(function: &Function) -> bool {
    match function.class.get() {
        Class::Tuple => true,
        Class::Record => function.domain.is_empty(),
        _ => match function.interval {
            Some((low, _)) => low == 1 || function.domain.is_empty(),
            None => function.domain.iter().enumerate().all(
                |(index, key)| matches!(key, Value::Int(int) if *int as i64 == index as i64 + 1),
            ),
        },
    }
}

/// TLC's `equals`, as the store's: values of kinds TLC can't compare fail, but a model value
/// without a type is unequal to anything else.
pub fn equals(left: &Value, right: &Value) -> Evaluated<bool> {
    if matches!(left, Value::Null) || matches!(right, Value::Null) {
        return fail("an equality involving a nested null tool value");
    }
    comparing(left, || equal_values(left, right))
}

fn equal_values(left: &Value, right: &Value) -> Evaluated<bool> {
    if comparison_normalizes(left, right) {
        normalize_enumeration(left)?;
    }
    if let Value::Unsorted(values) = left
        && matches!(
            right,
            Value::Set(_) | Value::Interval(..) | Value::Unsorted(_)
        )
    {
        return Err(unsorted_failure(values));
    }
    // `SetEnumValue.equals` converts a lazy set to its enumeration before it normalizes itself.
    if let (Value::Unsorted(values), Value::Lazy(lazy)) = (left, right)
        && !lazy.is_overridden()
    {
        elements(right)?;
        return Err(unsorted_failure(values));
    }
    if comparison_normalizes(left, right) {
        normalize_enumeration(right)?;
    }
    match (left, right) {
        (Value::Int(left), Value::Int(right)) => Ok(left == right),
        (Value::Bool(left), Value::Bool(right)) => Ok(left == right),
        (Value::Str(left), Value::Str(right)) => Ok(left.units == right.units),
        (Value::Model(left_text), Value::Model(right_text)) => {
            check_model_types(left, right, true)?;
            Ok(left_text.units == right_text.units)
        }
        // `UserValue.equals` compares, which puts any model value first.
        (Value::Lazy(lazy), Value::Model(_)) if lazy.is_overridden() => Ok(false),
        // `FcnLambdaValue.equals` builds the function first (`toFcnRcd`).
        (Value::Lambda(lambda), Value::Model(_)) => lambda_as_function(lambda),
        (Value::Model(model), _) | (_, Value::Model(model)) => {
            if model.model_type() == 0 {
                Ok(false)
            } else {
                typed_model_failure(left, right, true)
            }
        }
        // `SetEnumValue.equals` normalizes a set TLC holds unnormalized, which fails.
        (Value::Unsorted(values), Value::Set(_) | Value::Interval(..) | Value::Unsorted(_)) => {
            Err(unsorted_failure(values))
        }
        (Value::Function(left_function), Value::Function(right_function)) => {
            let (left_value, right_value) = (left, right);
            let (left, right) = (left_function, right_function);
            sort(left);
            sort(right);
            let size = left.domain.len();
            // `RecordValue.equals` fails on a function `toRcd` can't make a record of. A
            // `FcnRcdValue` or a `TupleValue` takes the other as a function (`toFcnRcd`), a record
            // as the function of its fields' names in its order, and compares sizes, then keys,
            // as below, where an integer key equated with a string fails in the key's `equals`.
            // The evaluator follows that where each domain is all integers or all strings, which
            // TLC holds sorted, and where the receiver is a function of a known class with another
            // of a known class (`is_function_receiver`).
            let is_plain_domain = |function: &Function| {
                is_record(function)
                    || function
                        .domain
                        .iter()
                        .all(|key| matches!(key, Value::Int(_)))
            };
            if size > 0
                && !right.domain.is_empty()
                && is_record(left) != is_record(right)
                && (left.class.get() == Class::Record
                    || !is_plain_domain(left)
                    || !is_plain_domain(right))
                && !is_function_receiver(left, right)
            {
                return non_record(left_value, right_value, true);
            }
            if size != right.domain.len() {
                return Ok(false);
            }
            // `FcnRcdValue.equals`, which `TupleValue.equals` reaches with the other as a function:
            // the keys of one over an interval as integers against the other's.
            let are_keys_equal = match (function_interval(left), function_interval(right)) {
                (Some(low), Some(other)) => size == 0 || low == other,
                (Some(low), None) => are_interval_keys(low, &right.domain)?,
                (None, Some(low)) => are_interval_keys(low, &left.domain)?,
                (None, None) => {
                    let mut are_equal = true;
                    for (left, right) in left.domain.iter().zip(&right.domain) {
                        if !equals(left, right)? {
                            are_equal = false;
                            break;
                        }
                    }
                    are_equal
                }
            };
            if !are_keys_equal {
                return Ok(false);
            }
            for (left, right) in left.range.iter().zip(&right.range) {
                if !equals(left, right)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        (Value::Function(function), Value::Lambda(lambda)) => lambda_as_operand(function, lambda),
        (Value::Lambda(lambda), _) => lambda_as_function(lambda),
        // `UserValue.equals` is its `compareTo`.
        (Value::Lazy(lazy), _) if lazy.is_overridden() => {
            Ok(compare_overridden(left, lazy, right)? == Ordering::Equal)
        }
        (_, Value::Lazy(lazy)) if lazy.is_overridden() && left.is_set() => {
            incomparable(left, right, true)
        }
        (Value::Lazy(left_lazy), Value::Lazy(right_lazy))
            if is_same_construction(left_lazy, right_lazy) =>
        {
            let compared = equal_constructions(left, left_lazy, right, right_lazy);
            if is_own_filter_failure(&compared)
                && has_unsourced_parts(left_lazy)
                && has_unsourced_parts(right_lazy)
            {
                COMPARED_FILTER.with(|is_compared| is_compared.set(true));
                return compared;
            }
            unplaced(compared)
        }
        // A set enumeration TLC holds unnormalized is a set too, which `SetEnumValue.equals`
        // normalizes after the receiver.
        _ if left.is_set() && (right.is_set() || matches!(right, Value::Unsorted(_))) => {
            // `IntervalValue.equals` sizes the interval first, and the other interval where its
            // own is empty, or converts it to a set enumeration, which sizes it.
            if let Value::Interval(low, high, _) = left {
                interval_size(*low, *high)?;
                if let Value::Interval(other_low, other_high, _) = right
                    && low > high
                {
                    interval_size(*other_low, *other_high)?;
                }
            }
            if let (Value::Interval(low, high, _), Value::Interval(other_low, other_high, _)) =
                (left, right)
            {
                // `IntervalValue.equals` counts the receiver's elements, and the other's only
                // where the receiver is empty; a set enumeration's `equals` converts the other
                // (`toSetEnum`), which counts it. Counting fails past 2^31 - 1 elements.
                if matches!(left, Value::Interval(_, _, Some(SetClass::Interval))) {
                    if interval_size(*low, *high)? == 0 {
                        return Ok(interval_size(*other_low, *other_high)? == 0);
                    }
                    return Ok(low == other_low && high == other_high);
                }
                if matches!(right, Value::Interval(_, _, Some(SetClass::Interval))) {
                    interval_size(*other_low, *other_high)?;
                }
                let is_empty = low > high;
                return Ok(if is_empty || other_low > other_high {
                    is_empty && other_low > other_high
                } else {
                    low == other_low && high == other_high
                });
            }
            // A set TLC keeps lazy converts itself to a set enumeration to compare
            // (`convertAndCache`, `SetEnumValue.equals`'s `toSetEnum`), the receiver first.
            crate::sets::check_enumerated_bound(left)?;
            let left = converted(left)?;
            crate::sets::check_enumerated_bound(right)?;
            let right = counted(right)?;
            if left.len() != right.len() {
                return Ok(false);
            }
            for (left, right) in left.iter().zip(right.iter()) {
                if !equals(left, right)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        _ => incomparable(left, right, true),
    }
}

// Whether a function's keys are those of the interval from `low`, up to the first that isn't, as
// `FcnRcdValue.equals` asks them, failing at one that isn't an integer.
fn are_interval_keys(low: i32, keys: &[Value]) -> Evaluated<bool> {
    for (index, key) in keys.iter().enumerate() {
        let Value::Int(key) = key else {
            return fail_runtime(
                "a function over an interval compared with one over other keys",
                format!(
                    "Attempted to compare an integer with non-integer:\n{}.",
                    format_pretty(key)
                ),
            );
        };
        if i64::from(*key) != i64::from(low) + index as i64 {
            return Ok(false);
        }
    }
    Ok(true)
}

pub(crate) fn is_same_construction(left: &Lazy, right: &Lazy) -> bool {
    matches!(
        (left, right),
        (Lazy::Subset(_), Lazy::Subset(_))
            | (Lazy::FunctionSet(..), Lazy::FunctionSet(..))
            | (Lazy::RecordSet(..), Lazy::RecordSet(..))
            | (Lazy::Product(..), Lazy::Product(..))
    )
}

// Whether a comparison failed in the Enumerator of a filter of a set TLC can't enumerate
// (`SetPredValue.Enumerator`), which no other value's method wraps.
fn is_own_filter_failure<T>(compared: &Evaluated<T>) -> bool {
    compared.as_ref().err().is_some_and(|error| {
        error.message.as_ref().is_some_and(|message| {
            message.code.is_none()
                && message
                    .text
                    .starts_with("Attempted to enumerate { x \\in S : p(x) } when S:\n")
        })
    })
}

// Whether the sets a power set or a set of functions, records or tuples is built of are each
// a set enumeration of plain values, an interval TLC counts, or a filter of a set TLC can't
// enumerate, or of such a filter: comparing two such sets fails, if at all, in the innermost
// filter's own Enumerator, which the Enumerator of each filter around it makes as it is made
// (`SetPredValue.Enumerator`), before any predicate is evaluated, and `CallStackTool` copies a
// filter without its source, so the FingerprintException passes through no part with one, and
// the receiver's `equals` alone heads it. A set enumeration of numbers, strings, booleans, model
// values, and tuples, records, functions and set enumerations of those, sorted already, compares
// and asks whether it is empty without failing.
fn has_unsourced_parts(lazy: &Lazy) -> bool {
    fn is_plain_element(element: &Value) -> bool {
        match element {
            Value::Int(_) | Value::Str(_) | Value::Bool(_) | Value::Model(_) => true,
            Value::Set(set) => set.as_slice().iter().all(is_plain_element),
            Value::Function(function) => {
                function.domain.iter().all(is_plain_element)
                    && function.range.iter().all(is_plain_element)
            }
            _ => false,
        }
    }
    let is_unsourced = |part: &Value| match part {
        Value::Set(set) => set.as_slice().iter().all(is_plain_element),
        Value::Interval(low, high, _) => interval_size(*low, *high).is_ok(),
        Value::Lazy(_) => crate::sets::is_unenumerable_filter(part),
        _ => false,
    };
    match lazy {
        Lazy::Subset(base) => is_unsourced(base),
        Lazy::FunctionSet(domain, range) => is_unsourced(domain) && is_unsourced(range),
        Lazy::RecordSet(fields, _) => fields.iter().all(|(_, part)| is_unsourced(part)),
        Lazy::Product(factors) => factors.iter().all(is_unsourced),
        _ => false,
    }
}

// `equals` of `SetOfFcnsValue`, `SetOfRcdsValue` and `SetOfTuplesValue` with another of their
// class: by emptiness, then by the sets they're built from, without enumerating them.
fn equal_constructions(
    left: &Value,
    left_lazy: &Lazy,
    right: &Value,
    right_lazy: &Lazy,
) -> Evaluated<bool> {
    use crate::eval::is_empty;
    // `SubsetValue.equals`: by the sets.
    if let (Lazy::Subset(base), Lazy::Subset(other_base)) = (left_lazy, right_lazy) {
        return equals(base, other_base);
    }
    if let (Lazy::FunctionSet(domain, range), Lazy::FunctionSet(other_domain, other_range)) =
        (left_lazy, right_lazy)
    {
        let is_unit = is_empty(domain)?;
        let is_other_unit = is_empty(other_domain)?;
        if is_unit || is_other_unit {
            return Ok(is_unit == is_other_unit);
        }
        let is_empty_range = is_empty(range)?;
        let is_other_empty_range = is_empty(other_range)?;
        if is_empty_range || is_other_empty_range {
            return Ok(is_empty_range == is_other_empty_range);
        }
        return Ok(equals(domain, other_domain)? && equals(range, other_range)?);
    }
    let is_empty_left = is_empty(left)?;
    if is_empty_left {
        return is_empty(right);
    }
    if is_empty(right)? {
        return Ok(false);
    }
    match (left_lazy, right_lazy) {
        (Lazy::RecordSet(fields, _), Lazy::RecordSet(other_fields, _)) => {
            if fields.len() != other_fields.len() {
                return Ok(false);
            }
            for ((name, set), (other_name, other_set)) in fields.iter().zip(other_fields) {
                if name.units != other_name.units || !equals(set, other_set)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        (Lazy::Product(factors), Lazy::Product(other_factors)) => {
            if factors.len() != other_factors.len() {
                return Ok(false);
            }
            for (factor, other_factor) in factors.iter().zip(other_factors) {
                if !equals(factor, other_factor)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        _ => unreachable!("the same construction"),
    }
}

// Whether `equals` of two functions is a `FcnRcdValue`'s or a `TupleValue`'s, of a known class,
// with another of a known class, which it takes as a function (`toFcnRcd`). A function TLC
// built at once over a set it enumerates is a `FcnRcdValue`, whatever its printing class.
fn is_function_receiver(left: &Function, right: &Function) -> bool {
    matches!(left.java_class.get(), Some(Class::Plain | Class::Tuple))
        && matches!(
            right.java_class.get(),
            Some(Class::Plain | Class::Tuple | Class::Record)
        )
}

// A record compared with a function that isn't one: `RecordValue`'s failure where the record is
// the left operand, and otherwise the evaluator's limit.
fn non_record<T>(left: &Value, right: &Value, is_equality: bool) -> Evaluated<T> {
    let reason = "record compared with a function";
    let Value::Function(function) = left else {
        return fail(reason);
    };
    if function.class.get() != Class::Record {
        return fail(reason);
    }
    let verb = if is_equality {
        "check equality of"
    } else {
        "compare"
    };
    fail_runtime(
        reason,
        format!(
            "Attempted to {verb} record:\n{}\nwith non-record\n{}",
            format_pretty(left),
            format_pretty(right)
        ),
    )
}

/// A function TLC keeps lazy that a function compares or equates with: a `TupleValue` takes it
/// as a tuple (`toTuple`), and a `FcnRcdValue` or a `RecordValue` as the function it builds
/// (`toFcnRcd`, `toRcd`). Where the evaluator doesn't know the receiver's class it declines.
fn lambda_as_operand<T>(function: &Function, lambda: &crate::eval::Lambda) -> Evaluated<T> {
    match function.java_class.get() {
        Some(Class::Tuple) => lambda_as_tuple(lambda),
        Some(Class::Plain | Class::Record) => lambda_as_function(lambda),
        _ => fail("compared a function TLC keeps lazy with a function of an unknown class"),
    }
}

/// `FcnLambdaValue.toFcnRcd`, which a comparison or a membership in a set of functions builds:
/// a domain TLC overrides fails as `UserValue.size` does, and any other the evaluator declines.
pub fn lambda_as_function<T>(lambda: &crate::eval::Lambda) -> Evaluated<T> {
    match lambda.domain() {
        Value::Lazy(lazy) if lazy.is_overridden() => fail_runtime(
            BUILT_OVER_OVERRIDDEN,
            format!(
                "Attempted to compute the number of elements in the overridden value {}.",
                format_pretty(lambda.domain())
            ),
        ),
        _ => Err(lambda.build_failure()),
    }
}

/// `lambda_as_function` where TLC may fail elsewhere: a membership in a set of functions or
/// records, which fails in the set's method with its source. A startup definition that failed so
/// declines (`is_unsure_failure`). A comparison or an equality follows TLC's receiver, as the
/// evaluator's membership does (`ValueVec.search`: `elem.compareTo` in a sorted set, the
/// element's `equals` in another): the function TLC keeps lazy builds itself (`toFcnRcd`), and
/// another receiver's class decides (`lambda_as_operand`).
pub fn lambda_as_function_unsure<T>(lambda: &crate::eval::Lambda) -> Evaluated<T> {
    lambda_as_function(lambda).map_err(|mut error| {
        if error.reason == BUILT_OVER_OVERRIDDEN {
            error.reason = UNSURE_OVER_OVERRIDDEN.into();
        }
        error
    })
}

pub(crate) const BUILT_OVER_OVERRIDDEN: &str = "built a function over a set TLC doesn't enumerate";
pub(crate) const UNSURE_OVER_OVERRIDDEN: &str =
    "built a function over a set TLC doesn't enumerate, where TLC may not";

/// `FcnLambdaValue.toTuple`, which a membership in a set of tuples or sequences takes: a domain
/// TLC's module overrides has no set enumeration, and the evaluator declines any other.
pub fn lambda_as_tuple<T>(lambda: &crate::eval::Lambda) -> Evaluated<T> {
    match lambda.domain() {
        Value::Lazy(lazy)
            if matches!(***lazy, Lazy::Nat | Lazy::Int | Lazy::Strings | Lazy::Seq(_)) =>
        {
            fail_runtime(
                "made a tuple of a function over a set TLC doesn't enumerate",
                "To convert a function of form [x \\in S |-> f(x)] to a tuple, the set S must be enumerable."
                    .into(),
            )
        }
        // `Value.toSetEnum` of a value that isn't a set is null.
        Value::Bool(_)
        | Value::Int(_)
        | Value::Str(_)
        | Value::Model(_)
        | Value::Function(_)
        | Value::Lambda(_)
            if lambda.is_domain_printed() =>
        {
            fail_runtime(
                "made a tuple of a function over a value that isn't a set",
                "To convert a function of form [x \\in S |-> f(x)] to a tuple, the set S must be enumerable."
                    .into(),
            )
        }
        // A set's `toSetEnum` enumerates it, and `normalize` sorts that: either fails as the
        // set's enumeration does. A domain that enumerates goes on to the body, which the
        // evaluator doesn't follow for a function it holds lazy.
        domain if lambda.is_domain_printed() && is_enumerable(domain) => match elements(domain) {
            Err(error) if error.message.is_some() => Err(error),
            _ => fail("made a tuple of a function over an infinite set"),
        },
        _ => fail("made a tuple of a function over an infinite set"),
    }
}

thread_local! {
    static UNPLACED_COMPONENT: Cell<bool> = const { Cell::new(false) };
    static COMPARED_FILTER: Cell<bool> = const { Cell::new(false) };
    static WALKS_DECLINED: Cell<bool> = const { Cell::new(false) };
}

/// The reason for an interval too large to build that the evaluator enumerates where it
/// declines to say whether TLC counts it: `IntervalValue.elements` walks an interval without
/// counting it, and many of TLC's methods enumerate a set so (`isSubsetEq`, `member` of a power
/// set, a filter, a union), where others count it first (`toSetEnum`).
pub(crate) const WALKED_INTERVAL: &str = "an interval too large to build that TLC may walk";

/// Where the evaluator walks an interval too large to build as TLC's `IntervalValue.Enumerator`
/// does, the decline `decline_walked_intervals` asks for.
pub(crate) fn check_walk(low: i32, high: i32) -> Evaluated<()> {
    if i64::from(high) - i64::from(low) >= MAXIMUM_INTERVAL as i64 && WALKS_DECLINED.with(Cell::get)
    {
        return fail(WALKED_INTERVAL);
    }
    Ok(())
}

/// Makes the enumeration of an interval too large to build decline (`WALKED_INTERVAL`), rather
/// than fail as TLC's `IntervalValue.size` does, as it must where the search stopped at a value
/// TLC can't enumerate or count: TLC may walk the interval and answer, or fail otherwise.
pub(crate) fn decline_walked_intervals(is_declined: bool) {
    WALKS_DECLINED.with(|declined| declined.set(is_declined));
}

/// The reason for a failure the evaluator doesn't place: comparing the sets a lazy set is built
/// of, or the ranges of two Seq(S).
pub(crate) const UNPLACED_COMPONENT_FAILURE: &str =
    "a failure comparing the sets a set TLC keeps lazy is built of";

// Notes a failure comparing the sets a lazy set is built of, in their own methods, where a set
// with a source heads TLC's FingerprintException, which the evaluator doesn't place.
fn unplaced<T>(result: Evaluated<T>) -> Evaluated<T> {
    if result.is_err() {
        UNPLACED_COMPONENT.with(|is_unplaced| is_unplaced.set(true));
    }
    result
}

/// Whether a failure since the last call was a filter's own, in a comparison of two sets built
/// of parts no value with a source wraps (`has_unsourced_parts`).
pub(crate) fn take_compared_filter() -> bool {
    COMPARED_FILTER.with(|is_compared| is_compared.replace(false))
}

/// Whether a failure since the last call compared the sets a lazy set is built of, which the
/// evaluator doesn't place among the values with sources TLC's methods throw it through.
pub(crate) fn take_unplaced_component() -> bool {
    UNPLACED_COMPONENT.with(|is_unplaced| is_unplaced.replace(false))
}

// `UserValue.compareTo`: an overridden set compares with another by its module's `compareTo`
// (Nat before Int, Seq(S) by its range), and with nothing else.
fn compare_overridden(left: &Value, lazy: &Lazy, right: &Value) -> Evaluated<Ordering> {
    let shown = || format_pretty(left);
    if let Some(error) = print_failure(right) {
        return Err(error);
    }
    let Value::Lazy(other) = right else {
        return fail_runtime(
            "compared an overridden set with another value",
            format!(
                "Attempted to compare overridden value {} with non-overridden value:\n{}",
                shown(),
                format_pretty(right)
            ),
        );
    };
    if !other.is_overridden() {
        return fail_runtime(
            "compared an overridden set with another value",
            format!(
                "Attempted to compare overridden value {} with non-overridden value:\n{}",
                shown(),
                format_pretty(right)
            ),
        );
    }
    match (lazy, &***other) {
        (Lazy::Nat, Lazy::Nat) | (Lazy::Int, Lazy::Int) | (Lazy::Strings, Lazy::Strings) => {
            Ok(Ordering::Equal)
        }
        (Lazy::Nat, Lazy::Int) => Ok(Ordering::Less),
        (Lazy::Int, Lazy::Nat) => Ok(Ordering::Greater),
        // Both unbounded: by the range.
        // TLC compares the ranges in `Sequences.compareTo`, where a range with a source heads
        // the FingerprintException of a failure, which the evaluator doesn't place.
        (Lazy::Seq(range), Lazy::Seq(other_range)) => unplaced(compare(range, other_range)),
        (Lazy::Real, _) | (_, Lazy::Real) => fail("compared Real"),
        _ => fail_coded(
            "compared overridden sets of different modules",
            COMPARE_VALUE,
            format!(
                "Attempted to compare {} with the value\n{}",
                shown(),
                format_pretty(right)
            ),
        ),
    }
}

/// `EC.TLC_MODULE_COMPARE_VALUE`.
const COMPARE_VALUE: u32 = 2155;

thread_local! {
    static SUPPRESS_NEW_FUNCTION_DIAGNOSTIC: Cell<bool> = const { Cell::new(false) };
}

pub(crate) struct FunctionDiagnosticScope(bool);

pub(crate) fn suppress_new_function_diagnostic(suppress: bool) -> FunctionDiagnosticScope {
    FunctionDiagnosticScope(
        SUPPRESS_NEW_FUNCTION_DIAGNOSTIC.with(|flag| flag.replace(suppress || flag.get())),
    )
}

impl Drop for FunctionDiagnosticScope {
    fn drop(&mut self) {
        SUPPRESS_NEW_FUNCTION_DIAGNOSTIC.with(|flag| flag.set(self.0));
    }
}

// The kind of the elements of a set enumeration TLC sorts without failing whatever pairs it
// compares: `None` where it may fail or the evaluator doesn't keep the class TLC prints, and
// `Some(None)` for the empty set, which compares with a set of any kind by its size first.
#[derive(Clone, Copy, PartialEq, Eq)]
enum SortedKind {
    Int,
    Bool,
    Str,
    Set(Option<&'static SortedKind>),
}

fn sorted_text_kind(value: &Value) -> Option<Option<SortedKind>> {
    let Value::Set(set) = value else {
        return None;
    };
    if set.java_class != Some(SetClass::Enumeration) {
        return None;
    }
    let mut kind: Option<SortedKind> = None;
    for element in set.iter() {
        let own = match element {
            Value::Int(_) => SortedKind::Int,
            Value::Bool(_) => SortedKind::Bool,
            Value::Str(_) => SortedKind::Str,
            Value::Set(_) => SortedKind::Set(match sorted_text_kind(element)? {
                None => None,
                Some(SortedKind::Int) => Some(&SortedKind::Int),
                Some(SortedKind::Bool) => Some(&SortedKind::Bool),
                Some(SortedKind::Str) => Some(&SortedKind::Str),
                // Sets of sets of sets are left to the evaluator's limit.
                Some(SortedKind::Set(_)) => return None,
            }),
            _ => return None,
        };
        kind = Some(match (kind, own) {
            (None, own) => own,
            (Some(SortedKind::Set(None)), SortedKind::Set(inner))
            | (Some(SortedKind::Set(inner)), SortedKind::Set(None)) => SortedKind::Set(inner),
            (Some(kind), own) if kind == own => kind,
            _ => return None,
        });
    }
    Some(kind)
}

/// Whether TLC prints a union `S \\cup T` it holds lazy (`SetCupValue`) failing where the
/// evaluator does: S a set enumeration or an interval of integers, of booleans or of strings, a
/// set enumeration of sets of one such kind, or the power set of such a set enumeration, and T a
/// set of tuples, records or functions of such sets, none empty. `PrintT` normalizes both deeply,
/// then `toString` enumerates S and then T into a set enumeration it normalizes, whose sort
/// inserts S's elements, every two of which compare, and then fails comparing T's first, a
/// tuple, record or function, with S's middle one (`ValueVec.sort`), which the evaluator's
/// enumeration of the union does alike.
pub(crate) fn is_known_cup_print(value: &Value) -> bool {
    let Value::Lazy(lazy) = value else {
        return false;
    };
    let Lazy::Cup(left, right) = &***lazy else {
        return false;
    };
    let is_scalar_set = |set: &Value| match set {
        Value::Interval(low, high, class) => low <= high && *class == Some(SetClass::Interval),
        Value::Set(_) => matches!(
            sorted_text_kind(set),
            Some(Some(SortedKind::Int | SortedKind::Bool | SortedKind::Str))
        ),
        _ => false,
    };
    let is_left_known = match left {
        Value::Set(_) => matches!(
            sorted_text_kind(left),
            Some(Some(
                SortedKind::Int
                    | SortedKind::Bool
                    | SortedKind::Str
                    | SortedKind::Set(Some(SortedKind::Int | SortedKind::Bool | SortedKind::Str))
            ))
        ),
        Value::Lazy(base) => match &***base {
            Lazy::Subset(base) => matches!(base, Value::Set(_)) && is_scalar_set(base),
            _ => false,
        },
        _ => is_scalar_set(left),
    };
    let Value::Lazy(right_lazy) = right else {
        return false;
    };
    let parts_are_scalar = match &***right_lazy {
        Lazy::Product(factors) => !factors.is_empty() && factors.iter().all(is_scalar_set),
        Lazy::RecordSet(fields, _) => {
            !fields.is_empty() && fields.iter().all(|(_, set)| is_scalar_set(set))
        }
        Lazy::FunctionSet(domain, range) => is_scalar_set(domain) && is_scalar_set(range),
        _ => false,
    };
    lazy.java_class == Some(SetClass::Cup)
        && is_left_known
        && comparison_text_is_known(left, &mut HashMap::new())
        && parts_are_scalar
        && comparison_text_is_known(right, &mut HashMap::new())
}

/// Whether TLC prints the value as the evaluator does (`toString`), as a failure's message does.
pub(crate) fn is_text_known(value: &Value) -> bool {
    comparison_text_is_known(value, &mut HashMap::new())
}

// A new function diagnostic may only use default formatting whose evaluation and retained
// representation are known. A pending entry also guards recursive or shared value graphs.
fn comparison_text_is_known(value: &Value, known: &mut HashMap<usize, bool>) -> bool {
    match value {
        Value::Null => false,
        Value::Function(function) => {
            let pointer = Rc::as_ptr(function) as usize;
            if let Some(result) = known.get(&pointer) {
                return *result;
            }
            known.insert(pointer, false);
            let class_is_known = matches!(
                function.java_class.get(),
                Some(Class::Plain | Class::Tuple | Class::Record)
            ) && !(function.java_class.get() == Some(Class::Record)
                && function.domain.is_empty());
            // `FcnRcdValue.toString` prints a function of integer keys as it sorts a copy of it
            // (`isTuple`), whatever order TLC holds it in.
            let order_is_known = function.class.get() != Class::Plain
                || function.domain.len() < 2
                || function.written.borrow().is_some()
                || function.search.get() == Search::Sorted
                || function.interval.is_some()
                || function
                    .domain
                    .iter()
                    .all(|key| matches!(key, Value::Int(_)));
            let keys_are_known = function.domain.iter().all(|key| {
                !matches!(key, Value::Str(text)
                    if tla_values::print::get_field_name(&text.units).is_none())
                    && comparison_text_is_known(key, known)
            });
            let result = class_is_known
                && order_is_known
                && keys_are_known
                && function
                    .range
                    .iter()
                    .all(|value| comparison_text_is_known(value, known));
            known.insert(pointer, result);
            result
        }
        Value::Str(text) | Value::Model(text) => text
            .units
            .iter()
            .all(|unit| matches!(unit, 9 | 10 | 12 | 13 | 32..=126)),
        // A set of tuples, of sets, of records or of functions prints the set it enumerates,
        // normalized, where that set is small (`toString` with `TLCGlobals.expand`), and its
        // operation otherwise: one built of sets every two of whose elements compare, so that
        // every two of its own compare too.
        Value::Lazy(lazy) => {
            let mut is_part_known = |set: &Value| match set {
                Value::Interval(_, _, class) => *class == Some(SetClass::Interval),
                Value::Set(_) => comparison_text_is_known(set, known),
                _ => false,
            };
            match (&***lazy, lazy.java_class) {
                (Lazy::Nat | Lazy::Int | Lazy::Strings | Lazy::Any, Some(SetClass::Overridden)) => {
                    true
                }
                // `Sequences.toString`: Seq of its range's text.
                (Lazy::Seq(range), Some(SetClass::Overridden)) => is_part_known(range),
                (Lazy::Product(factors), Some(SetClass::Product)) => {
                    factors.iter().all(is_part_known)
                }
                (Lazy::Subset(base), Some(SetClass::Subset)) => is_part_known(base),
                (Lazy::RecordSet(fields, _), Some(SetClass::Records)) => {
                    fields.iter().all(|(_, set)| is_part_known(set))
                }
                // Functions of integer keys, which print alike in whatever order TLC holds them.
                (Lazy::FunctionSet(domain, range), Some(SetClass::Functions)) => {
                    (matches!(domain, Value::Interval(..))
                        || sorted_text_kind(domain)
                            .is_some_and(|kind| matches!(kind, None | Some(SortedKind::Int))))
                        && is_part_known(domain)
                        && is_part_known(range)
                }
                _ => false,
            }
        }
        Value::Interval(_, _, class) => *class == Some(SetClass::Interval),
        // `SetEnumValue.toString` normalizes the set before it prints it, which only a set of
        // elements every pair of which compares, in whatever order TLC sorts them, does for
        // certain: one of integers, booleans or strings, or of such sets, all of one kind.
        Value::Set(_) => {
            sorted_text_kind(value).is_some() && {
                let mut pending = vec![value];
                let mut is_known = true;
                while let Some(Value::Set(set)) = pending.pop() {
                    for element in set.iter() {
                        match element {
                            Value::Set(_) => pending.push(element),
                            _ => is_known &= comparison_text_is_known(element, known),
                        }
                    }
                }
                is_known
            }
        }
        Value::Unsorted(_) | Value::Lambda(_) => false,
        _ => true,
    }
}

thread_local! {
    // Whether a comparison failed as its message printed a set TLC holds unnormalized, since the
    // frame of the call stack that last took it.
    static UNSORTED_PRINT_FAILURE: Cell<bool> = const { Cell::new(false) };
}

/// Whether a comparison failed printing a set TLC holds unnormalized since the last call.
pub(crate) fn take_unsorted_print_failure() -> bool {
    UNSORTED_PRINT_FAILURE.replace(false)
}

// TLC's error for two values of kinds it can't compare, worded by the class of the left operand.
// A set compares as `toSetEnum` enumerates it.
fn incomparable<T>(left: &Value, right: &Value, is_equality: bool) -> Evaluated<T> {
    if contains_uninitialized(left) || contains_uninitialized(right) {
        return fail("formatting a comparison with nested null tool values");
    }
    let reason = if is_equality {
        "equality of values TLC can't compare"
    } else {
        "values TLC can't compare"
    };
    // The message prints the left operand and then the right one, and `SetEnumValue.toString`
    // first normalizes a set enumeration TLC holds unnormalized, which fails as its sort does.
    // That failure passes through the set's own `normalize`, whose source the call stack doesn't
    // place.
    if let Value::Unsorted(set) = left {
        UNSORTED_PRINT_FAILURE.set(true);
        return Err(unsorted_failure(set));
    }
    // `SetEnumValue.compareTo` and `equals` normalize their own set and then the other's, which
    // fails as its sort does where TLC holds the other unnormalized, before either prints; an
    // interval does as the set it converts to (`IntervalValue.toSetEnum`).
    if let (Value::Set(_) | Value::Interval(..), Value::Unsorted(set)) = (left, right) {
        UNSORTED_PRINT_FAILURE.set(true);
        return Err(unsorted_failure(set));
    }
    // A lazy set converts itself first (`convertAndCache`), in ways the evaluator doesn't follow,
    // but for a product, a set of functions or records, or a power set of set enumerations or
    // intervals that hold no set TLC can't normalize: `SetOfTuplesValue.equals` and its siblings convert it to the set
    // enumeration of its elements, normalized, whose `equals` then normalizes the argument, which
    // fails as its sort does, as the message names it (`named_text`).
    if let (Value::Lazy(lazy), Value::Unsorted(_)) = (left, right) {
        let parts: Vec<&Value> = match &***lazy {
            Lazy::Product(factors) => factors.iter().collect(),
            Lazy::FunctionSet(domain, range) => vec![domain, range],
            Lazy::RecordSet(fields, _) => fields.iter().map(|(_, set)| set).collect(),
            Lazy::Subset(base) => vec![base],
            _ => return fail(reason),
        };
        if !parts.iter().all(|part| {
            matches!(part, Value::Set(_) | Value::Interval(..)) && !holds_unnormalizable_part(part)
        }) {
            return fail(reason);
        }
    }
    let right_fails_to_print = |known: &mut HashMap<usize, bool>| match right {
        Value::Unsorted(set) if comparison_text_is_known(left, known) => {
            UNSORTED_PRINT_FAILURE.set(true);
            Some(unsorted_failure(set))
        }
        _ => None,
    };
    if let Value::Function(function) = left {
        if SUPPRESS_NEW_FUNCTION_DIAGNOSTIC.with(Cell::get) {
            return fail(reason);
        }
        let mut known = HashMap::new();
        if let Some(error) = right_fails_to_print(&mut known) {
            return Err(error);
        }
        if !comparison_text_is_known(left, &mut known)
            || !comparison_text_is_known(right, &mut known)
        {
            return fail(reason);
        }
        let verb = if is_equality {
            "check equality of"
        } else {
            "compare"
        };
        let message = if function.java_class.get() == Some(Class::Record) {
            format!(
                "Attempted to {verb} record:\n{}\nwith non-record\n{}",
                format_pretty(left),
                format_pretty(right)
            )
        } else {
            format!(
                "Attempted to {verb} the function {} with the value:\n{}",
                format_pretty(left),
                format_pretty(right)
            )
        };
        // A function, a tuple or a record reads a lazy set it fails on only as it prints it: the
        // set is none (`toFcnRcd`, `toTuple`, `toRcd`).
        return fail_runtime(reason, message).map_err(|mut error| {
            error.is_followed_comparison = matches!(right, Value::Lazy(_));
            error
        });
    }
    let (subject, other) = match left {
        Value::Int(_) => ("integer", "non-integer:"),
        Value::Bool(_) => ("boolean", "non-boolean:"),
        Value::Str(_) => ("string", "non-string:"),
        _ if left.is_set() => ("the set", "the value:"),
        _ => return fail(reason),
    };
    if matches!(left, Value::Int(_) | Value::Bool(_) | Value::Str(_))
        && let Some(error) = right_fails_to_print(&mut HashMap::new())
    {
        return Err(error);
    }
    let verb = match left {
        Value::Bool(_) if is_equality => "compare equality of",
        _ if is_equality => "check equality of",
        _ => "compare",
    };
    // TLC words the failure with `toString` of the values it names, the left where it is a set
    // and then the right. `SetEnumValue.toString` normalizes a set enumeration TLC holds
    // unnormalized, so a set TLC fails to normalize fails there instead, with that failure; the
    // evaluator declines one nested deeper in a named value. A lazy set or an interval on the
    // left names its elements, which it enumerates as `toSetEnum` does.
    let shown = match left {
        Value::Interval(..) | Value::Lazy(_) => {
            let elements = elements(left).map_err(|mut error| {
                error.is_named_normalization = error.is_set_normalization;
                error
            })?;
            let shown = Value::set_from_rc(elements, Some(SetClass::Enumeration));
            named_text(&shown, reason)?
        }
        _ => named_text(left, reason)?,
    };
    // `toString` normalizes a lazy set's parts, or the set it enumerates, before it prints it,
    // which fails where one of them holds a set TLC can't normalize, as the evaluator doesn't
    // follow.
    if matches!(right, Value::Lazy(_)) && holds_unnormalizable_part(right) {
        return fail(reason);
    }
    // The lazy set compared itself, as the argument of the comparison, and not a value its own
    // method compares. The message prints it as `toString` enumerates it, which may fail, or
    // prints it otherwise, so the comparison is followed only where the evaluator knows its
    // text.
    let is_followed_comparison = matches!(left, Value::Int(_) | Value::Bool(_) | Value::Str(_))
        && matches!(right, Value::Lazy(_))
        && comparison_text_is_known(right, &mut HashMap::new());
    let shown_right = named_text(right, reason)?;
    fail_runtime(
        reason,
        format!("Attempted to {verb} {subject} {shown} with {other}\n{shown_right}"),
    )
    .map_err(|mut error| {
        error.is_followed_comparison = is_followed_comparison;
        error
    })
}

/// Whether TLC may hold a function's keys out of order, as `CombineFcn` builds a FcnRcdValue,
/// the first function's keys first, where two or more of its values hold a set TLC can't
/// normalize: `deepNormalize` walks the values in the order TLC holds them and fails on the first
/// such, which the evaluator's sorted function doesn't tell.
pub(crate) fn may_hold_values_out_of_order(function: &Function) -> bool {
    function.class.get() == Class::Plain
        && function.written.borrow().is_none()
        && function.search.get() != Search::Sorted
        && function.interval.is_none()
        && function
            .range
            .iter()
            .filter(|value| holds_unnormalizable_part(value))
            .count()
            > 1
}

/// Whether a value holds, anywhere, a function [`may_hold_values_out_of_order`].
pub(crate) fn holds_values_out_of_order(value: &Value) -> bool {
    let mut pending = vec![value];
    let mut seen = std::collections::HashSet::new();
    while let Some(value) = pending.pop() {
        match value {
            Value::Set(set) | Value::Unsorted(set) => {
                if seen.insert(Rc::as_ptr(set) as usize) {
                    pending.extend(set.iter());
                }
            }
            Value::Function(function) => {
                if may_hold_values_out_of_order(function) {
                    return true;
                }
                if seen.insert(Rc::as_ptr(function) as usize) {
                    pending.extend(function.domain.iter().chain(&function.range));
                }
            }
            Value::Lambda(lambda) => pending.push(lambda.domain()),
            Value::Lazy(lazy) => match &***lazy {
                Lazy::Subset(base)
                | Lazy::Seq(base)
                | Lazy::Union(base)
                | Lazy::Filter(base, _) => pending.push(base),
                Lazy::FunctionSet(left, right)
                | Lazy::Cap(left, right)
                | Lazy::Cup(left, right)
                | Lazy::Diff(left, right) => pending.extend([left, right]),
                Lazy::RecordSet(fields, _) => pending.extend(fields.iter().map(|(_, set)| set)),
                Lazy::Product(sets) => pending.extend(sets),
                Lazy::Nat | Lazy::Int | Lazy::Real | Lazy::Strings | Lazy::Any => {}
            },
            _ => {}
        }
    }
    false
}

/// Whether a value, or a part of a lazy set it is, holds a set enumeration TLC can't normalize.
pub(crate) fn holds_unnormalizable_part(value: &Value) -> bool {
    let mut pending = vec![value];
    let mut seen = std::collections::HashSet::new();
    while let Some(value) = pending.pop() {
        match value {
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
            Value::Lazy(lazy) => match &***lazy {
                Lazy::Subset(base)
                | Lazy::Seq(base)
                | Lazy::Union(base)
                | Lazy::Filter(base, _) => pending.push(base),
                Lazy::FunctionSet(left, right)
                | Lazy::Cap(left, right)
                | Lazy::Cup(left, right)
                | Lazy::Diff(left, right) => pending.extend([left, right]),
                Lazy::RecordSet(fields, _) => pending.extend(fields.iter().map(|(_, value)| value)),
                Lazy::Product(sets) => pending.extend(sets),
                _ => {}
            },
            _ => {}
        }
    }
    false
}

// The text of a value TLC names in a failure (`toString`): where it is a set enumeration TLC fails
// to normalize, that failure, and the evaluator declines one that holds such a set deeper.
fn named_text(value: &Value, reason: &str) -> Evaluated<String> {
    if let Value::Unsorted(elements) = value {
        let mut error = unsorted_failure(elements);
        error.is_named_normalization = true;
        return Err(error);
    }
    if holds_unsorted_part(value) {
        return fail(reason);
    }
    Ok(format_pretty(value))
}

// Whether a value holds a set enumeration TLC fails to normalize below its top level: an element
// of a set, a part of a function or an operand of a lazy set.
fn holds_unsorted_part(value: &Value) -> bool {
    let mut pending: Vec<&Value> = Vec::new();
    let mut seen = std::collections::HashSet::new();
    let mut is_top = true;
    pending.push(value);
    while let Some(value) = pending.pop() {
        if !is_top && matches!(value, Value::Unsorted(_)) {
            return true;
        }
        is_top = false;
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
            Value::Lazy(lazy) => match &***lazy {
                Lazy::Subset(base)
                | Lazy::Seq(base)
                | Lazy::Union(base)
                | Lazy::Filter(base, _) => pending.push(base),
                Lazy::FunctionSet(left, right)
                | Lazy::Cap(left, right)
                | Lazy::Cup(left, right)
                | Lazy::Diff(left, right) => pending.extend([left, right]),
                Lazy::RecordSet(fields, _) => pending.extend(fields.iter().map(|(_, set)| set)),
                Lazy::Product(sets) => pending.extend(sets),
                Lazy::Nat | Lazy::Int | Lazy::Real | Lazy::Strings | Lazy::Any => {}
            },
            _ => {}
        }
    }
    false
}

// Whether elements `sorts_without_effects` accepts are in TLC's order already, none twice.
fn is_strictly_sorted<'a>(elements: impl Iterator<Item = &'a Value> + Clone) -> bool {
    elements
        .clone()
        .zip(elements.skip(1))
        .all(|(left, right)| compare_without_effects(left, right) == Ordering::Less)
}

// Whether elements sort without effects (`sorts_without_effects`), and if so whether they are in
// TLC's order already, none twice, in one walk of them: each element's kinds are checked before
// it is compared with the one before it.
fn is_sorted_without_effects(elements: &[Value]) -> Option<(Sorting, bool)> {
    if elements.len() < 2 {
        return Some((Sorting::Plain, true));
    }
    if let Some(is_atoms) = are_atoms(elements) {
        return is_atoms.then(|| (Sorting::Plain, is_strictly_sorted(elements.iter())));
    }
    let mut walk = SortWalk::default();
    let mut is_sorted = true;
    for (index, element) in elements.iter().enumerate() {
        walk.walk(element, 0)?;
        is_sorted = is_sorted
            && (index == 0
                || compare_without_effects(&elements[index - 1], element) == Ordering::Less);
    }
    Some((walk.sorting, is_sorted))
}

/// A set of elements in any order and with duplicates, sorted into TLC's order.
pub fn set_of(elements: Vec<Value>) -> Evaluated<Value> {
    let distinct = normalized_unique(&elements)?;
    // Elements in order already, none twice, make the set as they are.
    if distinct.len() == elements.len()
        && distinct
            .iter()
            .zip(&elements)
            .all(|(kept, element)| std::ptr::eq(*kept, element))
    {
        drop(distinct);
        return Ok(Value::set(elements));
    }
    Ok(Value::set(distinct.into_iter().cloned().collect()))
}

/// The failure of normalizing a set enumeration TLC keeps unnormalized.
/// Where TLC prints a value in the message it fails with (`Values.ppr(v.toString())`), the
/// failure it reaches instead where the value is a set enumeration it can't normalize:
/// `SetEnumValue.toString` normalizes it first, which fails comparing, as any normalization of
/// that set does. Only for a set whose normalization the evaluator follows.
pub(crate) fn print_failure(value: &Value) -> Option<EvalError> {
    let Value::Unsorted(elements) = value else {
        return None;
    };
    // The set's `getNewHead` adds its source to a fingerprint stack, which the evaluator can't
    // (`is_named_normalization`), as where the message names a compared value.
    normalize_unsorted_failure(elements)
        .filter(|error| error.is_set_normalization && error.message.is_some())
        .map(|mut error| {
            error.is_named_normalization = true;
            error
        })
}

pub fn unsorted_failure(elements: &Set) -> EvalError {
    normalize_unsorted_failure(elements).unwrap_or_else(|| EvalError {
        runtime_exception: RuntimeException::Runtime,
        is_set_normalization: false,
        is_set_reduction: false,
        is_followed_comparison: false,
        is_named_normalization: false,
        reason: "normalized a set enumeration that sorts".into(),
        message: None,
    })
}

/// Where TLC fails to normalize a set enumeration: the first comparison that fails as
/// `ValueVec.sort` inserts each element, in the order written, into those it sorted before it.
pub fn normalize_failure(elements: &[Value]) -> Option<EvalError> {
    normalized_unique(elements).err()
}

/// Where TLC fails to normalize a set enumeration it normalizes twice in a row, as
/// `FcnLambdaValue.toString` does: `toFcnRcd` fails enumerating the domain, which it swallows,
/// and `FcnParams.toString` sorts the same set again. `ValueVec.sort` moves the elements it
/// inserted before it failed in place, so the second sort starts from that order. The failure
/// is TLC's only where both sorts fail at the same comparison; elsewhere there is none.
pub(crate) fn normalize_unsorted_failure_twice(elements: &Set) -> Option<EvalError> {
    let first = normalize_unsorted_failure(elements)?;
    // `ValueVec.sort`, in place, up to the comparison that throws; `elementCount` stays.
    let mut data: Vec<&Value> = elements.iter().collect();
    let mut count = usize::from(!data.is_empty());
    for index in 1..data.len() {
        let element = data[index];
        let (mut low, mut high, mut middle) = (0, count, 0);
        let mut order = Ordering::Equal;
        while low < high {
            middle = low + ((high - low) >> 1);
            match compare(element, data[middle]) {
                Ok(Ordering::Equal) => {
                    order = Ordering::Equal;
                    break;
                }
                Ok(Ordering::Less) => {
                    order = Ordering::Less;
                    high = middle;
                }
                Ok(Ordering::Greater) => {
                    order = Ordering::Greater;
                    low = middle + 1;
                }
                Err(_) => {
                    let second = normalize_failure(&data.into_iter().cloned().collect::<Vec<_>>())?;
                    return (second.message == first.message).then_some(first);
                }
            }
        }
        if order == Ordering::Equal {
            continue;
        }
        let at = if order == Ordering::Less {
            middle
        } else {
            middle + 1
        };
        let mut position = count;
        while position > at {
            data[position] = data[position - 1];
            position -= 1;
        }
        data[at] = element;
        count += 1;
    }
    None
}

/// A normalization consumer, with the physical enumeration and default formats proved.
pub(crate) fn normalize_unsorted_failure(elements: &Set) -> Option<EvalError> {
    let known = normalization_arguments_are_known(elements);
    normalize_failure(elements).map(|mut error| {
        error.is_set_normalization = known;
        error
    })
}

fn normalization_arguments_are_known(elements: &Set) -> bool {
    if elements.java_class != Some(SetClass::Enumeration) {
        return false;
    }
    let mut pending: Vec<&Value> = elements.iter().collect();
    let mut known = HashMap::new();
    while let Some(value) = pending.pop() {
        match value {
            Value::Set(set) => {
                if set.java_class != Some(SetClass::Enumeration) {
                    return false;
                }
                // Default formatting normalizes a nested set before reporting the outer error.
                if set.len() > 1
                    && !set.iter().all(|other| match (&set[0], other) {
                        (Value::Bool(_), Value::Bool(_))
                        | (Value::Int(_), Value::Int(_))
                        | (Value::Str(_), Value::Str(_)) => true,
                        (Value::Model(left), Value::Model(right)) => {
                            left.model_type() == right.model_type()
                        }
                        _ => false,
                    })
                {
                    return false;
                }
                let key = Rc::as_ptr(set) as usize;
                if known.insert(key, true).is_none() {
                    pending.extend(set.iter());
                }
            }
            Value::Unsorted(_) | Value::Lambda(_) => return false,
            Value::Function(function) => {
                let flat = function.domain.iter().chain(&function.range).all(|value| {
                    matches!(
                        value,
                        Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::Model(_)
                    )
                });
                if !flat || !comparison_text_is_known(value, &mut known) {
                    return false;
                }
            }
            _ if !comparison_text_is_known(value, &mut known) => return false,
            _ => {}
        }
    }
    true
}

/// How the elements of a set sort, where every comparison `ValueVec.sort` can make among them
/// succeeds, so that any sort finds TLC's order: the elements are all integers, all booleans, all
/// strings TLC ranked as it started, or all set enumerations whose elements, all together, are
/// such elements again. TLC compares each element at least once where there are two or more,
/// normalizing it first (`SetEnumValue.compareTo`); a set TLC holds unnormalized among them
/// normalizes its elements as TLC built them, which are then such elements too.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Sorting {
    /// The sort changes nothing but normalize each element.
    Plain,
    /// Some set within an element is one TLC holds unnormalized, and normalizes only where a
    /// comparison reaches it: the sets within each element are then all such sets of integers,
    /// booleans or ranked strings, whose own normalization changes nothing more
    /// (`reach_nested`).
    Nested,
}

/// How the elements sort without effects but those of `Sorting`, or `None` where a comparison
/// can fail or normalize a set deeper within an element (or nests sets too deeply to follow).
fn sorts_without_effects(elements: &[Value]) -> Option<Sorting> {
    if let Some(is_atoms) = are_atoms(elements) {
        return is_atoms.then_some(Sorting::Plain);
    }
    let mut walk = SortWalk::default();
    for value in elements {
        walk.walk(value, 0)?;
    }
    Some(walk.sorting)
}

// Where the first element isn't a set, whether all are integers, all booleans or all ranked
// strings, as `sorts_without_effects` asks, in one pass.
fn are_atoms(elements: &[Value]) -> Option<bool> {
    Some(match elements.first()? {
        Value::Int(_) => elements.iter().all(|value| matches!(value, Value::Int(_))),
        Value::Bool(_) => elements.iter().all(|value| matches!(value, Value::Bool(_))),
        Value::Set(_) => return None,
        _ => elements
            .iter()
            .all(|value| matches!(value, Value::Str(text) if text.rank != -1)),
    })
}

// The kind of the values at a depth, all of one kind: integers, booleans, ranked strings or
// sets, where a set's values one deeper are its elements and those it was built with.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Int,
    Bool,
    Str,
    Set,
}

// As deep as `sorts_without_effects` follows sets, which bounds the kinds it keeps without
// allocating.
const SORT_DEPTHS: usize = 8;

// The walk of `sorts_without_effects`: the kind at each depth, and how the elements sort.
struct SortWalk {
    kinds: [Option<Kind>; SORT_DEPTHS],
    sorting: Sorting,
}

impl Default for SortWalk {
    fn default() -> Self {
        SortWalk {
            kinds: [None; SORT_DEPTHS],
            sorting: Sorting::Plain,
        }
    }
}

impl SortWalk {
    fn walk(&mut self, value: &Value, depth: usize) -> Option<()> {
        let kind = match value {
            Value::Int(_) => Kind::Int,
            Value::Bool(_) => Kind::Bool,
            Value::Str(text) if text.rank != -1 => Kind::Str,
            Value::Set(_) => Kind::Set,
            _ => return None,
        };
        match self.kinds.get_mut(depth)? {
            Some(known) if *known != kind => return None,
            Some(_) => {}
            unknown => *unknown = Some(kind),
        }
        if let Value::Set(set) = value {
            if let Some(written) = written_of(set) {
                match depth {
                    0 => {}
                    1 => self.sorting = Sorting::Nested,
                    _ => return None,
                }
                for value in written.iter() {
                    self.walk(value, depth + 1)?;
                }
                // Elements written in their order, without duplicates, are the same values.
                if matches!(written, WrittenRef::Held(_)) || is_same_values(&written, set) {
                    return Some(());
                }
            }
            for value in set.iter() {
                self.walk(value, depth + 1)?;
            }
        }
        Some(())
    }
}

// Whether two lists hold the same values in the same order: the same sets, by address, and
// equal integers, booleans and strings.
fn is_same_values(left: &[Value], right: &[Value]) -> bool {
    left.len() == right.len()
        && left.iter().zip(right).all(|pair| match pair {
            (Value::Set(left), Value::Set(right)) => Rc::ptr_eq(left, right),
            (Value::Int(left), Value::Int(right)) => left == right,
            (Value::Bool(left), Value::Bool(right)) => left == right,
            (Value::Str(left), Value::Str(right)) => Rc::ptr_eq(left, right),
            _ => false,
        })
}

/// Normalizes the sets within sorted elements that `ValueVec.sort`'s comparisons reach, where
/// they sort as `Sorting::Nested`. `SetEnumValue.compareTo` of two sets of one size compares
/// their elements in order up to the first that differs, normalizing each pair it compares, so
/// that a comparison of two elements reaches the sets within both up to the first that differs.
/// Insertion by halves compares each element with its neighbours in the sorted order, and with
/// each element equal to it; any other element it compares shares a shorter prefix with it, as
/// the order is by size and then by the elements in order. So the sets a sort reaches in an
/// element are those up to where it first differs from either neighbour of its size, and all of
/// those of an element with an equal one, whichever sort finds the order.
fn reach_nested(sorted: &[&Value]) -> Evaluated<()> {
    let reached = reached_within(sorted, false).expect("any sorted elements");
    for (element, reach) in sorted.iter().zip(reached) {
        if let Value::Set(set) = element {
            set.iter().take(reach).try_for_each(normalize_enumeration)?;
        }
    }
    Ok(())
}

// How many of the sets within each of the sorted elements TLC's sort reaches (`reach_nested`),
// or `None` where `is_distinct` and two neighbours are equal or out of order.
fn reached_within(sorted: &[&Value], is_distinct: bool) -> Option<Vec<usize>> {
    let mut reached = vec![0; sorted.len()];
    for (index, pair) in sorted.windows(2).enumerate() {
        let reach = reached_between(pair[0], pair[1], is_distinct)?;
        reached[index] = reached[index].max(reach);
        reached[index + 1] = reached[index + 1].max(reach);
    }
    Some(reached)
}

// How many of the sets within two neighbouring sorted elements TLC's sort reaches as it compares
// them (`reach_nested`), or `None` where `is_distinct` and they are equal or out of order.
fn reached_between(left: &Value, right: &Value, is_distinct: bool) -> Option<usize> {
    let (Value::Set(left), Value::Set(right)) = (left, right) else {
        unreachable!("elements sorts_without_effects accepts")
    };
    if left.len() != right.len() {
        return (!is_distinct || left.len() < right.len()).then_some(0);
    }
    let shared = left
        .iter()
        .zip(right.iter())
        .take_while(|(left, right)| compare_without_effects(left, right) == Ordering::Equal)
        .count();
    if is_distinct
        && (shared == left.len()
            || compare_without_effects(&left[shared], &right[shared]) != Ordering::Less)
    {
        return None;
    }
    Some((shared + 1).min(left.len()))
}

/// `compare_values` on elements `sorts_without_effects` accepts, without its bookkeeping.
fn compare_without_effects(left: &Value, right: &Value) -> Ordering {
    match (left, right) {
        (Value::Int(left), Value::Int(right)) => left.cmp(right),
        (Value::Bool(left), Value::Bool(right)) => left.cmp(right),
        (Value::Str(left), Value::Str(right)) if left.units == right.units => Ordering::Equal,
        (Value::Str(left), Value::Str(right)) => left.rank.cmp(&right.rank),
        (Value::Set(left), Value::Set(right)) => left.len().cmp(&right.len()).then_with(|| {
            left.iter()
                .zip(right.iter())
                .map(|(left, right)| compare_without_effects(left, right))
                .find(|comparison| *comparison != Ordering::Equal)
                .unwrap_or(Ordering::Equal)
        }),
        _ => unreachable!("elements sorts_without_effects accepts"),
    }
}

/// `SetEnumValue.normalize` of a set's elements as written, for its failure and what it
/// normalizes, without the order it finds, which is the set's own (`held`).
fn normalize_written(held: &[Value], written: &[Value], sorting: Option<Sorting>) -> Evaluated<()> {
    // One element or none sorts without a comparison.
    if written.len() < 2 {
        return Ok(());
    }
    if let Some(sorting) = sorting.or_else(|| sorts_without_effects(written)) {
        written.iter().try_for_each(normalize_enumeration)?;
        if sorting == Sorting::Nested {
            // The set's own elements are the written ones in TLC's order where they are the same
            // sets, none twice, which spares sorting them again.
            // No comparison of them fails, so the sets reached before finding the elements
            // aren't so are normalized as the sort normalizes them anyway.
            let mut is_sorted = is_same_sets(held, written);
            let mut reached_before = 0;
            for (index, element) in held.iter().enumerate().take_while(|_| is_sorted) {
                let reached_after = match held.get(index + 1) {
                    Some(next) => match reached_between(element, next, true) {
                        Some(reach) => reach,
                        None => {
                            is_sorted = false;
                            break;
                        }
                    },
                    None => 0,
                };
                if let Value::Set(set) = element {
                    let reach = reached_before.max(reached_after);
                    set.iter().take(reach).try_for_each(normalize_enumeration)?;
                }
                reached_before = reached_after;
            }
            if !is_sorted {
                drop(sorted_unique(written, true)?);
            }
        }
        return Ok(());
    }
    normalized_unique(written).map(drop)
}

// Whether two lists hold the same sets, by address, as many times each.
fn is_same_sets(left: &[Value], right: &[Value]) -> bool {
    let is_same = |left: &Value, right: &Value| matches!((left, right), (Value::Set(left), Value::Set(right)) if Rc::ptr_eq(left, right));
    if left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|(left, right)| is_same(left, right))
    {
        return true;
    }
    let addresses = |values: &mut dyn Iterator<Item = &Value>| {
        let mut addresses = values
            .map(|value| match value {
                Value::Set(set) => Some(Rc::as_ptr(set) as usize),
                _ => None,
            })
            .collect::<Option<Vec<usize>>>()?;
        addresses.sort_unstable();
        Some(addresses)
    };
    left.len() == right.len()
        && addresses(&mut left.iter())
            .is_some_and(|left| addresses(&mut right.iter()).is_some_and(|right| left == right))
}

fn normalized_unique(elements: &[Value]) -> Evaluated<Vec<&Value>> {
    // Where no comparison fails, and none normalizes a set but the elements, the order TLC
    // compares in shows only in the result, which a stable sort that keeps each first duplicate
    // finds as TLC's insertion does, in linear time on elements already in order.
    if elements.len() > 1
        && let Some(sorting) = sorts_without_effects(elements)
    {
        if matches!(elements[0], Value::Set(_)) {
            for element in elements {
                normalize_enumeration(element)?;
            }
        }
        return sorted_unique(elements, sorting == Sorting::Nested);
    }
    inserted_unique(elements)
}

// The elements `sorts_without_effects` accepts in TLC's order, without duplicates, having
// normalized the sets within them that TLC's sort reaches where `is_nested`.
fn sorted_unique(elements: &[Value], is_nested: bool) -> Evaluated<Vec<&Value>> {
    let mut sorted: Vec<&Value> = elements.iter().collect();
    let is_sorted = is_strictly_sorted(elements.iter());
    if !is_sorted {
        sorted.sort_by(|left, right| compare_without_effects(left, right));
    }
    if is_nested {
        reach_nested(&sorted)?;
    }
    if !is_sorted {
        sorted.dedup_by(|later, kept| compare_without_effects(later, kept) == Ordering::Equal);
    }
    Ok(sorted)
}

// `ValueVec.sort`: each element in the order written, the receiver of `compareTo`, inserted by
// halves among those sorted before it, unless it equals one of them.
fn inserted_unique(elements: &[Value]) -> Evaluated<Vec<&Value>> {
    let mut sorted: Vec<&Value> = Vec::with_capacity(elements.len());
    for element in elements {
        let (mut low, mut high) = (0, sorted.len());
        let mut is_duplicate = false;
        while low < high {
            let middle = low + (high - low) / 2;
            match compare(element, sorted[middle])? {
                Ordering::Equal => {
                    is_duplicate = true;
                    break;
                }
                Ordering::Less => high = middle,
                Ordering::Greater => low = middle + 1,
            }
        }
        if !is_duplicate {
            sorted.insert(low, element);
        }
    }
    Ok(sorted)
}

/// From how many keys TLC searches a sorted function's domain by halves
/// (`FcnRcdValue.LINEAR_SEARCH_THRESHOLD`).
pub(crate) const BINARY_SEARCH_KEYS: usize = 32;

/// The position of a key in a function's domain, as TLC searches for it. `FcnRcdValue.select`
/// searches a sorted domain of 32 keys or more with Java's `Arrays.binarySearch`, which asks the
/// key in the middle to compare itself with the argument, and a shorter one key by key, asking
/// each whether it equals the argument. A function TLC keeps lazy asks its bound's set, which
/// asks the argument to compare itself with the element in the middle (`ValueVec.search`).
/// Where two can't compare, TLC's message is the one of the question asked, and names them in
/// that order. TLC searches what it hasn't sorted in the order it built it, which the evaluator
/// doesn't keep, as it doesn't a record's or a tuple's search: there a failure to compare has no
/// message.
pub fn find_key(function: &Function, key: &Value) -> Evaluated<Option<usize>> {
    let is_function = matches!(function.class.get(), Class::Plain | Class::Lambda);
    let search = if is_function && function.interval.is_none() {
        function.search.get()
    } else {
        Search::Unknown
    };
    // `FcnRcdValue.selectBinarySearch` searches fewer than 32 keys linearly, with `equals`, in
    // the order it holds them, whether or not it has sorted them: a single key has one order.
    let is_single_key = search == Search::Unknown
        && function.class.get() == Class::Plain
        && function.java_class.get() == Some(Class::Plain)
        && function.interval.is_none()
        && function.domain.len() == 1;
    if is_single_key {
        // Where the key's `equals` fails, a key TLC built from an expression has its source,
        // and TLC reports the failure as a fingerprint failure ending at that key
        // (`FingerprintException`), which the evaluator words only for an integer's or a
        // string's, as a literal TLC shares has none.
        let own = &function.domain[0];
        return match equals(own, key) {
            Ok(is_equal) => Ok(is_equal.then_some(0)),
            Err(error) if matches!(own, Value::Int(_) | Value::Str(_)) => Err(error),
            Err(_) => fail("a single-key function whose key fails to equal the argument"),
        };
    }
    if search == Search::Sorted {
        if function.domain.len() >= BINARY_SEARCH_KEYS {
            let (mut low, mut high) = (0, function.domain.len() - 1);
            while low <= high {
                let middle = (low + high) / 2;
                match compare(&function.domain[middle], key)? {
                    Ordering::Equal => return Ok(Some(middle)),
                    Ordering::Less => low = middle + 1,
                    Ordering::Greater if middle == 0 => break,
                    Ordering::Greater => high = middle - 1,
                }
            }
            return Ok(None);
        }
        for (position, own) in function.domain.iter().enumerate() {
            if equals(own, key)? {
                return Ok(Some(position));
            }
        }
        return Ok(None);
    }
    let (mut low, mut high) = (0, function.domain.len());
    while low < high {
        let middle = low + (high - low) / 2;
        let order = compare(key, &function.domain[middle]).map_err(|error| EvalError {
            runtime_exception: error.runtime_exception,
            is_set_normalization: false,
            is_set_reduction: false,
            is_followed_comparison: false,
            is_named_normalization: false,
            reason: error.reason,
            message: error.message.filter(|_| search == Search::SortedDomain),
        })?;
        match order {
            Ordering::Equal => return Ok(Some(middle)),
            Ordering::Less => high = middle,
            Ordering::Greater => low = middle + 1,
        }
    }
    Ok(None)
}

/// Notes that TLC has sorted a value, a constant definition's as it starts
/// (`SpecProcessor.evalConstantDefn`): each function in it that the evaluator holds sorted too.
pub fn note_sorted(value: &Value) {
    match value {
        // TLC normalizes what it computes at startup, as it fingerprints it.
        Value::Set(elements) => {
            normalize(value);
            elements.iter().for_each(note_sorted);
        }
        Value::Function(function) => {
            if function.written.borrow().is_none() {
                function.search.set(Search::Sorted);
            }
            function.domain.iter().for_each(note_sorted);
            function.range.iter().for_each(note_sorted);
        }
        _ => {}
    }
}

/// TLC's fingerprint of a value as a trace rebuilds a state: it sorts each function it reaches
/// and turns a lambda into the function it enumerates, as `settleRecoveredState` does.
pub fn settle(value: &Value) {
    match value {
        // Fingerprinting normalizes a set (`SetEnumValue.fingerPrint`).
        Value::Set(elements) => {
            normalize(value);
            elements.iter().for_each(settle);
        }
        Value::Function(function) => {
            sort(function);
            function.search.set(Search::Sorted);
            if function.class.get() == Class::Lambda {
                function.class.set(Class::Plain);
            }
            function.domain.iter().for_each(settle);
            function.range.iter().for_each(settle);
        }
        // A lazy set enumerates into its parts' values, so fingerprinting it settles them.
        Value::Lazy(lazy) => match &***lazy {
            Lazy::Subset(base) | Lazy::Seq(base) => settle(base),
            Lazy::FunctionSet(domain, range) => {
                settle(domain);
                settle(range);
            }
            Lazy::RecordSet(fields, _) => fields.iter().for_each(|(_, set)| settle(set)),
            Lazy::Product(factors) => factors.iter().for_each(settle),
            Lazy::Union(sets) | Lazy::Filter(sets, _) => settle(sets),
            Lazy::Cap(left, right) | Lazy::Cup(left, right) | Lazy::Diff(left, right) => {
                settle(left);
                settle(right);
            }
            Lazy::Nat | Lazy::Int | Lazy::Real | Lazy::Strings | Lazy::Any => {}
        },
        _ => {}
    }
}

/// Whether a value is the one an id of the store holds, by a walk that reads the store only.
pub fn matches(store: &Store, id: u32, value: &Value) -> bool {
    let kind = store.kind_of(id);
    match value {
        Value::Lazy(lazy) if matches!(***lazy, Lazy::Any) => kind == KIND_ANY,
        Value::Bool(boolean) => kind == KIND_BOOL && (id == TRUE) == *boolean,
        Value::Int(int) => kind == KIND_INT && store.int_of(id) == *int,
        Value::Str(text) => kind == KIND_STRING && *store.text_of(id) == *text.units,
        Value::Model(text) => kind == KIND_MODEL && *store.text_of(id) == *text.units,
        Value::Lazy(lazy) if matches!(***lazy, Lazy::Nat | Lazy::Int | Lazy::Strings) => {
            kind == KIND_INFINITE_SET
                && store.infinite_name_of(id)
                    == match ***lazy {
                        Lazy::Nat => NAT,
                        Lazy::Int => INT,
                        _ => STRINGS,
                    }
        }
        Value::Function(function) => {
            let size = function.domain.len();
            if kind == KIND_SET
                || kind <= KIND_MODEL
                || kind == KIND_INFINITE_SET
                || kind == KIND_ANY
                || store.size_of(id) as usize != size
            {
                return false;
            }
            (0..size).all(|index| {
                let is_key = if kind == KIND_TUPLE {
                    matches!(function.domain[index], Value::Int(key) if key == index as i32 + 1)
                } else {
                    store
                        .peek_key(id, index as u32)
                        .is_some_and(|key| matches(store, key, &function.domain[index]))
                };
                is_key
                    && matches(
                        store,
                        store.get_range_value(id, index as u32),
                        &function.range[index],
                    )
            })
        }
        _ => {
            let Ok(elements) = elements(value) else {
                return false;
            };
            kind == KIND_SET
                && store.size_of(id) as usize == elements.len()
                && elements.iter().enumerate().all(|(index, element)| {
                    matches(store, store.element_at(id, index as u32), element)
                })
        }
    }
}

/// TLC's `deepNormalize` of a value it permutes or compares whole (`forgetDeepWrittenOrder`): it
/// sorts each function it reaches, but a lambda it evaluates again to print.
pub fn settle_deep(value: &Value) {
    match value {
        Value::Set(elements) => elements.iter().for_each(settle_deep),
        Value::Function(function) if function.class.get() != Class::Lambda => {
            sort(function);
            function.domain.iter().for_each(settle_deep);
            function.range.iter().for_each(settle_deep);
        }
        _ => {}
    }
}

/// `IValue.deepNormalize` as TLCStateMut.fingerPrint applies it to a state under a VIEW
/// (`forgetNormalizedWrittenOrder`): a set or a domain sorts its elements, comparing them, only when
/// it has two or more.
pub fn settle_normalized(value: &Value) {
    let settle_sorted = |values: &[Value]| {
        if values.len() > 1 {
            values.iter().for_each(settle_deep);
        } else {
            values.iter().for_each(settle_normalized);
        }
    };
    match value {
        Value::Set(elements) => settle_sorted(elements),
        Value::Function(function) if function.class.get() != Class::Lambda => {
            sort(function);
            if function.domain.len() > 1 {
                settle_sorted(&function.domain);
            }
            function.range.iter().for_each(settle_normalized);
        }
        _ => {}
    }
}

/// `deepNormalize` of a state whose lambdas TLC has built into the functions they enumerate, as
/// permuting the state under SYMMETRY builds them: each lambda becomes the function it enumerates,
/// and then the state normalizes as `settle_normalized` does.
pub fn settle_built(value: &Value) {
    build_lambdas(value);
    settle_normalized(value);
}

fn build_lambdas(value: &Value) {
    match value {
        Value::Set(elements) => elements.iter().for_each(build_lambdas),
        Value::Function(function) => {
            if function.java_class.get() == Some(Class::Lambda) {
                function.java_class.set(None);
            }
            if function.class.get() == Class::Lambda {
                function.class.set(Class::Plain);
            }
            function.domain.iter().for_each(build_lambdas);
            function.range.iter().for_each(build_lambdas);
        }
        _ => {}
    }
}

/// Whether two values are the same, by a walk that sorts nothing, unlike TLC's comparisons.
pub fn is_same(left: &Value, right: &Value) -> bool {
    match (left, right) {
        (Value::Bool(left), Value::Bool(right)) => left == right,
        (Value::Int(left), Value::Int(right)) => left == right,
        (Value::Str(left), Value::Str(right)) | (Value::Model(left), Value::Model(right)) => {
            left.units == right.units
        }
        (Value::Function(left), Value::Function(right)) => {
            left.domain.len() == right.domain.len()
                && left
                    .domain
                    .iter()
                    .zip(&right.domain)
                    .all(|(left, right)| is_same(left, right))
                && left
                    .range
                    .iter()
                    .zip(&right.range)
                    .all(|(left, right)| is_same(left, right))
        }
        _ if left.is_set() && right.is_set() => match (elements(left), elements(right)) {
            (Ok(left), Ok(right)) => {
                left.len() == right.len()
                    && left
                        .iter()
                        .zip(right.iter())
                        .all(|(left, right)| is_same(left, right))
            }
            _ => false,
        },
        _ => false,
    }
}

/// The value an id of the store holds, as TLC holds it normalized: a tuple as a tuple, a function
/// of strings as a record. A function the engine kept lazy is the machine's that built it, which
/// the store alone can't give.
pub fn from_store(store: &Store, id: u32) -> Result<Value, Unsupported> {
    let text = || {
        Rc::new(Text {
            units: store.text_of(id).into(),
            rank: store.text_rank_of(id),
        })
    };
    let size = store.size_of(id);
    Ok(match store.kind_of(id) {
        KIND_ANY => Value::lazy(Lazy::Any),
        KIND_BOOL => Value::Bool(id == TRUE),
        KIND_INT => Value::Int(store.int_of(id)),
        KIND_STRING => Value::Str(text()),
        KIND_MODEL => Value::Model(text()),
        KIND_INFINITE_SET => Value::lazy(match store.infinite_name_of(id) {
            NAT => Lazy::Nat,
            INT => Lazy::Int,
            _ => Lazy::Strings,
        }),
        KIND_SET => Value::set_with_class(
            (0..size)
                .map(|index| from_store(store, store.element_at(id, index)))
                .collect::<Result<_, _>>()?,
            None,
        ),
        kind @ (KIND_FUNCTION | KIND_TUPLE) => {
            let range = (0..size)
                .map(|index| from_store(store, store.get_range_value(id, index)))
                .collect::<Result<_, _>>()?;
            if kind == KIND_TUPLE {
                let value = Value::tuple(range);
                if let Value::Function(function) = &value {
                    function.java_class.set(None);
                    function.is_counter_example.set(None);
                }
                return Ok(value);
            }
            let domain: Vec<Value> = (0..size)
                .filter_map(|index| store.peek_key(id, index))
                .map(|key| from_store(store, key))
                .collect::<Result<_, _>>()?;
            let class = if store.is_record(id) {
                Class::Record
            } else {
                Class::Plain
            };
            let value = Value::function(domain, range, class);
            if let Value::Function(function) = &value {
                function.java_class.set(None);
                function.is_counter_example.set(None);
            }
            value
        }
        _ => {
            return Err(Unsupported(
                "a value the search left holding a function TLC keeps lazy".into(),
            ));
        }
    })
}

/// A value with its model values renamed by a permutation of a symmetry set, as TLC's `permute`
/// gives it: sorted again.
pub fn permute(value: &Value, permutation: &[(Rc<Text>, Rc<Text>)]) -> Evaluated<Value> {
    Ok(match value {
        Value::Model(text) => Value::Model(
            permutation
                .iter()
                .find(|(from, _)| from.units == text.units)
                .map_or_else(|| Rc::clone(text), |(_, to)| Rc::clone(to)),
        ),
        Value::Set(elements) => {
            let result = set_of(
                elements
                    .iter()
                    .map(|element| permute(element, permutation))
                    .collect::<Evaluated<_>>()?,
            )?;
            if elements.java_class.is_some() {
                result
            } else {
                result.without_set_provenance()
            }
        }
        Value::Function(function) if function.interval.is_some() => {
            Value::Function(Rc::new(Function {
                domain: function.domain.clone(),
                range: function
                    .range
                    .iter()
                    .map(|value| permute(value, permutation))
                    .collect::<Evaluated<_>>()?,
                class: function.class.clone(),
                java_class: Cell::new(function.java_class.get().map(|class| {
                    if class == Class::Lambda {
                        Class::Plain
                    } else {
                        class
                    }
                })),
                is_counter_example: std::cell::Cell::new(Some(false)),
                is_eager_record: std::cell::Cell::new(false),
                written: RefCell::new(None),
                search: Cell::new(Search::Unknown),
                interval: function.interval,
                is_domain_interval: Cell::new(false),
            }))
        }
        Value::Function(function) => {
            let keys = function
                .domain
                .iter()
                .map(|key| permute(key, permutation))
                .collect::<Evaluated<_>>()?;
            let values = function
                .range
                .iter()
                .map(|value| permute(value, permutation))
                .collect::<Evaluated<_>>()?;
            let permuted = sorted_function(keys, values, function.class.get())?;
            if let Value::Function(permuted) = &permuted {
                permuted.is_counter_example.set(if permutation.is_empty() {
                    function.is_counter_example.get()
                } else {
                    function
                        .is_counter_example
                        .get()
                        .filter(|is_counter| !is_counter)
                });
                permuted
                    .java_class
                    .set(function.java_class.get().map(|class| {
                        if class == Class::Lambda {
                            Class::Plain
                        } else {
                            class
                        }
                    }));
            }
            permuted
        }
        Value::Lazy(_) => return fail("permuting a lazy set"),
        _ => value.clone(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn interval_functions_retain_extreme_keys_and_empty_domains() {
        let singleton = Value::over_interval(i32::MAX, vec![Value::Int(7)], Class::Plain);
        assert!(matches!(
            crate::eval::apply_value(&singleton, &Value::Int(i32::MAX)),
            Ok(Value::Int(7))
        ));
        let empty = Value::over_interval(i32::MIN, Vec::new(), Class::Plain);
        assert!(crate::eval::apply_value(&empty, &Value::Int(i32::MIN)).is_err());
        assert!(
            matches!(empty, Value::Function(function) if function.domain.is_empty() && function.range.is_empty())
        );
    }

    // A comparison that fails outside `failing_comparisons`, as sorting a set's elements does,
    // keeps none of its operands, while `failing_comparisons` gives the operand that failed.
    #[test]
    fn keeps_comparisons_only_while_finding_a_failing_one() {
        let set = Value::set(vec![Value::Int(1)]);
        assert!(compare(&set, &Value::Int(2)).is_err());
        assert!(COMPARING.with_borrow(Option::is_none));
        let failed = failing_comparisons(|| compare(&set, &Value::Int(2)));
        assert_eq!(failed.err().map(|values| values.len()), Some(1));
        assert!(COMPARING.with_borrow(Option::is_none));
    }

    #[test]
    fn sorts_comparable_sets_as_tlcs_insertion_does() {
        // Sets of sets of integers, strings and booleans, with duplicates, some held
        // unnormalized with their elements written out of order, in a scrambled order.
        let mut state = 7_u64;
        let mut next = |bound: u64| {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1);
            (state >> 33) % bound
        };
        let text = |rank: i32| {
            Value::Str(Rc::new(Text {
                units: format!("s{rank}").encode_utf16().collect(),
                rank,
            }))
        };
        for kind in 0..3 {
            for _ in 0..40 {
                clear_unnormalized();
                let size = next(30) as usize;
                let mut held = Vec::new();
                let values: Vec<Value> = (0..size)
                    .map(|_| {
                        let mut written: Vec<Value> = (0..next(4))
                            .map(|_| {
                                let atom = next(5) as i32;
                                match kind {
                                    0 => Value::Int(atom),
                                    1 => text(atom),
                                    _ => Value::Bool(atom % 2 == 0),
                                }
                            })
                            .collect();
                        let sorted = inserted_unique(&written)
                            .expect("comparable values")
                            .into_iter()
                            .cloned()
                            .collect();
                        let set = Value::set(sorted);
                        if next(2) == 0 {
                            written.reverse();
                            held.push((set.clone(), written));
                        }
                        set
                    })
                    .collect();
                let mark = |held: &[(Value, Vec<Value>)]| {
                    for (set, written) in held {
                        mark_unnormalized(set, written.clone());
                    }
                };
                mark(&held);
                assert_eq!(sorts_without_effects(&values), Some(Sorting::Plain));
                let expected = inserted_unique(&values).expect("comparable values");
                let normalized_by_insertion: Vec<bool> = held
                    .iter()
                    .map(|(set, _)| unnormalized(set).is_none())
                    .collect();
                clear_unnormalized();
                mark(&held);
                let sorted = normalized_unique(&values).expect("comparable values");
                assert_eq!(sorted.len(), expected.len());
                assert!(
                    sorted
                        .iter()
                        .zip(&expected)
                        .all(|(left, right)| std::ptr::eq(*left, *right))
                );
                let normalized: Vec<bool> = held
                    .iter()
                    .map(|(set, _)| unnormalized(set).is_none())
                    .collect();
                assert_eq!(normalized, normalized_by_insertion);
            }
        }
        clear_unnormalized();
    }

    #[test]
    fn reaches_the_sets_within_elements_as_tlcs_insertion_does() {
        // Sets of sets of integers, with duplicates at both levels, some sets at either level
        // held unnormalized with their elements written out of order.
        let mut state = 11_u64;
        let mut next = |bound: u64| {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1);
            (state >> 33) % bound
        };
        for _ in 0..300 {
            clear_unnormalized();
            let mut held = Vec::new();
            let inner = |next: &mut dyn FnMut(u64) -> u64, held: &mut Vec<(Value, Vec<Value>)>| {
                let mut written: Vec<Value> =
                    (0..next(3)).map(|_| Value::Int(next(3) as i32)).collect();
                let sorted = inserted_unique(&written)
                    .expect("comparable values")
                    .into_iter()
                    .cloned()
                    .collect();
                let set = Value::set(sorted);
                if next(3) != 0 {
                    written.reverse();
                    held.push((set.clone(), written));
                }
                set
            };
            let pool: Vec<Value> = (0..next(6) + 1)
                .map(|_| inner(&mut next, &mut held))
                .collect();
            let values: Vec<Value> = (0..next(25))
                .map(|_| {
                    let mut written: Vec<Value> = (0..next(4))
                        .map(|_| {
                            if next(2) == 0 {
                                pool[next(pool.len() as u64) as usize].clone()
                            } else {
                                inner(&mut next, &mut held)
                            }
                        })
                        .collect();
                    let sorted = preserving_set_normalization(|| {
                        inserted_unique(&written)
                            .expect("comparable values")
                            .into_iter()
                            .cloned()
                            .collect()
                    });
                    let set = Value::set(sorted);
                    if next(2) == 0 {
                        written.reverse();
                        held.push((set.clone(), written));
                    }
                    set
                })
                .collect();
            let mark = |held: &[(Value, Vec<Value>)]| {
                for (set, written) in held {
                    mark_unnormalized(set, written.clone());
                }
            };
            mark(&held);
            let sorting = sorts_without_effects(&values);
            assert!(sorting.is_some());
            let expected = inserted_unique(&values).expect("comparable values");
            let normalized_by_insertion: Vec<bool> = held
                .iter()
                .map(|(set, _)| unnormalized(set).is_none())
                .collect();
            clear_unnormalized();
            mark(&held);
            let sorted = normalized_unique(&values).expect("comparable values");
            assert_eq!(sorted.len(), expected.len());
            assert!(
                sorted
                    .iter()
                    .zip(&expected)
                    .all(|(left, right)| std::ptr::eq(*left, *right))
            );
            let normalized: Vec<bool> = held
                .iter()
                .map(|(set, _)| unnormalized(set).is_none())
                .collect();
            assert_eq!(normalized, normalized_by_insertion, "{sorting:?}");
            // A set built of them, which TLC normalizes by sorting them as written.
            clear_unnormalized();
            mark(&held);
            let set = Value::set(expected.iter().map(|value| (*value).clone()).collect());
            mark_unnormalized(&set, values.clone());
            elements(&set).expect("comparable values");
            let normalized: Vec<bool> = held
                .iter()
                .map(|(set, _)| unnormalized(set).is_none())
                .collect();
            assert_eq!(normalized, normalized_by_insertion, "{sorting:?}");
        }
        clear_unnormalized();
    }

    #[test]
    fn normalizes_built_sets_as_tlcs_insertion_does() {
        // Sets of sets of sets of integers a replay builds, with duplicates at each level, which
        // keep how their elements sort from when they were built.
        let mut state = 5_u64;
        let mut next = |bound: u64| {
            state = state
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1);
            (state >> 33) % bound
        };
        let built = |values: Vec<Value>| held_set_of(values).expect("comparable values");
        for _ in 0..300 {
            clear_unnormalized();
            let mut sets = Vec::new();
            let inner: Vec<Value> = (0..next(5) + 1)
                .map(|_| built((0..next(3)).map(|_| Value::Int(next(3) as i32)).collect()))
                .collect();
            sets.extend(inner.iter().cloned());
            let outer: Vec<Value> = (0..next(6) + 1)
                .map(|_| {
                    built(
                        (0..next(4))
                            .map(|_| inner[next(inner.len() as u64) as usize].clone())
                            .collect(),
                    )
                })
                .collect();
            sets.extend(outer.iter().cloned());
            let values: Vec<Value> = (0..next(12))
                .map(|_| outer[next(outer.len() as u64) as usize].clone())
                .collect();
            let written: Vec<Option<Vec<Value>>> = sets.iter().map(unnormalized).collect();
            let top = built(values.clone());
            elements(&top).expect("comparable values");
            let normalized: Vec<bool> =
                sets.iter().map(|set| unnormalized(set).is_none()).collect();
            clear_unnormalized();
            for (set, written) in sets.iter().zip(&written) {
                if let Some(written) = written {
                    mark_unnormalized(set, written.clone());
                }
            }
            inserted_unique(&values).expect("comparable values");
            let expected: Vec<bool> = sets.iter().map(|set| unnormalized(set).is_none()).collect();
            assert_eq!(normalized, expected);
        }
        clear_unnormalized();
    }

    #[test]
    fn normalizes_in_tlc_order_and_keeps_the_first_duplicate() {
        let values = [Value::Int(2), Value::Int(1), Value::Int(2), Value::Int(3)];
        let sorted = normalized_unique(&values).expect("comparable values");
        assert!(std::ptr::eq(sorted[0], &values[1]));
        assert!(std::ptr::eq(sorted[1], &values[0]));
        assert!(std::ptr::eq(sorted[2], &values[3]));
    }

    #[test]
    fn normalization_returns_tlcs_first_failing_comparison() {
        let values = vec![Value::Int(1), Value::Int(2), Value::Bool(false)];
        let error = normalize_failure(&values).expect("the values cannot compare");
        assert_eq!(set_of(values).err(), Some(error.clone()));
        let text = error.message.expect("TLC's comparison message").text;
        assert!(text.contains("boolean FALSE"));
        assert!(text.ends_with('2'));
    }

    #[test]
    fn keeps_set_runtime_provenance_separate_from_enumerated_contents() {
        assert_eq!(std::mem::size_of::<Value>(), 16);
        let contents = Rc::new(vec![Value::Int(1)]);
        let enumeration = Value::set_from_rc(Rc::clone(&contents), Some(SetClass::Enumeration));
        let predicate = Value::set_from_rc(Rc::clone(&contents), Some(SetClass::Predicate));
        let transferred = Value::set_from_rc(Rc::clone(&contents), None);
        for value in [&enumeration, &predicate, &transferred] {
            assert!(equals(value, &enumeration).expect("equal contents"));
            assert!(Rc::ptr_eq(&elements(value).expect("enumerated"), &contents));
        }
        assert_eq!(java_set_class(&enumeration), Some(SetClass::Enumeration));
        assert_eq!(
            java_set_class(&predicate.clone()),
            Some(SetClass::Predicate)
        );
        assert_eq!(java_set_class(&transferred.clone()), None);
        let written = vec![Value::Int(2), Value::Int(1)];
        let set = set_of(written.clone()).expect("a set");
        mark_unnormalized(&set, written);
        let unknown = set.without_set_provenance();
        assert!(matches!(
            unnormalized(&unknown).expect("written order")[0],
            Value::Int(2)
        ));
        assert_eq!(java_set_class(&unknown), None);
        assert_eq!(
            java_set_class(&permute(&transferred, &[]).expect("permuted")),
            None
        );
        let interval = Value::interval(1, 3).without_set_provenance();
        assert_eq!(java_set_class(&interval), None);
        assert_eq!(
            java_set_class(&permute(&interval, &[]).expect("permuted")),
            None
        );
        let lazy = Value::lazy(Lazy::Subset(enumeration)).without_set_provenance();
        assert_eq!(java_set_class(&lazy), None);
        assert_eq!(elements(&lazy).expect("enumerated").len(), 2);
        assert_eq!(java_set_class(&lazy), None);
    }

    // A set a replay built unnormalized is gone once nothing else holds it.
    #[test]
    fn keeps_no_set_built_unnormalized_once_dropped() {
        let Value::Set(elements) = Value::set(vec![Value::Int(2), Value::Int(1)]) else {
            unreachable!("a set enumeration")
        };
        let held = Rc::downgrade(&elements);
        let set = Value::Set(elements);
        mark_unnormalized(&set, vec![Value::Int(2), Value::Int(1)]);
        assert_eq!(unnormalized(&set).map(|written| written.len()), Some(2));
        drop(set);
        assert!(held.upgrade().is_none());
        clear_unnormalized();
    }
    #[test]
    fn failed_left_normalization_leaves_the_right_set_unnormalized() {
        let right = set_of(vec![Value::Int(3), Value::Int(1), Value::Int(2)]).expect("a set");
        mark_unnormalized(&right, vec![Value::Int(3), Value::Int(1), Value::Int(2)]);
        let left = Value::unsorted(vec![Value::Int(1), Value::Bool(true)]);
        assert!(equals(&left, &right).is_err());
        assert!(unnormalized(&right).is_some());
    }

    #[test]
    fn constructor_sorting_does_not_normalize_a_held_inner_set() {
        let inner = set_of(vec![Value::Int(20), Value::Int(10)]).expect("a set");
        mark_unnormalized(&inner, vec![Value::Int(20), Value::Int(10)]);
        let singleton = Value::set(vec![Value::Int(1)]);
        preserving_set_normalization(|| {
            preserving_set_normalization(|| {
                set_of(vec![inner.clone(), singleton.clone()]).expect("an outer set")
            })
        });
        assert!(unnormalized(&inner).is_some());
        set_of(vec![inner.clone(), singleton]).expect("a real comparison");
        assert!(unnormalized(&inner).is_none());
    }
}
