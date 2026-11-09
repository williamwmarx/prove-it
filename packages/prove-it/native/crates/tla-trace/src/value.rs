//! The evaluator's values: trees that keep what TLC's `Value` classes keep and the store forgets,
//! as the TypeScript `Value` of `values.ts` does: a record's written order until TLC sorts it, the
//! function classes, intervals, and the lazy sets TLC keeps. Values are ordered as the store
//! orders them, rule for rule, so a set's elements are in TLC's order and a value matches the
//! store's id of it ([`matches`]).

use std::cell::{Cell, RefCell};
use std::cmp::Ordering;
use std::collections::HashMap;
use std::rc::Rc;

use tla_values::Store;

use crate::print::format_pretty;
use tla_values::store::{
    INT, KIND_BOOL, KIND_INFINITE_SET, KIND_INT, KIND_MODEL, KIND_SET, KIND_STRING, KIND_TUPLE,
    NAT, STRINGS, TRUE,
};

/// Why an evaluation failed, as TLC would have, or where the evaluator can't follow it: the
/// evaluator's reason, and TLC's message where the failure gives TLC's text.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EvalError {
    pub reason: String,
    pub message: Option<TlcMessage>,
}

/// TLC's message for an error: its text, the code of TLC's message it is where it is one of
/// `tlc2.output.MP`'s, and whether TLC raises it as an EvalException rather than a
/// RuntimeException.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TlcMessage {
    pub text: String,
    pub code: Option<u32>,
    pub is_eval_exception: bool,
}

pub type Evaluated<T> = Result<T, EvalError>;

pub fn fail<T>(reason: impl Into<String>) -> Evaluated<T> {
    Err(EvalError {
        reason: reason.into(),
        message: None,
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
        }),
    })
}

/// A failure with TLC's message for it.
pub fn fail_with<T>(reason: impl Into<String>, message: TlcMessage) -> Evaluated<T> {
    Err(EvalError {
        reason: reason.into(),
        message: Some(message),
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
        }),
    })
}

/// A string or a model value's name, with TLC's rank of it: the order TLC interned the text in,
/// or -1 for a text the IR doesn't rank, which compares by its units, as the store's does.
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
    pub written: RefCell<Option<Vec<u32>>>,
    /// The interval the function was built over, which DOMAIN gives back, as TLC keeps a
    /// tuple's or a function's over `a..b` (`getDomainInterval`); `None` for any other domain.
    pub interval: Option<(i32, i32)>,
}

/// The sets TLC keeps lazily, and the infinite ones.
#[derive(Debug)]
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
}

impl Lazy {
    /// Whether TLC holds the set as a `UserValue` its module overrides (Nat, Int, Real, STRING,
    /// Seq(S)), which isn't `Enumerable` and compares only with another.
    pub fn is_overridden(&self) -> bool {
        matches!(
            self,
            Lazy::Nat | Lazy::Int | Lazy::Real | Lazy::Strings | Lazy::Seq(_)
        )
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
    Bool(bool),
    Int(i32),
    Str(Rc<Text>),
    Model(Rc<Text>),
    /// A set enumeration, its elements distinct and in TLC's order.
    Set(Rc<Vec<Value>>),
    /// A set enumeration TLC fails to normalize, its elements as written: TLC keeps it as it is
    /// until it fingerprints or prints it, which then fails.
    Unsorted(Rc<Vec<Value>>),
    /// `low..high`, an `IntervalValue`.
    Interval(i32, i32),
    Function(Rc<Function>),
    Lazy(Rc<Lazy>),
}

impl Value {
    pub fn empty_set() -> Value {
        Value::Set(Rc::new(Vec::new()))
    }

    pub fn function(domain: Vec<Value>, range: Vec<Value>, class: Class) -> Value {
        Value::Function(Rc::new(Function {
            domain,
            range,
            class: Cell::new(class),
            written: RefCell::new(None),
            interval: None,
        }))
    }

    /// A function over `low..low + range.len() - 1`, built over that interval.
    pub fn over_interval(low: i32, range: Vec<Value>, class: Class) -> Value {
        let high = low + range.len() as i32 - 1;
        Value::Function(Rc::new(Function {
            domain: (low..=high).map(Value::Int).collect(),
            range,
            class: Cell::new(class),
            written: RefCell::new(None),
            interval: Some((low, high)),
        }))
    }

    pub fn tuple(elements: Vec<Value>) -> Value {
        Value::over_interval(1, elements, Class::Tuple)
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
            Value::Bool(_) => "boolean",
            Value::Int(_) => "integer",
            Value::Str(_) => "string",
            Value::Model(_) => "model value",
            Value::Function(_) => "function",
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
        class: Cell::new(class),
        written: RefCell::new(written),
        interval: None,
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

fn compare_texts(left: &Text, right: &Text) -> Ordering {
    match (left.rank, right.rank) {
        (-1, -1) => left.units.cmp(&right.units),
        (_, -1) => Ordering::Less,
        (-1, _) => Ordering::Greater,
        (left, right) => left.cmp(&right),
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
    // The sets a replay built that TLC holds unnormalized still, by address, each with its
    // elements in the order TLC built it. Each entry holds its set, so that no other set takes
    // its address while the entry lasts.
    static UNNORMALIZED: RefCell<HashMap<usize, Unnormalized>> = RefCell::new(HashMap::new());
}

// A set TLC holds unnormalized, with its elements as TLC built it.
type Unnormalized = (Rc<Vec<Value>>, Vec<Value>);

/// Records a set a replay built as TLC holds it unnormalized (`SetEnumValue` with `isNorm`
/// false), with its elements as TLC built it.
pub(crate) fn mark_unnormalized(set: &Value, written: Vec<Value>) {
    if let Value::Set(elements) = set {
        UNNORMALIZED.with(|sets| {
            sets.borrow_mut().insert(
                Rc::as_ptr(elements) as usize,
                (Rc::clone(elements), written),
            )
        });
    }
}

/// The elements of a set TLC holds unnormalized, as TLC built it.
pub(crate) fn unnormalized(set: &Value) -> Option<Vec<Value>> {
    let Value::Set(elements) = set else {
        return None;
    };
    UNNORMALIZED.with(|sets| {
        sets.borrow()
            .get(&(Rc::as_ptr(elements) as usize))
            .map(|entry| entry.1.clone())
    })
}

/// Forgets the sets the last replay built.
pub(crate) fn clear_unnormalized() {
    UNNORMALIZED.with(|sets| sets.borrow_mut().clear());
}

// TLC normalizes a set to enumerate, compare or print it.
pub(crate) fn normalize(value: &Value) {
    if let Value::Set(elements) = value {
        UNNORMALIZED.with(|sets| {
            let mut sets = sets.borrow_mut();
            if !sets.is_empty() {
                sets.remove(&(Rc::as_ptr(elements) as usize));
            }
        });
    }
}

/// The elements of a set TLC can enumerate, in TLC's order.
/// `IntervalValue.size`: an interval of more than 2^31 - 1 elements has no int size.
pub fn interval_size(low: i32, high: i32) -> Evaluated<usize> {
    let size = (i64::from(high) - i64::from(low) + 1).max(0);
    if size > i64::from(i32::MAX) {
        return fail_runtime(
            "an interval too large to size",
            format!(
                "Size of interval value exceeds the maximum representable size (32bits): {}.",
                format_pretty(&Value::Interval(low, high))
            ),
        );
    }
    Ok(size as usize)
}

/// The most elements of an interval the evaluator builds.
const MAXIMUM_INTERVAL: usize = 1 << 24;

pub fn elements(value: &Value) -> Evaluated<Rc<Vec<Value>>> {
    normalize(value);
    match value {
        Value::Set(elements) => Ok(Rc::clone(elements)),
        // An interval TLC walks without building it, which the evaluator builds, up to a size.
        Value::Interval(low, high)
            if i64::from(*high) - i64::from(*low) >= MAXIMUM_INTERVAL as i64 =>
        {
            interval_size(*low, *high)?;
            fail("an interval too large to build")
        }
        Value::Interval(low, high) => Ok(Rc::new((*low..=*high).map(Value::Int).collect())),
        // TLC finds a set its parts empty to be empty before it enumerates any of them.
        Value::Lazy(_) if crate::sets::is_empty_by_argument(value) => Ok(Rc::new(Vec::new())),
        Value::Lazy(lazy) => crate::sets::enumerate(lazy).map(Rc::new),
        _ => fail(format!("expected a set, not a {}", value.kind_name())),
    }
}

fn is_record(function: &Function) -> bool {
    function
        .domain
        .iter()
        .all(|key| matches!(key, Value::Str(_)))
}

/// Forgets the written order of a function TLC sorts to compare it.
fn sort(function: &Function) {
    function.written.borrow_mut().take();
}

/// TLC's `compareTo`, as the store's `compare`: an error where TLC can't compare the two.
pub fn compare(left: &Value, right: &Value) -> Evaluated<Ordering> {
    normalize(left);
    normalize(right);
    match (left, right) {
        (Value::Int(left), Value::Int(right)) => Ok(left.cmp(right)),
        (Value::Bool(left), Value::Bool(right)) => Ok(left.cmp(right)),
        (Value::Str(left), Value::Str(right)) => Ok(compare_texts(left, right)),
        (Value::Model(left_text), Value::Model(right_text)) => {
            check_model_types(left, right, false)?;
            Ok(compare_texts(left_text, right_text))
        }
        (Value::Model(model), _) => {
            if model.model_type() == 0 {
                Ok(Ordering::Less)
            } else {
                typed_model_failure(left, right, false)
            }
        }
        (_, Value::Model(model)) => {
            if model.model_type() == 0 {
                Ok(Ordering::Greater)
            } else {
                typed_model_failure(left, right, false)
            }
        }
        (Value::Function(left), Value::Function(right)) => compare_functions(left, right),
        (Value::Lazy(lazy), _) if lazy.is_overridden() => compare_overridden(left, lazy, right),
        (_, Value::Lazy(lazy)) if lazy.is_overridden() && left.is_set() => {
            incomparable(left, right, false)
        }
        _ if left.is_set() && right.is_set() => {
            let (left, right) = (elements(left)?, elements(right)?);
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
    let size = left.domain.len();
    if size != right.domain.len() {
        if size > 0 && !right.domain.is_empty() && is_record(left) != is_record(right) {
            return fail("record compared with a function");
        }
        return Ok(size.cmp(&right.domain.len()));
    }
    for (left, right) in left.domain.iter().zip(&right.domain) {
        let comparison = compare(left, right)?;
        if comparison != Ordering::Equal {
            return Ok(comparison);
        }
    }
    for (left, right) in left.range.iter().zip(&right.range) {
        let comparison = compare(left, right)?;
        if comparison != Ordering::Equal {
            return Ok(comparison);
        }
    }
    Ok(Ordering::Equal)
}

/// TLC's `equals`, as the store's: values of kinds TLC can't compare fail, but a model value
/// without a type is unequal to anything else.
pub fn equals(left: &Value, right: &Value) -> Evaluated<bool> {
    normalize(left);
    normalize(right);
    match (left, right) {
        (Value::Int(left), Value::Int(right)) => Ok(left == right),
        (Value::Bool(left), Value::Bool(right)) => Ok(left == right),
        (Value::Str(left), Value::Str(right)) => Ok(left.units == right.units),
        (Value::Model(left_text), Value::Model(right_text)) => {
            check_model_types(left, right, true)?;
            Ok(left_text.units == right_text.units)
        }
        (Value::Model(model), _) | (_, Value::Model(model)) => {
            if model.model_type() == 0 {
                Ok(false)
            } else {
                typed_model_failure(left, right, true)
            }
        }
        (Value::Function(left), Value::Function(right)) => {
            sort(left);
            sort(right);
            let size = left.domain.len();
            if size > 0 && !right.domain.is_empty() && is_record(left) != is_record(right) {
                return fail("record compared with a function");
            }
            if size != right.domain.len() {
                return Ok(false);
            }
            for (left, right) in left.domain.iter().zip(&right.domain) {
                if !equals(left, right)? {
                    return Ok(false);
                }
            }
            for (left, right) in left.range.iter().zip(&right.range) {
                if !equals(left, right)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
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
            equal_constructions(left, left_lazy, right, right_lazy)
        }
        _ if left.is_set() && right.is_set() => {
            if let (Value::Interval(low, high), Value::Interval(other_low, other_high)) =
                (left, right)
            {
                let is_empty = low > high;
                return Ok(if is_empty || other_low > other_high {
                    is_empty && other_low > other_high
                } else {
                    low == other_low && high == other_high
                });
            }
            let (left, right) = (elements(left)?, elements(right)?);
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

fn is_same_construction(left: &Lazy, right: &Lazy) -> bool {
    matches!(
        (left, right),
        (Lazy::FunctionSet(..), Lazy::FunctionSet(..))
            | (Lazy::RecordSet(..), Lazy::RecordSet(..))
            | (Lazy::Product(..), Lazy::Product(..))
    )
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

// `UserValue.compareTo`: an overridden set compares with another by its module's `compareTo`
// (Nat before Int, Seq(S) by its range), and with nothing else.
fn compare_overridden(left: &Value, lazy: &Lazy, right: &Value) -> Evaluated<Ordering> {
    let shown = || format_pretty(left);
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
    match (lazy, &**other) {
        (Lazy::Nat, Lazy::Nat) | (Lazy::Int, Lazy::Int) | (Lazy::Strings, Lazy::Strings) => {
            Ok(Ordering::Equal)
        }
        (Lazy::Nat, Lazy::Int) => Ok(Ordering::Less),
        (Lazy::Int, Lazy::Nat) => Ok(Ordering::Greater),
        // Both unbounded: by the range.
        (Lazy::Seq(range), Lazy::Seq(other_range)) => compare(range, other_range),
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

// TLC's error for two values of kinds it can't compare, worded by the class of the left operand.
// A set compares as `toSetEnum` enumerates it.
fn incomparable<T>(left: &Value, right: &Value, is_equality: bool) -> Evaluated<T> {
    let reason = if is_equality {
        "equality of values TLC can't compare"
    } else {
        "values TLC can't compare"
    };
    let (subject, other) = match left {
        Value::Int(_) => ("integer", "non-integer:"),
        Value::Bool(_) => ("boolean", "non-boolean:"),
        Value::Str(_) => ("string", "non-string:"),
        _ if left.is_set() => ("the set", "the value:"),
        _ => return fail(reason),
    };
    let verb = match left {
        Value::Bool(_) if is_equality => "compare equality of",
        _ if is_equality => "check equality of",
        _ => "compare",
    };
    let shown = match left {
        Value::Interval(..) | Value::Lazy(_) => format_pretty(&Value::Set(elements(left)?)),
        _ => format_pretty(left),
    };
    fail_runtime(
        reason,
        format!(
            "Attempted to {verb} {subject} {shown} with {other}\n{}",
            format_pretty(right)
        ),
    )
}

/// A set of elements in any order and with duplicates, sorted into TLC's order.
pub fn set_of(mut elements: Vec<Value>) -> Evaluated<Value> {
    let mut failure = None;
    elements.sort_by(|left, right| {
        compare(left, right).unwrap_or_else(|error| {
            failure.get_or_insert(error);
            Ordering::Equal
        })
    });
    if let Some(error) = failure {
        return Err(error);
    }
    let mut distinct: Vec<Value> = Vec::with_capacity(elements.len());
    for element in elements {
        if let Some(last) = distinct.last()
            && compare(last, &element)? == Ordering::Equal
        {
            continue;
        }
        distinct.push(element);
    }
    Ok(Value::Set(Rc::new(distinct)))
}

/// Where TLC fails to normalize a set enumeration: the first comparison that fails as
/// `ValueVec.sort` inserts each element, in the order written, into those it sorted before it.
pub fn normalize_failure(elements: &[Value]) -> Option<EvalError> {
    let mut sorted: Vec<&Value> = Vec::with_capacity(elements.len());
    for element in elements {
        let (mut low, mut high) = (0, sorted.len());
        let mut is_duplicate = false;
        while low < high {
            let middle = low + (high - low) / 2;
            match compare(element, sorted[middle]) {
                Err(error) => return Some(error),
                Ok(Ordering::Equal) => {
                    is_duplicate = true;
                    break;
                }
                Ok(Ordering::Less) => high = middle,
                Ok(Ordering::Greater) => low = middle + 1,
            }
        }
        if !is_duplicate {
            sorted.insert(low, element);
        }
    }
    None
}

/// The position of a key in a function's domain, by binary search in TLC's order.
pub fn find_key(function: &Function, key: &Value) -> Evaluated<Option<usize>> {
    let (mut low, mut high) = (0, function.domain.len());
    while low < high {
        let middle = low + (high - low) / 2;
        match compare(key, &function.domain[middle])? {
            Ordering::Equal => return Ok(Some(middle)),
            Ordering::Less => high = middle,
            Ordering::Greater => low = middle + 1,
        }
    }
    Ok(None)
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
            if function.class.get() == Class::Lambda {
                function.class.set(Class::Plain);
            }
            function.domain.iter().for_each(settle);
            function.range.iter().for_each(settle);
        }
        // A lazy set enumerates into its parts' values, so fingerprinting it settles them.
        Value::Lazy(lazy) => match &**lazy {
            Lazy::Subset(base) | Lazy::Seq(base) => settle(base),
            Lazy::FunctionSet(domain, range) => {
                settle(domain);
                settle(range);
            }
            Lazy::RecordSet(fields, _) => fields.iter().for_each(|(_, set)| settle(set)),
            Lazy::Product(factors) => factors.iter().for_each(settle),
            Lazy::Cap(left, right) | Lazy::Cup(left, right) | Lazy::Diff(left, right) => {
                settle(left);
                settle(right);
            }
            Lazy::Nat | Lazy::Int | Lazy::Real | Lazy::Strings => {}
        },
        _ => {}
    }
}

/// Whether a value is the one an id of the store holds, by a walk that reads the store only.
pub fn matches(store: &Store, id: u32, value: &Value) -> bool {
    let kind = store.kind_of(id);
    match value {
        Value::Bool(boolean) => kind == KIND_BOOL && (id == TRUE) == *boolean,
        Value::Int(int) => kind == KIND_INT && store.int_of(id) == *int,
        Value::Str(text) => kind == KIND_STRING && *store.text_of(id) == *text.units,
        Value::Model(text) => kind == KIND_MODEL && *store.text_of(id) == *text.units,
        Value::Lazy(lazy) if matches!(**lazy, Lazy::Nat | Lazy::Int | Lazy::Strings) => {
            kind == KIND_INFINITE_SET
                && store.infinite_name_of(id)
                    == match **lazy {
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
/// of strings as a record.
pub fn from_store(store: &Store, id: u32) -> Value {
    let text = || {
        Rc::new(Text {
            units: store.text_of(id).into(),
            rank: store.text_rank_of(id),
        })
    };
    let size = store.size_of(id);
    match store.kind_of(id) {
        KIND_BOOL => Value::Bool(id == TRUE),
        KIND_INT => Value::Int(store.int_of(id)),
        KIND_STRING => Value::Str(text()),
        KIND_MODEL => Value::Model(text()),
        KIND_INFINITE_SET => Value::Lazy(Rc::new(match store.infinite_name_of(id) {
            NAT => Lazy::Nat,
            INT => Lazy::Int,
            _ => Lazy::Strings,
        })),
        KIND_SET => Value::Set(Rc::new(
            (0..size)
                .map(|index| from_store(store, store.element_at(id, index)))
                .collect(),
        )),
        kind => {
            let range = (0..size)
                .map(|index| from_store(store, store.get_range_value(id, index)))
                .collect();
            if kind == KIND_TUPLE {
                return Value::tuple(range);
            }
            let domain: Vec<Value> = (0..size)
                .filter_map(|index| store.peek_key(id, index))
                .map(|key| from_store(store, key))
                .collect();
            let class = if store.is_record(id) {
                Class::Record
            } else {
                Class::Plain
            };
            Value::function(domain, range, class)
        }
    }
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
        Value::Set(elements) => set_of(
            elements
                .iter()
                .map(|element| permute(element, permutation))
                .collect::<Evaluated<_>>()?,
        )?,
        Value::Function(function) if function.interval.is_some() => {
            Value::Function(Rc::new(Function {
                domain: function.domain.clone(),
                range: function
                    .range
                    .iter()
                    .map(|value| permute(value, permutation))
                    .collect::<Evaluated<_>>()?,
                class: function.class.clone(),
                written: RefCell::new(None),
                interval: function.interval,
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
            sorted_function(keys, values, function.class.get())?
        }
        Value::Lazy(_) => return fail("permuting a lazy set"),
        _ => value.clone(),
    })
}
