//! The evaluator's values: trees that keep what TLC's `Value` classes keep and the store forgets,
//! as the TypeScript `Value` of `values.ts` does: a record's written order until TLC sorts it, the
//! function classes, intervals, and the lazy sets TLC keeps. Values are ordered as the store
//! orders them, rule for rule, so a set's elements are in TLC's order and a value matches the
//! store's id of it ([`matches`]).

use std::cell::{Cell, RefCell};
use std::cmp::Ordering;
use std::rc::Rc;

use tla_values::Store;
use tla_values::store::{KIND_BOOL, KIND_INT, KIND_MODEL, KIND_SET, KIND_STRING, KIND_TUPLE, TRUE};

/// Why an evaluation failed, as TLC would have, or where the evaluator can't follow it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EvalError(pub String);

pub type Evaluated<T> = Result<T, EvalError>;

pub fn fail<T>(reason: impl Into<String>) -> Evaluated<T> {
    Err(EvalError(reason.into()))
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
}

#[derive(Clone, Debug)]
pub enum Value {
    Bool(bool),
    Int(i32),
    Str(Rc<Text>),
    Model(Rc<Text>),
    /// A set enumeration, its elements distinct and in TLC's order.
    Set(Rc<Vec<Value>>),
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

fn check_model_types(left: &Text, right: &Text) -> Evaluated<()> {
    let (left_type, right_type) = (left.model_type(), right.model_type());
    if left_type != 0 && right_type != 0 && left_type != right_type {
        return fail("differently typed model values");
    }
    Ok(())
}

/// The elements of a set TLC can enumerate, in TLC's order.
pub fn elements(value: &Value) -> Evaluated<Rc<Vec<Value>>> {
    match value {
        Value::Set(elements) => Ok(Rc::clone(elements)),
        Value::Interval(low, high) => Ok(Rc::new((*low..=*high).map(Value::Int).collect())),
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
    match (left, right) {
        (Value::Int(left), Value::Int(right)) => Ok(left.cmp(right)),
        (Value::Bool(left), Value::Bool(right)) => Ok(left.cmp(right)),
        (Value::Str(left), Value::Str(right)) => Ok(compare_texts(left, right)),
        (Value::Model(left), Value::Model(right)) => {
            check_model_types(left, right)?;
            Ok(compare_texts(left, right))
        }
        (Value::Model(model), _) => {
            if model.model_type() == 0 {
                Ok(Ordering::Less)
            } else {
                fail("typed model value")
            }
        }
        (_, Value::Model(model)) => {
            if model.model_type() == 0 {
                Ok(Ordering::Greater)
            } else {
                fail("typed model value")
            }
        }
        (Value::Function(left), Value::Function(right)) => compare_functions(left, right),
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
        _ => fail("values TLC can't compare"),
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
    match (left, right) {
        (Value::Int(left), Value::Int(right)) => Ok(left == right),
        (Value::Bool(left), Value::Bool(right)) => Ok(left == right),
        (Value::Str(left), Value::Str(right)) => Ok(left.units == right.units),
        (Value::Model(left), Value::Model(right)) => {
            check_model_types(left, right)?;
            Ok(left.units == right.units)
        }
        (Value::Model(model), _) | (_, Value::Model(model)) => {
            if model.model_type() == 0 {
                Ok(false)
            } else {
                fail("typed model value")
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
        _ => fail("equality of values TLC can't compare"),
    }
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
        Value::Set(elements) => elements.iter().for_each(settle),
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
        Value::Function(function) => {
            let size = function.domain.len();
            if kind == KIND_SET || kind <= KIND_MODEL || store.size_of(id) as usize != size {
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
