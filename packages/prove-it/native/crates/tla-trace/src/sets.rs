//! Sets: what TLC keeps lazily, enumerated and tested for membership, and the set operators.

use std::cmp::Ordering;
use std::rc::Rc;

use crate::print::{format_pretty, format_value};
use crate::value::{
    Class, Evaluated, Lazy, Value, compare, elements, equals, fail, fail_coded, fail_runtime,
    find_key, is_enumerable, mark_unnormalized, set_of, unnormalized,
};

/// How many elements the evaluator enumerates of a lazy set before it gives up, as the engine
/// refuses a power set past 2^20.
const MAXIMUM_ENUMERATION: usize = 1 << 20;

fn checked_size(size: usize, factor: usize) -> Evaluated<usize> {
    match size.checked_mul(factor) {
        Some(size) if size <= MAXIMUM_ENUMERATION => Ok(size),
        _ => fail("a set too large to enumerate"),
    }
}

/// The elements of a lazy set in TLC's order.
pub fn enumerate(lazy: &Lazy) -> Evaluated<Vec<Value>> {
    match lazy {
        Lazy::Nat | Lazy::Int | Lazy::Real | Lazy::Strings | Lazy::Seq(_) | Lazy::Any => {
            fail("enumerated an infinite set")
        }
        // `SubsetValue.toSetEnum` sizes the power set first, which an overridden base fails.
        Lazy::Subset(base) => {
            if matches!(base, Value::Lazy(inner) if inner.is_overridden()) {
                cardinality(base)?;
            }
            let base = elements(base)?;
            if base.len() > 20 {
                return fail("a power set too large to build");
            }
            let mut subsets = Vec::with_capacity(1 << base.len());
            for mask in 0u32..(1 << base.len()) {
                let subset = (0..base.len())
                    .filter(|&bit| mask & (1 << bit) != 0)
                    .map(|bit| base[bit].clone())
                    .collect();
                subsets.push(Value::Set(Rc::new(subset)));
            }
            sorted(subsets)
        }
        Lazy::FunctionSet(domain_set, range) => {
            // A domain its own parts empty holds nothing to enumerate, whatever they are, so the
            // set holds the empty function alone.
            if is_empty_by_argument(domain_set) {
                return Ok(vec![Value::function(Vec::new(), Vec::new(), Class::Plain)]);
            }
            if is_infinite(domain_set) {
                return fail_runtime(
                    "enumerated an infinite set",
                    format!(
                        "Attempted to enumerate a set of the form [D -> R],but the domain D:\n{}\ncannot be enumerated.",
                        format_value(domain_set)
                    ),
                );
            }
            let domain = elements(domain_set)?;
            if !domain.is_empty() && is_infinite(range) {
                return fail_runtime(
                    "enumerated an infinite set",
                    format!(
                        "Attempted to enumerate a set of the form [D -> R],but the range R:\n{}\ncannot be enumerated.",
                        format_value(range)
                    ),
                );
            }
            // Over an empty domain the set holds the empty function alone, whatever the range.
            let range = if domain.is_empty() {
                Rc::new(Vec::new())
            } else {
                elements(range)?
            };
            let tuples = product(&vec![Rc::clone(&range); domain.len()])?;
            // A function over an interval keeps it as its domain.
            let build = |values: Vec<Value>| match domain_set {
                Value::Interval(low, _) => Value::over_interval(*low, values, Class::Plain),
                _ => Value::function(domain.to_vec(), values, Class::Plain),
            };
            sorted(tuples.into_iter().map(build).collect())
        }
        Lazy::RecordSet(fields, _) => {
            let sets = component_elements(fields.iter().map(|(_, set)| set), |index, set| {
                format!(
                    "Attempted to enumerate a set of the form [l1 : v1, ..., ln : vn],\nbut can't enumerate the value of the `{}' field:\n{}",
                    String::from_utf16_lossy(&fields[index].0.units),
                    format_value(set)
                )
            })?;
            let domain: Vec<Value> = fields
                .iter()
                .map(|(name, _)| Value::Str(Rc::clone(name)))
                .collect();
            sorted(
                product(&sets)?
                    .into_iter()
                    .map(|values| Value::function(domain.clone(), values, Class::Record))
                    .collect(),
            )
        }
        Lazy::Product(factors) => {
            let sets = component_elements(factors.iter(), |index, factor| {
                format!(
                    "Attempted to enumerate a set of the form s1 \\X s2 ... \\X sn,\nbut can't enumerate s{index}:\n{}",
                    format_value(factor)
                )
            })?;
            sorted(product(&sets)?.into_iter().map(Value::tuple).collect())
        }
        // `SetCapValue.Enumerator`: the first operand TLC can enumerate, filtered by the other.
        Lazy::Cap(left, right) => {
            let (enumerated, tested) = if is_enumerable(left) {
                (left, right)
            } else if is_enumerable(right) {
                (right, left)
            } else {
                return fail_runtime(
                    "enumerated S \\cap T, neither of which TLC enumerates",
                    format!(
                        "Attempted to enumerate S \\cap T when neither S:\n{}\nnor T:\n{}\nis enumerable",
                        format_pretty(left),
                        format_pretty(right)
                    ),
                );
            };
            let mut kept = Vec::new();
            for element in elements(enumerated)?.iter() {
                if is_member(element, tested)? {
                    kept.push(element.clone());
                }
            }
            sorted(kept)
        }
        // `SetPredValue.Enumerator`: the set, which TLC must enumerate, filtered by the predicate,
        // which only the evaluator tests: a lazy filter is of a set it fails to enumerate.
        Lazy::Filter(base, _) => {
            if !is_enumerable(base) {
                return fail_runtime(
                    "enumerated a filter of a set TLC doesn't enumerate",
                    format!(
                        "Attempted to enumerate {{ x \\in S : p(x) }} when S:\n{}\nis not enumerable",
                        format_pretty(base)
                    ),
                );
            }
            elements(base)?;
            fail("enumerated a lazy filter")
        }
        // `UnionValue.Enumerator`: each element of the set, the first of which TLC must enumerate.
        Lazy::Union(sets) => {
            if !is_enumerable(sets) {
                return fail("enumerated the union of a set TLC doesn't enumerate");
            }
            let mut all = Vec::new();
            for (index, inner) in elements(sets)?.iter().enumerate() {
                if !is_enumerable(inner) {
                    if index > 0 {
                        return fail("enumerated a union with a later set TLC doesn't enumerate");
                    }
                    return fail_runtime(
                        "enumerated a union with a set TLC doesn't enumerate",
                        "Attempted to enumerate UNION(s), but some element of s is nonenumerable."
                            .into(),
                    );
                }
                all.extend(elements(inner)?.iter().cloned());
            }
            sorted(all)
        }
        // `SetCupValue.Enumerator`: both operands, which TLC must both enumerate.
        Lazy::Cup(left, right) => {
            if !is_enumerable(left) || !is_enumerable(right) {
                return fail_runtime(
                    "enumerated S \\cup T, not both of which TLC enumerates",
                    format!(
                        "Attempted to enumerate S \\cup T when S:\n{}\nand T:\n{}\nare not both enumerable",
                        format_pretty(left),
                        format_pretty(right)
                    ),
                );
            }
            let mut all = elements(left)?.to_vec();
            all.extend(elements(right)?.iter().cloned());
            sorted(all)
        }
        // `SetDiffValue.Enumerator`: the first operand, filtered by the second.
        Lazy::Diff(left, right) => {
            if !is_enumerable(left) {
                return fail_runtime(
                    "enumerated S \\ T, whose S TLC doesn't enumerate",
                    format!(
                        "Attempted to enumerate S \\ T when S:\n{}\nis not enumerable.",
                        format_pretty(left)
                    ),
                );
            }
            let mut kept = Vec::new();
            for element in elements(left)?.iter() {
                if !is_member(element, right)? {
                    kept.push(element.clone());
                }
            }
            sorted(kept)
        }
    }
}

// The sets TLC overrides with Java classes it can't enumerate: Nat, Int, Real and STRING.
fn is_infinite(set: &Value) -> bool {
    matches!(set, Value::Lazy(lazy) if matches!(**lazy, Lazy::Nat | Lazy::Int | Lazy::Real | Lazy::Strings))
}

// The elements of each set a set of records or tuples combines, as `getComponentElements` reads
// them: TLC's message for the first it can't enumerate, and no combinations past an empty one.
fn component_elements<'a>(
    sets: impl Iterator<Item = &'a Value>,
    describe: impl Fn(usize, &Value) -> String,
) -> Evaluated<Vec<Rc<Vec<Value>>>> {
    // TLC finds the set empty by a component that is, before it enumerates any
    // (`SetOfRcdsValue.elements`, `SetOfTuplesValue.elements`).
    let sets: Vec<&Value> = sets.collect();
    if sets.iter().any(|set| is_empty(set)) {
        return Ok(vec![Rc::new(Vec::new())]);
    }
    let mut lists = Vec::new();
    for (index, set) in sets.into_iter().enumerate() {
        if is_infinite(set) {
            return fail_runtime("enumerated an infinite set", describe(index, set));
        }
        let elements = elements(set)?;
        if elements.is_empty() {
            return Ok(vec![elements]);
        }
        lists.push(elements);
    }
    Ok(lists)
}

fn sorted(values: Vec<Value>) -> Evaluated<Vec<Value>> {
    match set_of(values)? {
        Value::Set(elements) => Ok(Rc::unwrap_or_clone(elements)),
        _ => unreachable!("set_of makes a set"),
    }
}

// Every choice of one element from each set, the last set varying fastest.
fn product(sets: &[Rc<Vec<Value>>]) -> Evaluated<Vec<Vec<Value>>> {
    let mut size = 1;
    for set in sets {
        size = checked_size(size, set.len())?;
    }
    let mut choices = Vec::with_capacity(size);
    let mut positions = vec![0; sets.len()];
    if sets.iter().any(|set| set.is_empty()) {
        return Ok(choices);
    }
    loop {
        choices.push(
            positions
                .iter()
                .zip(sets)
                .map(|(&position, set)| set[position].clone())
                .collect(),
        );
        let mut level = sets.len();
        loop {
            if level == 0 {
                return Ok(choices);
            }
            level -= 1;
            positions[level] += 1;
            if positions[level] < sets[level].len() {
                break;
            }
            positions[level] = 0;
        }
    }
}

/// TLC's `member`: whether a value is in a set, failing where TLC can't tell.
// TLC's `EC.TLC_MODULE_CHECK_MEMBER_OF`, for a value that can't be an element of a set of the
// standard modules.
fn mistyped(value: &Value, set: &str) -> Evaluated<bool> {
    fail_coded(
        format!("a mistyped membership in {set}"),
        2158,
        format!(
            "Attempted to check if the value:\n{}\nis an element of {set}.",
            format_value(value)
        ),
    )
}

/// The sets nested in `set` whose own membership tests a failing `is_member(value, set)` was in,
/// outermost first: the values whose `member` TLC's failure passes through after `set`'s. `None`
/// where the failure isn't followed to the set whose own test fails.
pub fn failing_sets(value: &Value, set: &Value) -> Option<Vec<Value>> {
    let Value::Lazy(lazy) = set else {
        return Some(Vec::new());
    };
    // Each element a nested set tests, in the order `is_member` tests them.
    let tested: Vec<(&Value, &Value)> = match (&**lazy, value) {
        (Lazy::FunctionSet(domain, range), Value::Function(function)) => {
            equals(&Value::Set(Rc::new(function.domain.clone())), domain).ok()?;
            function
                .range
                .iter()
                .map(|element| (element, range))
                .collect()
        }
        (Lazy::RecordSet(fields, _), Value::Function(function)) => fields
            .iter()
            .map(|(name, set)| {
                let position = find_key(function, &Value::Str(Rc::clone(name))).ok()??;
                Some((&function.range[position], set))
            })
            .collect::<Option<_>>()?,
        (Lazy::Product(factors), _) => match as_tuple(value) {
            Some(tuple) if tuple.len() == factors.len() => tuple.iter().zip(factors).collect(),
            _ => return None,
        },
        (Lazy::Seq(base), _) => as_tuple(value)?
            .iter()
            .map(|element| (element, base))
            .collect(),
        // The failure is in the set's own test: a mistyped value.
        (
            Lazy::Nat | Lazy::Int | Lazy::Strings | Lazy::FunctionSet(..) | Lazy::RecordSet(..),
            _,
        ) => return Some(Vec::new()),
        _ => return None,
    };
    for (element, nested) in tested {
        match is_member(element, nested) {
            Ok(true) => {}
            Ok(false) => return None,
            Err(_) => {
                let mut sets = vec![nested.clone()];
                sets.extend(failing_sets(element, nested)?);
                return Some(sets);
            }
        }
    }
    None
}

pub fn is_member(value: &Value, set: &Value) -> Evaluated<bool> {
    // TLC tests a set it holds unnormalized element by element, as it built it, asking each
    // element whether it equals the value (`ValueVec.search`).
    if let Some(written) = unnormalized(set) {
        for element in &written {
            if equals(element, value)? {
                return Ok(true);
            }
        }
        return Ok(false);
    }
    match set {
        Value::Set(elements) => {
            let (mut low, mut high) = (0, elements.len());
            while low < high {
                let middle = low + (high - low) / 2;
                match compare(value, &elements[middle])? {
                    Ordering::Equal => return Ok(true),
                    Ordering::Less => high = middle,
                    Ordering::Greater => low = middle + 1,
                }
            }
            Ok(false)
        }
        // An untyped model value is in no interval or lazy set: TLC's `member` of each hands it
        // to `ModelValue.modelValueMember`, which says false.
        Value::Interval(..) | Value::Lazy(_) if matches!(value, Value::Model(model) if model.model_type() == 0) => {
            Ok(false)
        }
        // A typed one fails there, for the sets whose `member` hands it to it.
        Value::Lazy(lazy)
            if matches!(value, Value::Model(_))
                && matches!(
                    **lazy,
                    Lazy::Nat
                        | Lazy::Int
                        | Lazy::Strings
                        | Lazy::Seq(_)
                        | Lazy::FunctionSet(..)
                        | Lazy::RecordSet(..)
                        | Lazy::Product(_)
                ) =>
        {
            fail_runtime(
                "a typed model value's membership",
                format!(
                    "Attempted to check if the typed model value {} is an element of\n{}",
                    format_pretty(value),
                    format_pretty(set)
                ),
            )
        }
        Value::Interval(low, high) => match value {
            Value::Int(int) => Ok(low <= int && int <= high),
            _ if low > high => Ok(false),
            _ => fail_runtime(
                "a mistyped membership in an interval",
                format!(
                    "Attempted to check if the value:\n{}\nis in the integer interval {}",
                    format_pretty(value),
                    format_pretty(set)
                ),
            ),
        },
        Value::Lazy(lazy) => match &**lazy {
            Lazy::Nat => match value {
                Value::Int(int) => Ok(*int >= 0),
                _ => mistyped(value, "Nat"),
            },
            Lazy::Int => match value {
                Value::Int(_) => Ok(true),
                _ => mistyped(value, "Int"),
            },
            Lazy::Real => fail("a membership in Real"),
            // `AnySet.member`.
            Lazy::Any => Ok(true),
            Lazy::Strings => match value {
                Value::Str(_) => Ok(true),
                _ => mistyped(value, "STRING"),
            },
            // `SubsetValue.member`.
            Lazy::Subset(base) => {
                if !is_enumerable(value) {
                    return fail_runtime(
                        "a membership in SUBSET of a non-enumerable value",
                        format!(
                            "Attempted to check if the non-enumerable value\n{}\nis element of\n{}",
                            format_pretty(value),
                            format_pretty(set)
                        ),
                    );
                }
                for element in elements(value)?.iter() {
                    if !is_member(element, base)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Lazy::FunctionSet(domain, range) => {
                if let Value::Lambda(lambda) = value {
                    return crate::value::lambda_as_function(lambda);
                }
                let Value::Function(function) = value else {
                    return fail_runtime(
                        "a mistyped membership in a set of functions",
                        format!(
                            "Attempted to check if \n{}\nwhich is not a TLC function value, is in the set of functions:\n{}",
                            format_value(value),
                            format_pretty(set)
                        ),
                    );
                };
                if !equals(&Value::Set(Rc::new(function.domain.clone())), domain)? {
                    return Ok(false);
                }
                for element in &function.range {
                    if !is_member(element, range)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            // `SetOfRcdsValue.member`: a value `toRcd` makes no record of fails.
            Lazy::RecordSet(fields, _) => {
                let Value::Function(function) = value else {
                    return non_record(value, set);
                };
                let is_record = match function.class.get() {
                    Class::Tuple => function.domain.is_empty(),
                    _ => function
                        .domain
                        .iter()
                        .all(|key| matches!(key, Value::Str(_))),
                };
                if !is_record {
                    return non_record(value, set);
                }
                if function.domain.len() != fields.len() {
                    return Ok(false);
                }
                for (name, set) in fields {
                    match find_key(function, &Value::Str(Rc::clone(name)))? {
                        Some(position) => {
                            if !is_member(&function.range[position], set)? {
                                return Ok(false);
                            }
                        }
                        None => return Ok(false),
                    }
                }
                Ok(true)
            }
            // `SetOfTuplesValue.member`: a function `toTuple` makes no tuple of is in none, but a
            // value that isn't a function, or a function over a key that isn't an integer, fails.
            Lazy::Product(factors) => {
                let Some(tuple) = as_tuple(value) else {
                    let Value::Function(function) = value else {
                        return non_tuple(value, set);
                    };
                    if function.interval.is_none()
                        && !function
                            .domain
                            .iter()
                            .all(|key| matches!(key, Value::Int(_)))
                    {
                        return non_tuple(value, set);
                    }
                    return Ok(false);
                };
                if tuple.len() != factors.len() {
                    return Ok(false);
                }
                for (element, factor) in tuple.iter().zip(factors) {
                    if !is_member(element, factor)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            // `Sequences.member`.
            Lazy::Seq(base) => {
                let Some(tuple) = as_tuple(value) else {
                    return mistyped(value, &format_pretty(set));
                };
                for element in tuple {
                    if !is_member(element, base)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Lazy::Filter(..) => fail("a lazy filter's membership outside the evaluator"),
            // `UnionValue.member`: in an element of an enumerable set of sets.
            Lazy::Union(sets) => {
                if !is_enumerable(sets) {
                    return fail("a membership in the union of a set TLC doesn't enumerate");
                }
                for inner in elements(sets)?.iter() {
                    if is_member(value, inner)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
            Lazy::Cap(left, right) => Ok(is_member(value, left)? && is_member(value, right)?),
            Lazy::Cup(left, right) => Ok(is_member(value, left)? || is_member(value, right)?),
            Lazy::Diff(left, right) => Ok(is_member(value, left)? && !is_member(value, right)?),
        },
        // The `member` of each class of value that isn't a set.
        _ => {
            let kind = match set {
                Value::Bool(_) => "boolean",
                Value::Int(_) => "integer",
                Value::Str(_) => "string",
                Value::Model(_) => "model value",
                Value::Function(function) if function.class.get() == Class::Tuple => {
                    return fail_runtime(
                        "a membership in a tuple",
                        "Attempted to check set membership in a tuple value.".into(),
                    );
                }
                Value::Function(function) if function.class.get() == Class::Record => {
                    return fail_runtime(
                        "a membership in a record",
                        format!(
                            "Attempted to check if element:\n{}\nis in the record:\n{}",
                            format_pretty(value),
                            format_pretty(set)
                        ),
                    );
                }
                Value::Function(_) | Value::Lambda(_) => "function",
                _ => {
                    return fail(format!(
                        "a membership in a {}, which isn't a set",
                        set.kind_name()
                    ));
                }
            };
            fail_runtime(
                format!("a membership in a {kind}"),
                format!(
                    "Attempted to check if the value:\n{}\nis an element of the {kind} {}",
                    format_pretty(value),
                    format_pretty(set)
                ),
            )
        }
    }
}

fn non_record(value: &Value, set: &Value) -> Evaluated<bool> {
    if matches!(value, Value::Model(_)) {
        return fail("a model value's membership in a set of records");
    }
    fail_runtime(
        "a mistyped membership in a set of records",
        format!(
            "Attempted to check if non-record\n{}\nis in the set of records:\n{}",
            format_value(value),
            format_pretty(set)
        ),
    )
}

fn non_tuple(value: &Value, set: &Value) -> Evaluated<bool> {
    if matches!(value, Value::Model(_)) {
        return fail("a model value's membership in a set of tuples");
    }
    fail_runtime(
        "a mistyped membership in a set of tuples",
        format!(
            "Attempted to check if non-tuple\n{}\nis in the set of tuples:\n{}",
            format_pretty(value),
            format_pretty(set)
        ),
    )
}

/// The elements of a function whose domain is 1..n, in order.
pub fn as_tuple(value: &Value) -> Option<&[Value]> {
    let Value::Function(function) = value else {
        return None;
    };
    let is_tuple = function
        .domain
        .iter()
        .enumerate()
        .all(|(index, key)| matches!(key, Value::Int(int) if *int == index as i32 + 1));
    is_tuple.then_some(&function.range[..])
}

// TLC's reducible sets, a set enumeration or an interval, which combine with another set element by
// element.
fn is_reducible(value: &Value) -> bool {
    matches!(value, Value::Set(_) | Value::Interval(..))
}

fn is_empty_reducible(value: &Value) -> bool {
    match value {
        Value::Set(elements) => elements.is_empty(),
        Value::Interval(low, high) => low > high,
        _ => false,
    }
}

/// `\cup`. TLC keeps the other operand as it is when one is an empty set enumeration or interval:
/// the right one after an empty left one, and a lazy left one before an empty right one, as
/// `combineReducible` does; otherwise it enumerates the union.
pub fn union(left: &Value, right: &Value) -> Evaluated<Value> {
    if is_empty_reducible(left) {
        return Ok(right.clone());
    }
    if is_empty_reducible(right) && !is_reducible(left) {
        return Ok(left.clone());
    }
    // `Tool`'s OPCODE_cup: a reducible operand's `cup`, the other's lazy union otherwise.
    match (is_reducible(left), is_reducible(right)) {
        (true, true) => {
            let mut all = elements(left)?.to_vec();
            all.extend(elements(right)?.iter().cloned());
            set_of(all)
        }
        (true, false) | (false, false) => Ok(lazy(Lazy::Cup(left.clone(), right.clone()))),
        (false, true) => Ok(lazy(Lazy::Cup(right.clone(), left.clone()))),
    }
}

fn lazy(lazy: Lazy) -> Value {
    Value::Lazy(Rc::new(lazy))
}

/// `\cap` (`Tool`'s OPCODE_cap): a reducible operand's elements in the other, the left's first,
/// and a lazy intersection where neither is reducible.
pub fn intersection(left: &Value, right: &Value) -> Evaluated<Value> {
    let (enumerated, tested) = match (is_reducible(left), is_reducible(right)) {
        (true, _) => (left, right),
        (false, true) => (right, left),
        (false, false) => return Ok(lazy(Lazy::Cap(left.clone(), right.clone()))),
    };
    filter(enumerated, |element| is_member(element, tested))
}

/// `\` (`Tool`'s OPCODE_setdiff): a reducible left operand's elements not in the right, and a
/// lazy difference otherwise.
pub fn difference(left: &Value, right: &Value) -> Evaluated<Value> {
    if !is_reducible(left) {
        return Ok(lazy(Lazy::Diff(left.clone(), right.clone())));
    }
    filter(left, |element| Ok(!is_member(element, right)?))
}

// The elements of a set that `keep` keeps. TLC's `cap` and `diff` of a set enumeration test its
// elements as it holds them and keep its normalization, so a set TLC holds unnormalized gives one it
// holds unnormalized.
fn filter(left: &Value, keep: impl Fn(&Value) -> Evaluated<bool>) -> Evaluated<Value> {
    let written = unnormalized(left);
    let held = match &written {
        Some(written) => written.clone(),
        None => elements(left)?.to_vec(),
    };
    let mut kept = Vec::new();
    for element in held {
        if keep(&element)? {
            kept.push(element);
        }
    }
    if written.is_none() {
        return Ok(Value::Set(Rc::new(kept)));
    }
    let set = set_of(kept.clone())?;
    mark_unnormalized(&set, kept);
    Ok(set)
}

/// Whether a set of functions, records or tuples is empty by an empty argument, which TLC decides
/// without enumerating the others (`isEmpty` of `SetOfFcnsValue`, `SetOfRcdsValue` and
/// `SetOfTuplesValue`): `[S -> T]` where S isn't empty and T is, and a set of records or tuples one
/// of whose sets is.
pub(crate) fn is_empty_by_argument(set: &Value) -> bool {
    let is_empty = |value: &Value| match value {
        Value::Set(elements) => elements.is_empty(),
        Value::Interval(low, high) => low > high,
        Value::Lazy(_) => is_empty_by_argument(value),
        _ => false,
    };
    let is_nonempty = |value: &Value| match value {
        Value::Set(elements) => !elements.is_empty(),
        Value::Interval(low, high) => low <= high,
        // A set of functions, records or tuples is nonempty unless its parts empty it
        // (`SetOfFcnsValue.isEmpty`), and SUBSET S and Seq(S) always are.
        Value::Lazy(lazy) => match **lazy {
            Lazy::Nat | Lazy::Int | Lazy::Real | Lazy::Strings | Lazy::Subset(_) | Lazy::Seq(_) => {
                true
            }
            Lazy::Any => false,
            Lazy::FunctionSet(..) | Lazy::RecordSet(..) | Lazy::Product(_) => {
                !is_empty_by_argument(value)
            }
            // TLC can't tell without enumerating it.
            Lazy::Cap(..) | Lazy::Cup(..) | Lazy::Diff(..) | Lazy::Union(_) | Lazy::Filter(..) => {
                false
            }
        },
        _ => false,
    };
    let Value::Lazy(lazy) = set else {
        return false;
    };
    match &**lazy {
        Lazy::FunctionSet(domain, range) => is_nonempty(domain) && is_empty(range),
        Lazy::RecordSet(fields, _) => fields.iter().any(|(_, set)| is_empty(set)),
        Lazy::Product(factors) => factors.iter().any(is_empty),
        _ => false,
    }
}

/// The number of elements of a set TLC can count (`size` of its values).
pub fn cardinality(set: &Value) -> Evaluated<usize> {
    match set {
        Value::Interval(low, high) => crate::value::interval_size(*low, *high),
        Value::Lazy(lazy) => match &**lazy {
            Lazy::FunctionSet(domain, range) => function_set_size(set, domain, range),
            // `UserValue.size`.
            lazy if lazy.is_overridden() => fail_runtime(
                "sized a set TLC doesn't enumerate",
                format!(
                    "Attempted to compute the number of elements in the overridden value {}.",
                    format_pretty(set)
                ),
            ),
            // `SubsetValue.size`: 2^|S|, past an int an overflow.
            Lazy::Subset(base) => {
                let size = cardinality(base)?;
                if size >= 31 {
                    return Err(crate::value::EvalError {
                        reason: "a power set too large to count".into(),
                        message: Some(crate::value::TlcMessage {
                            text: format!(
                                "Overflow when computing the number of elements in:\n{}",
                                format_pretty(set)
                            ),
                            code: Some(OVERFLOW),
                            is_eval_exception: false,
                        }),
                    });
                }
                Ok(1 << size)
            }
            // `SetOfRcdsValue.size` and `SetOfTuplesValue.size`: the product of the parts' sizes.
            Lazy::RecordSet(fields, _) => {
                parts_size(set, fields.iter().map(|(_, part)| part), true)
            }
            Lazy::Product(factors) => parts_size(set, factors.iter(), false),
            _ => Ok(elements(set)?.len()),
        },
        _ => Ok(elements(set)?.len()),
    }
}

/// `EC.TLC_MODULE_OVERFLOW`.
const OVERFLOW: u32 = 2178;

fn parts_size<'v>(
    set: &Value,
    parts: impl Iterator<Item = &'v Value>,
    is_record: bool,
) -> Evaluated<usize> {
    if crate::eval::is_empty(set)? {
        return Ok(0);
    }
    let mut size: i64 = 1;
    for part in parts {
        size = size.saturating_mul(cardinality(part)? as i64);
        if size > i64::from(i32::MAX) {
            let (text, code) = if is_record {
                (
                    format!(
                        "Overflow when computing the number of elements in:\n{}",
                        format_pretty(set)
                    ),
                    Some(OVERFLOW),
                )
            } else {
                (
                    format!(
                        "Overflow when computing the number of elements in {}",
                        format_pretty(set)
                    ),
                    None,
                )
            };
            return Err(crate::value::EvalError {
                reason: "a set too large to count".into(),
                message: Some(crate::value::TlcMessage {
                    text,
                    code,
                    is_eval_exception: false,
                }),
            });
        }
    }
    Ok(size as usize)
}

// Whether a set is empty, as TLC's `isEmpty` finds without enumerating it: an enumeration or an
// interval by itself, a set of functions, records or tuples by its parts.
fn is_empty(set: &Value) -> bool {
    match set {
        Value::Set(elements) => elements.is_empty(),
        Value::Interval(low, high) => low > high,
        _ => is_empty_by_argument(set),
    }
}

// `SetOfFcnsValue.size`: one function over an empty domain, none into an empty range, one into a
// range of one element whatever the domain, and otherwise the range's size to the power of the
// domain's, which fails where it overflows an int.
fn function_set_size(set: &Value, domain: &Value, range: &Value) -> Evaluated<usize> {
    if crate::eval::is_empty(domain)? {
        return Ok(1);
    }
    if crate::eval::is_empty(range)? {
        return Ok(0);
    }
    let range = cardinality(range)?;
    if range == 1 {
        return Ok(1);
    }
    let domain = cardinality(domain)?;
    let mut count: i64 = 1;
    for _ in 0..domain {
        count = count.saturating_mul(range as i64);
        if count > i64::from(i32::MAX) {
            return fail_runtime(
                "a function set too large to count",
                format!(
                    "Overflow when computing the number of elements in:\n{}",
                    format_pretty(set)
                ),
            );
        }
    }
    Ok(count as usize)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::Text;

    fn message(result: Evaluated<bool>) -> String {
        result
            .expect_err("a failure")
            .message
            .expect("TLC's message")
            .text
    }

    #[test]
    fn keeps_a_set_operation_lazy_as_tlc_does() {
        let nat = || Value::Lazy(Rc::new(Lazy::Nat));
        let set =
            |ints: &[i32]| Value::Set(Rc::new(ints.iter().map(|&int| Value::Int(int)).collect()));
        // A reducible operand is filtered by the other, whichever side it is on.
        let cap = intersection(&nat(), &set(&[-1, 1, 2])).expect("an intersection");
        assert!(equals(&cap, &set(&[1, 2])).expect("comparable"));
        // \cup with an enumerable operand and Nat stays lazy, which TLC tests for membership
        // but can't enumerate.
        let cup = union(&set(&[-1]), &nat()).expect("a union");
        assert!(is_member(&Value::Int(-1), &cup).expect("a member"));
        assert!(is_member(&Value::Int(7), &cup).expect("a member"));
        assert_eq!(
            message(elements(&cup).map(|_| true)),
            "Attempted to enumerate S \\cup T when S:\n{-1}\nand T:\nNat\nare not both enumerable"
        );
        let difference = difference(&nat(), &set(&[0])).expect("a difference");
        assert!(is_member(&Value::Int(1), &difference).expect("a member"));
        assert!(!is_member(&Value::Int(0), &difference).expect("a member"));
        assert_eq!(
            message(elements(&difference).map(|_| true)),
            "Attempted to enumerate S \\ T when S:\nNat\nis not enumerable."
        );
    }

    #[test]
    fn tests_a_lazy_union_and_any_as_tlc_does() {
        let union = Value::Lazy(Rc::new(Lazy::Union(Value::Set(Rc::new(vec![
            Value::Lazy(Rc::new(Lazy::Nat)),
        ])))));
        assert!(is_member(&Value::Int(1), &union).expect("a member"));
        assert!(!is_member(&Value::Int(-1), &union).expect("a member"));
        assert_eq!(
            message(elements(&union).map(|_| true)),
            "Attempted to enumerate UNION(s), but some element of s is nonenumerable."
        );
        let any = Value::Lazy(Rc::new(Lazy::Any));
        assert!(is_member(&Value::Int(1), &any).expect("a member"));
        assert_eq!(
            message(crate::eval::is_empty(&any)),
            "Shouldn't call isEmpty() on value ANY"
        );
    }

    #[test]
    fn compares_an_overridden_set_as_tlc_does() {
        let nat = || Value::Lazy(Rc::new(Lazy::Nat));
        let int = Value::Lazy(Rc::new(Lazy::Int));
        assert!(equals(&nat(), &nat()).expect("comparable"));
        assert_eq!(compare(&nat(), &int).expect("comparable"), Ordering::Less);
        assert_eq!(
            message(equals(&nat(), &Value::Set(Rc::new(vec![Value::Int(1)])))),
            "Attempted to compare overridden value Nat with non-overridden value:\n{1}"
        );
    }

    #[test]
    fn sizes_an_interval_as_tlc_does() {
        assert_eq!(
            cardinality(&Value::Interval(0, i32::MAX - 1)).expect("a size"),
            i32::MAX as usize
        );
        assert_eq!(
            message(cardinality(&Value::Interval(0, i32::MAX)).map(|_| true)),
            "Size of interval value exceeds the maximum representable size (32bits): 0..2147483647."
        );
    }

    #[test]
    fn counts_a_function_set_as_tlc_does() {
        let set = |domain, range| Value::Lazy(Rc::new(Lazy::FunctionSet(domain, range)));
        let count = cardinality(&set(Value::Interval(1, 3), Value::Interval(1, 4)));
        assert_eq!(count.expect("a count"), 64);
        let huge = cardinality(&set(Value::Interval(0, 2), Value::Interval(1, 2000)));
        assert_eq!(
            huge.expect_err("an overflow")
                .message
                .expect("TLC's message")
                .text,
            "Overflow when computing the number of elements in:\n[0..2 -> 1..2000]"
        );
        // An empty part decides before TLC asks anything of Nat, and a range of one element
        // makes one function whatever the domain.
        let nat = || Value::Lazy(Rc::new(Lazy::Nat));
        let count = |domain, range| cardinality(&set(domain, range)).expect("a count");
        assert_eq!(count(nat(), Value::empty_set()), 0);
        assert_eq!(count(Value::empty_set(), nat()), 1);
        assert_eq!(count(nat(), Value::Interval(1, 1)), 1);
        let large = Value::Lazy(Rc::new(Lazy::Subset(Value::Interval(1, 40))));
        assert_eq!(count(large, Value::Interval(1, 1)), 1);
        assert!(cardinality(&set(nat(), Value::Interval(1, 2))).is_err());
        // A set its parts empty enumerates to nothing, and an empty domain to one function.
        let emptied = set(nat(), Value::empty_set());
        assert!(elements(&emptied).expect("no elements").is_empty());
        let unit = set(emptied, Value::Interval(1, 2));
        assert_eq!(elements(&unit).expect("one function").len(), 1);
    }

    #[test]
    fn reports_a_non_integer_in_an_interval_as_tlc_does() {
        let empty = Value::Set(Rc::new(Vec::new()));
        assert_eq!(
            message(is_member(&empty, &Value::Interval(1, 4))),
            "Attempted to check if the value:\n{}\nis in the integer interval 1..4"
        );
        // An empty interval holds nothing, whatever is checked against it.
        assert!(!is_member(&empty, &Value::Interval(4, 1)).expect("no failure"));
        let string = Value::Str(Rc::new(Text {
            units: "a".encode_utf16().collect(),
            rank: 0,
        }));
        assert_eq!(
            message(equals(&Value::Int(1), &string)),
            "Attempted to check equality of integer 1 with non-integer:\n\"a\""
        );
        assert_eq!(
            message(compare(&Value::Interval(1, 2), &Value::Int(1)).map(|_| true)),
            "Attempted to compare the set {1, 2} with the value:\n1"
        );
    }
}

#[cfg(test)]
mod enumeration_tests {
    use super::*;
    use crate::value::Text;

    fn text(name: &str) -> Rc<Text> {
        Rc::new(Text {
            units: name.encode_utf16().collect(),
            rank: -1,
        })
    }

    fn message(lazy: Lazy) -> Option<String> {
        enumerate(&lazy)
            .err()
            .and_then(|error| error.message)
            .map(|message| message.text)
    }

    #[test]
    fn names_what_tlc_cant_enumerate_in_a_set_it_combines() {
        let int = Value::Lazy(Rc::new(Lazy::Int));
        // IOUtils's Serialize: CHOOSE r \in [exitValue : Int, stdout : STRING, ...] : TRUE.
        let records = Lazy::RecordSet(
            vec![
                (text("exitValue"), int.clone()),
                (text("stdout"), Value::Lazy(Rc::new(Lazy::Strings))),
            ],
            vec![0, 1],
        );
        assert_eq!(
            message(records).as_deref(),
            Some(
                "Attempted to enumerate a set of the form [l1 : v1, ..., ln : vn],\nbut can't enumerate the value of the `exitValue' field:\nInt"
            )
        );
        let functions = Lazy::FunctionSet(Value::Lazy(Rc::new(Lazy::Strings)), int.clone());
        assert_eq!(
            message(functions).as_deref(),
            Some(
                "Attempted to enumerate a set of the form [D -> R],but the domain D:\nSTRING\ncannot be enumerated."
            )
        );
        let product = Lazy::Product(vec![Value::Interval(1, 2), int]);
        assert_eq!(
            message(product).as_deref(),
            Some(
                "Attempted to enumerate a set of the form s1 \\X s2 ... \\X sn,\nbut can't enumerate s1:\nInt"
            )
        );
    }
}
