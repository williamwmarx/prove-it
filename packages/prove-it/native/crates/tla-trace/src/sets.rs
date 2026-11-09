//! Sets: what TLC keeps lazily, enumerated and tested for membership, and the set operators.

use std::cmp::Ordering;
use std::rc::Rc;

use crate::value::{
    Class, Evaluated, Lazy, Value, compare, elements, equals, fail, find_key, set_of,
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
        Lazy::Nat | Lazy::Int | Lazy::Real | Lazy::Strings | Lazy::Seq(_) => {
            fail("enumerated an infinite set")
        }
        Lazy::Subset(base) => {
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
            let domain = elements(domain_set)?;
            let range = elements(range)?;
            let tuples = product(&vec![Rc::clone(&range); domain.len()])?;
            // A function over an interval keeps it as its domain.
            let build = |values: Vec<Value>| match domain_set {
                Value::Interval(low, _) => Value::over_interval(*low, values, Class::Plain),
                _ => Value::function(domain.to_vec(), values, Class::Plain),
            };
            sorted(tuples.into_iter().map(build).collect())
        }
        Lazy::RecordSet(fields, _) => {
            let sets = fields
                .iter()
                .map(|(_, set)| elements(set))
                .collect::<Evaluated<Vec<_>>>()?;
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
            let sets = factors
                .iter()
                .map(elements)
                .collect::<Evaluated<Vec<_>>>()?;
            sorted(product(&sets)?.into_iter().map(Value::tuple).collect())
        }
    }
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
pub fn is_member(value: &Value, set: &Value) -> Evaluated<bool> {
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
        Value::Interval(low, high) => match value {
            Value::Int(int) => Ok(low <= int && int <= high),
            Value::Model(model) if model.model_type() == 0 => Ok(false),
            _ => fail("a mistyped membership in an interval"),
        },
        Value::Lazy(lazy) => match &**lazy {
            Lazy::Nat => match value {
                Value::Int(int) => Ok(*int >= 0),
                _ => fail("a mistyped membership in Nat"),
            },
            Lazy::Int => match value {
                Value::Int(_) => Ok(true),
                _ => fail("a mistyped membership in Int"),
            },
            Lazy::Real => fail("a membership in Real"),
            Lazy::Strings => match value {
                Value::Str(_) => Ok(true),
                Value::Model(model) if model.model_type() == 0 => Ok(false),
                _ => fail("a mistyped membership in STRING"),
            },
            Lazy::Subset(base) => {
                if !value.is_set() {
                    return fail("a membership in SUBSET of a non-set");
                }
                for element in elements(value)?.iter() {
                    if !is_member(element, base)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Lazy::FunctionSet(domain, range) => {
                let Value::Function(function) = value else {
                    return fail("a mistyped membership in a set of functions");
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
            Lazy::RecordSet(fields, _) => {
                let Value::Function(function) = value else {
                    return fail("a mistyped membership in a set of records");
                };
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
            Lazy::Product(factors) => {
                let Some(tuple) = as_tuple(value) else {
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
            Lazy::Seq(base) => {
                let Some(tuple) = as_tuple(value) else {
                    return Ok(false);
                };
                for element in tuple {
                    if !is_member(element, base)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
        },
        _ => fail(format!(
            "a membership in a {}, which isn't a set",
            set.kind_name()
        )),
    }
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
    let mut all = elements(left)?.to_vec();
    all.extend(elements(right)?.iter().cloned());
    set_of(all)
}

pub fn intersection(left: &Value, right: &Value) -> Evaluated<Value> {
    let mut kept = Vec::new();
    for element in elements(left)?.iter() {
        if is_member(element, right)? {
            kept.push(element.clone());
        }
    }
    Ok(Value::Set(Rc::new(kept)))
}

pub fn difference(left: &Value, right: &Value) -> Evaluated<Value> {
    let mut kept = Vec::new();
    for element in elements(left)?.iter() {
        if !is_member(element, right)? {
            kept.push(element.clone());
        }
    }
    Ok(Value::Set(Rc::new(kept)))
}

pub fn is_subset(left: &Value, right: &Value) -> Evaluated<bool> {
    for element in elements(left)?.iter() {
        if !is_member(element, right)? {
            return Ok(false);
        }
    }
    Ok(true)
}

/// The number of elements of a set TLC can count.
pub fn cardinality(set: &Value) -> Evaluated<usize> {
    match set {
        Value::Interval(low, high) => Ok((i64::from(*high) - i64::from(*low) + 1).max(0) as usize),
        _ => Ok(elements(set)?.len()),
    }
}
