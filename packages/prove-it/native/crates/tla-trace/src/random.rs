//! TLC!RandomElement and Randomization!RandomSubset over the evaluator's values, as TLC draws
//! them (`TLC.RandomElement`, `Enumerable.getRandomSubset`), from the draws `tla-values` shares
//! with the engine.

use std::rc::Rc;

use tla_values::random::{JavaRandom, get_large_subset_indices, get_subset_indices};

use crate::print::format_pretty;
use crate::value::{
    Class, Evaluated, Lazy, SetClass, Value, elements, fail, fail_coded, fail_runtime,
    is_enumerable, java_set_class, set_of, sorted_function,
};

// A set's elements in its normalized order (`toSetEnum` and `normalize`).
fn normalized(set: &Value) -> Evaluated<Rc<Vec<Value>>> {
    match set_of(elements(set)?.to_vec())? {
        Value::Set(elements) => Ok(Rc::clone(&elements.elements)),
        _ => fail("a set that isn't one"),
    }
}

pub(crate) fn check_random_element_argument(set: &Value) -> Evaluated<()> {
    if java_set_class(set) == Some(SetClass::Overridden) {
        return fail_coded(
            "RandomElement of a value that isn't a finite set",
            2176,
            format!(
                "Applying RandomElement to the following value,\nwhich is not a finite set:\n{}",
                format_pretty(set)
            ),
        );
    }
    Ok(())
}

fn random_element_normalization_is_known(value: &Value) -> bool {
    matches!(value, Value::Lazy(lazy) if matches!(&***lazy, Lazy::Nat | Lazy::Int | Lazy::Real | Lazy::Strings | Lazy::Any))
        || subset_set_input_is_known(value)
}

fn wrong_random_element(set: &Value) -> Evaluated<()> {
    let symbolic_function = matches!(set, Value::Lazy(lazy) if matches!(&***lazy, Lazy::FunctionSet(domain, range)
        if matches!(domain, Value::Lazy(domain) if matches!(&***domain, Lazy::Nat | Lazy::Int | Lazy::Real | Lazy::Strings | Lazy::Any))
            && (matches!(range, Value::Interval(..)) || matches!(range, Value::Set(elements) if elements.iter().all(|value| matches!(value, Value::Int(_) | Value::Bool(_) | Value::Str(_) | Value::Model(_)))))));
    if !symbolic_function {
        crate::eval::check_merge_argument_format(set)?;
    }
    fail_coded(
        "RandomElement of a value that isn't a finite set",
        2176,
        format!(
            "Applying RandomElement to the following value,\nwhich is not a finite set:\n{}",
            crate::print::format_pretty(set)
        ),
    )
}

pub(crate) fn validate_random_element(set: &Value) -> Evaluated<()> {
    check_random_element_argument(set)?;
    if !is_enumerable(set) {
        return wrong_random_element(set);
    }
    if let Value::Lazy(lazy) = set {
        match &***lazy {
            Lazy::FunctionSet(domain, range)
                if random_element_normalization_is_known(domain)
                    && random_element_normalization_is_known(range) =>
            {
                crate::value::normalize(domain);
                crate::value::normalize(range);
                if !is_enumerable(domain) {
                    return wrong_random_element(set);
                }
                if !normalized(domain)?.is_empty() {
                    validate_random_element(range)?;
                }
            }
            Lazy::RecordSet(fields, _)
                if fields
                    .iter()
                    .all(|(_, set)| random_element_normalization_is_known(set)) =>
            {
                for (_, set) in fields {
                    crate::value::normalize(set);
                }
                if let Some((_, first)) = fields.first() {
                    validate_random_element(first)?;
                }
            }
            Lazy::Product(parts) if parts.iter().all(random_element_normalization_is_known) => {
                for set in parts {
                    crate::value::normalize(set);
                }
                if let Some(first) = parts.first() {
                    validate_random_element(first)?;
                }
            }
            _ => {}
        }
    }
    Ok(())
}

/// RandomElement(set): each component of a set of functions, records or tuples in turn, and
/// otherwise the normalized set indexed with nextDouble.
pub fn random_element(
    random: &mut JavaRandom,
    set: &Value,
    default_method: bool,
) -> Evaluated<Value> {
    check_random_element_argument(set)?;
    if default_method {
        validate_random_element(set)?;
    }
    match set {
        Value::Lazy(lazy) => match &***lazy {
            Lazy::FunctionSet(domain, range) => {
                let keys = normalized(domain)?.to_vec();
                let values = keys
                    .iter()
                    .map(|_| random_element(random, range, default_method))
                    .collect::<Evaluated<_>>()?;
                return sorted_function(keys, values, Class::Plain);
            }
            Lazy::RecordSet(fields, _) => {
                let keys = fields
                    .iter()
                    .map(|(name, _)| Value::Str(Rc::clone(name)))
                    .collect();
                let values = fields
                    .iter()
                    .map(|(_, set)| random_element(random, set, default_method))
                    .collect::<Evaluated<_>>()?;
                return sorted_function(keys, values, Class::Record);
            }
            Lazy::Product(factors) => {
                let values = factors
                    .iter()
                    .map(|factor| random_element(random, factor, default_method))
                    .collect::<Evaluated<_>>()?;
                return Ok(Value::tuple(values));
            }
            _ => {}
        },
        Value::Interval(low, high, _) => {
            let size = (i64::from(*high) - i64::from(*low) + 1).max(0) as usize;
            let offset = random.next_index(size);
            if offset >= size {
                if !default_method {
                    return fail("RandomElement of the empty set");
                }
                return fail_runtime(
                    "RandomElement of the empty set",
                    "Attempted to retrieve out-of-bounds element from the interval value {}."
                        .to_owned(),
                );
            }
            return Ok(Value::Int(low + offset as i32));
        }
        _ => {}
    }
    let elements = normalized(set)?;
    match elements.get(random.next_index(elements.len())) {
        Some(element) => Ok(element.clone()),
        None if !default_method => fail("RandomElement of the empty set"),
        None => fail_runtime(
            "RandomElement of the empty set",
            "Index 0 out of bounds for length 0".to_owned(),
        ),
    }
}

/// RandomSubset(count, set): the set of `count` elements drawn as `getRandomSubset` draws them,
/// from an interval by its bounds, a product of sets component by component, and otherwise the
/// normalized set.
pub fn random_subset(random: &mut JavaRandom, count: u64, set: &Value) -> Evaluated<Value> {
    if crate::sets::is_empty_by_argument(set) {
        return set_of(Vec::new());
    }
    if let Value::Interval(low, high, _) = set {
        let size = (i64::from(*high) - i64::from(*low) + 1).max(0) as u64;
        let drawn = get_subset_indices(count, size, random, false)
            .into_iter()
            .map(|index| Value::Int(low + index as i32))
            .collect();
        return set_of(drawn);
    }
    // The lists a product draws an element of each from, and the keys of a function or record.
    // An empty set, of any shape, draws nothing.
    let product = match set {
        Value::Lazy(lazy) => match &***lazy {
            Lazy::FunctionSet(domain, range) => {
                let keys = normalized(domain)?.to_vec();
                let range = normalized(range)?;
                Some((vec![range; keys.len()], Some((keys, Class::Plain))))
            }
            Lazy::RecordSet(fields, _) => {
                let lists = fields
                    .iter()
                    .map(|(_, set)| normalized(set))
                    .collect::<Evaluated<_>>()?;
                let keys = fields
                    .iter()
                    .map(|(name, _)| Value::Str(Rc::clone(name)))
                    .collect();
                Some((lists, Some((keys, Class::Record))))
            }
            Lazy::Product(factors) => Some((
                factors.iter().map(normalized).collect::<Evaluated<_>>()?,
                None,
            )),
            _ => None,
        },
        _ => None,
    };
    let Some((lists, keys)) = product else {
        let elements = normalized(set)?;
        let drawn = get_subset_indices(count, elements.len() as u64, random, false)
            .into_iter()
            .map(|index| elements[index as usize].clone())
            .collect();
        return set_of(drawn);
    };
    // TLC indexes a product with a BigInteger, which i128 holds exactly up to its maximum.
    let Some(size) = lists
        .iter()
        .try_fold(1u128, |size, list| size.checked_mul(list.len() as u128))
        .filter(|&size| size <= i128::MAX as u128)
    else {
        return fail("RandomSubset of a product too large to index");
    };
    let indices: Vec<u128> = if size > i32::MAX as u128 {
        get_large_subset_indices(count, size, random)
    } else {
        get_subset_indices(count, size as u64, random, false)
            .into_iter()
            .map(u128::from)
            .collect()
    };
    let mut drawn = Vec::with_capacity(indices.len());
    for index in indices {
        // The last list varies fastest.
        let mut remaining = index;
        let mut values = vec![Value::Bool(false); lists.len()];
        for (value, list) in values.iter_mut().zip(&lists).rev() {
            *value = list[(remaining % list.len() as u128) as usize].clone();
            remaining /= list.len() as u128;
        }
        drawn.push(match &keys {
            Some((keys, class)) => sorted_function(keys.clone(), values, *class)?,
            None => Value::tuple(values),
        });
    }
    set_of(drawn)
}

/// RandomSubsetSet: exactly `count` coin-toss choices; duplicate choices are not retried.
pub fn random_subset_set(
    random: &mut JavaRandom,
    count: u32,
    probability: f64,
    set: &Value,
) -> Evaluated<Value> {
    let elements = normalized(set)?;
    let mut indices = std::collections::BTreeSet::new();
    for _ in 0..count {
        indices.insert(tla_values::random::coin_subset_indices(
            random,
            elements.len(),
            probability,
        ));
    }
    let subsets = indices
        .into_iter()
        .map(|indices| {
            set_of(
                indices
                    .into_iter()
                    .map(|index| elements[index].clone())
                    .collect(),
            )
        })
        .collect::<Evaluated<Vec<_>>>()?;
    let value = set_of(subsets)?;
    // HashSet.add fingerprints each generated subset, normalizing its shared concrete values.
    crate::value::settle(&value);
    Ok(value)
}

/// Shapes whose size and fingerprint normalization the value tree can preserve without deferred
/// function evaluation or a lazy set's mutable conversion cache.
pub fn subset_set_input_is_known(value: &Value) -> bool {
    match value {
        Value::Unsorted(_) | Value::Lambda(_) | Value::Lazy(_) => false,
        Value::Set(set) => {
            set.java_class == Some(crate::value::SetClass::Enumeration)
                && set.iter().all(subset_set_input_is_known)
        }
        Value::Function(function) => {
            matches!(
                function.java_class.get(),
                Some(Class::Plain | Class::Tuple | Class::Record)
            ) && function
                .domain
                .iter()
                .chain(&function.range)
                .all(subset_set_input_is_known)
        }
        _ => true,
    }
}
