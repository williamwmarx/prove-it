//! TLC!RandomElement and Randomization!RandomSubset over the evaluator's values, as TLC draws
//! them (`TLC.RandomElement`, `Enumerable.getRandomSubset`), from the draws `tla-values` shares
//! with the engine.

use std::rc::Rc;

use tla_values::random::{JavaRandom, get_large_subset_indices, get_subset_indices};

use crate::value::{Class, Evaluated, Lazy, Value, elements, fail, set_of, sorted_function};

// A set's elements in its normalized order (`toSetEnum` and `normalize`).
fn normalized(set: &Value) -> Evaluated<Rc<Vec<Value>>> {
    match set_of(elements(set)?.to_vec())? {
        Value::Set(elements) => Ok(elements),
        _ => fail("a set that isn't one"),
    }
}

/// RandomElement(set): each component of a set of functions, records or tuples in turn, and
/// otherwise the normalized set indexed with nextDouble.
pub fn random_element(random: &mut JavaRandom, set: &Value) -> Evaluated<Value> {
    match set {
        Value::Lazy(lazy) => match &**lazy {
            Lazy::FunctionSet(domain, range) => {
                let keys = normalized(domain)?.to_vec();
                let values = keys
                    .iter()
                    .map(|_| random_element(random, range))
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
                    .map(|(_, set)| random_element(random, set))
                    .collect::<Evaluated<_>>()?;
                return sorted_function(keys, values, Class::Record);
            }
            Lazy::Product(factors) => {
                let values = factors
                    .iter()
                    .map(|factor| random_element(random, factor))
                    .collect::<Evaluated<_>>()?;
                return Ok(Value::tuple(values));
            }
            _ => {}
        },
        Value::Interval(low, high) => {
            let size = (i64::from(*high) - i64::from(*low) + 1).max(0) as usize;
            let offset = random.next_index(size);
            if offset >= size {
                return fail("RandomElement of the empty set");
            }
            return Ok(Value::Int(low + offset as i32));
        }
        _ => {}
    }
    let elements = normalized(set)?;
    match elements.get(random.next_index(elements.len())) {
        Some(element) => Ok(element.clone()),
        None => fail("RandomElement of the empty set"),
    }
}

/// RandomSubset(count, set): the set of `count` elements drawn as `getRandomSubset` draws them,
/// from an interval by its bounds, a product of sets component by component, and otherwise the
/// normalized set.
pub fn random_subset(random: &mut JavaRandom, count: u64, set: &Value) -> Evaluated<Value> {
    if let Value::Interval(low, high) = set {
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
        Value::Lazy(lazy) => match &**lazy {
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
