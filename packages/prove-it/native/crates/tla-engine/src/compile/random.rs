//! RandomElement and RandomSubset over the engine's values, as `tlc/random.ts` draws them.

use tla_values::random::{get_large_subset_indices, get_subset_indices};
use tla_values::store::{KIND_SET, Outcome, is_function_kind};
use tla_values::{Bail, Id};

use super::lazy::Lazy;
use crate::machine::Machine;

/// The elements of a set in its normalized order (`toFiniteSet`).
fn normalized(machine: &mut Machine<'_>, set: &Lazy) -> Outcome<Vec<Id>> {
    let set = match set {
        Lazy::Set(set) => *set,
        lazy => {
            let elements = lazy.enumerate(machine)?;
            machine.store.set_of(&elements)?
        }
    };
    if machine.store.kind_of(set) != KIND_SET {
        return Err(Bail("drew from a value that isn't a set"));
    }
    Ok(machine.store.set_elements(set).to_vec())
}

/// Whether a set the engine holds as its elements may be one TLC keeps as a set of functions,
/// records or tuples, which it draws from component by component.
pub(crate) fn is_shape_forgotten(machine: &Machine<'_>, set: Id) -> bool {
    machine.store.kind_of(set) == KIND_SET && {
        let elements = machine.store.set_elements(set);
        !elements.is_empty()
            && elements
                .iter()
                .all(|&element| is_function_kind(machine.store.kind_of(element)))
    }
}

/// TLC!RandomElement: each component of a set of functions, records or tuples in turn, and
/// otherwise the enumerated set indexed with nextDouble.
pub(crate) fn random_element(
    machine: &mut Machine<'_>,
    set: &Lazy,
    default_method: bool,
) -> Outcome<Id> {
    if default_method
        && (matches!(set, Lazy::Infinite(_) | Lazy::Tested(_))
            || matches!(set, Lazy::Set(id) if machine.store.kind_of(*id) != KIND_SET))
    {
        return Err(Bail("RandomElement of a value that isn't a finite set"));
    }
    match set {
        Lazy::FunctionSet(domain, range) => {
            if default_method && matches!(&**domain, Lazy::Infinite(_) | Lazy::Tested(_)) {
                return Err(Bail("RandomElement of a value that isn't a finite set"));
            }
            let keys = normalized(machine, domain)?;
            let mut values = Vec::with_capacity(keys.len());
            for _ in &keys {
                values.push(random_element(machine, range, default_method)?);
            }
            let function = machine.store.function_of_sorted(&keys, &values);
            Ok(machine.store.mark_built_as_function(function))
        }
        Lazy::RecordSet(keys, sets) => {
            let mut values = Vec::with_capacity(sets.len());
            for set in sets {
                values.push(random_element(machine, set, default_method)?);
            }
            Ok(machine.store.function_of_sorted(keys, &values))
        }
        Lazy::Product(factors) => {
            let mut values = Vec::with_capacity(factors.len());
            for factor in factors {
                values.push(random_element(machine, factor, default_method)?);
            }
            Ok(machine.store.tuple_of(&values))
        }
        _ => {
            let elements = normalized(machine, set)?;
            let index = machine.random.next_index(elements.len());
            elements
                .get(index)
                .copied()
                .ok_or(Bail("RandomElement of the empty set"))
        }
    }
}

/// RandomElement of `low..high`, without the interval.
pub(crate) fn random_offset(machine: &mut Machine<'_>, low: i64, high: i64) -> Outcome<i64> {
    let size = (high - low + 1).max(0);
    let offset = machine.random.next_index(size as usize) as i64;
    if offset >= size {
        return Err(Bail("RandomElement of the empty set"));
    }
    Ok(low + offset)
}

/// What RandomSubset draws from: an interval by its bounds, or a set.
pub(crate) enum Source {
    Interval(i64, i64),
    Set(Lazy),
}

// TLCGlobals.setBound: TLC 1.7.4's ValueVec holds at most this many elements of a set.
const SET_BOUND_174: u128 = 1_000_000;

/// Enumerable#getRandomSubset, which Randomization's RandomSubset calls.
pub(crate) fn random_subset(
    machine: &mut Machine<'_>,
    count: u64,
    source: &Source,
    is_174: bool,
) -> Outcome<Vec<Id>> {
    let set = match source {
        Source::Interval(low, high) => {
            let size = (high - low + 1).max(0) as u64;
            // TLC draws the first index with nextInt(size), whose bound is an int.
            if size > i32::MAX as u64 {
                return Err(Bail("RandomSubset of an interval too large to draw from"));
            }
            let indices = get_subset_indices(count, size, &mut machine.random, is_174);
            return indices
                .into_iter()
                .map(|index| machine.store.int(low + index as i64))
                .collect();
        }
        Source::Set(set) => set,
    };
    if set.is_empty(machine)? {
        return Ok(Vec::new());
    }
    let product = match set {
        Lazy::Product(factors) if is_174 => {
            let mut size = 1u128;
            for factor in factors {
                size = size.saturating_mul(normalized(machine, factor)?.len() as u128);
            }
            if size > SET_BOUND_174 {
                return Err(Bail("a set with too many elements for TLC 1.7.4"));
            }
            None
        }
        Lazy::FunctionSet(domain, range) => {
            let keys = normalized(machine, domain)?;
            let range = normalized(machine, range)?;
            Some((vec![range; keys.len()], Some(keys)))
        }
        Lazy::RecordSet(_, sets) | Lazy::Product(sets) => {
            let mut lists = Vec::with_capacity(sets.len());
            for set in sets {
                lists.push(normalized(machine, set)?);
            }
            let keys = match set {
                Lazy::RecordSet(keys, _) => Some(keys.clone()),
                _ => None,
            };
            Some((lists, keys))
        }
        _ => None,
    };
    let Some((lists, keys)) = product else {
        let elements = normalized(machine, set)?;
        let indices = get_subset_indices(count, elements.len() as u64, &mut machine.random, is_174);
        return Ok(indices
            .into_iter()
            .map(|index| elements[index as usize])
            .collect());
    };
    // TLC indexes a product with a BigInteger, which i128 holds exactly up to its maximum.
    let size = lists
        .iter()
        .try_fold(1u128, |size, list| size.checked_mul(list.len() as u128))
        .filter(|&size| size <= i128::MAX as u128)
        .ok_or(Bail("RandomSubset of a product too large to index"))?;
    let indices = if size > i32::MAX as u128 {
        get_large_subset_indices(count, size, &mut machine.random)
    } else {
        get_subset_indices(count, size as u64, &mut machine.random, is_174)
            .into_iter()
            .map(u128::from)
            .collect()
    };
    let mut drawn = Vec::with_capacity(indices.len());
    for index in indices {
        // The last list varies fastest.
        let mut remaining = index;
        let mut values = vec![0; lists.len()];
        for (value, list) in values.iter_mut().zip(&lists).rev() {
            *value = list[(remaining % list.len() as u128) as usize];
            remaining /= list.len() as u128;
        }
        drawn.push(match &keys {
            Some(keys) => {
                let function = machine.store.function_of_sorted(keys, &values);
                machine.store.mark_built_as_function(function)
            }
            None => machine.store.tuple_of(&values),
        });
    }
    Ok(drawn)
}

/// `SubsetValue.CoinTossingSubsetEnumerator`, with duplicate picks removed without another draw.
pub(crate) fn random_subset_set(
    machine: &mut Machine<'_>,
    count: u32,
    probability: f64,
    source: &Source,
) -> Outcome<Id> {
    random_coin_subsets(machine, count, probability, None, source)
}

pub(crate) fn random_set_of_subsets(
    machine: &mut Machine<'_>,
    count: u32,
    average: u32,
    source: &Source,
) -> Outcome<Id> {
    random_coin_subsets(machine, count, f64::NAN, Some(average), source)
}

fn random_coin_subsets(
    machine: &mut Machine<'_>,
    count: u32,
    probability: f64,
    average: Option<u32>,
    source: &Source,
) -> Outcome<Id> {
    if matches!(source, Source::Set(set) if !matches!(set, Lazy::Set(_))) {
        return Err(Bail(
            "RandomSubsetSet of a value with untracked lazy normalization",
        ));
    }
    let elements = match source {
        Source::Set(set) => normalized(machine, set)?,
        Source::Interval(low, high) => {
            let size = (high - low + 1).max(0) as usize;
            if size > tla_values::SET_BOUND {
                return Err(tla_values::SET_BOUND_EXCEEDED);
            }
            (0..size)
                .map(|index| machine.store.int(low + index as i64))
                .collect::<Outcome<Vec<_>>>()?
        }
    };
    if elements
        .iter()
        .any(|&element| machine.store.holds_lazy_function(element))
    {
        return Err(Bail(
            "RandomSubsetSet of a value with untracked lazy normalization",
        ));
    }
    if (32 - count.leading_zeros()) as usize > elements.len()
        && count as i32 > 1i32.wrapping_shl(elements.len() as u32)
    {
        return Err(Bail(
            "RandomSubsetSet of a count greater than the number of subsets",
        ));
    }
    let probability = if let Some(average) = average {
        if average as usize > elements.len() {
            return Err(Bail(
                "RandomSetOfSubsets of an average larger than the base cardinality",
            ));
        }
        f64::from(average) / elements.len() as f64
    } else {
        probability
    };
    let mut picks = std::collections::BTreeSet::new();
    for _ in 0..count {
        picks.insert(tla_values::random::coin_subset_indices(
            &mut machine.random,
            elements.len(),
            probability,
        ));
    }
    let mut subsets = Vec::with_capacity(picks.len());
    for pick in picks {
        let members = pick
            .into_iter()
            .map(|index| elements[index])
            .collect::<Vec<_>>();
        subsets.push(machine.store.set_of(&members)?);
    }
    machine.store.set_of(&subsets)
}
