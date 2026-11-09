//! TLC's random draws: java.util.Random, which `RandomEnumerableValues` extends, and
//! RandomElement and RandomSubset as `tlc/random.ts` draws them.

use std::sync::OnceLock;

use tla_values::store::{KIND_SET, Outcome, is_function_kind};
use tla_values::{Bail, Id};

use super::lazy::Lazy;
use crate::machine::Machine;

const MULTIPLIER: u64 = 0x5_deec_e66d;
const MASK: u64 = (1 << 48) - 1;

/// java.util.Random.
#[derive(Clone, Copy)]
pub struct JavaRandom {
    state: u64,
}

impl JavaRandom {
    /// A generator seeded as `setSeed` seeds it.
    pub fn seeded(seed: u64) -> JavaRandom {
        JavaRandom {
            state: (seed ^ MULTIPLIER) & MASK,
        }
    }

    /// A generator in a state another left.
    pub fn from_state(state: u64) -> JavaRandom {
        JavaRandom {
            state: state & MASK,
        }
    }

    fn next(&mut self, bits: u32) -> i32 {
        self.state = self.state.wrapping_mul(MULTIPLIER).wrapping_add(0xb) & MASK;
        (self.state >> (48 - bits)) as u32 as i32
    }

    fn next_int(&mut self, bound: i32) -> i32 {
        let mask = bound - 1;
        let first = self.next(31);
        if bound & mask == 0 {
            return ((i64::from(bound) * i64::from(first)) >> 31) as i32;
        }
        let mut candidate = first;
        loop {
            let value = candidate % bound;
            if i64::from(candidate) - i64::from(value) + i64::from(mask) <= i64::from(i32::MAX) {
                return value;
            }
            candidate = self.next(31);
        }
    }

    fn next_long(&mut self) -> i64 {
        (i64::from(self.next(32)) << 32).wrapping_add(i64::from(self.next(32)))
    }

    fn next_double(&mut self) -> f64 {
        let high = i64::from(self.next(26));
        let low = i64::from(self.next(27));
        ((high << 27) + low) as f64 * f64::powi(2.0, -53)
    }

    // An index below `size`, as `Math.floor(random.nextDouble() * size)`.
    fn next_index(&mut self, size: usize) -> usize {
        (self.next_double() * size as f64).floor() as usize
    }
}

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
pub(crate) fn random_element(machine: &mut Machine<'_>, set: &Lazy) -> Outcome<Id> {
    match set {
        Lazy::FunctionSet(domain, range) => {
            let keys = normalized(machine, domain)?;
            let mut values = Vec::with_capacity(keys.len());
            for _ in &keys {
                values.push(random_element(machine, range)?);
            }
            Ok(machine.store.function_of_sorted(&keys, &values))
        }
        Lazy::RecordSet(keys, sets) => {
            let mut values = Vec::with_capacity(sets.len());
            for set in sets {
                values.push(random_element(machine, set)?);
            }
            Ok(machine.store.function_of_sorted(keys, &values))
        }
        Lazy::Product(factors) => {
            let mut values = Vec::with_capacity(factors.len());
            for factor in factors {
                values.push(random_element(machine, factor)?);
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

// RandomGenerator.primes: the 1341 consecutive primes from 1277011 to 1295953.
fn get_primes() -> &'static [u64] {
    static PRIMES: OnceLock<Vec<u64>> = OnceLock::new();
    PRIMES.get_or_init(|| {
        (1_277_011..)
            .filter(|&candidate: &u64| {
                (2..)
                    .take_while(|divisor| divisor * divisor <= candidate)
                    .all(|divisor| candidate % divisor != 0)
            })
            .take(1341)
            .collect()
    })
}

fn next_prime(random: &mut JavaRandom) -> u64 {
    let primes = get_primes();
    loop {
        let index = random.next_index(primes.len());
        if index < primes.len() {
            return primes[index];
        }
    }
}

// EnumerableValue.computeOptimalMandA: the smallest modulus m >= max(size, 9) that isn't a multiple
// of 4 and has a repeated prime factor, and the multiplier 1 + the product of its distinct prime
// factors.
fn get_modulus_and_multiplier(size: u64) -> (u64, u64) {
    (size.max(9)..)
        .find_map(|modulus| {
            let mut factors = Vec::new();
            let mut remaining = modulus;
            let mut divisor = 2;
            while divisor * divisor <= remaining {
                while remaining % divisor == 0 {
                    factors.push(divisor);
                    remaining /= divisor;
                }
                divisor += 1;
            }
            if remaining > 1 {
                factors.push(remaining);
            }
            let mut distinct = factors.clone();
            distinct.dedup();
            (modulus % 4 != 0 && distinct.len() != factors.len())
                .then(|| (modulus, distinct.iter().product::<u64>() + 1))
        })
        .expect("a modulus")
}

// EnumerableValue.SubsetEnumerator: count indices below size from a full-period linear
// congruential generator that starts at random.nextInt(size), or in TLC 1.7.4 the i-th index
// (x * i + a) mod size for a prime x above size and a = random.nextInt(size).
fn get_subset_indices(count: u64, size: u64, random: &mut JavaRandom, is_174: bool) -> Vec<u64> {
    if size == 0 {
        return Vec::new();
    }
    let start = random.next_int(size as i32) as u64;
    if is_174 {
        let stride = if size < 191 { 191 } else { i32::MAX as u64 };
        return (0..count.min(size))
            .map(|index| (stride * index + start) % size)
            .collect();
    }
    let (modulus, multiplier) = get_modulus_and_multiplier(size);
    let increment = next_prime(random);
    let mut index = start;
    (0..count)
        .map(|_| {
            loop {
                index = ((u128::from(multiplier) * u128::from(index) + u128::from(increment))
                    % u128::from(modulus)) as u64;
                if index < size {
                    return index;
                }
            }
        })
        .collect()
}

const LARGE_STRIDE: i128 = i64::MAX as i128 - 24;

// SetOfFcnsOrRcdsValue.BigIntegerSubsetEnumerator, for products with more than 2^31 - 1 elements.
fn get_large_subset_indices(count: u64, size: u128, random: &mut JavaRandom) -> Vec<u128> {
    let signed = random.next_long();
    let offset = i128::from(if signed < 0 {
        signed.wrapping_neg()
    } else {
        signed
    });
    (0..count)
        .map(|index| (LARGE_STRIDE * index as i128 + offset).rem_euclid(size as i128) as u128)
        .collect()
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
            Some(keys) => machine.store.function_of_sorted(keys, &values),
            None => machine.store.tuple_of(&values),
        });
    }
    Ok(drawn)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn draws_as_java_util_random() {
        // new java.util.Random(42): nextInt(100), nextDouble(), nextLong() and nextInt(7).
        let mut random = JavaRandom::seeded(42);
        assert_eq!(random.next_int(100), 30);
        assert_eq!(random.next_double(), 0.05466526274716077);
        assert_eq!(random.next_long(), 884324181205335268);
        assert_eq!(random.next_int(7), 4);
    }

    #[test]
    fn lists_the_primes_tlc_draws_increments_from() {
        let primes = get_primes();
        assert_eq!((primes[0], primes[1340]), (1_277_011, 1_295_953));
    }
}
