//! TLC's random draws: java.util.Random, which `RandomEnumerableValues` extends, and the indices
//! RandomSubset draws, as `tlc/random.ts` draws them. The engine and the trace evaluator draw
//! RandomElement and RandomSubset from them, each over values of its own.

use std::sync::OnceLock;

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

    /// The state another generator can go on from (`from_state`).
    pub fn state(&self) -> u64 {
        self.state
    }

    fn next(&mut self, bits: u32) -> i32 {
        self.state = self.state.wrapping_mul(MULTIPLIER).wrapping_add(0xb) & MASK;
        (self.state >> (48 - bits)) as u32 as i32
    }

    pub fn next_int(&mut self, bound: i32) -> i32 {
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

    pub fn next_long(&mut self) -> i64 {
        (i64::from(self.next(32)) << 32).wrapping_add(i64::from(self.next(32)))
    }

    pub fn next_double(&mut self) -> f64 {
        let high = i64::from(self.next(26));
        let low = i64::from(self.next(27));
        ((high << 27) + low) as f64 * f64::powi(2.0, -53)
    }

    // An index below `size`, as `Math.floor(random.nextDouble() * size)`.
    pub fn next_index(&mut self, size: usize) -> usize {
        (self.next_double() * size as f64).floor() as usize
    }
}

// RandomGenerator.primes: the 1341 consecutive primes from 1277011 to 1295953.
pub fn get_primes() -> &'static [u64] {
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
pub fn get_subset_indices(
    count: u64,
    size: u64,
    random: &mut JavaRandom,
    is_174: bool,
) -> Vec<u64> {
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
pub fn get_large_subset_indices(count: u64, size: u128, random: &mut JavaRandom) -> Vec<u128> {
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
