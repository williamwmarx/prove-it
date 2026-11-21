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

/// `RandomGenerator.nextPrime`: one of the primes, drawn by `nextDouble`.
pub fn next_prime(random: &mut JavaRandom) -> u64 {
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

/// `Double.valueOf`, whose accepted probability literals include hex floats and type suffixes.
pub fn parse_java_double(units: &[u16]) -> Option<f64> {
    let first = units.iter().position(|&unit| unit > 0x20)?;
    let last = units.iter().rposition(|&unit| unit > 0x20)?;
    let bytes = units[first..=last]
        .iter()
        .map(|&unit| u8::try_from(unit).ok().filter(u8::is_ascii))
        .collect::<Option<Vec<_>>>()?;
    let text = std::str::from_utf8(&bytes).ok()?;
    let (negative, unsigned) = match text.as_bytes().first() {
        Some(b'-') => (true, &text[1..]),
        Some(b'+') => (false, &text[1..]),
        _ => (false, text),
    };
    match unsigned {
        "NaN" => return Some(f64::NAN),
        "Infinity" => {
            return Some(if negative {
                f64::NEG_INFINITY
            } else {
                f64::INFINITY
            });
        }
        _ => {}
    }
    let number = unsigned
        .strip_suffix(['f', 'F', 'd', 'D'])
        .unwrap_or(unsigned);
    let value = if let Some(hex) = number
        .strip_prefix("0x")
        .or_else(|| number.strip_prefix("0X"))
    {
        parse_hex_double(hex)?
    } else {
        let mut digits = 0;
        let mut dot = false;
        let mut at = 0;
        let bytes = number.as_bytes();
        while at < bytes.len() {
            match bytes[at] {
                b'0'..=b'9' => digits += 1,
                b'.' if !dot => dot = true,
                _ => break,
            }
            at += 1;
        }
        if digits == 0 {
            return None;
        }
        if at < bytes.len() && matches!(bytes[at], b'e' | b'E') {
            at += 1;
            if at < bytes.len() && matches!(bytes[at], b'+' | b'-') {
                at += 1;
            }
            let start = at;
            while at < bytes.len() && bytes[at].is_ascii_digit() {
                at += 1;
            }
            if at == start {
                return None;
            }
        }
        if at != bytes.len() {
            return None;
        }
        number.parse::<f64>().ok()?
    };
    Some(if negative { -value } else { value })
}

fn parse_hex_double(text: &str) -> Option<f64> {
    let (mantissa, exponent) = text.split_once(['p', 'P'])?;
    let (negative, exponent) = match exponent.as_bytes().first() {
        Some(b'-') => (true, &exponent[1..]),
        Some(b'+') => (false, &exponent[1..]),
        _ => (false, exponent),
    };
    if exponent.is_empty() || !exponent.bytes().all(|byte| byte.is_ascii_digit()) {
        return None;
    }
    let exponent = exponent.bytes().fold(0i64, |value, byte| {
        value
            .saturating_mul(10)
            .saturating_add(i64::from(byte - b'0'))
    });
    let exponent = if negative { -exponent } else { exponent };
    let mut bits = Vec::new();
    let mut dot = false;
    let mut fractional = 0i64;
    for byte in mantissa.bytes() {
        if byte == b'.' && !dot {
            dot = true;
            continue;
        }
        let digit = char::from(byte).to_digit(16)?;
        for bit in (0..4).rev() {
            bits.push(digit & (1 << bit) != 0);
        }
        if dot {
            fractional = fractional.saturating_add(4);
        }
    }
    if bits.is_empty() {
        return None;
    }
    let Some(first) = bits.iter().position(|bit| *bit) else {
        return Some(0.0);
    };
    let bits = &bits[first..];
    let scale = exponent.saturating_sub(fractional);
    let power = scale.saturating_add(bits.len() as i64 - 1);
    if power > 1023 {
        return Some(f64::INFINITY);
    }
    if power < -1075 {
        return Some(0.0);
    }
    if power < -1022 {
        return Some(f64::from_bits(round_hex_bits(bits, -1074 - scale)));
    }
    let mut significand = round_hex_bits(bits, bits.len() as i64 - 53);
    let mut power = power;
    if significand == 1 << 53 {
        significand >>= 1;
        power += 1;
    }
    if power > 1023 {
        return Some(f64::INFINITY);
    }
    Some(f64::from_bits(
        ((power + 1023) as u64) << 52 | (significand & ((1 << 52) - 1)),
    ))
}

fn round_hex_bits(bits: &[bool], shift: i64) -> u64 {
    let kept = (bits.len() as i64 - shift).clamp(0, bits.len() as i64) as usize;
    let mut value = bits[..kept]
        .iter()
        .fold(0u64, |value, &bit| (value << 1) | u64::from(bit));
    if shift < 0 {
        return value << -shift;
    }
    if kept < bits.len()
        && shift <= bits.len() as i64
        && bits[kept]
        && (value & 1 != 0 || bits[kept + 1..].iter().any(|bit| *bit))
    {
        value += 1;
    }
    value
}

/// One `CoinTossingSubsetEnumerator` choice, including a draw for probabilities 0 and 1.
pub fn coin_subset_indices(random: &mut JavaRandom, size: usize, probability: f64) -> Vec<usize> {
    (0..size)
        .filter(|_| random.next_double() < probability)
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

#[cfg(test)]
mod java_double_tests {
    #[test]
    fn parses_probabilities_as_java_double() {
        for line in include_str!("../tests/java-double.tsv")
            .lines()
            .chain(include_str!("../tests/java-double-fuzz.tsv").lines())
        {
            let (text, expected) = line.split_once('\t').expect("a recorded row");
            let units = text.replace("\\t", "\t").encode_utf16().collect::<Vec<_>>();
            let actual = super::parse_java_double(&units).map(f64::to_bits);
            let expected = (expected != "invalid")
                .then(|| u64::from_str_radix(expected, 16).expect("recorded bits"));
            assert_eq!(actual, expected, "{text:?}");
        }
    }
}
