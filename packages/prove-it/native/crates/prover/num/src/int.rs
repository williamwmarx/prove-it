//! An arbitrary-precision integer with JavaScript `bigint`'s semantics: `/` truncates toward zero,
//! `%` takes the dividend's sign, `>>` floors, `&` acts on the infinite two's complement, and
//! printing and parsing are decimal. Values that fit an `i64` are kept inline; larger ones as a
//! sign and a little-endian magnitude of `u32` limbs. Division is Knuth's algorithm D,
//! multiplication schoolbook: the SMT solver's operands are a few limbs.

use std::cmp::Ordering;
use std::fmt;
use std::ops::{
    Add, AddAssign, BitAnd, Div, DivAssign, Mul, MulAssign, Neg, Rem, RemAssign, Shl, Shr, Sub,
    SubAssign,
};
use std::str::FromStr;

#[derive(Clone, PartialEq, Eq, Hash)]
enum Repr {
    Small(i64),
    /// Only for values outside `i64`: a sign and a magnitude with no high zero limbs.
    Big {
        is_negative: bool,
        magnitude: Vec<u32>,
    },
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Int(Repr);

/// A text that isn't a decimal integer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParseIntError;

impl fmt::Display for ParseIntError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str("not a decimal integer")
    }
}

impl std::error::Error for ParseIntError {}

const DECIMAL_CHUNK: u32 = 1_000_000_000;
const DECIMAL_CHUNK_DIGITS: usize = 9;

impl Int {
    pub const fn zero() -> Int {
        Int(Repr::Small(0))
    }

    pub const fn one() -> Int {
        Int(Repr::Small(1))
    }

    pub fn is_zero(&self) -> bool {
        matches!(self.0, Repr::Small(0))
    }

    pub fn is_negative(&self) -> bool {
        match &self.0 {
            Repr::Small(value) => *value < 0,
            Repr::Big { is_negative, .. } => *is_negative,
        }
    }

    pub fn is_positive(&self) -> bool {
        !self.is_zero() && !self.is_negative()
    }

    /// -1, 0 or 1.
    pub fn signum(&self) -> i32 {
        if self.is_zero() {
            0
        } else if self.is_negative() {
            -1
        } else {
            1
        }
    }

    pub fn abs(&self) -> Int {
        if self.is_negative() {
            -self
        } else {
            self.clone()
        }
    }

    /// The value when it fits an `i64`.
    pub fn to_i64(&self) -> Option<i64> {
        match self.0 {
            Repr::Small(value) => Some(value),
            Repr::Big { .. } => None,
        }
    }

    /// JavaScript's `Number(value)`: the nearest `f64`, ties to even, infinite past `f64::MAX`.
    pub fn to_f64(&self) -> f64 {
        let (is_negative, magnitude) = match &self.0 {
            Repr::Small(value) => return *value as f64,
            Repr::Big {
                is_negative,
                magnitude,
            } => (*is_negative, magnitude),
        };
        let bits = bit_length_of(magnitude);
        // The top 64 bits, with a sticky low bit for any bit below them, round as the whole does.
        let shift = bits - 64;
        let top = shr_magnitude(magnitude, shift);
        let mut mantissa = u64::from(top[0]) | (u64::from(*top.get(1).unwrap_or(&0)) << 32);
        if has_low_bits(magnitude, shift) {
            mantissa |= 1;
        }
        let scale = if shift > 1023 {
            f64::INFINITY
        } else {
            f64::from_bits((1023 + shift) << 52)
        };
        let value = mantissa as f64 * scale;
        if is_negative { -value } else { value }
    }

    /// The number of bits of the magnitude, 0 for zero: `abs(value).toString(2).length` but for
    /// zero, whose binary text "0" has length 1.
    pub fn bit_length(&self) -> u64 {
        match &self.0 {
            Repr::Small(value) => u64::from(64 - value.unsigned_abs().leading_zeros()),
            Repr::Big { magnitude, .. } => bit_length_of(magnitude),
        }
    }

    /// `(value & 1n) === 1n`, whatever the sign.
    pub fn is_odd(&self) -> bool {
        match &self.0 {
            Repr::Small(value) => value & 1 == 1,
            Repr::Big { magnitude, .. } => magnitude[0] & 1 == 1,
        }
    }

    /// The number of low zero bits of the magnitude, 0 for zero.
    pub fn trailing_zeros(&self) -> u64 {
        match &self.0 {
            Repr::Small(0) => 0,
            Repr::Small(value) => u64::from(value.trailing_zeros()),
            Repr::Big { magnitude, .. } => magnitude
                .iter()
                .position(|limb| *limb != 0)
                .map_or(0, |index| {
                    32 * index as u64 + u64::from(magnitude[index].trailing_zeros())
                }),
        }
    }

    /// `value ** exponent`.
    pub fn pow(&self, exponent: u32) -> Int {
        let mut result = Int::one();
        let mut base = self.clone();
        let mut rest = exponent;
        while rest > 0 {
            if rest & 1 == 1 {
                result = &result * &base;
            }
            rest >>= 1;
            if rest > 0 {
                base = &base * &base;
            }
        }
        result
    }

    fn from_parts(is_negative: bool, mut magnitude: Vec<u32>) -> Int {
        while magnitude.last() == Some(&0) {
            magnitude.pop();
        }
        if magnitude.len() <= 2 {
            let value = u64::from(*magnitude.first().unwrap_or(&0))
                | (u64::from(*magnitude.get(1).unwrap_or(&0)) << 32);
            if is_negative && value <= 1 << 63 {
                return Int(Repr::Small((value as i64).wrapping_neg()));
            }
            if !is_negative && value < 1 << 63 {
                return Int(Repr::Small(value as i64));
            }
        }
        Int(Repr::Big {
            is_negative,
            magnitude,
        })
    }

    fn to_parts(&self) -> (bool, Vec<u32>) {
        match &self.0 {
            Repr::Small(value) => (*value < 0, magnitude_of_u64(value.unsigned_abs())),
            Repr::Big {
                is_negative,
                magnitude,
            } => (*is_negative, magnitude.clone()),
        }
    }

    /// `(quotient, remainder)` truncated toward zero, as JavaScript's `/` and `%`.
    pub fn div_rem(&self, divisor: &Int) -> (Int, Int) {
        if let (Repr::Small(left), Repr::Small(right)) = (&self.0, &divisor.0) {
            assert!(*right != 0, "division by zero");
            if let (Some(quotient), Some(remainder)) =
                (left.checked_div(*right), left.checked_rem(*right))
            {
                return (Int::from(quotient), Int::from(remainder));
            }
        }
        let (left_negative, left) = self.to_parts();
        let (right_negative, right) = divisor.to_parts();
        assert!(!right.is_empty(), "division by zero");
        let (quotient, remainder) = div_rem_magnitude(&left, &right);
        (
            Int::from_parts(left_negative != right_negative, quotient),
            Int::from_parts(left_negative, remainder),
        )
    }

    fn add_signed(&self, other: &Int, is_other_negated: bool) -> Int {
        if let (Repr::Small(left), Repr::Small(right)) = (&self.0, &other.0) {
            let result = if is_other_negated {
                left.checked_sub(*right)
            } else {
                left.checked_add(*right)
            };
            if let Some(result) = result {
                return Int::from(result);
            }
        }
        let (left_negative, left) = self.to_parts();
        let (right_negative, right) = other.to_parts();
        let right_negative = right_negative != is_other_negated && !right.is_empty();
        if left_negative == right_negative {
            return Int::from_parts(left_negative, add_magnitude(&left, &right));
        }
        match compare_magnitude(&left, &right) {
            Ordering::Equal => Int::zero(),
            Ordering::Greater => Int::from_parts(left_negative, sub_magnitude(&left, &right)),
            Ordering::Less => Int::from_parts(right_negative, sub_magnitude(&right, &left)),
        }
    }

    fn mul_ref(&self, other: &Int) -> Int {
        if let (Repr::Small(left), Repr::Small(right)) = (&self.0, &other.0)
            && let Some(result) = left.checked_mul(*right)
        {
            return Int::from(result);
        }
        let (left_negative, left) = self.to_parts();
        let (right_negative, right) = other.to_parts();
        Int::from_parts(
            left_negative != right_negative,
            mul_magnitude(&left, &right),
        )
    }

    /// Two's complement limbs, `length` of them, of a value that fits them.
    fn to_twos_complement(&self, length: usize) -> Vec<u32> {
        let (is_negative, mut magnitude) = self.to_parts();
        magnitude.resize(length, 0);
        if is_negative {
            let mut carry = 1u64;
            for limb in &mut magnitude {
                let sum = u64::from(!*limb) + carry;
                *limb = sum as u32;
                carry = sum >> 32;
            }
        }
        magnitude
    }

    fn from_twos_complement(mut limbs: Vec<u32>) -> Int {
        let is_negative = limbs.last().is_some_and(|limb| limb >> 31 == 1);
        if is_negative {
            let mut carry = 1u64;
            for limb in &mut limbs {
                let sum = u64::from(!*limb) + carry;
                *limb = sum as u32;
                carry = sum >> 32;
            }
        }
        Int::from_parts(is_negative, limbs)
    }

    fn limb_count(&self) -> usize {
        match &self.0 {
            Repr::Small(_) => 2,
            Repr::Big { magnitude, .. } => magnitude.len(),
        }
    }
}

fn magnitude_of_u64(value: u64) -> Vec<u32> {
    if value == 0 {
        Vec::new()
    } else if value >> 32 == 0 {
        vec![value as u32]
    } else {
        vec![value as u32, (value >> 32) as u32]
    }
}

fn bit_length_of(magnitude: &[u32]) -> u64 {
    magnitude.last().map_or(0, |top| {
        32 * (magnitude.len() as u64 - 1) + u64::from(32 - top.leading_zeros())
    })
}

fn has_low_bits(magnitude: &[u32], bits: u64) -> bool {
    let limbs = (bits / 32) as usize;
    let rest = bits % 32;
    magnitude[..limbs.min(magnitude.len())]
        .iter()
        .any(|limb| *limb != 0)
        || (rest > 0 && limbs < magnitude.len() && magnitude[limbs] & ((1 << rest) - 1) != 0)
}

fn compare_magnitude(left: &[u32], right: &[u32]) -> Ordering {
    left.len()
        .cmp(&right.len())
        .then_with(|| left.iter().rev().cmp(right.iter().rev()))
}

fn add_magnitude(left: &[u32], right: &[u32]) -> Vec<u32> {
    let (long, short) = if left.len() >= right.len() {
        (left, right)
    } else {
        (right, left)
    };
    let mut result = Vec::with_capacity(long.len() + 1);
    let mut carry = 0u64;
    for (index, limb) in long.iter().enumerate() {
        let sum = u64::from(*limb) + u64::from(*short.get(index).unwrap_or(&0)) + carry;
        result.push(sum as u32);
        carry = sum >> 32;
    }
    if carry > 0 {
        result.push(carry as u32);
    }
    result
}

/// `left - right` where `left >= right`.
fn sub_magnitude(left: &[u32], right: &[u32]) -> Vec<u32> {
    let mut result = Vec::with_capacity(left.len());
    let mut borrow = 0i64;
    for (index, limb) in left.iter().enumerate() {
        let difference = i64::from(*limb) - i64::from(*right.get(index).unwrap_or(&0)) - borrow;
        borrow = i64::from(difference < 0);
        result.push((difference + (borrow << 32)) as u32);
    }
    result
}

fn mul_magnitude(left: &[u32], right: &[u32]) -> Vec<u32> {
    if left.is_empty() || right.is_empty() {
        return Vec::new();
    }
    let mut result = vec![0u32; left.len() + right.len()];
    for (left_index, left_limb) in left.iter().enumerate() {
        let mut carry = 0u64;
        for (right_index, right_limb) in right.iter().enumerate() {
            let slot = &mut result[left_index + right_index];
            let product = u64::from(*left_limb) * u64::from(*right_limb) + u64::from(*slot) + carry;
            *slot = product as u32;
            carry = product >> 32;
        }
        result[left_index + right.len()] = carry as u32;
    }
    result
}

fn div_rem_small(left: &[u32], divisor: u32) -> (Vec<u32>, u32) {
    let mut quotient = vec![0u32; left.len()];
    let mut remainder = 0u64;
    for index in (0..left.len()).rev() {
        let current = (remainder << 32) | u64::from(left[index]);
        quotient[index] = (current / u64::from(divisor)) as u32;
        remainder = current % u64::from(divisor);
    }
    (quotient, remainder as u32)
}

/// Knuth's algorithm D (TAOCP 4.3.1) on magnitudes, `right` not zero.
fn div_rem_magnitude(left: &[u32], right: &[u32]) -> (Vec<u32>, Vec<u32>) {
    if compare_magnitude(left, right) == Ordering::Less {
        return (Vec::new(), left.to_vec());
    }
    if right.len() == 1 {
        let (quotient, remainder) = div_rem_small(left, right[0]);
        return (quotient, magnitude_of_u64(u64::from(remainder)));
    }
    let shift = right[right.len() - 1].leading_zeros();
    let divisor = shl_magnitude(right, u64::from(shift));
    let mut dividend = shl_magnitude(left, u64::from(shift));
    dividend.resize(left.len() + 1, 0);
    let divisor_length = divisor.len();
    let top = u64::from(divisor[divisor_length - 1]);
    let next = u64::from(divisor[divisor_length - 2]);
    let mut quotient = vec![0u32; dividend.len() - divisor_length];
    for position in (0..quotient.len()).rev() {
        let numerator = (u64::from(dividend[position + divisor_length]) << 32)
            | u64::from(dividend[position + divisor_length - 1]);
        let mut estimate = numerator / top;
        let mut remainder = numerator % top;
        while estimate > u64::from(u32::MAX)
            || estimate * next
                > ((remainder << 32) | u64::from(dividend[position + divisor_length - 2]))
        {
            estimate -= 1;
            remainder += top;
            if remainder > u64::from(u32::MAX) {
                break;
            }
        }
        let mut borrow = 0i64;
        let mut carry = 0u64;
        for index in 0..divisor_length {
            let product = estimate * u64::from(divisor[index]) + carry;
            carry = product >> 32;
            let difference =
                i64::from(dividend[position + index]) - i64::from(product as u32) - borrow;
            borrow = i64::from(difference < 0);
            dividend[position + index] = (difference + (borrow << 32)) as u32;
        }
        let difference = i64::from(dividend[position + divisor_length]) - carry as i64 - borrow;
        let is_overdrawn = difference < 0;
        dividend[position + divisor_length] = difference as u32;
        if is_overdrawn {
            estimate -= 1;
            let mut carry = 0u64;
            for index in 0..divisor_length {
                let sum = u64::from(dividend[position + index]) + u64::from(divisor[index]) + carry;
                dividend[position + index] = sum as u32;
                carry = sum >> 32;
            }
            dividend[position + divisor_length] =
                dividend[position + divisor_length].wrapping_add(carry as u32);
        }
        quotient[position] = estimate as u32;
    }
    dividend.truncate(divisor_length);
    (quotient, shr_magnitude(&dividend, u64::from(shift)))
}

fn shl_magnitude(magnitude: &[u32], bits: u64) -> Vec<u32> {
    if magnitude.is_empty() {
        return Vec::new();
    }
    let limbs = (bits / 32) as usize;
    let rest = (bits % 32) as u32;
    let mut result = vec![0u32; limbs];
    result.reserve(magnitude.len() + 1);
    if rest == 0 {
        result.extend_from_slice(magnitude);
        return result;
    }
    let mut carry = 0u32;
    for limb in magnitude {
        result.push((limb << rest) | carry);
        carry = limb >> (32 - rest);
    }
    if carry != 0 {
        result.push(carry);
    }
    result
}

fn shr_magnitude(magnitude: &[u32], bits: u64) -> Vec<u32> {
    let limbs = (bits / 32) as usize;
    if limbs >= magnitude.len() {
        return Vec::new();
    }
    let rest = (bits % 32) as u32;
    let source = &magnitude[limbs..];
    if rest == 0 {
        return source.to_vec();
    }
    (0..source.len())
        .map(|index| {
            (source[index] >> rest) | source.get(index + 1).map_or(0, |next| next << (32 - rest))
        })
        .collect()
}

impl Default for Int {
    fn default() -> Int {
        Int::zero()
    }
}

macro_rules! from_primitive {
    ($($primitive:ty),*) => {$(
        impl From<$primitive> for Int {
            fn from(value: $primitive) -> Int {
                Int(Repr::Small(i64::from(value)))
            }
        }
    )*};
}

from_primitive!(i8, i16, i32, i64, u8, u16, u32);

impl From<u64> for Int {
    fn from(value: u64) -> Int {
        Int::from_parts(false, magnitude_of_u64(value))
    }
}

impl From<usize> for Int {
    fn from(value: usize) -> Int {
        Int::from(value as u64)
    }
}

impl Ord for Int {
    fn cmp(&self, other: &Int) -> Ordering {
        if let (Repr::Small(left), Repr::Small(right)) = (&self.0, &other.0) {
            return left.cmp(right);
        }
        match (self.is_negative(), other.is_negative()) {
            (true, false) => Ordering::Less,
            (false, true) => Ordering::Greater,
            (is_negative, _) => {
                let ordering = compare_magnitude(&self.to_parts().1, &other.to_parts().1);
                if is_negative {
                    ordering.reverse()
                } else {
                    ordering
                }
            }
        }
    }
}

impl PartialOrd for Int {
    fn partial_cmp(&self, other: &Int) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq<i64> for Int {
    fn eq(&self, other: &i64) -> bool {
        self.0 == Repr::Small(*other)
    }
}

impl PartialOrd<i64> for Int {
    fn partial_cmp(&self, other: &i64) -> Option<Ordering> {
        Some(match self.0 {
            Repr::Small(value) => value.cmp(other),
            Repr::Big { is_negative, .. } => {
                if is_negative {
                    Ordering::Less
                } else {
                    Ordering::Greater
                }
            }
        })
    }
}

impl Neg for &Int {
    type Output = Int;
    fn neg(self) -> Int {
        match &self.0 {
            Repr::Small(value) => value
                .checked_neg()
                .map_or_else(|| Int::from_parts(false, vec![0, 1 << 31]), Int::from),
            Repr::Big {
                is_negative,
                magnitude,
            } => Int::from_parts(!is_negative, magnitude.clone()),
        }
    }
}

impl Neg for Int {
    type Output = Int;
    fn neg(self) -> Int {
        -&self
    }
}

macro_rules! binary_operator {
    ($trait:ident, $method:ident, $assign_trait:ident, $assign_method:ident, $body:expr) => {
        impl $trait<&Int> for &Int {
            type Output = Int;
            fn $method(self, other: &Int) -> Int {
                let body: fn(&Int, &Int) -> Int = $body;
                body(self, other)
            }
        }
        impl $trait<Int> for &Int {
            type Output = Int;
            fn $method(self, other: Int) -> Int {
                self.$method(&other)
            }
        }
        impl $trait<&Int> for Int {
            type Output = Int;
            fn $method(self, other: &Int) -> Int {
                (&self).$method(other)
            }
        }
        impl $trait<Int> for Int {
            type Output = Int;
            fn $method(self, other: Int) -> Int {
                (&self).$method(&other)
            }
        }
        impl $assign_trait<&Int> for Int {
            fn $assign_method(&mut self, other: &Int) {
                *self = (&*self).$method(other);
            }
        }
        impl $assign_trait<Int> for Int {
            fn $assign_method(&mut self, other: Int) {
                *self = (&*self).$method(&other);
            }
        }
    };
}

binary_operator!(Add, add, AddAssign, add_assign, |left, right| left
    .add_signed(right, false));
binary_operator!(Sub, sub, SubAssign, sub_assign, |left, right| left
    .add_signed(right, true));
binary_operator!(Mul, mul, MulAssign, mul_assign, Int::mul_ref);
binary_operator!(Div, div, DivAssign, div_assign, |left, right| left
    .div_rem(right)
    .0);
binary_operator!(Rem, rem, RemAssign, rem_assign, |left, right| left
    .div_rem(right)
    .1);

impl BitAnd<&Int> for &Int {
    type Output = Int;
    fn bitand(self, other: &Int) -> Int {
        if let (Repr::Small(left), Repr::Small(right)) = (&self.0, &other.0) {
            return Int::from(left & right);
        }
        let length = self.limb_count().max(other.limb_count()) + 1;
        let left = self.to_twos_complement(length);
        let right = other.to_twos_complement(length);
        Int::from_twos_complement(
            left.iter()
                .zip(&right)
                .map(|(left, right)| left & right)
                .collect(),
        )
    }
}

impl BitAnd<Int> for Int {
    type Output = Int;
    fn bitand(self, other: Int) -> Int {
        &self & &other
    }
}

impl Shl<u64> for &Int {
    type Output = Int;
    fn shl(self, bits: u64) -> Int {
        if let Repr::Small(value) = self.0
            && bits < 63
            && value.unsigned_abs() >> (63 - bits) == 0
        {
            return Int::from(value << bits);
        }
        let (is_negative, magnitude) = self.to_parts();
        Int::from_parts(is_negative, shl_magnitude(&magnitude, bits))
    }
}

impl Shl<u64> for Int {
    type Output = Int;
    fn shl(self, bits: u64) -> Int {
        &self << bits
    }
}

/// Floors, as JavaScript's `>>` on a `bigint`.
impl Shr<u64> for &Int {
    type Output = Int;
    fn shr(self, bits: u64) -> Int {
        if let Repr::Small(value) = self.0 {
            return Int::from(value >> bits.min(63));
        }
        let (is_negative, magnitude) = self.to_parts();
        if !is_negative {
            return Int::from_parts(false, shr_magnitude(&magnitude, bits));
        }
        // floor(-m / 2^n) = -(((m - 1) >> n) + 1)
        let reduced = shr_magnitude(&sub_magnitude(&magnitude, &[1]), bits);
        Int::from_parts(true, add_magnitude(&reduced, &[1]))
    }
}

impl Shr<u64> for Int {
    type Output = Int;
    fn shr(self, bits: u64) -> Int {
        &self >> bits
    }
}

impl fmt::Display for Int {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (is_negative, mut magnitude) = match &self.0 {
            Repr::Small(value) => return write!(formatter, "{value}"),
            Repr::Big {
                is_negative,
                magnitude,
            } => (*is_negative, magnitude.clone()),
        };
        let mut chunks = Vec::new();
        while !magnitude.is_empty() {
            let (quotient, remainder) = div_rem_small(&magnitude, DECIMAL_CHUNK);
            chunks.push(remainder);
            magnitude = quotient;
            while magnitude.last() == Some(&0) {
                magnitude.pop();
            }
        }
        let mut text = String::with_capacity(chunks.len() * DECIMAL_CHUNK_DIGITS + 1);
        if is_negative {
            text.push('-');
        }
        let mut rest = chunks.iter().rev();
        if let Some(first) = rest.next() {
            text.push_str(&first.to_string());
        }
        for chunk in rest {
            text.push_str(&format!("{chunk:09}"));
        }
        formatter.write_str(&text)
    }
}

impl fmt::Debug for Int {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, formatter)
    }
}

/// An optional `-` and decimal digits.
impl FromStr for Int {
    type Err = ParseIntError;
    fn from_str(text: &str) -> Result<Int, ParseIntError> {
        let (is_negative, digits) = text
            .strip_prefix('-')
            .map_or((false, text), |digits| (true, digits));
        if digits.is_empty() || !digits.bytes().all(|byte| byte.is_ascii_digit()) {
            return Err(ParseIntError);
        }
        if let Ok(value) = text.parse::<i64>() {
            return Ok(Int::from(value));
        }
        let mut magnitude: Vec<u32> = Vec::new();
        let head = digits.len() % DECIMAL_CHUNK_DIGITS;
        let chunks = std::iter::once(&digits[..head]).chain(
            digits.as_bytes()[head..]
                .chunks(DECIMAL_CHUNK_DIGITS)
                .map(|chunk| std::str::from_utf8(chunk).unwrap_or("0")),
        );
        for chunk in chunks.filter(|chunk| !chunk.is_empty()) {
            let scale = 10u64.pow(chunk.len() as u32);
            let mut carry = chunk.parse::<u64>().map_err(|_| ParseIntError)?;
            for limb in &mut magnitude {
                let product = u64::from(*limb) * scale + carry;
                *limb = product as u32;
                carry = product >> 32;
            }
            if carry > 0 {
                magnitude.push(carry as u32);
            }
        }
        Ok(Int::from_parts(is_negative, magnitude))
    }
}
