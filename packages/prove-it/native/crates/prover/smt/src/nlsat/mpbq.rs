//! Ported from Z3 (src/util/mpbq.{h,cpp}), MIT license, see z3-license.txt. Binary rationals
//! num/2^k, normalized so that k is 0 or num is odd. Like Z3, mul, div2 and power skip normalizing
//! when a normalized input cannot need it, so an unnormalized input stays unnormalized. That
//! matters because magnitudes and is_int read k.

use std::fmt;

use super::{Int, Rational};

fn get_power_of_two_multiple(value: &Int) -> u64 {
    if value.is_zero() {
        return 0;
    }
    value.trailing_zeros()
}

/// mpz log2: the position of the most significant bit of |value|, 0 for zero.
pub fn get_log2(value: &Int) -> i64 {
    value.bit_length().max(1) as i64 - 1
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Mpbq {
    pub num: Int,
    pub k: u32,
}

impl Mpbq {
    pub fn zero() -> Mpbq {
        Mpbq {
            num: Int::zero(),
            k: 0,
        }
    }

    pub fn one() -> Mpbq {
        Mpbq {
            num: Int::one(),
            k: 0,
        }
    }

    pub fn of(num: Int, k: u32) -> Mpbq {
        if k == 0 || num.is_zero() {
            return Mpbq { num, k: 0 };
        }
        let shift = get_power_of_two_multiple(&num).min(u64::from(k));
        Mpbq {
            num: &num >> shift,
            k: k - shift as u32,
        }
    }

    /// to_mpbq: q when its denominator is a power of two, else the binary rational with q's
    /// numerator over 2^(log2(den) + 1), which is not equal to q. Returns the value and whether it
    /// is exact.
    pub fn from_rational(value: &Rational) -> (Mpbq, bool) {
        if *value.den() == Int::one() {
            return (Mpbq::of(value.num().clone(), 0), true);
        }
        let log2 = get_log2(value.den()) as u32;
        if *value.den() == &Int::one() << u64::from(log2) {
            return (Mpbq::of(value.num().clone(), log2), true);
        }
        (Mpbq::of(value.num().clone(), log2 + 1), false)
    }

    pub fn is_zero(&self) -> bool {
        self.num.is_zero()
    }

    pub fn is_neg(&self) -> bool {
        self.num.is_negative()
    }

    pub fn is_pos(&self) -> bool {
        self.num.is_positive()
    }

    pub fn is_int(&self) -> bool {
        self.k == 0
    }

    pub fn to_rational(&self) -> Rational {
        Rational::of(self.num.clone(), &Int::one() << u64::from(self.k))
    }

    fn align(&self, other: &Mpbq) -> (Int, Int, u32) {
        let k = self.k.max(other.k);
        (
            &self.num << u64::from(k - self.k),
            &other.num << u64::from(k - other.k),
            k,
        )
    }

    pub fn add(&self, other: &Mpbq) -> Mpbq {
        let aligned = self.align(other);
        Mpbq::of(aligned.0 + aligned.1, aligned.2)
    }

    pub fn sub(&self, other: &Mpbq) -> Mpbq {
        let aligned = self.align(other);
        Mpbq::of(aligned.0 - aligned.1, aligned.2)
    }

    /// mul: normalized only when a factor is an integer.
    pub fn mul(&self, other: &Mpbq) -> Mpbq {
        let product = Mpbq {
            num: &self.num * &other.num,
            k: self.k + other.k,
        };
        if self.k == 0 || other.k == 0 {
            Mpbq::of(product.num, product.k)
        } else {
            product
        }
    }

    /// mul(a, b, b): Z3 reads b's k after writing the product's, so it normalizes only when a is
    /// an integer.
    pub fn mul_into_other(&self, other: &Mpbq) -> Mpbq {
        let product = Mpbq {
            num: &self.num * &other.num,
            k: self.k + other.k,
        };
        if self.k == 0 {
            Mpbq::of(product.num, product.k)
        } else {
            product
        }
    }

    pub fn neg(&self) -> Mpbq {
        Mpbq {
            num: -&self.num,
            k: self.k,
        }
    }

    pub fn div2(&self) -> Mpbq {
        if self.k == 0 {
            Mpbq::of(self.num.clone(), 1)
        } else {
            Mpbq {
                num: self.num.clone(),
                k: self.k + 1,
            }
        }
    }

    pub fn mul2k(&self, k: u32) -> Mpbq {
        if self.k >= k {
            Mpbq {
                num: self.num.clone(),
                k: self.k - k,
            }
        } else {
            Mpbq::of(&self.num << u64::from(k - self.k), 0)
        }
    }

    pub fn power(&self, exponent: u32) -> Mpbq {
        Mpbq {
            num: self.num.pow(exponent),
            k: self.k * exponent,
        }
    }

    pub fn compare(&self, other: &Mpbq) -> i32 {
        let aligned = self.align(other);
        if aligned.0 < aligned.1 {
            -1
        } else if aligned.0 > aligned.1 {
            1
        } else {
            0
        }
    }

    pub fn compare_rational(&self, other: &Rational) -> i32 {
        self.to_rational().compare(other) as i32
    }

    /// lt_1div2k: this < 1/2^k.
    pub fn is_less_than_one_div2k(&self, k: u32) -> bool {
        if !self.num.is_positive() {
            return true;
        }
        if self.k <= k {
            return false;
        }
        self.num < &Int::one() << u64::from(self.k - k)
    }

    pub fn floor(&self) -> Int {
        if self.is_int() {
            self.num.clone()
        } else {
            &self.num >> u64::from(self.k)
        }
    }

    pub fn ceil(&self) -> Int {
        if self.is_int() {
            self.num.clone()
        } else {
            (&self.num >> u64::from(self.k)) + Int::one()
        }
    }
}

impl fmt::Display for Mpbq {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.k {
            0 => write!(formatter, "{}", self.num),
            1 => write!(formatter, "{}/2", self.num),
            _ => write!(formatter, "{}/2^{}", self.num, self.k),
        }
    }
}

/// refine_upper: l < q < u, where q is not a binary rational. Bisects until the midpoint is above
/// q, which becomes the new u. Returns the new (lower, upper).
pub fn refine_upper(value: &Rational, lower: &Mpbq, upper: &Mpbq) -> (Mpbq, Mpbq) {
    let mut current_lower = lower.clone();
    loop {
        let middle = current_lower.add(upper).div2();
        if middle.compare_rational(value) > 0 {
            return (current_lower, middle);
        }
        current_lower = middle;
    }
}

/// refine_lower: as refine_upper, until the midpoint is below q, which becomes the new l. Returns
/// the new (lower, upper).
pub fn refine_lower(value: &Rational, lower: &Mpbq, upper: &Mpbq) -> (Mpbq, Mpbq) {
    let mut current_upper = upper.clone();
    loop {
        let middle = lower.add(&current_upper).div2();
        if middle.compare_rational(value) < 0 {
            return (middle, current_upper);
        }
        current_upper = middle;
    }
}
