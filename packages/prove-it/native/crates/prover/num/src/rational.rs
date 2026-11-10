//! Ported from Z3 (src/util/rational.h), MIT license, through `src/prover/smt/solver/rational.ts`.
//! Exact rationals for the simplex tableau, normalized with a positive denominator.

use std::cmp::Ordering;
use std::fmt;
use std::ops::{Add, Div, Mul, Neg, Sub};

use crate::Int;

/// `getGcd`: never negative, and `gcd(0, 0)` is 0.
pub fn get_gcd(first: &Int, second: &Int) -> Int {
    let mut left = first.abs();
    let mut right = second.abs();
    while !right.is_zero() {
        let remainder = &left % &right;
        left = right;
        right = remainder;
    }
    left
}

/// `getLcm`: `|first * second| / gcd`.
pub fn get_lcm(first: &Int, second: &Int) -> Int {
    (first * second).abs() / get_gcd(first, second)
}

/// mpz_manager's div: SMT-LIB's, whose remainder is never negative. By a positive divisor, div is
/// the floor of the quotient.
pub fn get_euclidean_div(dividend: &Int, divisor: &Int) -> Int {
    let quotient = dividend / divisor;
    if !dividend.is_negative() || &(&quotient * divisor) == dividend {
        return quotient;
    }
    if divisor.is_negative() {
        quotient + Int::one()
    } else {
        quotient - Int::one()
    }
}

/// mpz_manager's mod: never negative.
pub fn get_euclidean_mod(dividend: &Int, divisor: &Int) -> Int {
    let remainder = dividend % divisor;
    if !remainder.is_negative() {
        return remainder;
    }
    if divisor.is_positive() {
        remainder + divisor
    } else {
        remainder - divisor
    }
}

/// The n-th root of an integer when it is exact.
fn get_int_root(value: &Int, degree: u32) -> Option<Int> {
    if value.is_negative() {
        if degree.is_multiple_of(2) {
            return None;
        }
        return get_int_root(&-value, degree).map(|root| -root);
    }
    if *value < 2 || degree == 1 {
        return Some(value.clone());
    }
    let mut low = Int::zero();
    let mut high = Int::one();
    while &high.pow(degree) <= value {
        high = &high * &Int::from(2);
    }
    while &high - &low > Int::one() {
        let mid = (&low + &high) / Int::from(2);
        if &mid.pow(degree) <= value {
            low = mid;
        } else {
            high = mid;
        }
    }
    (&low.pow(degree) == value).then_some(low)
}

/// `isBigInt`: mpz keeps a value outside a 32-bit int as a bignum.
fn is_big_int(value: &Int) -> bool {
    *value <= i64::from(i32::MIN) || *value > i64::from(i32::MAX)
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Rational {
    num: Int,
    den: Int,
}

impl Rational {
    pub fn zero() -> Rational {
        Rational::from_int(Int::zero())
    }

    pub fn one() -> Rational {
        Rational::from_int(Int::one())
    }

    pub fn minus_one() -> Rational {
        Rational::from_int(Int::from(-1))
    }

    /// `Rational.of`: normalizes by the gcd, with a positive denominator.
    pub fn of(num: Int, den: Int) -> Rational {
        if den == 1 {
            return Rational::from_int(num);
        }
        let divisor = get_gcd(&num, &den);
        let (num, den) = if den.is_negative() {
            (-num, -den)
        } else {
            (num, den)
        };
        Rational {
            num: num / &divisor,
            den: den / &divisor,
        }
    }

    pub fn from_int(num: Int) -> Rational {
        Rational {
            num,
            den: Int::one(),
        }
    }

    /// `Rational.fromNumber` of an integer.
    pub fn from_i64(value: i64) -> Rational {
        Rational::from_int(Int::from(value))
    }

    pub fn num(&self) -> &Int {
        &self.num
    }

    pub fn den(&self) -> &Int {
        &self.den
    }

    pub fn is_zero(&self) -> bool {
        self.num.is_zero()
    }

    pub fn is_int(&self) -> bool {
        self.den == 1
    }

    pub fn is_positive(&self) -> bool {
        self.num.is_positive()
    }

    pub fn is_negative(&self) -> bool {
        self.num.is_negative()
    }

    pub fn add(&self, other: &Rational) -> Rational {
        if self.num.is_zero() {
            return other.clone();
        }
        if other.num.is_zero() {
            return self.clone();
        }
        if self.is_int() && other.is_int() {
            return Rational::from_int(&self.num + &other.num);
        }
        Rational::of(
            &self.num * &other.den + &other.num * &self.den,
            &self.den * &other.den,
        )
    }

    pub fn sub(&self, other: &Rational) -> Rational {
        if other.num.is_zero() {
            return self.clone();
        }
        if self.is_int() && other.is_int() {
            return Rational::from_int(&self.num - &other.num);
        }
        Rational::of(
            &self.num * &other.den - &other.num * &self.den,
            &self.den * &other.den,
        )
    }

    pub fn mul(&self, other: &Rational) -> Rational {
        if self.is_int() && other.is_int() {
            return Rational::from_int(&self.num * &other.num);
        }
        Rational::of(&self.num * &other.num, &self.den * &other.den)
    }

    /// Panics on a zero divisor, where JavaScript throws a `RangeError`.
    pub fn div(&self, other: &Rational) -> Rational {
        Rational::of(&self.num * &other.den, &self.den * &other.num)
    }

    pub fn neg(&self) -> Rational {
        Rational {
            num: -&self.num,
            den: self.den.clone(),
        }
    }

    pub fn abs(&self) -> Rational {
        if self.num.is_negative() {
            self.neg()
        } else {
            self.clone()
        }
    }

    /// The n-th root when it is rational.
    pub fn root(&self, degree: u32) -> Option<Rational> {
        let num = get_int_root(&self.num, degree)?;
        let den = get_int_root(&self.den, degree)?;
        Some(Rational::of(num, den))
    }

    pub fn pow(&self, exponent: u32) -> Rational {
        Rational::of(self.num.pow(exponent), self.den.pow(exponent))
    }

    /// `is_big`: a numerator or denominator outside a 32-bit int.
    pub fn is_big(&self) -> bool {
        is_big_int(&self.num) || is_big_int(&self.den)
    }

    pub fn compare(&self, other: &Rational) -> Ordering {
        (&self.num * &other.den).cmp(&(&other.num * &self.den))
    }

    pub fn floor(&self) -> Rational {
        if self.is_int() {
            return self.clone();
        }
        let quotient = &self.num / &self.den;
        Rational::from_int(if self.num.is_negative() {
            quotient - Int::one()
        } else {
            quotient
        })
    }

    pub fn ceil(&self) -> Rational {
        if self.is_int() {
            return self.clone();
        }
        let quotient = &self.num / &self.den;
        Rational::from_int(if self.num.is_negative() {
            quotient
        } else {
            quotient + Int::one()
        })
    }
}

impl Ord for Rational {
    fn cmp(&self, other: &Rational) -> Ordering {
        self.compare(other)
    }
}

impl PartialOrd for Rational {
    fn partial_cmp(&self, other: &Rational) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl From<Int> for Rational {
    fn from(num: Int) -> Rational {
        Rational::from_int(num)
    }
}

impl From<i64> for Rational {
    fn from(value: i64) -> Rational {
        Rational::from_i64(value)
    }
}

macro_rules! rational_operator {
    ($trait:ident, $method:ident) => {
        impl $trait<&Rational> for &Rational {
            type Output = Rational;
            fn $method(self, other: &Rational) -> Rational {
                Rational::$method(self, other)
            }
        }
        impl $trait<Rational> for Rational {
            type Output = Rational;
            fn $method(self, other: Rational) -> Rational {
                Rational::$method(&self, &other)
            }
        }
    };
}

rational_operator!(Add, add);
rational_operator!(Sub, sub);
rational_operator!(Mul, mul);
rational_operator!(Div, div);

impl Neg for &Rational {
    type Output = Rational;
    fn neg(self) -> Rational {
        Rational::neg(self)
    }
}

impl Neg for Rational {
    type Output = Rational;
    fn neg(self) -> Rational {
        Rational::neg(&self)
    }
}

/// `toString`: `num` or `num/den`.
impl fmt::Display for Rational {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_int() {
            write!(formatter, "{}", self.num)
        } else {
            write!(formatter, "{}/{}", self.num, self.den)
        }
    }
}

impl fmt::Debug for Rational {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, formatter)
    }
}
