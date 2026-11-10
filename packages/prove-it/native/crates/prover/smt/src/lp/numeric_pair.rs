// Ported from Z3 (src/math/lp/numeric_pair.h), MIT license, see z3-license.txt. The value x + δy
// of a column, where δ is a positive infinitesimal that encodes strict bounds.
use std::cmp::Ordering;
use std::fmt;

use crate::util::rational::Rational;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Impq {
    pub x: Rational,
    pub y: Rational,
}

impl Impq {
    pub fn new(x: Rational, y: Rational) -> Impq {
        Impq { x, y }
    }

    pub fn from_x(x: Rational) -> Impq {
        Impq {
            x,
            y: Rational::zero(),
        }
    }

    pub fn zero() -> Impq {
        Impq {
            x: Rational::zero(),
            y: Rational::zero(),
        }
    }

    pub fn add(&self, other: &Impq) -> Impq {
        Impq::new(self.x.add(&other.x), self.y.add(&other.y))
    }

    pub fn sub(&self, other: &Impq) -> Impq {
        Impq::new(self.x.sub(&other.x), self.y.sub(&other.y))
    }

    pub fn mul(&self, coeff: &Rational) -> Impq {
        Impq::new(self.x.mul(coeff), self.y.mul(coeff))
    }

    pub fn div(&self, coeff: &Rational) -> Impq {
        Impq::new(self.x.div(coeff), self.y.div(coeff))
    }

    pub fn neg(&self) -> Impq {
        Impq::new(self.x.neg(), self.y.neg())
    }

    // Lexicographic, as δ is smaller than any positive rational.
    pub fn compare(&self, other: &Impq) -> Ordering {
        self.x
            .compare(&other.x)
            .then_with(|| self.y.compare(&other.y))
    }

    pub fn is_zero(&self) -> bool {
        self.x.is_zero() && self.y.is_zero()
    }

    pub fn is_int(&self) -> bool {
        self.y.is_zero() && self.x.is_int()
    }

    // floor and ceil of numeric_pair: x + δy rounded, for a positive δ smaller than any gap.
    pub fn floor(&self) -> Rational {
        if !self.x.is_int() {
            return self.x.floor();
        }
        if self.y.is_negative() {
            self.x.sub(&Rational::one())
        } else {
            self.x.clone()
        }
    }

    pub fn ceil(&self) -> Rational {
        if !self.x.is_int() {
            return self.x.ceil();
        }
        if self.y.is_positive() {
            self.x.add(&Rational::one())
        } else {
            self.x.clone()
        }
    }
}

impl fmt::Display for Impq {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.y.is_zero() {
            write!(formatter, "{}", self.x)
        } else {
            write!(formatter, "({}, {})", self.x, self.y)
        }
    }
}
