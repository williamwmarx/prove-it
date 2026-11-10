//! Ported from Z3 (src/math/polynomial/upolynomial.{h,cpp}, src/util/mpzzp.h,
//! src/math/polynomial/polynomial_primes.h), MIT license, see z3-license.txt. Univariate
//! polynomials with integer coefficients, as coefficient arrays from the constant term up with no
//! leading zeros, over Z or over Z_p. Root isolation by Descartes' rule of signs, Sturm sequences
//! and refinement of isolating intervals with binary rational endpoints.

use super::mpbq::{Mpbq, get_log2, refine_lower, refine_upper};
use super::{Int, Rational, SmtError, get_gcd};

pub type Upolynomial = Vec<Int>;

/// g_big_primes: the primes mod_gcd tries, in order.
const BIG_PRIMES: [i64; 231] = [
    39103, 39107, 39113, 39119, 39133, 39139, 39157, 39161, 39163, 39181, 39191, 39199, 39209,
    39217, 39227, 39229, 39233, 39239, 39241, 39251, 39293, 39301, 39313, 39317, 39323, 39341,
    39343, 39359, 39367, 39371, 39373, 39383, 39397, 39409, 39419, 39439, 39443, 39451, 39461,
    39499, 39503, 39509, 39511, 39521, 39541, 39551, 39563, 39569, 39581, 39607, 39619, 39623,
    39631, 39659, 39667, 39671, 39679, 39703, 39709, 39719, 39727, 39733, 39749, 39761, 39769,
    39779, 39791, 39799, 39821, 39827, 39829, 39839, 39841, 39847, 39857, 39863, 39869, 39877,
    39883, 39887, 39901, 39929, 39937, 39953, 39971, 39979, 39983, 39989, 40009, 40013, 40031,
    40037, 40039, 40063, 40087, 40093, 40099, 40111, 40123, 40127, 40129, 40151, 40153, 40163,
    40169, 40177, 40189, 40193, 40213, 40231, 40237, 40241, 40253, 40277, 40283, 40289, 40343,
    40351, 40357, 40361, 40387, 40423, 40427, 40429, 40433, 40459, 40471, 40483, 40487, 40493,
    40499, 40507, 40519, 40529, 40531, 40543, 40559, 40577, 40583, 40591, 40597, 40609, 40627,
    40637, 40639, 40693, 40697, 40699, 40709, 40739, 40751, 40759, 40763, 40771, 40787, 40801,
    40813, 40819, 40823, 40829, 40841, 40847, 40849, 40853, 40867, 40879, 40883, 40897, 40903,
    40927, 40933, 40939, 40949, 40961, 40973, 40993, 41011, 41017, 41023, 41039, 41047, 41051,
    41057, 41077, 41081, 41113, 41117, 41131, 41141, 41143, 41149, 41161, 41177, 41179, 41183,
    41189, 41201, 41203, 41213, 41221, 41227, 41231, 41233, 41243, 41257, 41263, 41269, 41281,
    41299, 41333, 41341, 41351, 41357, 41381, 41387, 41389, 41399, 41411, 41413, 41443, 41453,
    41467, 41479, 41491, 41507, 41513, 41519, 41521, 41539, 41543, 41549,
];

/// mpz div: rounds toward minus infinity.
fn floor_div(dividend: &Int, divisor: &Int) -> Int {
    let quotient = dividend / divisor;
    if !(dividend % divisor).is_zero() && dividend.is_negative() != divisor.is_negative() {
        quotient - Int::one()
    } else {
        quotient
    }
}

/// mpz gcd(a, b, x, y, g): a*x + b*y = g. Returns (x, y, g).
fn get_extended_gcd(first: &Int, second: &Int) -> (Int, Int, Int) {
    let (mut old_r, mut r) = (first.clone(), second.clone());
    let (mut old_s, mut s) = (Int::one(), Int::zero());
    let (mut old_t, mut t) = (Int::zero(), Int::one());
    while !r.is_zero() {
        let quotient = &old_r / &r;
        (old_r, r) = (r.clone(), &old_r - &(&quotient * &r));
        (old_s, s) = (s.clone(), &old_s - &(&quotient * &s));
        (old_t, t) = (t.clone(), &old_t - &(&quotient * &t));
    }
    if old_r.is_negative() {
        (-old_s, -old_t, -old_r)
    } else {
        (old_s, old_t, old_r)
    }
}

fn trim(mut coeffs: Vec<Int>) -> Vec<Int> {
    while coeffs.last().is_some_and(Int::is_zero) {
        coeffs.pop();
    }
    coeffs
}

fn coeff_or_zero(coeffs: &[Int], index: usize) -> Int {
    coeffs.get(index).cloned().unwrap_or_default()
}

pub struct IsolatedRoots {
    pub roots: Vec<Mpbq>,
    pub lowers: Vec<Mpbq>,
    pub uppers: Vec<Mpbq>,
}

/// An interval (a, b) refined around the root of a square-free polynomial, or the root itself.
#[derive(Clone, Debug)]
pub struct Refinement {
    pub is_interval: bool,
    pub lower: Mpbq,
    pub upper: Mpbq,
}

/// div_rem's result: lc(p2)^power * p1 = quotient * p2 + remainder.
pub struct DivRem {
    pub quotient: Upolynomial,
    pub remainder: Upolynomial,
    pub power: u32,
}

/// rem's result: the pseudo-remainder and the number of pseudo-division steps.
pub struct RemWithPower {
    pub remainder: Upolynomial,
    pub power: u32,
}

/// ext_gcd's result: a*u + b*v = d.
pub struct ExtGcd {
    pub u: Upolynomial,
    pub v: Upolynomial,
    pub d: Upolynomial,
}

struct DrsFrame {
    parent: Option<usize>,
    coeffs: Vec<Int>,
    is_first: bool,
    is_left: bool,
}

#[derive(Clone, Debug, Default)]
pub struct UpolynomialManager {
    /// Z_p when set, else Z. Coefficients over Z_p lie in the symmetric range around zero. Hensel
    /// lifting also sets a prime power.
    modulus: Option<Int>,
    is_prime_modulus: bool,
}

impl UpolynomialManager {
    pub fn new(modulus: Option<Int>) -> UpolynomialManager {
        UpolynomialManager {
            modulus,
            is_prime_modulus: true,
        }
    }

    pub fn zp(&self) -> Option<&Int> {
        self.modulus.as_ref()
    }

    /// field: Z_p for a prime p. Over a prime power, division falls back to pseudo-division.
    fn is_field(&self) -> bool {
        self.modulus.is_some() && self.is_prime_modulus
    }

    /// set_zp
    pub fn set_zp(&mut self, prime: Int) {
        self.modulus = Some(prime);
        self.is_prime_modulus = true;
    }

    /// set_p_sq: from Z_m to Z_(m^2).
    pub fn square_modulus(&mut self) -> Result<(), SmtError> {
        let Some(modulus) = &self.modulus else {
            return Err(SmtError::Invariant("squaring the modulus of Z".into()));
        };
        self.modulus = Some(modulus * modulus);
        self.is_prime_modulus = false;
        Ok(())
    }

    /// scoped_set_zp. Unlike the TS, it also restores the ring when the body returns an error.
    pub fn with_zp<T>(&mut self, prime: Int, body: impl FnOnce(&mut UpolynomialManager) -> T) -> T {
        let saved_modulus = self.modulus.clone();
        let saved_is_prime = self.is_prime_modulus;
        self.set_zp(prime);
        let result = body(self);
        self.modulus = saved_modulus;
        self.is_prime_modulus = saved_is_prime;
        result
    }

    // Numerals.

    /// p_normalize
    pub fn normalize_numeral(&self, value: &Int) -> Int {
        let Some(modulus) = &self.modulus else {
            return value.clone();
        };
        let upper = modulus / &Int::from(2);
        let lower = if (modulus % &Int::from(2)).is_zero() {
            -&upper + Int::one()
        } else {
            -&upper
        };
        let rest = value % modulus;
        if rest > upper {
            rest - modulus
        } else if rest < lower {
            rest + modulus
        } else {
            rest
        }
    }

    // The inverse of value modulo the current modulus, as inv computes it.
    fn get_inverse(&self, value: &Int, modulus: &Int) -> Int {
        self.normalize_numeral(&get_extended_gcd(&self.normalize_numeral(value), modulus).0)
    }

    pub fn inv(&self, value: &Int) -> Result<Int, SmtError> {
        let Some(modulus) = &self.modulus else {
            return Err(SmtError::Invariant("inverse over Z".into()));
        };
        Ok(self.get_inverse(value, modulus))
    }

    /// mpzzp div: exact over Z (rounding toward minus infinity), multiplication by the inverse over
    /// Z_p.
    fn div_numeral(&self, dividend: &Int, divisor: &Int) -> Int {
        match &self.modulus {
            None => floor_div(dividend, divisor),
            Some(modulus) => {
                self.normalize_numeral(&(dividend * &self.get_inverse(divisor, modulus)))
            }
        }
    }

    fn divides_numeral(&self, divisor: &Int, dividend: &Int) -> bool {
        if self.is_field() && !divisor.is_zero() {
            return true;
        }
        if divisor.is_zero() {
            dividend.is_zero()
        } else {
            (dividend % divisor).is_zero()
        }
    }

    /// set: the coefficients reduced to the current ring.
    pub fn set(&self, coeffs: &[Int]) -> Upolynomial {
        trim(
            coeffs
                .iter()
                .map(|coeff| self.normalize_numeral(coeff))
                .collect(),
        )
    }

    // Core operations.

    pub fn get_content(&self, coeffs: &[Int]) -> Int {
        let mut content = Int::zero();
        for coeff in coeffs {
            content = get_gcd(&content, coeff);
        }
        content
    }

    pub fn get_primitive(&self, coeffs: &[Int]) -> Upolynomial {
        let content = self.get_content(coeffs);
        if content == Int::one() {
            return coeffs.to_vec();
        }
        trim(coeffs.iter().map(|coeff| coeff / &content).collect())
    }

    pub fn neg(&self, coeffs: &[Int]) -> Upolynomial {
        coeffs
            .iter()
            .map(|coeff| self.normalize_numeral(&-coeff))
            .collect()
    }

    pub fn add(&self, first: &[Int], second: &[Int]) -> Upolynomial {
        let size = first.len().max(second.len());
        trim(
            (0..size)
                .map(|index| {
                    self.normalize_numeral(
                        &(coeff_or_zero(first, index) + coeff_or_zero(second, index)),
                    )
                })
                .collect(),
        )
    }

    pub fn sub(&self, first: &[Int], second: &[Int]) -> Upolynomial {
        let size = first.len().max(second.len());
        trim(
            (0..size)
                .map(|index| {
                    self.normalize_numeral(
                        &(coeff_or_zero(first, index) - coeff_or_zero(second, index)),
                    )
                })
                .collect(),
        )
    }

    pub fn mul(&self, first: &[Int], second: &[Int]) -> Upolynomial {
        if first.is_empty() || second.is_empty() {
            return Vec::new();
        }
        let mut result = vec![Int::zero(); first.len() + second.len() - 1];
        for index in 0..first.len() {
            if first[index].is_zero() {
                continue;
            }
            for other in 0..second.len() {
                if !second[other].is_zero() {
                    result[index + other] = self.normalize_numeral(
                        &(&result[index + other] + &(&first[index] * &second[other])),
                    );
                }
            }
        }
        trim(result)
    }

    pub fn mul_const(&self, coeffs: &[Int], factor: &Int) -> Upolynomial {
        if factor.is_zero() {
            return Vec::new();
        }
        trim(
            coeffs
                .iter()
                .map(|coeff| self.normalize_numeral(&(coeff * factor)))
                .collect(),
        )
    }

    /// div(p, b): each coefficient divided by b, which divides it.
    pub fn div_const(&self, coeffs: &[Int], divisor: &Int) -> Upolynomial {
        if *divisor == Int::one() {
            return coeffs.to_vec();
        }
        trim(
            coeffs
                .iter()
                .map(|coeff| self.div_numeral(coeff, divisor))
                .collect(),
        )
    }

    pub fn derivative(&self, coeffs: &[Int]) -> Upolynomial {
        if coeffs.len() <= 1 {
            return Vec::new();
        }
        trim(
            coeffs[1..]
                .iter()
                .enumerate()
                .map(|(index, coeff)| {
                    self.normalize_numeral(&(coeff * &Int::from(index as i64 + 1)))
                })
                .collect(),
        )
    }

    /// normalize: the coefficients divided by their gcd, or the sign of a constant.
    pub fn normalize(&self, coeffs: &[Int]) -> Upolynomial {
        if coeffs.is_empty() {
            return Vec::new();
        }
        if coeffs.len() == 1 {
            return vec![if coeffs[0].is_positive() {
                Int::one()
            } else {
                self.normalize_numeral(&Int::from(-1))
            }];
        }
        let content = self.get_content(coeffs);
        if content == Int::one() {
            return coeffs.to_vec();
        }
        coeffs
            .iter()
            .map(|coeff| self.div_numeral(coeff, &content))
            .collect()
    }

    pub fn flip_sign_if_lm_neg(&self, coeffs: &[Int]) -> Upolynomial {
        if coeffs.last().is_some_and(Int::is_negative) {
            self.neg(coeffs)
        } else {
            coeffs.to_vec()
        }
    }

    // The polynomial times the inverse of its leading coefficient, as mk_monic computes it.
    fn get_monic(&self, coeffs: &[Int], modulus: &Int) -> Upolynomial {
        if coeffs.last().is_none_or(|leading| *leading == Int::one()) {
            return coeffs.to_vec();
        }
        let last = coeffs.len() - 1;
        let inverse = self.get_inverse(&coeffs[last], modulus);
        coeffs
            .iter()
            .enumerate()
            .map(|(index, coeff)| {
                if index == last {
                    Int::one()
                } else {
                    self.normalize_numeral(&(coeff * &inverse))
                }
            })
            .collect()
    }

    /// mk_monic: the polynomial divided by its leading coefficient, over Z_p.
    pub fn mk_monic(&self, coeffs: &[Int]) -> Result<Upolynomial, SmtError> {
        if coeffs.last().is_none_or(|leading| *leading == Int::one()) {
            return Ok(coeffs.to_vec());
        }
        let Some(modulus) = &self.modulus else {
            return Err(SmtError::Invariant("inverse over Z".into()));
        };
        Ok(self.get_monic(coeffs, modulus))
    }

    /// div_rem: q and r with lc(p2)^d * p1 = q * p2 + r over Z, or p1 = q * p2 + r over a field.
    pub fn div_rem(&self, dividend: &[Int], divisor: &[Int]) -> DivRem {
        let is_field = self.is_field();
        if divisor.len() == 1 {
            let quotient = if is_field {
                self.div_const(dividend, &divisor[0])
            } else {
                self.set(dividend)
            };
            return DivRem {
                quotient,
                remainder: Vec::new(),
                power: 0,
            };
        }
        let mut remainder = self.set(dividend);
        if dividend.len() <= 1 {
            return DivRem {
                quotient: Vec::new(),
                remainder,
                power: 0,
            };
        }
        let quotient_size = if dividend.len() >= divisor.len() {
            dividend.len() - divisor.len() + 1
        } else {
            0
        };
        let mut quotient = vec![Int::zero(); quotient_size];
        let leading = &divisor[divisor.len() - 1];
        let mut power = 0;
        while remainder.len() >= divisor.len() {
            let size = remainder.len();
            let shift = size - divisor.len();
            if is_field {
                let ratio = self.div_numeral(&remainder[size - 1], leading);
                quotient[shift] = self.normalize_numeral(&(&quotient[shift] + &ratio));
                for index in 0..divisor.len() - 1 {
                    remainder[index + shift] = self.normalize_numeral(
                        &(&remainder[index + shift] - &(&ratio * &divisor[index])),
                    );
                }
            } else {
                power += 1;
                let top = remainder[size - 1].clone();
                for coeff in &mut remainder[..size - 1] {
                    *coeff = self.normalize_numeral(&(&*coeff * leading));
                }
                for coeff in &mut quotient {
                    *coeff = self.normalize_numeral(&(&*coeff * leading));
                }
                quotient[shift] = self.normalize_numeral(&(&quotient[shift] + &top));
                for index in 0..divisor.len() - 1 {
                    remainder[index + shift] = self.normalize_numeral(
                        &(&remainder[index + shift] - &(&top * &divisor[index])),
                    );
                }
            }
            remainder.truncate(size - 1);
            remainder = trim(remainder);
        }
        DivRem {
            quotient: trim(quotient),
            remainder,
            power,
        }
    }

    pub fn div(&self, dividend: &[Int], divisor: &[Int]) -> Upolynomial {
        self.div_rem(dividend, divisor).quotient
    }

    /// rem: the pseudo-remainder, with the number of pseudo-division steps.
    pub fn rem_with_power(&self, dividend: &[Int], divisor: &[Int]) -> RemWithPower {
        if divisor.len() == 1 {
            return RemWithPower {
                remainder: Vec::new(),
                power: 0,
            };
        }
        let mut remainder = self.set(dividend);
        if dividend.len() <= 1 {
            return RemWithPower {
                remainder,
                power: 0,
            };
        }
        let is_field = self.is_field();
        let leading = &divisor[divisor.len() - 1];
        let mut power = 0;
        while remainder.len() >= divisor.len() {
            let size = remainder.len();
            let shift = size - divisor.len();
            if is_field {
                let ratio = self.div_numeral(&remainder[size - 1], leading);
                for index in 0..divisor.len() - 1 {
                    remainder[index + shift] = self.normalize_numeral(
                        &(&remainder[index + shift] - &(&ratio * &divisor[index])),
                    );
                }
            } else {
                power += 1;
                let top = remainder[size - 1].clone();
                for coeff in &mut remainder[..size - 1] {
                    *coeff = self.normalize_numeral(&(&*coeff * leading));
                }
                for index in 0..divisor.len() - 1 {
                    remainder[index + shift] = self.normalize_numeral(
                        &(&remainder[index + shift] - &(&top * &divisor[index])),
                    );
                }
            }
            remainder.truncate(size - 1);
            remainder = trim(remainder);
        }
        RemWithPower { remainder, power }
    }

    pub fn rem(&self, dividend: &[Int], divisor: &[Int]) -> Upolynomial {
        self.rem_with_power(dividend, divisor).remainder
    }

    /// srem: the signed pseudo-remainder, negated unless an odd number of steps by a negative
    /// leading coefficient already flipped it.
    pub fn srem(&self, dividend: &[Int], divisor: &[Int]) -> Upolynomial {
        let result = self.rem_with_power(dividend, divisor);
        if result.power.is_multiple_of(2) || divisor.last().is_some_and(Int::is_positive) {
            self.neg(&result.remainder)
        } else {
            result.remainder
        }
    }

    /// divides: whether divisor divides dividend, checking only the leading coefficients.
    pub fn divides(&self, dividend: &[Int], divisor: &[Int]) -> bool {
        if divisor.is_empty() {
            return false;
        }
        if dividend.is_empty() {
            return true;
        }
        let leading = &divisor[divisor.len() - 1];
        let mut rest = self.set(dividend);
        while !rest.is_empty() {
            if divisor.len() > rest.len() || !self.divides_numeral(leading, &rest[rest.len() - 1]) {
                return false;
            }
            let shift = rest.len() - divisor.len();
            let ratio = self.div_numeral(&rest[rest.len() - 1], leading);
            for index in 0..divisor.len() - 1 {
                if !divisor[index].is_zero() {
                    rest[index + shift] = self
                        .normalize_numeral(&(&rest[index + shift] - &(&ratio * &divisor[index])));
                }
            }
            let last = rest.len() - 1;
            rest[last] = Int::zero();
            rest = trim(rest);
        }
        true
    }

    /// exact_div: dividend / divisor when the division is exact, else None.
    pub fn exact_div(&self, dividend: &[Int], divisor: &[Int]) -> Option<Upolynomial> {
        if divisor.is_empty() {
            return None;
        }
        if dividend.is_empty() {
            return Some(Vec::new());
        }
        let leading = &divisor[divisor.len() - 1];
        if divisor.len() > dividend.len() {
            return None;
        }
        let mut result = vec![Int::zero(); dividend.len() - divisor.len() + 1];
        let mut rest = self.set(dividend);
        while !rest.is_empty() {
            if divisor.len() > rest.len()
                || !self.divides_numeral(leading, &rest[rest.len() - 1])
                || !self.divides_numeral(&divisor[0], &rest[0])
            {
                return None;
            }
            let shift = rest.len() - divisor.len();
            let ratio = self.div_numeral(&rest[rest.len() - 1], leading);
            result[shift] = ratio.clone();
            for index in 0..divisor.len() - 1 {
                if !divisor[index].is_zero() {
                    rest[index + shift] = self
                        .normalize_numeral(&(&rest[index + shift] - &(&ratio * &divisor[index])));
                }
            }
            let last = rest.len() - 1;
            rest[last] = Int::zero();
            rest = trim(rest);
        }
        Some(trim(result))
    }

    // GCD.

    fn euclid_gcd(&self, first: &[Int], second: &[Int]) -> Upolynomial {
        if first.is_empty() {
            return self.flip_sign_if_lm_neg(&self.set(second));
        }
        if second.is_empty() {
            return self.flip_sign_if_lm_neg(&self.set(first));
        }
        let mut a = self.set(first);
        let mut b = self.set(second);
        while !b.is_empty() {
            let remainder = self.normalize(&self.rem(&a, &b));
            a = b;
            b = remainder;
        }
        let normalized = self.normalize(&a);
        match &self.modulus {
            Some(modulus) if self.is_field() => self.get_monic(&normalized, modulus),
            _ => self.flip_sign_if_lm_neg(&normalized),
        }
    }

    /// CRA_combine_images: the image modulo bound * prime, in the symmetric range. Returns the
    /// coefficients and the new bound.
    fn combine_images(
        &self,
        image: &[Int],
        prime: &Int,
        combined: &[Int],
        bound: &Int,
    ) -> (Upolynomial, Int) {
        let inverses = get_extended_gcd(prime, bound);
        let modulo = |value: &Int, modulus: &Int| ((value % modulus) + modulus) % modulus;
        let inverse1 = modulo(&inverses.0, bound);
        let inverse2 = modulo(&inverses.1, prime);
        let factor1 = bound * &inverse2;
        let factor2 = prime * &inverse1;
        let new_bound = prime * bound;
        let upper = &new_bound / &Int::from(2);
        let size = image.len().max(combined.len());
        let mut result = Vec::new();
        for index in 0..size {
            let value = modulo(
                &(coeff_or_zero(image, index) * &factor1
                    + coeff_or_zero(combined, index) * &factor2),
                &new_bound,
            );
            result.push(if value > upper {
                value - &new_bound
            } else {
                value
            });
        }
        (result, new_bound)
    }

    /// mod_gcd: the gcd over Z from images modulo big primes, combined by the Chinese remainder
    /// theorem.
    fn mod_gcd(&mut self, first: &[Int], second: &[Int]) -> Upolynomial {
        let content_u = self.get_content(first);
        let content_v = self.get_content(second);
        let pp_u = self.get_primitive(first);
        let pp_v = self.get_primitive(second);
        let content_g = get_gcd(&content_u, &content_v);
        let degree_u = first.len() - 1;
        let degree_v = second.len() - 1;
        let lc_g = get_gcd(&pp_u[degree_u], &pp_v[degree_v]);
        let mut combined: Vec<Int> = Vec::new();
        let mut bound = Int::zero();
        for prime in BIG_PRIMES {
            let prime = Int::from(prime);
            let image = self.with_zp(prime.clone(), |um| {
                let u_zp = um.set(&pp_u);
                let v_zp = um.set(&pp_v);
                if u_zp.len() < degree_u + 1 || v_zp.len() < degree_v + 1 {
                    return None;
                }
                Some(um.mul_const(&um.get_monic(&um.euclid_gcd(&u_zp, &v_zp), &prime), &lc_g))
            });
            let Some(image) = image else {
                continue;
            };
            if image.len() <= 1 {
                return vec![content_g];
            }
            // The first image, or one of lower degree, replaces the accumulated image. Before the
            // first image the bound is zero, which is even.
            if image.len() < combined.len() || (&bound % &Int::from(2)).is_zero() {
                combined = image;
                bound = prime;
            } else {
                let next = self.combine_images(&image, &prime, &combined, &bound);
                combined = next.0;
                bound = next.1;
            }
            let candidate = self.get_primitive(&combined);
            if self.divides_numeral(&candidate[candidate.len() - 1], &lc_g)
                && self.divides(&pp_u, &candidate)
                && self.divides(&pp_v, &candidate)
            {
                return self.flip_sign_if_lm_neg(&self.mul_const(&candidate, &content_g));
            }
        }
        self.euclid_gcd(first, second)
    }

    pub fn gcd(&mut self, first: &[Int], second: &[Int]) -> Upolynomial {
        if first.is_empty() {
            return self.flip_sign_if_lm_neg(&self.set(second));
        }
        if second.is_empty() {
            return self.flip_sign_if_lm_neg(&self.set(first));
        }
        if self.modulus.is_none() {
            self.mod_gcd(first, second)
        } else {
            self.euclid_gcd(first, second)
        }
    }

    /// square_free: p divided by gcd(p, p'), normalized.
    pub fn square_free(&mut self, coeffs: &[Int]) -> Upolynomial {
        if coeffs.len() <= 1 {
            return self.set(coeffs);
        }
        let common = self.gcd(coeffs, &self.derivative(coeffs));
        if common.len() <= 1 {
            self.set(coeffs)
        } else {
            self.normalize(&self.div(coeffs, &common))
        }
    }

    pub fn is_square_free(&mut self, coeffs: &[Int]) -> bool {
        coeffs.len() <= 1 || self.gcd(coeffs, &self.derivative(coeffs)).len() <= 1
    }

    pub fn pw(&self, coeffs: &[Int], exponent: u32) -> Upolynomial {
        if exponent == 0 {
            return vec![Int::one()];
        }
        let mut result = self.set(coeffs);
        for _ in 1..exponent {
            result = self.mul(&result, coeffs);
        }
        result
    }

    /// ext_gcd over Z_p: u, v and the monic d with a*u + b*v = d.
    pub fn ext_gcd(&self, first: &[Int], second: &[Int]) -> Result<ExtGcd, SmtError> {
        let mut u = vec![Int::one()];
        let mut d = self.mk_monic(&self.set(first))?;
        let mut v1 = Vec::new();
        let mut v3 = self.set(second);
        while !v3.is_empty() {
            let division = self.div_rem(&d, &v3);
            let t = self.sub(&u, &self.mul(&v1, &division.quotient));
            u = v1;
            d = v3;
            v1 = t;
            v3 = division.remainder;
        }
        let v = self.div(&self.sub(&d, &self.mul(first, &u)), second);
        if d.last().is_none_or(|leading| *leading == Int::one()) {
            return Ok(ExtGcd { u, v, d });
        }
        let inverse = self.inv(&d[d.len() - 1])?;
        Ok(ExtGcd {
            u: self.mul_const(&u, &inverse),
            v: self.mul_const(&v, &inverse),
            d: self.mk_monic(&d)?,
        })
    }

    // Transformations.

    pub fn has_zero_roots(&self, coeffs: &[Int]) -> bool {
        coeffs.first().is_some_and(Int::is_zero)
    }

    pub fn remove_zero_roots(&self, coeffs: &[Int]) -> Upolynomial {
        let mut index = 0;
        while index < coeffs.len() && coeffs[index].is_zero() {
            index += 1;
        }
        coeffs[index..].to_vec()
    }

    /// has_one_half_root: 2^n * p(1/2) = 0.
    fn has_one_half_root(&self, coeffs: &[Int]) -> bool {
        if coeffs.is_empty() {
            return true;
        }
        if coeffs.len() == 1 {
            return false;
        }
        let mut result = coeffs[coeffs.len() - 1].clone();
        for (shift, index) in (1..).zip((0..coeffs.len() - 1).rev()) {
            result += &coeffs[index] << shift;
        }
        result.is_zero()
    }

    /// descartes_bound_0_1: the sign changes of (x+1)^n p(1/(x+1)), stopping above 1.
    fn descartes_bound01(&self, coeffs: &[Int]) -> u32 {
        if coeffs.len() <= 1 {
            return 0;
        }
        let mut work = coeffs.to_vec();
        let mut previous = 0;
        let mut changes = 0;
        for index in 0..work.len() {
            let mut position = 1;
            while position < work.len() - index {
                work[position] = &work[position] + &work[position - 1];
                position += 1;
            }
            let current = work[position - 1].signum();
            if current == 0 {
                continue;
            }
            if current != previous && previous != 0 {
                changes += 1;
                if changes > 1 {
                    return changes;
                }
            }
            previous = current;
        }
        changes
    }

    /// translate: p(x + 1).
    pub fn translate(&self, coeffs: &[Int]) -> Upolynomial {
        let mut result = coeffs.to_vec();
        let degree = result.len().saturating_sub(1);
        for step in 1..=degree {
            for index in degree - step..degree {
                result[index] = &result[index] + &result[index + 1];
            }
        }
        result
    }

    /// translate_q: den^n * p(x + q).
    pub fn translate_q(&self, coeffs: &[Int], value: &Rational) -> Upolynomial {
        if coeffs.len() <= 1 {
            return coeffs.to_vec();
        }
        let mut result = self.compose_an_p_x_div_a(coeffs, value.den());
        let degree = result.len() - 1;
        for step in 1..=degree {
            result[degree - step] =
                &result[degree - step] + &(value.num() * &result[degree - step + 1]);
            for index in degree - step + 1..degree {
                result[index] = &result[index] * value.den() + value.num() * &result[index + 1];
            }
            result[degree] = &result[degree] * value.den();
        }
        result
    }

    /// compose_2n_p_x_div_2: 2^n * p(x/2).
    fn compose2n_p_x_div2(&self, coeffs: &[Int]) -> Upolynomial {
        let degree = coeffs.len().saturating_sub(1);
        coeffs
            .iter()
            .enumerate()
            .map(|(index, coeff)| coeff << (degree - index) as u64)
            .collect()
    }

    /// p_minus_x: p(-x).
    pub fn p_minus_x(&self, coeffs: &[Int]) -> Upolynomial {
        coeffs
            .iter()
            .enumerate()
            .map(|(index, coeff)| {
                if index % 2 == 1 && !coeff.is_zero() {
                    -coeff
                } else {
                    coeff.clone()
                }
            })
            .collect()
    }

    /// p_1_div_x: x^n * p(1/x).
    pub fn p1_div_x(&self, coeffs: &[Int]) -> Upolynomial {
        coeffs.iter().rev().cloned().collect()
    }

    /// compose_p_2k_x: p(2^k * x).
    fn compose_p2k_x(&self, coeffs: &[Int], k: u32) -> Upolynomial {
        coeffs
            .iter()
            .enumerate()
            .map(|(index, coeff)| coeff << (u64::from(k) * index as u64))
            .collect()
    }

    /// compose_an_p_x_div_a: a^n * p(x/a).
    fn compose_an_p_x_div_a(&self, coeffs: &[Int], factor: &Int) -> Upolynomial {
        let degree = coeffs.len() - 1;
        coeffs
            .iter()
            .enumerate()
            .map(|(index, coeff)| {
                if coeff.is_zero() {
                    Int::zero()
                } else {
                    coeff * &factor.pow((degree - index) as u32)
                }
            })
            .collect()
    }

    /// compose_p_q_x: c^n * p(b*x/c) for q = b/c.
    pub fn compose_p_q_x(&self, coeffs: &[Int], value: &Rational) -> Upolynomial {
        let degree = coeffs.len().saturating_sub(1);
        coeffs
            .iter()
            .enumerate()
            .map(|(index, coeff)| {
                if coeff.is_zero() {
                    Int::zero()
                } else {
                    coeff
                        * &value.den().pow((degree - index) as u32)
                        * value.num().pow(index as u32)
                }
            })
            .collect()
    }

    // Signs.

    /// eval_sign_at for a binary rational: the sign of (2^k)^n * p(b).
    pub fn eval_sign_at_bq(&self, coeffs: &[Int], value: &Mpbq) -> i32 {
        if coeffs.is_empty() {
            return 0;
        }
        if coeffs.len() == 1 {
            return coeffs[0].signum();
        }
        let mut result = coeffs[coeffs.len() - 1].clone();
        let mut shift = value.k;
        for index in (0..coeffs.len() - 1).rev() {
            result = if coeffs[index].is_zero() {
                &result * &value.num
            } else {
                (&coeffs[index] << u64::from(shift)) + &result * &value.num
            };
            shift += value.k;
        }
        result.signum()
    }

    pub fn eval_sign_at_q(&self, coeffs: &[Int], value: &Rational) -> i32 {
        if coeffs.is_empty() {
            return 0;
        }
        if coeffs.len() == 1 {
            return coeffs[0].signum();
        }
        let mut result = coeffs[coeffs.len() - 1].clone();
        let mut denominator = value.den().clone();
        for index in (0..coeffs.len() - 1).rev() {
            result = if coeffs[index].is_zero() {
                &result * value.num()
            } else {
                &coeffs[index] * &denominator + &result * value.num()
            };
            denominator = &denominator * value.den();
        }
        result.signum()
    }

    pub fn eval_sign_at_zero(&self, coeffs: &[Int]) -> i32 {
        coeffs.first().map_or(0, Int::signum)
    }

    pub fn eval_sign_at_plus_inf(&self, coeffs: &[Int]) -> i32 {
        coeffs.last().map_or(0, Int::signum)
    }

    pub fn eval_sign_at_minus_inf(&self, coeffs: &[Int]) -> i32 {
        if coeffs.is_empty() {
            return 0;
        }
        let leading = coeffs[coeffs.len() - 1].signum();
        if (coeffs.len() - 1).is_multiple_of(2) {
            leading
        } else {
            -leading
        }
    }

    fn count_sign_variations(&self, signs: &[i32]) -> u32 {
        if signs.len() <= 1 {
            return 0;
        }
        let mut variations = 0;
        let mut previous = 0;
        for current in signs {
            if *current == 0 {
                continue;
            }
            if *current != previous && previous != 0 {
                variations += 1;
            }
            previous = *current;
        }
        variations
    }

    pub fn sign_variations_at_minus_inf(&self, sequence: &[Upolynomial]) -> u32 {
        self.count_sign_variations(
            &sequence
                .iter()
                .map(|coeffs| self.eval_sign_at_minus_inf(coeffs))
                .collect::<Vec<_>>(),
        )
    }

    pub fn sign_variations_at_plus_inf(&self, sequence: &[Upolynomial]) -> u32 {
        self.count_sign_variations(
            &sequence
                .iter()
                .map(|coeffs| self.eval_sign_at_plus_inf(coeffs))
                .collect::<Vec<_>>(),
        )
    }

    pub fn sign_variations_at_zero(&self, sequence: &[Upolynomial]) -> u32 {
        self.count_sign_variations(
            &sequence
                .iter()
                .map(|coeffs| self.eval_sign_at_zero(coeffs))
                .collect::<Vec<_>>(),
        )
    }

    pub fn sign_variations_at(&self, sequence: &[Upolynomial], value: &Mpbq) -> u32 {
        self.count_sign_variations(
            &sequence
                .iter()
                .map(|coeffs| self.eval_sign_at_bq(coeffs, value))
                .collect::<Vec<_>>(),
        )
    }

    // Root bounds.

    /// knuth_positive_root_upper_bound: k with every positive root below 2^k.
    pub fn knuth_positive_root_upper_bound(&self, coeffs: &[Int]) -> u32 {
        if coeffs.is_empty() {
            return 0;
        }
        let mut max = 0;
        let degree = coeffs.len() - 1;
        let is_leading_positive = coeffs[degree].is_positive();
        let log2_leading = get_log2(&coeffs[degree]);
        for k in 1..=degree {
            let coeff = &coeffs[degree - k];
            if coeff.is_zero() || coeff.is_positive() == is_leading_positive {
                continue;
            }
            let log2_coeff = get_log2(coeff);
            if log2_leading > log2_coeff {
                continue;
            }
            let current = log2_coeff + 1 - log2_leading;
            let k = k as i64;
            let bound = if current % k == 0 {
                current / k
            } else {
                current.div_euclid(k) + 1
            };
            if bound > max {
                max = bound;
            }
        }
        (max + 1) as u32
    }

    pub fn knuth_negative_root_upper_bound(&self, coeffs: &[Int]) -> u32 {
        self.knuth_positive_root_upper_bound(&self.p_minus_x(coeffs))
    }

    /// nonzero_root_lower_bound: k with every nonzero root of absolute value above 1/2^k.
    pub fn nonzero_root_lower_bound(&self, coeffs: &[Int]) -> u32 {
        let reversed = self.p1_div_x(&self.remove_zero_roots(coeffs));
        self.knuth_positive_root_upper_bound(&reversed)
            .max(self.knuth_negative_root_upper_bound(&reversed))
    }

    // Root isolation by Descartes' rule of signs.

    /// push_child_frames: the halves (0, 1/2) and (1/2, 1), as 2^n p(x/2) and its translation.
    fn push_child_frames(&self, coeffs: &[Int], frames: &mut Vec<DrsFrame>) {
        let parent = frames.len().checked_sub(1);
        let left = self.normalize(&self.compose2n_p_x_div2(coeffs));
        let right = self.normalize(&self.translate(&left));
        frames.push(DrsFrame {
            parent,
            coeffs: left,
            is_first: true,
            is_left: true,
        });
        frames.push(DrsFrame {
            parent,
            coeffs: right,
            is_first: true,
            is_left: false,
        });
    }

    /// The interval (0, 1), or the point 1/2, of the top frame mapped back through its ancestors.
    fn map_to_root(&self, frames: &[DrsFrame], value: &Mpbq) -> Mpbq {
        let mut result = value.clone();
        let mut index = frames.len().checked_sub(1);
        while let Some(current) = index {
            result = if frames[current].is_left {
                result.div2()
            } else {
                result.add(&Mpbq::one()).div2()
            };
            index = frames[current].parent;
        }
        result
    }

    fn drs_isolate01_roots(&self, coeffs: &[Int], result: &mut IsolatedRoots) {
        let bound = self.descartes_bound01(coeffs);
        if bound == 0 {
            return;
        }
        if bound == 1 {
            result.lowers.push(Mpbq::zero());
            result.uppers.push(Mpbq::one());
            return;
        }
        let half = Mpbq::of(Int::one(), 1);
        let mut frames: Vec<DrsFrame> = Vec::new();
        let two_x_minus_one = [Int::from(-1), Int::from(2)];
        if self.has_one_half_root(coeffs) {
            result.roots.push(half.clone());
            self.push_child_frames(&self.div(coeffs, &two_x_minus_one), &mut frames);
        } else {
            self.push_child_frames(coeffs, &mut frames);
        }
        while let Some(frame) = frames.last_mut() {
            if !frame.is_first {
                frames.pop();
                continue;
            }
            frame.is_first = false;
            let frame_coeffs = frame.coeffs.clone();
            let frame_bound = self.descartes_bound01(&frame_coeffs);
            if frame_bound == 0 {
                frames.pop();
                continue;
            }
            if frame_bound == 1 {
                result.lowers.push(self.map_to_root(&frames, &Mpbq::zero()));
                result.uppers.push(self.map_to_root(&frames, &Mpbq::one()));
                frames.pop();
                continue;
            }
            if self.has_one_half_root(&frame_coeffs) {
                result.roots.push(self.map_to_root(&frames, &half));
                self.push_child_frames(&self.div(&frame_coeffs, &two_x_minus_one), &mut frames);
            } else {
                self.push_child_frames(&frame_coeffs, &mut frames);
            }
        }
    }

    /// drs_isolate_roots: the positive roots in (0, 2^k) and the negative ones in (-2^k', 0), each
    /// found as the roots in (0, 1) of p(2^k x) or p(-2^k' x) and scaled back.
    fn drs_isolate_roots(&self, coeffs: &[Int], result: &mut IsolatedRoots) {
        let normalized = self.normalize(coeffs);
        let negative_k = self.knuth_negative_root_upper_bound(coeffs);
        let positive_k = negative_k.max(self.knuth_positive_root_upper_bound(coeffs));
        let isolate_scaled =
            |scaled: &[Int], k: u32, is_negated: bool, result: &mut IsolatedRoots| {
                let roots_start = result.roots.len();
                let bounds_start = result.lowers.len();
                self.drs_isolate01_roots(&self.compose_p2k_x(scaled, k), result);
                let adjust = |values: &mut Vec<Mpbq>, start: usize| {
                    for value in &mut values[start..] {
                        let scaled_value = value.mul2k(k);
                        *value = if is_negated {
                            scaled_value.neg()
                        } else {
                            scaled_value
                        };
                    }
                };
                adjust(&mut result.roots, roots_start);
                adjust(&mut result.lowers, bounds_start);
                adjust(&mut result.uppers, bounds_start);
                bounds_start
            };
        isolate_scaled(&normalized, positive_k, false, result);
        let negative_start = isolate_scaled(&self.p_minus_x(&normalized), negative_k, true, result);
        for index in negative_start..result.lowers.len() {
            let lower = result.lowers[index].clone();
            result.lowers[index] = result.uppers[index].clone();
            result.uppers[index] = lower;
        }
    }

    /// sqf_isolate_roots: the roots of a square-free polynomial, exact roots first when zero is
    /// one, then the isolating intervals of the others.
    pub fn sqf_isolate_roots(&self, coeffs: &[Int]) -> IsolatedRoots {
        let mut result = IsolatedRoots {
            roots: Vec::new(),
            lowers: Vec::new(),
            uppers: Vec::new(),
        };
        if self.has_zero_roots(coeffs) {
            result.roots.push(Mpbq::zero());
            self.drs_isolate_roots(&self.remove_zero_roots(coeffs), &mut result);
        } else {
            self.drs_isolate_roots(coeffs, &mut result);
        }
        result
    }

    // Sturm sequences.

    fn sturm_seq_core(&self, mut sequence: Vec<Upolynomial>) -> Vec<Upolynomial> {
        loop {
            let remainder = self.srem(&sequence[sequence.len() - 2], &sequence[sequence.len() - 1]);
            if remainder.is_empty() {
                return sequence;
            }
            sequence.push(self.normalize(&remainder));
        }
    }

    pub fn sturm_seq(&self, coeffs: &[Int]) -> Vec<Upolynomial> {
        self.sturm_seq_core(vec![coeffs.to_vec(), self.derivative(coeffs)])
    }

    pub fn sturm_tarski_seq(&self, first: &[Int], second: &[Int]) -> Vec<Upolynomial> {
        self.sturm_seq_core(vec![
            first.to_vec(),
            self.mul(&self.derivative(first), second),
        ])
    }

    // Refinement.

    /// isolating2refinable: an isolating interval of a square-free polynomial turned into one whose
    /// endpoint signs differ, or the root it contains.
    pub fn isolating2refinable(&self, coeffs: &[Int], lower: &Mpbq, upper: &Mpbq) -> Refinement {
        let sign_lower = self.eval_sign_at_bq(coeffs, lower);
        let sign_upper = self.eval_sign_at_bq(coeffs, upper);
        if sign_lower != 0 && sign_upper != 0 {
            return Refinement {
                is_interval: true,
                lower: lower.clone(),
                upper: upper.clone(),
            };
        }
        if sign_lower == 0 && sign_upper != 0 {
            let a = lower;
            let mut b = upper.clone();
            let mut new_a = a.add(&b).div2();
            loop {
                let sign_new_a = self.eval_sign_at_bq(coeffs, &new_a);
                if sign_new_a != sign_upper {
                    return Refinement {
                        is_interval: sign_new_a != 0,
                        lower: new_a,
                        upper: b,
                    };
                }
                b = new_a;
                new_a = b.add(a).div2();
            }
        }
        if sign_lower != 0 && sign_upper == 0 {
            let mut a = lower.clone();
            let b = upper;
            let mut new_b = a.add(b).div2();
            loop {
                let sign_new_b = self.eval_sign_at_bq(coeffs, &new_b);
                if sign_new_b != sign_lower {
                    return if sign_new_b == 0 {
                        Refinement {
                            is_interval: false,
                            lower: new_b,
                            upper: b.clone(),
                        }
                    } else {
                        Refinement {
                            is_interval: true,
                            lower: a,
                            upper: new_b,
                        }
                    };
                }
                a = new_b;
                new_b = b.add(&a).div2();
            }
        }
        let a1 = lower;
        let b2 = upper;
        let mut b1 = a1.add(b2).div2();
        let mut a2 = b1.clone();
        let sign_b1 = self.eval_sign_at_bq(coeffs, &b1);
        let sign_a2 = sign_b1;
        if sign_b1 == 0 {
            return Refinement {
                is_interval: false,
                lower: b1,
                upper: upper.clone(),
            };
        }
        let mut new_a1 = a1.add(&b1).div2();
        let mut new_b2 = a2.add(b2).div2();
        loop {
            let sign_new_a1 = self.eval_sign_at_bq(coeffs, &new_a1);
            if sign_new_a1 == 0 {
                return Refinement {
                    is_interval: false,
                    lower: new_a1,
                    upper: upper.clone(),
                };
            }
            if sign_new_a1 == -sign_b1 {
                return Refinement {
                    is_interval: true,
                    lower: new_a1,
                    upper: b1,
                };
            }
            let sign_new_b2 = self.eval_sign_at_bq(coeffs, &new_b2);
            if sign_new_b2 == 0 {
                return Refinement {
                    is_interval: false,
                    lower: new_b2,
                    upper: upper.clone(),
                };
            }
            if sign_new_b2 == -sign_a2 {
                return Refinement {
                    is_interval: true,
                    lower: a2,
                    upper: new_b2,
                };
            }
            b1 = new_a1;
            new_a1 = b1.add(a1).div2();
            a2 = new_b2;
            new_b2 = b2.add(&a2).div2();
        }
    }

    /// refine_core: one bisection of a refinable interval, or the root at its midpoint.
    pub fn refine_core(
        &self,
        coeffs: &[Int],
        sign_lower: i32,
        lower: &Mpbq,
        upper: &Mpbq,
    ) -> Refinement {
        let middle = lower.add(upper).div2();
        let sign_middle = self.eval_sign_at_bq(coeffs, &middle);
        if sign_middle == 0 {
            return Refinement {
                is_interval: false,
                lower: middle,
                upper: upper.clone(),
            };
        }
        if sign_middle == sign_lower {
            Refinement {
                is_interval: true,
                lower: middle,
                upper: upper.clone(),
            }
        } else {
            Refinement {
                is_interval: true,
                lower: lower.clone(),
                upper: middle,
            }
        }
    }

    pub fn refine(&self, coeffs: &[Int], lower: &Mpbq, upper: &Mpbq) -> Refinement {
        self.refine_core(coeffs, self.eval_sign_at_bq(coeffs, lower), lower, upper)
    }

    /// refine_core with a precision: bisects until the interval is narrower than 1/2^k.
    pub fn refine_to_precision(
        &self,
        coeffs: &[Int],
        lower: &Mpbq,
        upper: &Mpbq,
        precision: u32,
    ) -> Refinement {
        let sign_lower = self.eval_sign_at_bq(coeffs, lower);
        let mut current = Refinement {
            is_interval: true,
            lower: lower.clone(),
            upper: upper.clone(),
        };
        loop {
            if current
                .upper
                .sub(&current.lower)
                .is_less_than_one_div2k(precision)
            {
                return current;
            }
            current = self.refine_core(coeffs, sign_lower, &current.lower, &current.upper);
            if !current.is_interval {
                return current;
            }
        }
    }

    /// convert_q2bq_interval: a rational isolating interval (a, b) as a binary rational one (c, d),
    /// or the root itself in c.
    pub fn convert_q2bq_interval(&self, coeffs: &[Int], a: &Rational, b: &Rational) -> Refinement {
        let sign_a = self.eval_sign_at_q(coeffs, a);
        let sign_b = self.eval_sign_at_q(coeffs, b);
        let c;
        let mut d = Mpbq::zero();
        let mut is_found_d = false;
        let lower_of_a = Mpbq::from_rational(a);
        if lower_of_a.1 {
            c = lower_of_a.0;
        } else {
            let mut lower = lower_of_a.0;
            let mut upper = lower.mul2k(1);
            if a.num().is_negative() {
                std::mem::swap(&mut lower, &mut upper);
            }
            while upper.compare_rational(b) >= 0 {
                (lower, upper) = refine_upper(a, &lower, &upper);
            }
            loop {
                let sign_upper = self.eval_sign_at_bq(coeffs, &upper);
                if sign_upper == 0 {
                    return Refinement {
                        is_interval: false,
                        lower: upper.clone(),
                        upper,
                    };
                }
                if sign_upper == sign_a {
                    c = upper;
                    break;
                }
                if !is_found_d {
                    is_found_d = true;
                    d = upper.clone();
                }
                (lower, upper) = refine_upper(a, &lower, &upper);
            }
        }
        if is_found_d {
            return Refinement {
                is_interval: true,
                lower: c,
                upper: d,
            };
        }
        let lower_of_b = Mpbq::from_rational(b);
        if lower_of_b.1 {
            return Refinement {
                is_interval: true,
                lower: c,
                upper: lower_of_b.0,
            };
        }
        let mut lower = lower_of_b.0;
        let mut upper = lower.mul2k(1);
        if b.num().is_negative() {
            std::mem::swap(&mut lower, &mut upper);
        }
        while lower.compare(&c) <= 0 {
            (lower, upper) = refine_lower(b, &lower, &upper);
        }
        loop {
            let sign_lower = self.eval_sign_at_bq(coeffs, &lower);
            if sign_lower == 0 {
                return Refinement {
                    is_interval: false,
                    lower,
                    upper,
                };
            }
            if sign_lower == sign_b {
                return Refinement {
                    is_interval: true,
                    lower: c,
                    upper: lower,
                };
            }
            (lower, upper) = refine_lower(b, &lower, &upper);
        }
    }

    /// normalize_interval_core: a refinable interval around zero shrunk to the side of zero
    /// holding the root, given the sign at its lower end, as (lower, upper). None when zero is the
    /// root.
    pub fn normalize_interval(
        &self,
        coeffs: &[Int],
        lower: &Mpbq,
        upper: &Mpbq,
        sign_lower: i32,
    ) -> Option<(Mpbq, Mpbq)> {
        if !(lower.is_neg() && upper.is_pos()) {
            return Some((lower.clone(), upper.clone()));
        }
        if self.has_zero_roots(coeffs) {
            return None;
        }
        if sign_lower == self.eval_sign_at_zero(coeffs) {
            Some((Mpbq::zero(), upper.clone()))
        } else {
            Some((lower.clone(), Mpbq::zero()))
        }
    }

    /// get_root_id: the number of roots up to l.
    pub fn get_root_id(&self, coeffs: &[Int], lower: &Mpbq) -> u32 {
        let sequence = self.sturm_seq(coeffs);
        self.sign_variations_at_minus_inf(&sequence) - self.sign_variations_at(&sequence, lower)
    }
}

#[cfg(test)]
mod tests {
    use super::super::test_util::read_fixture;
    use super::super::{Int, Rational};
    use super::{Mpbq, UpolynomialManager};

    fn parse_rational(text: &str) -> Rational {
        let parts: Vec<&str> = text.split('/').collect();
        Rational::of(
            parts[0].parse().expect("an integer"),
            parts.get(1).unwrap_or(&"1").parse().expect("an integer"),
        )
    }

    fn show_coeffs(coeffs: &[Int]) -> String {
        let shown: Vec<String> = coeffs.iter().map(Int::to_string).collect();
        format!(" [{}]", shown.join(" "))
    }

    fn show_flag(is_true: bool) -> String {
        format!(" {}", if is_true { 1 } else { 0 })
    }

    // Isolates the roots of the square-free part, then makes each interval refinable, refines it
    // to width 1/2^20, and reports the root's index and the interval normalized around zero.
    fn show_isolation(um: &mut UpolynomialManager, coeffs: &[Int]) -> String {
        let square_free = um.square_free(coeffs);
        let isolated = um.sqf_isolate_roots(&square_free);
        let refined: Vec<String> = isolated
            .lowers
            .iter()
            .enumerate()
            .map(|(index, lower)| {
                let refinable =
                    um.isolating2refinable(&square_free, lower, &isolated.uppers[index]);
                if !refinable.is_interval {
                    return format!(" root {}", refinable.lower);
                }
                let result =
                    um.refine_to_precision(&square_free, &refinable.lower, &refinable.upper, 20);
                let root_id = um.get_root_id(&square_free, &result.lower);
                if !result.is_interval {
                    return format!(
                        " int {} {} proot {} id{root_id}",
                        refinable.lower, refinable.upper, result.lower
                    );
                }
                let sign_lower = um.eval_sign_at_bq(&square_free, &result.lower);
                let normalized =
                    um.normalize_interval(&square_free, &result.lower, &result.upper, sign_lower);
                let shown_normalized = match normalized {
                    None => format!(" n0 {} {}", result.lower, result.upper),
                    Some((lower, upper)) => format!(" n1 {lower} {upper}"),
                };
                format!(
                    " int {} {} p {} {} id{root_id}{shown_normalized}",
                    refinable.lower, refinable.upper, result.lower, result.upper
                )
            })
            .collect();
        let roots: String = isolated
            .roots
            .iter()
            .map(|root| format!(" {root}"))
            .collect();
        let intervals: String = isolated
            .lowers
            .iter()
            .enumerate()
            .map(|(index, lower)| format!(" {lower} {}", isolated.uppers[index]))
            .collect();
        format!(
            "{} roots{roots} intervals{intervals} refined{}",
            show_coeffs(&square_free),
            refined.join("")
        )
    }

    fn to_coeffs(um: &UpolynomialManager, operand: &[String]) -> Vec<Int> {
        um.set(
            &operand
                .iter()
                .map(|word| word.parse().expect("an integer"))
                .collect::<Vec<Int>>(),
        )
    }

    fn show_sequence(sequence: &[Vec<Int>]) -> String {
        sequence.iter().map(|coeffs| show_coeffs(coeffs)).collect()
    }

    // The harness commands: <op> <coefficients from the constant term up> [; <operand>]. The ops
    // starting with z take a prime first and run over Z_p.
    fn run_upolynomial_command(input: &str) -> String {
        let words: Vec<&str> = input.split(' ').collect();
        let op = words[0];
        let is_modular = op.starts_with('z');
        let operands: Vec<Vec<String>> = words[if is_modular { 2 } else { 1 }..]
            .join(" ")
            .split(" ; ")
            .map(|operand| {
                if operand.is_empty() {
                    Vec::new()
                } else {
                    operand.split(' ').map(str::to_string).collect()
                }
            })
            .collect();
        let mut um = UpolynomialManager::new(None);
        let first = to_coeffs(&um, &operands[0]);
        if is_modular {
            let prime: Int = words[1].parse().expect("a prime");
            let shown = um.with_zp(prime, |um| {
                let x = um.set(&first);
                let y = um.set(&to_coeffs(um, &operands[1]));
                match op {
                    "zgcd" => show_coeffs(&um.gcd(&x, &y)),
                    "zextgcd" => {
                        let result = um.ext_gcd(&x, &y).expect("ext_gcd over Z_p");
                        show_coeffs(&result.u) + &show_coeffs(&result.v) + &show_coeffs(&result.d)
                    }
                    "zdivrem" => {
                        let division = um.div_rem(&x, &y);
                        show_coeffs(&division.quotient) + &show_coeffs(&division.remainder)
                    }
                    "zsqf" => show_coeffs(&um.square_free(&x)),
                    "zsqfp" => show_flag(um.is_square_free(&x)),
                    "zmonic" => show_coeffs(&um.mk_monic(&x).expect("mk_monic over Z_p")),
                    "zdivides" => show_flag(um.divides(&x, &y)),
                    "zmul" => show_coeffs(&um.mul(&x, &y)),
                    _ => match um.exact_div(&x, &y) {
                        None => " 0".to_string(),
                        Some(exact) => format!(" 1{}", show_coeffs(&exact)),
                    },
                }
            });
            return format!("{op}{shown}");
        }
        let second = operands.get(1).cloned().unwrap_or_default();
        match op {
            "isolate" => format!("isolate{}", show_isolation(&mut um, &first)),
            "gcd" => {
                let second = to_coeffs(&um, &second);
                format!("gcd{}", show_coeffs(&um.gcd(&first, &second)))
            }
            "divrem" => {
                let division = um.div_rem(&first, &to_coeffs(&um, &second));
                format!(
                    "divrem {}{}{}",
                    division.power,
                    show_coeffs(&division.quotient),
                    show_coeffs(&division.remainder)
                )
            }
            "srem" => format!(
                "srem{}",
                show_coeffs(&um.srem(&first, &to_coeffs(&um, &second)))
            ),
            "exact" => match um.exact_div(&first, &to_coeffs(&um, &second)) {
                None => "exact 0".to_string(),
                Some(exact) => format!("exact 1{}", show_coeffs(&exact)),
            },
            "divides" => format!(
                "divides{}",
                show_flag(um.divides(&first, &to_coeffs(&um, &second)))
            ),
            "sqf" => format!("sqf{}", show_coeffs(&um.square_free(&first))),
            "sqfp" => format!("sqfp{}", show_flag(um.is_square_free(&first))),
            "sturm" => format!("sturm{}", show_sequence(&um.sturm_seq(&first))),
            "tarski" => format!(
                "tarski{}",
                show_sequence(&um.sturm_tarski_seq(&first, &to_coeffs(&um, &second)))
            ),
            "q2bq" => {
                let result = um.convert_q2bq_interval(
                    &first,
                    &parse_rational(&second[0]),
                    &parse_rational(&second[1]),
                );
                if result.is_interval {
                    format!("q2bq 1 {} {}", result.lower, result.upper)
                } else {
                    format!("q2bq 0 {}", result.lower)
                }
            }
            "knuth" => format!(
                "knuth {} {} {}",
                um.knuth_positive_root_upper_bound(&first),
                um.knuth_negative_root_upper_bound(&first),
                um.nonzero_root_lower_bound(&first)
            ),
            "flips" => format!(
                "flips{}{}{}",
                show_coeffs(&um.p_minus_x(&first)),
                show_coeffs(&um.p1_div_x(&first)),
                show_coeffs(&um.remove_zero_roots(&first))
            ),
            "transq" => format!(
                "transq{}",
                show_coeffs(&um.translate_q(&first, &parse_rational(&second[0])))
            ),
            "compq" => format!(
                "compq{}",
                show_coeffs(&um.compose_p_q_x(&first, &parse_rational(&second[0])))
            ),
            "signq" => format!(
                "signq {}",
                um.eval_sign_at_q(&first, &parse_rational(&second[0]))
            ),
            "signbq" => format!(
                "signbq {}",
                um.eval_sign_at_bq(
                    &first,
                    &Mpbq::of(
                        second[0].parse().expect("an integer"),
                        second[1].parse().expect("a k")
                    )
                )
            ),
            _ => format!(
                "pw{}",
                show_coeffs(&um.pw(&first, second[0].parse().expect("an exponent")))
            ),
        }
    }

    // Products of random factors up to degree 3, so with repeated, rational and irrational roots,
    // and what Z3's upolynomial manager computes for them: root isolation and refinement, gcds
    // over Z and Z_p, pseudo-division, Sturm sequences and the transformations algebraic numbers
    // use.
    #[test]
    fn computes_univariate_polynomials_as_z3() {
        let failures: Vec<String> = read_fixture("upolynomial.json")
            .into_iter()
            .filter_map(|(input, expected)| {
                let actual = run_upolynomial_command(&input);
                (actual != expected)
                    .then(|| format!("{input}\n  expected {expected}\n  actual   {actual}"))
            })
            .collect();
        assert!(failures.is_empty(), "{}", failures.join("\n"));
    }

    #[test]
    fn skips_primes_that_divide_a_leading_coefficient_in_the_modular_gcd() {
        let mut um = UpolynomialManager::new(None);
        let shared = vec![Int::from(-2), Int::from(39103 * 39107)];
        let first = um.mul(&[Int::from(3), Int::from(5), Int::from(7 * 39103)], &shared);
        let second = um.mul(&shared, &[Int::from(7), Int::from(1), Int::from(39103)]);
        assert_eq!(um.gcd(&first, &second), shared);
    }
}
