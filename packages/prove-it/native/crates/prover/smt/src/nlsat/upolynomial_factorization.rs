// Ported from Z3 (src/math/polynomial/upolynomial_factorization{.cpp,_int.h}, the factorization
// in src/math/polynomial/upolynomial.cpp, src/util/prime_generator.cpp and mpz_manager::root),
// MIT license, see z3-license.txt. Factorization of univariate integer polynomials: square-free
// decomposition, Berlekamp's algorithm in Z_p for small primes p, quadratic Hensel lifting to
// p^e above a Mignotte bound, and a search over combinations of the lifted factors (Zassenhaus).

use super::upolynomial::{Upolynomial, UpolynomialManager};
use super::{Int, SmtError};

const UINT_MAX: u32 = 4294967295;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FactorParams {
    /// Factor in Z_p for primes p up to max_prime.
    pub max_prime: u32,
    /// The number of factorizations in Z_p whose degree sets are intersected before lifting.
    pub prime_trials: u32,
    /// The most combinations of lifted factors the search tries.
    pub max_search_size: u32,
}

/// polynomial::factor_params(), which polynomial factorization and nlsat use.
pub const DEFAULT_FACTOR_PARAMS: FactorParams = FactorParams {
    max_prime: UINT_MAX,
    prime_trials: 4,
    max_search_size: UINT_MAX,
};

/// constant * factors[0]^degrees[0] * ... * factors[n]^degrees[n].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UpolynomialFactors {
    pub constant: Int,
    pub factors: Vec<Upolynomial>,
    pub degrees: Vec<u32>,
}

fn mk_factors() -> UpolynomialFactors {
    UpolynomialFactors {
        constant: Int::one(),
        factors: Vec::new(),
        degrees: Vec::new(),
    }
}

fn get_total_factors(fs: &UpolynomialFactors) -> u32 {
    fs.degrees.iter().sum()
}

fn get_total_degree(fs: &UpolynomialFactors) -> usize {
    fs.factors
        .iter()
        .enumerate()
        .map(|(index, factor)| (factor.len() - 1) * fs.degrees[index] as usize)
        .sum()
}

fn push_factor(um: &UpolynomialManager, fs: &mut UpolynomialFactors, factor: &[Int], degree: u32) {
    fs.factors.push(um.set(factor));
    fs.degrees.push(degree);
}

// factors::multiply
fn multiply_factors(um: &UpolynomialManager, fs: &UpolynomialFactors) -> Upolynomial {
    if fs.constant.is_zero() {
        return Vec::new();
    }
    let mut result = vec![um.normalize_numeral(&fs.constant)];
    for index in 0..fs.factors.len() {
        result = if fs.degrees[index] > 1 {
            um.mul(&result, &um.pw(&fs.factors[index], fs.degrees[index]))
        } else {
            um.mul(&result, &fs.factors[index])
        };
    }
    result
}

// prime_iterator: 2, 3, 5, 7, ...
fn mk_prime_iterator() -> impl FnMut() -> u64 {
    let mut current = 1u64;
    move || {
        current += 1;
        loop {
            let mut is_prime = true;
            let mut divisor = 2u64;
            while divisor * divisor <= current {
                if current.is_multiple_of(divisor) {
                    is_prime = false;
                    break;
                }
                divisor += 1;
            }
            if is_prime {
                return current;
            }
            current += 1;
        }
    }
}

// mpz_manager::root for n = 2: bisection from powers of two, returning the upper end when the
// square root is not an integer.
fn get_square_root(value: &Int) -> Int {
    if value.is_zero() {
        return value.clone();
    }
    let log2 = value.bit_length() - 1;
    let mut lower = Int::one() << (log2 / 2);
    let mut upper = Int::one() << (log2 + 1).div_ceil(2);
    if lower == upper {
        return lower;
    }
    loop {
        let middle = (&upper + &lower) >> 1;
        let square = &middle * &middle;
        if square == *value {
            return middle;
        }
        if middle == lower || middle == upper {
            return upper;
        }
        if square < *value {
            lower = middle;
        } else {
            upper = middle;
        }
    }
}

/// mpz_manager::is_perfect_square: the nonnegative square root, or None.
pub fn get_exact_square_root(value: &Int) -> Option<Int> {
    if value.is_negative() {
        return None;
    }
    let root = get_square_root(value);
    if &root * &root == *value {
        Some(root)
    } else {
        None
    }
}

// factorization_degree_set: the degrees that products of the factors can have.
fn get_degree_set(fs: &UpolynomialFactors) -> Vec<bool> {
    let mut set = vec![true];
    for index in 0..fs.factors.len() {
        let degree = fs.factors[index].len() - 1;
        for _count in 0..fs.degrees[index] {
            let shifted = [vec![false; degree], set.clone()].concat();
            set = shifted
                .iter()
                .enumerate()
                .map(|(position, is_in)| *is_in || set.get(position).copied().unwrap_or(false))
                .collect();
        }
    }
    set
}

fn is_trivial_degree_set(set: &[bool]) -> bool {
    for is_in in set.iter().take(set.len().saturating_sub(1)).skip(1) {
        if *is_in {
            return false;
        }
    }
    true
}

// berlekamp_matrix: Q - I, where row i of Q holds x^(p*i) modulo f.
struct BerlekampMatrix {
    zp: UpolynomialManager,
    matrix: Vec<Int>,
    size: usize,
    null_row: usize,
    column_pivot: Vec<Option<usize>>,
    row_pivot: Vec<Option<usize>>,
}

impl BerlekampMatrix {
    fn new(zp: &UpolynomialManager, f: &[Int]) -> BerlekampMatrix {
        let size = f.len() - 1;
        let prime = zp_number(zp);
        let mut matrix = vec![Int::one()];
        matrix.extend((0..size).map(|_unused| Int::zero()));
        let mut this = BerlekampMatrix {
            zp: zp.clone(),
            matrix,
            size,
            null_row: 1,
            column_pivot: vec![None; size],
            row_pivot: vec![None; size],
        };
        let mut row = 0;
        let mut previous_row = 0;
        let mut k = 1u64;
        loop {
            if k % prime == 1 {
                row += 1;
                if row >= size {
                    break;
                }
                this.matrix.extend((0..size).map(|_unused| Int::zero()));
            }
            let multiplier = this.get(previous_row, size - 1).clone();
            for column in (1..size).rev() {
                this.put(
                    row,
                    column,
                    this.get(previous_row, column - 1) - &multiplier * &f[column],
                );
            }
            this.put(row, 0, -(&f[0] * &multiplier));
            previous_row = row;
            k += 1;
        }
        for index in 0..size {
            this.put(index, index, this.get(index, index) - Int::one());
        }
        this
    }

    fn get(&self, row: usize, column: usize) -> &Int {
        &self.matrix[row * self.size + column]
    }

    fn put(&mut self, row: usize, column: usize, value: Int) {
        self.matrix[row * self.size + column] = self.zp.normalize_numeral(&value);
    }

    // diagonalize: column operations that turn each pivot into -1. Returns the rank of the null
    // space.
    fn diagonalize(&mut self) -> Result<usize, SmtError> {
        let mut null_rank = 0;
        for row in 0..self.size {
            let mut is_column_found = false;
            for column in 0..self.size {
                if self.column_pivot[column].is_some() || self.get(row, column).is_zero() {
                    continue;
                }
                is_column_found = true;
                self.column_pivot[column] = Some(row);
                self.row_pivot[row] = Some(column);
                let pivot_multiplier = self
                    .zp
                    .normalize_numeral(&-self.zp.inv(self.get(row, column))?);
                for other in self.null_row..self.size {
                    self.put(other, column, self.get(other, column) * &pivot_multiplier);
                }
                for other_column in 0..self.size {
                    if other_column == column {
                        continue;
                    }
                    let multiplier = self.get(row, other_column).clone();
                    for other in self.null_row..self.size {
                        self.put(
                            other,
                            other_column,
                            self.get(other, other_column) + &multiplier * self.get(other, column),
                        );
                    }
                }
            }
            if !is_column_found {
                null_rank += 1;
            }
        }
        Ok(null_rank)
    }

    // next_null_space_vector: the next basis vector of the null space, skipping [1, 0, ..., 0].
    fn next_null_space_vector(&mut self) -> Option<Vec<Int>> {
        while self.null_row < self.size {
            if self.row_pivot[self.null_row].is_some() {
                self.null_row += 1;
                continue;
            }
            let vector = (0..self.size)
                .map(|column| match self.row_pivot[column] {
                    Some(pivot_column) => self.get(self.null_row, pivot_column).clone(),
                    None if column == self.null_row => Int::one(),
                    None => Int::zero(),
                })
                .collect();
            self.null_row += 1;
            return Some(vector);
        }
        None
    }
}

// Number(zp.zp): the modulus of Z_p, which the callers set.
fn zp_number(zp: &UpolynomialManager) -> u64 {
    zp.zp()
        .and_then(Int::to_i64)
        .and_then(|prime| u64::try_from(prime).ok())
        .expect("a small prime modulus")
}

// zp_factor_square_free_berlekamp, deterministic: splits the monic square-free f in Z_p with
// gcd(v - s, f) for the null space vectors v of Q - I. Returns false when f is irreducible.
fn factor_square_free_in_zp(
    zp: &mut UpolynomialManager,
    f: &[Int],
    fs: &mut UpolynomialFactors,
) -> Result<bool, SmtError> {
    let prime = zp_number(zp);
    let mut matrix = BerlekampMatrix::new(zp, f);
    let first_factor = fs.factors.len();
    push_factor(zp, fs, f, 1);
    let null_rank = matrix.diagonalize()?;
    if null_rank == 1 {
        return Ok(false);
    }
    let mut vector = matrix.next_null_space_vector();
    while let Some(basis_vector) = vector {
        let mut trimmed = zp.set(&basis_vector);
        let factor_end = fs.factors.len();
        for factor_index in first_factor..factor_end {
            if fs.factors[factor_index].len() == 2 {
                continue;
            }
            for _shift in 0..prime {
                let current = fs.factors[factor_index].clone();
                trimmed[0] = zp.normalize_numeral(&(&trimmed[0] - Int::one()));
                let common = zp.gcd(&trimmed, &current);
                if common.len() != 1 && common.len() != current.len() {
                    fs.factors[factor_index] = zp.div(&current, &common);
                    push_factor(zp, fs, &common, 1);
                }
                if fs.factors.len() - first_factor == null_rank {
                    return Ok(true);
                }
            }
        }
        vector = matrix.next_null_space_vector();
    }
    Ok(true)
}

struct HenselPolynomials<'a> {
    u: &'a [Int],
    a: &'a [Int],
    v: &'a [Int],
    b: &'a [Int],
    c: &'a [Int],
}

struct LiftedFactors {
    a: Upolynomial,
    b: Upolynomial,
}

// hensel_lift: from C = A*B (mod b) and U*A + V*B = 1 (mod r) with r | b, the A1 = A (mod b) and
// B1 = B (mod b) with C = A1*B1 (mod b*r), deg(A1) = deg(A) and lc(A1) = lc(A).
fn hensel_lift_once(
    z: &UpolynomialManager,
    b: &Int,
    r: &Int,
    polynomials: &HenselPolynomials<'_>,
) -> LiftedFactors {
    let zr = UpolynomialManager::new(Some(r.clone()));
    let f = zr.set(&z.div_const(
        &z.sub(polynomials.c, &z.mul(polynomials.a, polynomials.b)),
        b,
    ));
    let division = zr.div_rem(&zr.mul(polynomials.v, &f), polynomials.a);
    let t = zr.add(
        &zr.mul(polynomials.u, &f),
        &zr.mul(polynomials.b, &division.quotient),
    );
    LiftedFactors {
        a: z.add(polynomials.a, &z.mul_const(&division.remainder, b)),
        b: z.add(polynomials.b, &z.mul_const(&t, b)),
    }
}

// hensel_lift_quadratic: lifts C = A*B from Z_p to Z_(p^e), squaring the modulus of zpe and
// lifting U*A + V*B = 1 along with A and B.
fn hensel_lift_quadratic(
    z: &UpolynomialManager,
    c: &[Int],
    zpe: &mut UpolynomialManager,
    a: &[Int],
    b: &[Int],
    e: u32,
) -> Result<LiftedFactors, SmtError> {
    let zp = UpolynomialManager::new(zpe.zp().cloned());
    let ext = zp.ext_gcd(a, b)?;
    let mut u = ext.u;
    let mut v = ext.v;
    let mut current_a = a.to_vec();
    let mut current_b = b.to_vec();
    let mut k = 1u32;
    while k < e {
        let modulus = zpe.zp().cloned().expect("Z_(p^e)");
        let lifted = hensel_lift_once(
            z,
            &modulus,
            &modulus,
            &HenselPolynomials {
                u: &u,
                a: &current_a,
                v: &v,
                b: &current_b,
                c,
            },
        );
        let g = zpe.set(&z.div_const(
            &z.sub(
                &z.sub(&[Int::one()], &z.mul(&lifted.a, &u)),
                &z.mul(&lifted.b, &v),
            ),
            &modulus,
        ));
        let division = zpe.div_rem(&zpe.mul(&g, &v), &current_a);
        let s = zpe.add(&zpe.mul(&g, &u), &zpe.mul(&division.quotient, &current_b));
        u = z.add(&u, &z.mul_const(&s, &modulus));
        v = z.add(&v, &z.mul_const(&division.remainder, &modulus));
        zpe.square_modulus()?;
        u = zpe.set(&u);
        v = zpe.set(&v);
        current_a = zpe.set(&lifted.a);
        current_b = zpe.set(&lifted.b);
        k *= 2;
    }
    Ok(LiftedFactors {
        a: current_a,
        b: current_b,
    })
}

// hensel_lift: the monic factors of f in Z_p lifted one by one to Z_(p^e), the last one carrying
// lc(f) until it is divided out.
fn hensel_lift_factors(
    z: &UpolynomialManager,
    f: &[Int],
    zp: &UpolynomialManager,
    zp_fs: &UpolynomialFactors,
    e: u32,
    zpe: &mut UpolynomialManager,
) -> Result<UpolynomialFactors, SmtError> {
    let prime = zp.zp().cloned().expect("Z_p");
    let mut zpe_fs = mk_factors();
    zpe.set_zp(prime.clone());
    let mut parts = z.set(f);
    let mut b = Vec::new();
    for index in 0..zp_fs.factors.len().saturating_sub(1) {
        let a = zp.set(&zp_fs.factors[index]);
        let c = if index > 0 {
            zp.set(&parts)
        } else {
            zp.mul_const(
                &multiply_factors(zp, zp_fs),
                &zp.normalize_numeral(&f[f.len() - 1]),
            )
        };
        zpe.set_zp(prime.clone());
        let lifted = hensel_lift_quadratic(z, &parts, zpe, &a, &zp.div(&c, &a), e)?;
        b = lifted.b;
        if index == 0 {
            parts = zpe.set(f);
        }
        parts = zpe.div(&parts, &lifted.a);
        zpe_fs.factors.push(lifted.a);
        zpe_fs.degrees.push(1);
    }
    zpe_fs
        .factors
        .push(zpe.mul_const(&b, &zpe.inv(&f[f.len() - 1])?));
    zpe_fs.degrees.push(1);
    Ok(zpe_fs)
}

// mignotte_bound: the e, a power of two, with p^e above 2^n * (|f| + |lc(f)|) for n = deg(f)/2,
// which bounds twice the coefficients of the factors of degree at most n.
fn get_mignotte_bound(f: &[Int], prime: &Int) -> u32 {
    let mut square_norm = Int::zero();
    for coeff in f {
        if !coeff.is_zero() {
            square_norm += coeff * coeff;
        }
    }
    let leading = &f[f.len() - 1];
    let bound = (Int::one() << ((f.len() - 1) / 2) as u64)
        * (get_square_root(&square_norm) + leading.abs());
    let mut e = 1;
    let mut power = prime.clone();
    while power <= bound {
        power = &power * &power;
        e *= 2;
    }
    e
}

// ufactorization_combination_iterator: the subsets of the enabled factors, smallest first and at
// most half of them, whose degree is in the degree set. Selected factors that turn out to be true
// factors are removed from later subsets.
struct CombinationIterator<'a> {
    zpe: &'a UpolynomialManager,
    fs: &'a UpolynomialFactors,
    degree_set: &'a [bool],
    total_size: usize,
    max_size: usize,
    is_enabled: Vec<bool>,
    current_size: usize,
    current: Vec<i64>,
}

impl<'a> CombinationIterator<'a> {
    fn new(
        zpe: &'a UpolynomialManager,
        fs: &'a UpolynomialFactors,
        degree_set: &'a [bool],
    ) -> CombinationIterator<'a> {
        let count = fs.factors.len();
        CombinationIterator {
            zpe,
            fs,
            degree_set,
            total_size: count,
            max_size: count / 2,
            is_enabled: vec![true; count],
            current_size: 0,
            current: vec![count as i64; count + 1],
        }
    }

    fn find(&self, position: usize, upper_bound: i64) -> i64 {
        let mut candidate = self.current[position] + 1;
        while candidate < upper_bound && !self.is_enabled[candidate as usize] {
            candidate += 1;
        }
        if candidate == upper_bound {
            -1
        } else {
            candidate
        }
    }

    fn next(&mut self, is_removing_current: bool) -> bool {
        let max_upper_bound = self.fs.factors.len() as i64;
        let mut is_removing = is_removing_current;
        loop {
            let mut position = self.current_size as i64 - 1;
            let mut value = -1;
            if is_removing {
                position = self.current_size as i64 - 1;
                while position > 0 {
                    self.is_enabled[self.current[position as usize] as usize] = false;
                    self.current[position as usize] = max_upper_bound;
                    position -= 1;
                }
                self.is_enabled[self.current[0] as usize] = false;
                is_removing = false;
                self.total_size -= self.current_size;
                self.max_size = self.total_size / 2;
            }
            while position >= 0 {
                value = self.find(position as usize, self.current[position as usize + 1]);
                if value >= 0 {
                    self.current[position as usize] = value;
                    break;
                }
                position -= 1;
            }
            loop {
                if value == -1 {
                    if self.current_size >= self.max_size {
                        return false;
                    }
                    self.current_size += 1;
                    self.current[0] = -1;
                    position = 0;
                    value = self.find(position as usize, max_upper_bound);
                    if value == -1 {
                        return false;
                    }
                    self.current[position as usize] = value;
                }
                position += 1;
                while position < self.current_size as i64 {
                    self.current[position as usize] = self.current[position as usize - 1];
                    value = self.find(position as usize, max_upper_bound);
                    if value == -1 {
                        self.current[0] = -1;
                        break;
                    }
                    self.current[position as usize] = value;
                    position += 1;
                }
                if value != -1 {
                    break;
                }
            }
            if self
                .degree_set
                .get(self.get_current_degree())
                .copied()
                .unwrap_or(false)
            {
                return true;
            }
        }
    }

    fn get_current_degree(&self) -> usize {
        let mut degree = 0;
        for index in 0..self.current_size {
            degree += self.fs.factors[self.current[index] as usize].len() - 1;
        }
        degree
    }

    // The enabled factors outside the selection, in order.
    fn get_rest(&self) -> Vec<usize> {
        let mut rest = Vec::new();
        let mut selected = 0;
        for factor in 0..self.fs.factors.len() {
            if !self.is_enabled[factor] {
                continue;
            }
            if selected >= self.current.len() || (factor as i64) < self.current[selected] {
                rest.push(factor);
            } else {
                selected += 1;
            }
        }
        rest
    }

    fn get_left(&self) -> Upolynomial {
        let mut result = self.zpe.set(&self.fs.factors[self.current[0] as usize]);
        for index in 1..self.current_size {
            result = self
                .zpe
                .mul(&result, &self.fs.factors[self.current[index] as usize]);
        }
        result
    }

    fn get_right(&self) -> Upolynomial {
        let mut result = Vec::new();
        for factor in self.get_rest() {
            result = if result.is_empty() {
                self.zpe.set(&self.fs.factors[factor])
            } else {
                self.zpe.mul(&result, &self.fs.factors[factor])
            };
        }
        result
    }

    // get_left_tail_coeff, get_right_tail_coeff: m times the constant terms of the side's factors.
    fn get_left_tail_coeff(&self, multiplier: &Int) -> Int {
        let mut result = self.zpe.normalize_numeral(multiplier);
        for index in 0..self.current_size {
            result = self
                .zpe
                .normalize_numeral(&(&result * &self.fs.factors[self.current[index] as usize][0]));
        }
        result
    }

    fn get_right_tail_coeff(&self, multiplier: &Int) -> Int {
        let mut result = self.zpe.normalize_numeral(multiplier);
        for factor in self.get_rest() {
            result = self
                .zpe
                .normalize_numeral(&(&result * &self.fs.factors[factor][0]));
        }
        result
    }
}

fn divides(divisor: &Int, dividend: &Int) -> bool {
    if divisor.is_zero() {
        dividend.is_zero()
    } else {
        (dividend % divisor).is_zero()
    }
}

/// factor_square_free: the factors of the primitive square-free f in Z[x], each pushed with
/// multiplicity k. Returns false when a limit in params stopped the search, leaving a factor that
/// may be reducible.
pub fn factor_square_free(
    z: &UpolynomialManager,
    f: &[Int],
    fs: &mut UpolynomialFactors,
    k: u32,
    params: &FactorParams,
) -> Result<bool, SmtError> {
    let mut f_pp = z.set(f);
    if f_pp.last().is_some_and(Int::is_negative) {
        f_pp = f_pp.iter().map(|coeff| -coeff).collect();
        if k % 2 == 1 {
            fs.constant = -&fs.constant;
        }
    }
    let mut zp = UpolynomialManager::new(Some(Int::from(2)));
    let mut zp_fs = mk_factors();
    let mut zp_fs_prime = Int::from(2);
    let mut degree_set = vec![true];
    let mut get_next_prime = mk_prime_iterator();
    let mut trials = 0;
    while trials <= params.prime_trials {
        let next_prime = get_next_prime();
        if next_prime > u64::from(params.max_prime) {
            push_factor(z, fs, &f_pp, k);
            return Ok(false);
        }
        let prime = Int::from(next_prime as i64);
        zp.set_zp(prime.clone());
        if (&f_pp[f_pp.len() - 1] % &prime).is_zero() {
            continue;
        }
        let f_pp_zp = zp.set(&f_pp);
        if !zp.is_square_free(&f_pp_zp) {
            continue;
        }
        let mut current_fs = mk_factors();
        let monic = zp.mk_monic(&f_pp_zp)?;
        if !factor_square_free_in_zp(&mut zp, &monic, &mut current_fs)? {
            push_factor(z, fs, &f_pp, k);
            return Ok(true);
        }
        let current_degree_set = get_degree_set(&current_fs);
        degree_set = if degree_set.len() == 1 {
            current_degree_set
        } else {
            degree_set
                .iter()
                .enumerate()
                .map(|(degree, is_in)| {
                    *is_in && current_degree_set.get(degree).copied().unwrap_or(false)
                })
                .collect()
        };
        if is_trivial_degree_set(&degree_set) {
            push_factor(z, fs, &f_pp, k);
            return Ok(true);
        }
        trials += 1;
        if zp_fs.factors.is_empty() || get_total_factors(&zp_fs) > get_total_factors(&current_fs) {
            zp_fs = current_fs;
            zp_fs_prime = prime;
        }
    }
    zp.set_zp(zp_fs_prime.clone());
    let mut zpe = UpolynomialManager::new(Some(zp_fs_prime.clone()));
    let zpe_fs = hensel_lift_factors(
        z,
        &f_pp,
        &zp,
        &zp_fs,
        get_mignotte_bound(&f_pp, &zp_fs_prime),
        &mut zpe,
    )?;
    let mut leading = zpe.normalize_numeral(&f_pp[f_pp.len() - 1]);
    f_pp = z.mul_const(&f_pp, &leading);
    let mut iterator = CombinationIterator::new(&zpe, &zpe_fs, &degree_set);
    let half_degree = get_total_degree(&zp_fs) / 2;
    let mut result = true;
    let mut is_removing = false;
    let mut counter = 0u64;
    while iterator.next(is_removing) {
        counter += 1;
        if counter > u64::from(params.max_search_size) {
            result = false;
            break;
        }
        let is_using_left = iterator.get_current_degree() <= half_degree;
        let tail = if is_using_left {
            iterator.get_left_tail_coeff(&leading)
        } else {
            iterator.get_right_tail_coeff(&leading)
        };
        if !divides(&tail, &f_pp[0]) {
            is_removing = false;
            continue;
        }
        let trial = zpe.mul_const(
            &if is_using_left {
                iterator.get_left()
            } else {
                iterator.get_right()
            },
            &leading,
        );
        let Some(quotient) = z.exact_div(&f_pp, &trial) else {
            is_removing = false;
            continue;
        };
        // The factor is the side of degree at most half, which the bound makes recoverable. The
        // search continues with the other side.
        push_factor(
            z,
            fs,
            &z.get_primitive(if is_using_left { &trial } else { &quotient }),
            k,
        );
        f_pp = z.get_primitive(if is_using_left { &quotient } else { &trial });
        leading = f_pp[f_pp.len() - 1].clone();
        f_pp = z.mul_const(&f_pp, &leading);
        is_removing = true;
    }
    if f_pp.len() > 1 {
        push_factor(z, fs, &z.div_const(&f_pp, &leading), k);
    }
    Ok(result)
}

// factor_2_sqf_pp: a square-free primitive quadratic splits when its discriminant is a square.
fn factor_quadratic(z: &UpolynomialManager, p: &[Int], fs: &mut UpolynomialFactors, k: u32) {
    let Some(root) = get_exact_square_root(&(&p[1] * &p[1] - Int::from(4) * &p[2] * &p[0])) else {
        push_factor(z, fs, p, k);
        return;
    };
    push_factor(
        z,
        fs,
        &z.normalize(&[&p[1] - &root, Int::from(2) * &p[2]]),
        k,
    );
    push_factor(
        z,
        fs,
        &z.normalize(&[&p[1] + &root, Int::from(2) * &p[2]]),
        k,
    );
}

// factor_sqf_pp
fn factor_sqf_pp(
    z: &UpolynomialManager,
    p: &[Int],
    fs: &mut UpolynomialFactors,
    k: u32,
    params: &FactorParams,
) -> Result<bool, SmtError> {
    if p.len() <= 2 {
        push_factor(z, fs, p, k);
        return Ok(true);
    }
    if p.len() == 3 {
        factor_quadratic(z, p, fs, k);
        return Ok(true);
    }
    factor_square_free(z, p, fs, k, params)
}

// flip_factor_sign_if_lm_neg
fn flip_factor_sign_if_lm_neg(p: &[Int], fs: &mut UpolynomialFactors, k: u32) -> Upolynomial {
    if p.last().is_none_or(|leading| !leading.is_negative()) {
        return p.to_vec();
    }
    if k % 2 == 1 {
        fs.constant = -&fs.constant;
    }
    p.iter().map(|coeff| -coeff).collect()
}

/// manager::factor: the content and the irreducible factors of p with their multiplicities, by
/// Yun's square-free decomposition. The flag is false when a limit in params left a factor that
/// may be reducible (TS `{ isComplete, factors }`).
pub fn factor_upolynomial(
    z: &mut UpolynomialManager,
    p: &[Int],
    params: &FactorParams,
) -> Result<(bool, UpolynomialFactors), SmtError> {
    let mut fs = mk_factors();
    if p.len() <= 1 {
        fs.constant = p.first().cloned().unwrap_or_else(Int::zero);
        return Ok((true, fs));
    }
    fs.constant = z.get_content(p);
    let primitive = z.get_primitive(p);
    let derivative = z.derivative(&primitive);
    let mut square = z.gcd(&primitive, &derivative);
    if square.len() <= 1 {
        let flipped = flip_factor_sign_if_lm_neg(&primitive, &mut fs, 1);
        let is_complete = factor_sqf_pp(z, &flipped, &mut fs, 1, params)?;
        return Ok((is_complete, fs));
    }
    let mut is_complete = true;
    let mut product = z
        .exact_div(&primitive, &square)
        .expect("the gcd divides the polynomial");
    let mut multiplicity = 1;
    while product.len() > 1 {
        let next = z.gcd(&product, &square);
        let factor = z
            .exact_div(&product, &next)
            .expect("the gcd divides the polynomial");
        if factor.len() > 1 {
            let flipped = flip_factor_sign_if_lm_neg(&factor, &mut fs, multiplicity);
            if !factor_sqf_pp(z, &flipped, &mut fs, multiplicity, params)? {
                is_complete = false;
            }
        } else if factor.first() == Some(&Int::from(-1)) && multiplicity % 2 == 1 {
            fs.constant = -&fs.constant;
        }
        square = z
            .exact_div(&square, &next)
            .expect("the gcd divides the polynomial");
        product = next;
        multiplicity += 1;
    }
    Ok((is_complete, fs))
}

#[cfg(test)]
mod tests {
    use super::super::Int;
    use super::super::test_util::read_fixture;
    use super::super::upolynomial::UpolynomialManager;
    use super::{DEFAULT_FACTOR_PARAMS, FactorParams, factor_upolynomial};

    fn show_coeffs(coeffs: &[Int]) -> String {
        format!(
            " [{}]",
            coeffs
                .iter()
                .map(Int::to_string)
                .collect::<Vec<_>>()
                .join(" ")
        )
    }

    // factor <coefficients> with polynomial::factor_params(), afactor with the algebraic number
    // module's limits.
    fn run_factor_command(input: &str) -> String {
        let words: Vec<&str> = input.split(' ').collect();
        let mut um = UpolynomialManager::new(None);
        let params = if words[0] == "afactor" {
            FactorParams {
                max_prime: 31,
                prime_trials: 1,
                max_search_size: 5000,
            }
        } else {
            DEFAULT_FACTOR_PARAMS
        };
        let coeffs: Vec<Int> = words[1..]
            .iter()
            .map(|word| word.parse::<Int>().expect("an integer"))
            .collect();
        let coeffs = um.set(&coeffs);
        let (is_complete, factors) =
            factor_upolynomial(&mut um, &coeffs, &params).expect("factoring succeeds");
        let shown: String = factors
            .factors
            .iter()
            .enumerate()
            .map(|(index, factor)| format!("{}^{}", show_coeffs(factor), factors.degrees[index]))
            .collect();
        format!(
            "{} {} {}{}",
            words[0],
            if is_complete { 1 } else { 0 },
            factors.constant,
            shown
        )
    }

    // Products of random factors up to degree 15, some with Swinnerton-Dyer style polynomials such
    // as x^4 - 10x^2 + 1 that split modulo every prime, factored as Z3 does: Berlekamp in Z_p,
    // Hensel lifting and the search over combinations of lifted factors.
    #[test]
    fn factors_the_fixture_polynomials() {
        let failures: Vec<String> = read_fixture("upolynomial-factorization.json")
            .into_iter()
            .filter_map(|(input, expected)| {
                let actual = run_factor_command(&input);
                (actual != expected)
                    .then(|| format!("{input}\n  expected {expected}\n  actual   {actual}"))
            })
            .collect();
        assert!(failures.is_empty(), "{}", failures.join("\n"));
    }

    // A double's square root of a 60-digit discriminant is off by about 2^44, so a search from it
    // does not end.
    #[test]
    fn factors_a_quadratic_whose_discriminant_is_past_the_precision_of_a_double() {
        let root: Int = "1234567890123456789012345678901"
            .parse()
            .expect("an integer");
        let five = Int::from(5);
        assert_eq!(
            run_factor_command(&format!("factor {} {} 1", &five * &root, -(&root + &five))),
            format!("factor 1 1 [{} 1]^1 [-5 1]^1", -&root)
        );
        let constant = &five * &root + Int::one();
        assert_eq!(
            run_factor_command(&format!("factor {} {} 1", constant, -(&root + &five))),
            format!("factor 1 1 [{} {} 1]^1", constant, -(&root + &five))
        );
    }
}
