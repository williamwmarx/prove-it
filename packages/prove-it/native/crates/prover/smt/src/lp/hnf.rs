// Ported from Z3 (src/math/lp/hnf.h, src/math/lp/general_matrix.h,
// src/math/lp/permutation_matrix.h, and the extended gcd of src/util/mpz.cpp), MIT license, see
// z3-license.txt. The Hermite normal form of an integer matrix, computed modulo a multiple of the
// determinant of its rows, as the HNF cutter needs it.
use std::cmp::Ordering;

use prove_num::Int;

use crate::util::rational::Rational;

// rem of mpq: the remainder of the numerators, truncated toward zero.
fn get_rem(first: &Rational, second: &Rational) -> Rational {
    Rational::from_int(first.num() % second.num())
}

struct ExtendedGcd {
    gcd: Rational,
    u: Rational,
    v: Rational,
}

// mpz_manager::gcd(r1, r2, a, b, g): the gcd g of r1 and r2, with a * r1 + b * r2 equal to it.
fn get_extended_gcd(first: &Rational, second: &Rational) -> ExtendedGcd {
    let mut left = first.num().abs();
    let mut right = second.num().abs();
    let mut a = Int::one();
    let mut b = Int::zero();
    let mut next_a = Int::zero();
    let mut next_b = Int::one();
    if left < right {
        std::mem::swap(&mut left, &mut right);
        std::mem::swap(&mut a, &mut b);
        std::mem::swap(&mut next_a, &mut next_b);
    }
    while right.is_positive() {
        let quotient = &left / &right;
        let remainder = &left % &right;
        left = std::mem::replace(&mut right, remainder);
        let following_a = &a - &(&quotient * &next_a);
        a = std::mem::replace(&mut next_a, following_a);
        let following_b = &b - &(&quotient * &next_b);
        b = std::mem::replace(&mut next_b, following_b);
    }
    ExtendedGcd {
        gcd: Rational::from_int(left),
        u: Rational::from_int(if first.num().is_negative() { -a } else { a }),
        v: Rational::from_int(if second.num().is_negative() { -b } else { b }),
    }
}

struct MinimalUv {
    d: Rational,
    u: Rational,
    v: Rational,
}

// extended_gcd_minimal_uv: the gcd d of a and b with a * u + b * v = d, where v is the smallest
// coefficient of its residue class with the sign of -b.
fn get_extended_gcd_minimal_uv(a: &Rational, b: &Rational) -> MinimalUv {
    if a.is_zero() {
        return MinimalUv {
            d: b.clone(),
            u: Rational::zero(),
            v: Rational::one(),
        };
    }
    if b.is_zero() {
        return MinimalUv {
            d: a.clone(),
            u: Rational::one(),
            v: Rational::zero(),
        };
    }
    let result = get_extended_gcd(a, b);
    let mut d = result.gcd;
    let mut u = result.u;
    let mut v = result.v;
    if d.is_negative() {
        d = d.neg();
        u = u.neg();
        v = v.neg();
    }
    if &d == a {
        return MinimalUv {
            d,
            u: Rational::one(),
            v: Rational::zero(),
        };
    }
    if d == a.neg() {
        return MinimalUv {
            d,
            u: Rational::minus_one(),
            v: Rational::zero(),
        };
    }
    let a_over_d = a.abs().div(&d);
    let mut k = Rational::from_int(v.num() / a_over_d.num());
    let mut r = Rational::from_int(v.num() % a_over_d.num());
    if r.is_negative() {
        r = r.add(&a_over_d);
        k = k.sub(&Rational::one());
    }
    let b_over_d = b.div(&d);
    let shift = if b.is_positive() {
        k.add(&Rational::one())
    } else {
        k
    };
    v = if b.is_positive() { r.sub(&a_over_d) } else { r };
    u = if a.is_positive() {
        u.add(&shift.mul(&b_over_d))
    } else {
        u.sub(&shift.mul(&b_over_d))
    };
    MinimalUv { d, u, v }
}

// permutation_matrix: a permutation and its inverse.
#[derive(Clone)]
struct Permutation {
    forward: Vec<usize>,
    reverse: Vec<usize>,
}

impl Permutation {
    fn identity(length: usize) -> Permutation {
        Permutation {
            forward: (0..length).collect(),
            reverse: (0..length).collect(),
        }
    }

    fn set_value(&mut self, index: usize, value: usize) {
        self.forward[index] = value;
        self.reverse[value] = index;
    }

    fn transpose_from_left(&mut self, first: usize, second: usize) {
        let first_index = self.reverse[first];
        let second_index = self.reverse[second];
        self.set_value(first_index, second);
        self.set_value(second_index, first);
    }

    fn transpose_from_right(&mut self, first: usize, second: usize) {
        let first_value = self.forward[first];
        let second_value = self.forward[second];
        self.set_value(first, second_value);
        self.set_value(second, first_value);
    }
}

// general_matrix: dense rows behind a row and a column permutation.
#[derive(Clone)]
pub struct GeneralMatrix {
    row_permutation: Permutation,
    column_permutation: Permutation,
    pub data: Vec<Vec<Rational>>,
}

impl GeneralMatrix {
    pub fn new(row_count: usize, column_count: usize) -> GeneralMatrix {
        GeneralMatrix {
            row_permutation: Permutation::identity(row_count),
            column_permutation: Permutation::identity(column_count),
            data: vec![vec![Rational::zero(); column_count]; row_count],
        }
    }

    pub fn get_row_count(&self) -> usize {
        self.data.len()
    }

    pub fn get_column_count(&self) -> usize {
        self.data.first().map_or(0, Vec::len)
    }

    pub fn adjust_row(&self, row: usize) -> usize {
        self.row_permutation.forward[row]
    }

    pub fn get(&self, row: usize, column: usize) -> &Rational {
        &self.data[self.adjust_row(row)][self.column_permutation.reverse[column]]
    }

    pub fn set(&mut self, row: usize, column: usize, value: Rational) {
        let data_row = self.adjust_row(row);
        let data_column = self.column_permutation.reverse[column];
        self.data[data_row][data_column] = value;
    }

    pub fn transpose_rows(&mut self, first: usize, second: usize) {
        self.row_permutation.transpose_from_right(first, second);
    }

    pub fn transpose_columns(&mut self, first: usize, second: usize) {
        self.column_permutation.transpose_from_left(first, second);
    }

    // shrink_to_rank: only the given data rows, leaving the permutations as they are.
    pub fn shrink_to_rank(&mut self, basis_rows: &[usize]) {
        if basis_rows.len() == self.get_row_count() {
            return;
        }
        self.data = basis_rows
            .iter()
            .map(|row| self.data[*row].clone())
            .collect();
    }
}

// prepare_pivot_for_lower_triangle: moves a nonzero entry of the lower right block to (r, r).
fn prepare_pivot(matrix: &mut GeneralMatrix, r: usize) -> bool {
    for row in r..matrix.get_row_count() {
        for column in r..matrix.get_column_count() {
            if matrix.get(row, column).is_zero() {
                continue;
            }
            if row != r {
                matrix.transpose_rows(row, r);
            }
            if column != r {
                matrix.transpose_columns(column, r);
            }
            return true;
        }
    }
    false
}

// pivot_column_non_fractional: a fraction-free elimination step under (r, r); false when an entry
// reaches the big number.
fn pivot_column_non_fractional(
    matrix: &mut GeneralMatrix,
    r: usize,
    big_number: &Rational,
) -> bool {
    let pivot = matrix.get(r, r).clone();
    let denominator = if r > 0 {
        Some(matrix.get(r - 1, r - 1).clone())
    } else {
        None
    };
    for column in r + 1..matrix.get_column_count() {
        let top = matrix.get(r, column).clone();
        for row in r + 1..matrix.get_row_count() {
            let mut value = matrix
                .get(row, column)
                .mul(&pivot)
                .sub(&matrix.get(row, r).mul(&top));
            if let Some(denominator) = &denominator {
                value = value.div(denominator);
            }
            let is_big = value.compare(big_number) != Ordering::Less;
            matrix.set(row, column, value);
            if is_big {
                return false;
            }
        }
    }
    true
}

// determinant_of_rectangular_matrix: the gcd of the last row of the triangulated matrix, a
// multiple of the gcd of its maximal minors, and the data rows of a basis; the big number when an
// entry grows too large.
pub fn get_determinant_of_rectangular_matrix(
    matrix: &GeneralMatrix,
    basis_rows: &mut Vec<usize>,
    big_number: &Rational,
) -> Rational {
    let mut triangle = matrix.clone();
    let mut rank = 0;
    while rank < triangle.get_row_count() {
        if !prepare_pivot(&mut triangle, rank) {
            break;
        }
        if !pivot_column_non_fractional(&mut triangle, rank, big_number) {
            return big_number.clone();
        }
        rank += 1;
    }
    if rank == 0 {
        return Rational::one();
    }
    for row in 0..rank {
        basis_rows.push(triangle.adjust_row(row));
    }
    let last = rank - 1;
    let mut gcd = Rational::zero();
    let mut column = last;
    while column < triangle.get_column_count() && gcd.is_zero() {
        let value = triangle.get(last, column);
        if !value.is_zero() {
            gcd = value.abs();
        }
        column += 1;
    }
    while column < triangle.get_column_count() {
        let value = triangle.get(last, column);
        if !value.is_zero() {
            gcd = get_extended_gcd(&gcd, value).gcd;
        }
        column += 1;
    }
    gcd
}

// hnf: W, the Hermite normal form of the rows of the matrix, computed modulo d. None when
// canceled.
pub fn get_hermite_normal_form(
    matrix: &GeneralMatrix,
    d: &Rational,
    is_canceled: &dyn Fn() -> bool,
) -> Option<Vec<Vec<Rational>>> {
    let mut w = matrix.data.clone();
    let row_count = matrix.get_row_count();
    let column_count = matrix.get_column_count();
    if row_count == 0 || column_count == 0 || d.is_zero() {
        return Some(w);
    }
    let two = Rational::from_i64(2);
    let mut buffer: Vec<Rational> = vec![Rational::zero(); row_count];
    let mut r = d.clone();
    let mut half_r = r.div(&two).floor();
    let get_mod_balanced = |value: &Rational, r: &Rational, half_r: &Rational| {
        let rem = get_rem(value, r);
        if rem.compare(half_r) == Ordering::Greater {
            return rem.sub(r);
        }
        if rem.compare(&half_r.neg()) == Ordering::Less {
            rem.add(r)
        } else {
            rem
        }
    };
    let get_mod = |value: &Rational, r: &Rational| {
        let rem = get_rem(value, r);
        if rem.is_negative() { rem.add(r) } else { rem }
    };
    for i in 0..row_count {
        if is_canceled() {
            return None;
        }
        for j in i + 1..column_count {
            let result = get_extended_gcd_minimal_uv(&w[i][i], &w[i][j]);
            if result.d.is_zero() {
                continue;
            }
            let ii_over_d = get_mod(&w[i][i].div(&result.d), &r);
            let ij_over_d = get_mod(&w[i][j].div(&result.d), &r);
            for k in i..row_count {
                buffer[k] =
                    get_mod_balanced(
                        &get_mod_balanced(&result.u.mul(&w[k][i]), &r, &half_r)
                            .add(&get_mod_balanced(&result.v.mul(&w[k][j]), &r, &half_r)),
                        &r,
                        &half_r,
                    );
            }
            w[i][j] = Rational::zero();
            for k in i + 1..row_count {
                w[k][j] = get_mod_balanced(
                    &get_mod_balanced(&ij_over_d.neg().mul(&w[k][i]), &r, &half_r)
                        .add(&get_mod_balanced(&ii_over_d.mul(&w[k][j]), &r, &half_r)),
                    &r,
                    &half_r,
                );
            }
            for k in i..row_count {
                w[k][i] = buffer[k].clone();
            }
        }
        let mut gcd = r.clone();
        let mut u = Rational::one();
        if w[i][i].is_zero() {
            w[i][i] = r.clone();
        } else {
            let result = get_extended_gcd_minimal_uv(&w[i][i], &r);
            gcd = result.d;
            u = result.u;
        }
        w[i][i] = get_mod(&w[i][i].mul(&u), &r);
        if w[i][i].is_zero() {
            w[i][i] = gcd;
        }
        let diagonal = w[i][i].clone();
        for k in i + 1..row_count {
            w[k][i] = get_mod_balanced(&w[k][i].mul(&u), &r, &half_r);
        }
        for j in 0..i {
            let value = w[i][j].clone();
            if !value.is_positive() && value.neg().compare(&diagonal) == Ordering::Less {
                continue;
            }
            let quotient = value.div(&diagonal).ceil();
            for k in i..row_count {
                w[k][j] = w[k][j].sub(&quotient.mul(&w[k][i]));
            }
        }
        r = r.div(&w[i][i]);
        half_r = r.div(&two).floor();
    }
    Some(w)
}
