// Ported from Z3 (src/math/lp/hnf_cutter.cpp, and get_equality_and_right_side_for_term_on_current_x
// in src/math/lp/lar_solver.cpp), MIT license, see z3-license.txt. Cuts from proofs: the integer
// terms tight at the current solution form A x = b; with A in Hermite normal form H, a row of
// H^-1 b that is fractional gives a cut that every integer solution meets.
use std::collections::HashMap;
use std::collections::hash_map::Entry;

use prove_num::Rational;

use crate::lp::dependency::Dependency;
use crate::lp::hnf::{
    GeneralMatrix, get_determinant_of_rectangular_matrix, get_hermite_normal_form,
};
use crate::lp::int_solver::{Lia, LiaMove};

// The -1 of find_cut_row_index: no entry is fractional.
const NO_ROW: usize = usize::MAX;

struct TightTerm {
    // The index of the term in lar_solver's terms.
    term: usize,
    is_upper: bool,
    right_side: Rational,
    dep: Dependency,
}

// get_equality_and_right_side_for_term_on_current_x: the non-strict bound of an integer term that
// its current value meets, without infinitesimals.
fn get_tight_term(lia: &Lia<'_, '_>, term_index: usize) -> Option<TightTerm> {
    let solver = &*lia.lra;
    let term = &solver.terms[term_index];
    let column = term.column;
    if !solver.is_int(column) {
        return None;
    }
    let mut right_side = Rational::zero();
    for entry in term.iter() {
        let value = solver.get_value(entry.0);
        if !value.y.is_zero() {
            return None;
        }
        right_side = right_side.add(&value.x.mul(entry.1));
    }
    let upper_witness = solver.get_upper_witness(column);
    let upper = solver.get_upper_bound(column);
    if upper_witness.is_some() && !upper.y.is_negative() && right_side == upper.x {
        return Some(TightTerm {
            term: term_index,
            is_upper: true,
            right_side,
            dep: upper_witness.clone(),
        });
    }
    let lower_witness = solver.get_lower_witness(column);
    let lower = solver.get_lower_bound(column);
    if lower_witness.is_some() && !lower.y.is_positive() && right_side == lower.x {
        return Some(TightTerm {
            term: term_index,
            is_upper: false,
            right_side: right_side.neg(),
            dep: lower_witness.clone(),
        });
    }
    None
}

// find_cut_row_index: a fractional entry, drawn uniformly by reservoir sampling.
fn find_cut_row_index(lia: &mut Lia<'_, '_>, values: &[Rational]) -> usize {
    let mut result = NO_ROW;
    let mut count = 0;
    for (index, value) in values.iter().enumerate() {
        if value.is_int() {
            continue;
        }
        if count == 0 {
            count = 1;
            result = index;
        } else {
            count += 1;
            if lia
                .lra
                .settings_mut()
                .get_random_next()
                .is_multiple_of(count)
            {
                result = index;
            }
        }
    }
    result
}

// make_hnf_cut: the cut, in the term and the explanation of the integer solver.
#[expect(
    clippy::needless_range_loop,
    reason = "a literal port of Z3's matrix loops, which index rows i, j, k and l together"
)]
pub fn make_hnf_cut(lia: &mut Lia<'_, '_>) -> LiaMove {
    let limit_on_rows = lia.lra.settings().limit_on_rows_for_hnf_cutter;
    let limit_on_columns = lia.lra.settings().limit_on_columns_for_hnf_cutter;
    let mut tight_terms = Vec::new();
    let mut columns = Vec::new();
    // Only looked up, never iterated.
    let mut local_columns = HashMap::new();
    let mut abs_max = Rational::zero();
    for term_index in 0..lia.lra.terms.len() {
        if tight_terms.len() >= limit_on_rows || columns.len() >= limit_on_columns {
            continue;
        }
        let Some(tight) = get_tight_term(lia, term_index) else {
            continue;
        };
        tight_terms.push(tight);
        for entry in lia.lra.terms[term_index].iter() {
            if let Entry::Vacant(vacant) = local_columns.entry(entry.0) {
                vacant.insert(columns.len());
                columns.push(entry.0);
            }
            let magnitude = entry.1.ceil().abs();
            if magnitude.compare(&abs_max).is_gt() {
                abs_max = magnitude;
            }
        }
    }
    if columns
        .iter()
        .all(|column| lia.lra.get_value(*column).is_int())
    {
        return LiaMove::Undef;
    }
    let mut matrix = GeneralMatrix::new(tight_terms.len(), columns.len());
    for (row, tight) in tight_terms.iter().enumerate() {
        let sign = if tight.is_upper {
            Rational::one()
        } else {
            Rational::minus_one()
        };
        for entry in lia.lra.terms[tight.term].iter() {
            matrix.data[row][local_columns.get(&entry.0).copied().unwrap_or(0)] = sign.mul(entry.1);
        }
    }
    let mut basis_rows = Vec::new();
    let big_number = abs_max.mul(&abs_max).mul(&abs_max);
    let d = get_determinant_of_rectangular_matrix(&matrix, &mut basis_rows, &big_number);
    if d.compare(&big_number).is_ge() || lia.lra.settings().is_canceled() {
        return LiaMove::Undef;
    }
    let is_full_rank = basis_rows.len() == tight_terms.len();
    matrix.shrink_to_rank(&basis_rows);
    let deps: Vec<Dependency> = if is_full_rank {
        tight_terms.iter().map(|tight| tight.dep.clone()).collect()
    } else {
        basis_rows
            .iter()
            .map(|row| tight_terms[*row].dep.clone())
            .collect()
    };
    let settings = lia.lra.settings();
    let Some(h) = get_hermite_normal_form(&matrix, &d, &|| settings.is_canceled()) else {
        return LiaMove::Undef;
    };
    let mut b: Vec<Rational> = if is_full_rank {
        tight_terms
            .iter()
            .map(|tight| tight.right_side.clone())
            .collect()
    } else {
        basis_rows
            .iter()
            .map(|row| tight_terms[*row].right_side.clone())
            .collect()
    };
    for i in 0..h.len() {
        for j in 0..i {
            b[i] = b[i].sub(&h[i][j].mul(&b[j]));
        }
        b[i] = b[i].div(&h[i][i]);
    }
    let cut_row = find_cut_row_index(lia, &b);
    if cut_row == NO_ROW {
        return LiaMove::Undef;
    }
    // get_ei_H_minus_1: the row cutRow of the inverse of H.
    let mut inverse_row = vec![Rational::zero(); matrix.get_column_count()];
    inverse_row[cut_row] = Rational::one().div(&h[cut_row][cut_row]);
    for k in (0..cut_row).rev() {
        let mut sum = Rational::zero();
        for l in k + 1..=cut_row {
            sum = sum.add(&h[l][k].mul(&inverse_row[l]));
        }
        inverse_row[k] = sum.neg().div(&h[k][k]);
    }
    for column in 0..matrix.get_column_count() {
        let mut coeff = Rational::zero();
        for row in 0..matrix.get_row_count() {
            coeff = coeff.add(&inverse_row[row].mul(matrix.get(row, column)));
        }
        if !coeff.is_zero() {
            lia.lia.term.add_monomial(&coeff, columns[column]);
        }
    }
    lia.lia.explanation.clear();
    for dep in &deps {
        lia.lia.explanation.push_dependency(dep);
    }
    LiaMove::Cut {
        offset: b[cut_row].floor(),
        is_upper: true,
    }
}
