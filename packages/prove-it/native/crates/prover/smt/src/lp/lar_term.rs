// Ported from Z3 (src/math/lp/lar_term.h), MIT license, see z3-license.txt. A linear combination of
// columns, kept in a u_map so that its iteration order is Z3's.
use crate::lp::numeric_pair::Impq;
use crate::util::hashtable::{ObjMap, get_identity_hash};
use crate::util::rational::Rational;

#[derive(Clone)]
pub struct LarTerm {
    pub coeffs: ObjMap<Rational>,
    // -1 in TypeScript until the term has a column.
    pub column: usize,
}

pub const NO_COLUMN: usize = usize::MAX;

impl Default for LarTerm {
    fn default() -> LarTerm {
        LarTerm::new()
    }
}

impl LarTerm {
    pub fn new() -> LarTerm {
        LarTerm {
            coeffs: ObjMap::new(get_identity_hash),
            column: NO_COLUMN,
        }
    }

    pub fn from_entries<'a>(entries: impl IntoIterator<Item = (usize, &'a Rational)>) -> LarTerm {
        let mut term = LarTerm::new();
        for (column, coeff) in entries {
            term.add_monomial(coeff, column);
        }
        term
    }

    pub fn size(&self) -> usize {
        self.coeffs.len()
    }

    // The (column, coefficient) entries in Z3's slot order.
    pub fn iter(&self) -> impl Iterator<Item = (usize, &Rational)> + '_ {
        self.coeffs.iter().map(|entry| (entry.0 as usize, entry.1))
    }

    pub fn get(&self, column: usize) -> Option<&Rational> {
        self.coeffs.get(column as u32)
    }

    pub fn clear(&mut self) {
        self.coeffs.clear();
    }

    pub fn add_monomial(&mut self, coeff: &Rational, column: usize) {
        if coeff.is_zero() {
            return;
        }
        let key = column as u32;
        let Some(existing) = self.coeffs.get(key) else {
            self.coeffs.insert(key, coeff.clone());
            return;
        };
        let sum = existing.add(coeff);
        if sum.is_zero() {
            self.coeffs.remove(key);
        } else {
            self.coeffs.replace(key, sum);
        }
    }

    // apply: the value of the term at the column values.
    pub fn apply(&self, values: &[Impq]) -> Impq {
        let mut value = Impq::zero();
        for (column, coeff) in self.iter() {
            value = value.add(&values[column].mul(coeff));
        }
        value
    }

    // subst_by_term: replaces the term column by its definition.
    pub fn subst_by_term(&mut self, term: &LarTerm, term_column: usize) {
        let Some(coeff) = self.coeffs.get(term_column as u32).cloned() else {
            return;
        };
        self.coeffs.remove(term_column as u32);
        for (column, entry) in term.iter() {
            self.add_monomial(&coeff.mul(entry), column);
        }
    }

    // get_normalized_by_min_var: the term divided by its first coefficient, and that coefficient.
    // None stands for the term itself, which TypeScript returns unchanged.
    pub fn get_normalized(&self) -> (Option<LarTerm>, Rational) {
        let entries: Vec<(usize, Rational)> = self
            .iter()
            .map(|entry| (entry.0, entry.1.clone()))
            .collect();
        if entries.is_empty() {
            return (None, Rational::one());
        }
        let coeff = entries[0].1.clone();
        if coeff.is_one() {
            return (None, coeff);
        }
        let mut term = LarTerm::new();
        term.add_monomial(&Rational::one(), entries[0].0);
        for entry in &entries[1..] {
            term.add_monomial(&entry.1.div(&coeff), entry.0);
        }
        (Some(term), coeff)
    }
}
