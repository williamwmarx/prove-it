//! Ported from Z3 (src/math/polynomial/polynomial.{h,cpp}, src/math/polynomial/polynomial_cache.cpp),
//! MIT license, see z3-license.txt. Multivariate polynomials over the integers for nlsat, with
//! Z3's factorization: univariate through upolynomial-factorization, quadratics through the square
//! root of the discriminant, and higher degrees through bivariate Hensel lifting. A polynomial
//! keeps its monomials in the order Z3's som buffers produce, with a monomial of maximal degree in
//! the maximal variable first, because factorization breaks ties on the order in which variables
//! occur.
//!
//! Deviations from Z3, which only change the order of equal results:
//! - gcd computes with Z3's subresultant PRS (gcd_prs), not its modular algorithms (mod_gcd,
//!   uni_mod_gcd). Both return the same polynomial, normalized to a positive leading coefficient,
//!   but its monomials may come out in another order. Z3's modular gcd can also return a constant
//!   other than 1 for coprime primitive polynomials, gcd(2x - 3, 2x - 1) = 2
//!   (polynomial.cpp:4815), where this port returns 1. The callers in scope only test whether
//!   the gcd is constant.
//! - Polynomial ids count up from zero. Z3 recycles the ids of deleted polynomials, so where nlsat
//!   breaks a tie between two root functions on their ids it may pick the other one. Matching Z3
//!   would take explicit reference counts at its roughly 490 polynomial_ref sites in polynomial,
//!   algebraic_numbers, explain, levelwise and nra, and every pm routine allocating the same
//!   temporaries as Z3's, not just returning the same result. Random differential tests hit such
//!   a tie in about 1 of 300 levelwise and 1 of 3,000 explain programs, and no corpus trace yet.
//!
//! In Rust a monomial is an id into the manager's monomial table, which holds its variables and
//! degrees (`rename` rewrites them in place), and a polynomial is a shared node whose terms sit in
//! a `RefCell`, because `lex_sort` and `make_first_maximal` reorder a shared polynomial in place,
//! as the TypeScript and Z3 do.

use std::cell::{Cell, Ref, RefCell};
use std::collections::{HashMap, HashSet};
use std::mem;
use std::rc::Rc;

use super::upolynomial::{Upolynomial, UpolynomialManager};
use super::upolynomial_factorization::{
    DEFAULT_FACTOR_PARAMS, UpolynomialFactors, factor_square_free, get_exact_square_root,
};
use super::{Int, Rational, SmtError, get_gcd};

pub type Var = i32;
pub const NULL_VAR: Var = -1;

// s_factor_eval_values and s_factor_primes: the points multivariate factorization evaluates the
// other variables at, and the primes it lifts modulo.
const FACTOR_EVAL_VALUES: [i64; 7] = [0, 1, -1, 2, -2, 3, -3];
const FACTOR_PRIMES: [i64; 4] = [39103, 104729, 1000003, 100000007];

// mpz div: rounds toward minus infinity.
fn floor_div(dividend: &Int, divisor: &Int) -> Int {
    let quotient = dividend / divisor;
    if !(dividend % divisor).is_zero() && dividend.is_negative() != divisor.is_negative() {
        quotient - Int::one()
    } else {
        quotient
    }
}

/// The arithmetic t_eval evaluates in: rationals, intervals or algebraic numbers.
pub trait ValueOps<T> {
    #[expect(clippy::wrong_self_convention, reason = "the TS name, fromInteger")]
    fn from_integer(&mut self, value: &Int) -> T;
    fn add(&mut self, first: &T, second: &T) -> Result<T, SmtError>;
    fn mul(&mut self, first: &T, second: &T) -> Result<T, SmtError>;
    fn power(&mut self, base: &T, exponent: u32) -> Result<T, SmtError>;
}

// RATIONAL_OPS
struct RationalOps;

impl ValueOps<Rational> for RationalOps {
    fn from_integer(&mut self, value: &Int) -> Rational {
        Rational::from_int(value.clone())
    }

    fn add(&mut self, first: &Rational, second: &Rational) -> Result<Rational, SmtError> {
        Ok(first.add(second))
    }

    fn mul(&mut self, first: &Rational, second: &Rational) -> Result<Rational, SmtError> {
        Ok(first.mul(second))
    }

    fn power(&mut self, base: &Rational, exponent: u32) -> Result<Rational, SmtError> {
        Ok(base.pow(exponent))
    }
}

/// A monomial: its id in the manager's monomial table.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Monomial(u32);

// vars and degrees change only when the manager renames the variables.
struct MonomialData {
    vars: Vec<Var>,
    degrees: Vec<u32>,
    total_degree: u32,
}

impl MonomialData {
    fn new(vars: Vec<Var>, degrees: Vec<u32>) -> MonomialData {
        let mut total = 0;
        for degree in &degrees {
            total += degree;
        }
        MonomialData {
            vars,
            degrees,
            total_degree: total,
        }
    }

    fn size(&self) -> usize {
        self.vars.len()
    }

    fn max_var(&self) -> Var {
        self.vars.last().copied().unwrap_or(NULL_VAR)
    }

    fn max_var_degree(&self) -> u32 {
        self.degrees.last().copied().unwrap_or(0)
    }

    fn degree_of(&self, variable: Var) -> u32 {
        self.vars
            .iter()
            .position(|current| *current == variable)
            .map_or(0, |index| self.degrees[index])
    }

    // max_smaller_than: the largest variable of the monomial below x.
    fn max_smaller_than(&self, variable: Var) -> Var {
        let mut result = NULL_VAR;
        for current in &self.vars {
            if *current < variable {
                result = *current;
            }
        }
        result
    }
}

// The manager's monomial table and polynomial id counter, apart from its som buffers so that the
// buffers can make monomials and polynomials while the manager lends them out.
struct Tables {
    monomials: Vec<MonomialData>,
    monomial_ids: HashMap<(Vec<Var>, Vec<u32>), Monomial>,
    next_polynomial_id: u32,
}

impl Tables {
    fn get(&self, monomial: Monomial) -> &MonomialData {
        &self.monomials[monomial.0 as usize]
    }

    fn mk_monomial(&mut self, vars: &[Var], degrees: &[u32]) -> Monomial {
        let key = (vars.to_vec(), degrees.to_vec());
        if let Some(existing) = self.monomial_ids.get(&key) {
            return *existing;
        }
        let monomial = Monomial(self.monomials.len() as u32);
        self.monomials
            .push(MonomialData::new(vars.to_vec(), degrees.to_vec()));
        self.monomial_ids.insert(key, monomial);
        monomial
    }

    fn mul_monomials(&mut self, first: Monomial, second: Monomial) -> Monomial {
        let first_data = self.get(first);
        let second_data = self.get(second);
        if first_data.size() == 0 {
            return second;
        }
        if second_data.size() == 0 {
            return first;
        }
        let mut vars = Vec::new();
        let mut degrees = Vec::new();
        let mut first_index = 0;
        let mut second_index = 0;
        while first_index < first_data.size() || second_index < second_data.size() {
            let first_var = if first_index < first_data.size() {
                i64::from(first_data.vars[first_index])
            } else {
                i64::MAX
            };
            let second_var = if second_index < second_data.size() {
                i64::from(second_data.vars[second_index])
            } else {
                i64::MAX
            };
            if first_var == second_var {
                vars.push(first_data.vars[first_index]);
                degrees.push(first_data.degrees[first_index] + second_data.degrees[second_index]);
                first_index += 1;
                second_index += 1;
            } else if first_var < second_var {
                vars.push(first_data.vars[first_index]);
                degrees.push(first_data.degrees[first_index]);
                first_index += 1;
            } else {
                vars.push(second_data.vars[second_index]);
                degrees.push(second_data.degrees[second_index]);
                second_index += 1;
            }
        }
        self.mk_monomial(&vars, &degrees)
    }

    // div: m1/m2, or None when m2 does not divide m1.
    fn div_monomials(&mut self, first: Monomial, second: Monomial) -> Option<Monomial> {
        let first_data = self.get(first);
        let second_data = self.get(second);
        let mut vars = Vec::new();
        let mut degrees = Vec::new();
        let mut second_index = 0;
        for index in 0..first_data.size() {
            let variable = first_data.vars[index];
            let mut degree = i64::from(first_data.degrees[index]);
            if second_index < second_data.size() && second_data.vars[second_index] == variable {
                degree -= i64::from(second_data.degrees[second_index]);
                second_index += 1;
                if degree < 0 {
                    return None;
                }
            } else if second_index < second_data.size() && second_data.vars[second_index] < variable
            {
                return None;
            }
            if degree > 0 {
                vars.push(variable);
                degrees.push(degree as u32);
            }
        }
        if second_index < second_data.size() {
            return None;
        }
        Some(self.mk_monomial(&vars, &degrees))
    }

    // div_x_k: m/x^k.
    fn div_xk(&mut self, monomial: Monomial, variable: Var, power: u32) -> Monomial {
        let data = self.get(monomial);
        let mut vars = Vec::new();
        let mut degrees = Vec::new();
        for (current, current_degree) in data.vars.iter().zip(&data.degrees) {
            let degree = if *current == variable {
                current_degree - power
            } else {
                *current_degree
            };
            if degree == 0 {
                continue;
            }
            vars.push(*current);
            degrees.push(degree);
        }
        self.mk_monomial(&vars, &degrees)
    }

    // div_x: m with x removed.
    fn div_x(&mut self, monomial: Monomial, variable: Var) -> Monomial {
        let degree = self.get(monomial).degree_of(variable);
        self.div_xk(monomial, variable, degree)
    }

    fn mk_polynomial_core(&mut self, as_: Vec<Int>, ms: Vec<Monomial>) -> Polynomial {
        let polynomial = Rc::new(PolynomialNode {
            id: self.next_polynomial_id,
            terms: RefCell::new(Terms { as_, ms }),
            is_lex_sorted: Cell::new(false),
        });
        self.next_polynomial_id += 1;
        polynomial.make_first_maximal(self);
        polynomial
    }

    // lex_compare: the biggest variable dominates, then its degree.
    fn lex_compare(&self, first: Monomial, second: Monomial) -> i32 {
        if first == second {
            return 0;
        }
        let first_data = self.get(first);
        let second_data = self.get(second);
        let mut first_index = first_data.size();
        let mut second_index = second_data.size();
        while first_index > 0 && second_index > 0 {
            let first_var = first_data.vars[first_index - 1];
            let second_var = second_data.vars[second_index - 1];
            if first_var == second_var {
                let first_degree = first_data.degrees[first_index - 1];
                let second_degree = second_data.degrees[second_index - 1];
                if first_degree == second_degree {
                    first_index -= 1;
                    second_index -= 1;
                    continue;
                }
                return if first_degree < second_degree { -1 } else { 1 };
            }
            return if first_var > second_var { 1 } else { -1 };
        }
        if first_index == 0 { -1 } else { 1 }
    }

    fn graded_lex_compare(&self, first: Monomial, second: Monomial) -> i32 {
        let first_total = self.get(first).total_degree;
        let second_total = self.get(second).total_degree;
        if first_total == second_total {
            self.lex_compare(first, second)
        } else if first_total < second_total {
            -1
        } else {
            1
        }
    }

    // po_gt: the order that puts a monomial with the maximal variable at its maximal degree first.
    fn is_po_greater(&self, first: Monomial, second: Monomial) -> bool {
        let first_data = self.get(first);
        let second_data = self.get(second);
        if first_data.size() == 0 {
            return false;
        }
        if second_data.size() == 0 {
            return true;
        }
        if first_data.max_var() != second_data.max_var() {
            return first_data.max_var() > second_data.max_var();
        }
        first_data.max_var_degree() > second_data.max_var_degree()
    }
}

/// A polynomial's coefficients and monomials, term by term.
pub struct Terms {
    pub as_: Vec<Int>,
    pub ms: Vec<Monomial>,
}

impl Terms {
    fn swap_first(&mut self, position: usize) {
        if position == 0 {
            return;
        }
        self.as_.swap(0, position);
        self.ms.swap(0, position);
    }
}

pub struct PolynomialNode {
    id: u32,
    terms: RefCell<Terms>,
    is_lex_sorted: Cell<bool>,
}

/// A shared polynomial: identity is its id, and its terms are reordered in place.
pub type Polynomial = Rc<PolynomialNode>;

impl PolynomialNode {
    pub fn id(&self) -> u32 {
        self.id
    }

    pub fn size(&self) -> usize {
        self.terms.borrow().ms.len()
    }

    pub fn coeff_at(&self, index: usize) -> Int {
        self.terms.borrow().as_[index].clone()
    }

    pub fn monomial_at(&self, index: usize) -> Monomial {
        self.terms.borrow().ms[index]
    }

    pub fn terms(&self) -> Ref<'_, Terms> {
        self.terms.borrow()
    }

    // make_first_maximal: a monomial with the maximal variable at its maximal degree first.
    fn make_first_maximal(&self, tables: &Tables) {
        let mut terms = self.terms.borrow_mut();
        if terms.ms.len() <= 1 {
            return;
        }
        let mut max_pos = 0;
        for index in 1..terms.ms.len() {
            if tables.is_po_greater(terms.ms[index], terms.ms[max_pos]) {
                max_pos = index;
            }
        }
        terms.swap_first(max_pos);
        self.is_lex_sorted.set(false);
    }

    // lex_sort: puts the monomials in decreasing lexicographic order, which Z3 does in place
    // whenever it hashes the polynomial.
    fn lex_sort(&self, tables: &Tables) {
        if self.is_lex_sorted.get() {
            return;
        }
        self.is_lex_sorted.set(true);
        let mut terms = self.terms.borrow_mut();
        if terms.ms.len() <= 1 {
            return;
        }
        let mut order: Vec<usize> = (0..terms.ms.len()).collect();
        order.sort_by(|first, second| {
            tables
                .lex_compare(terms.ms[*second], terms.ms[*first])
                .cmp(&0)
        });
        let as_ = order
            .iter()
            .map(|index| terms.as_[*index].clone())
            .collect();
        let ms = order.iter().map(|index| terms.ms[*index]).collect();
        terms.as_ = as_;
        terms.ms = ms;
    }

    // graded_lex_max_pos: None (the TS -1) for the zero polynomial.
    fn get_graded_lex_max_pos(&self, tables: &Tables) -> Option<usize> {
        let terms = self.terms.borrow();
        if terms.ms.is_empty() {
            return None;
        }
        let mut max_pos = 0;
        for index in 1..terms.ms.len() {
            if tables.graded_lex_compare(terms.ms[index], terms.ms[max_pos]) > 0 {
                max_pos = index;
            }
        }
        Some(max_pos)
    }
}

// som_buffer: a sum of monomials, each kept at the position where it first appeared. Zero entries
// stay until mk removes them.
#[derive(Default)]
struct SomBuffer {
    as_: Vec<Int>,
    ms: Vec<Monomial>,
    positions: HashMap<Monomial, usize>,
}

impl SomBuffer {
    fn reset(&mut self) {
        self.as_ = Vec::new();
        self.ms = Vec::new();
        self.positions.clear();
    }

    fn add_term(&mut self, coeff: Int, monomial: Monomial) {
        if coeff.is_zero() {
            return;
        }
        match self.positions.get(&monomial) {
            None => {
                self.positions.insert(monomial, self.ms.len());
                self.ms.push(monomial);
                self.as_.push(coeff);
            }
            Some(position) => self.as_[*position] = &self.as_[*position] + &coeff,
        }
    }

    fn add(&mut self, polynomial: &Polynomial) {
        let terms = polynomial.terms();
        for (coeff, monomial) in terms.as_.iter().zip(&terms.ms) {
            match self.positions.get(monomial) {
                None => {
                    self.positions.insert(*monomial, self.ms.len());
                    self.ms.push(*monomial);
                    self.as_.push(coeff.clone());
                }
                Some(position) => self.as_[*position] = &self.as_[*position] + coeff,
            }
        }
    }

    // addmul: adds a*m*p.
    fn addmul(
        &mut self,
        tables: &mut Tables,
        coeff: &Int,
        monomial: Monomial,
        polynomial: &Polynomial,
    ) {
        if coeff.is_zero() {
            return;
        }
        let terms = polynomial.terms();
        for (term_coeff, term_monomial) in terms.as_.iter().zip(&terms.ms) {
            let product = tables.mul_monomials(monomial, *term_monomial);
            match self.positions.get(&product) {
                None => {
                    self.positions.insert(product, self.ms.len());
                    self.ms.push(product);
                    self.as_.push(coeff * term_coeff);
                }
                Some(position) => {
                    self.as_[*position] = &self.as_[*position] + &(coeff * term_coeff);
                }
            }
        }
    }

    // addmul(a, m, buffer): adds a*m times each entry of another buffer, zero entries included,
    // which keeps their monomials at new positions as Z3 does.
    fn addmul_buffer(
        &mut self,
        tables: &mut Tables,
        coeff: &Int,
        monomial: Monomial,
        buffer: &SomBuffer,
    ) {
        if coeff.is_zero() {
            return;
        }
        for (buffer_coeff, buffer_monomial) in buffer.as_.iter().zip(&buffer.ms) {
            let product = tables.mul_monomials(monomial, *buffer_monomial);
            match self.positions.get(&product) {
                None => {
                    self.positions.insert(product, self.ms.len());
                    self.ms.push(product);
                    self.as_.push(coeff * buffer_coeff);
                }
                Some(position) => {
                    self.as_[*position] = &self.as_[*position] + &(coeff * buffer_coeff);
                }
            }
        }
    }

    // None for the TS -1: no nonzero entry.
    fn get_graded_lex_max_pos(&self, tables: &Tables) -> Option<usize> {
        let mut max_pos: Option<usize> = None;
        for index in 0..self.as_.len() {
            if self.as_[index].is_zero() {
                continue;
            }
            if max_pos.is_none_or(|current| {
                tables.graded_lex_compare(self.ms[index], self.ms[current]) > 0
            }) {
                max_pos = Some(index);
            }
        }
        max_pos
    }

    // mk(normalize): the nonzero entries, divided by the gcd of their coefficients when
    // normalizing.
    fn mk(&mut self, tables: &mut Tables, is_normalized: bool) -> Polynomial {
        let mut as_: Vec<Int> = Vec::new();
        let mut ms = Vec::new();
        for (coeff, monomial) in self.as_.iter().zip(&self.ms) {
            if coeff.is_zero() {
                continue;
            }
            as_.push(coeff.clone());
            ms.push(*monomial);
        }
        self.reset();
        let gcd = if is_normalized {
            as_.iter()
                .fold(Int::zero(), |current, coeff| get_gcd(&current, coeff))
        } else {
            Int::one()
        };
        let as_ = if gcd > Int::one() {
            as_.iter().map(|coeff| coeff / &gcd).collect()
        } else {
            as_
        };
        tables.mk_polynomial_core(as_, ms)
    }
}

// cheap_som_buffer: each monomial is added at most once, so it needs no position map.
#[derive(Default)]
struct CheapSomBuffer {
    as_: Vec<Int>,
    ms: Vec<Monomial>,
}

impl CheapSomBuffer {
    fn add(&mut self, coeff: Int, monomial: Monomial) {
        if coeff.is_zero() {
            return;
        }
        self.as_.push(coeff);
        self.ms.push(monomial);
    }

    fn addmul(
        &mut self,
        tables: &mut Tables,
        coeff: &Int,
        monomial: Monomial,
        polynomial: &Polynomial,
    ) {
        if coeff.is_zero() {
            return;
        }
        let terms = polynomial.terms();
        for (term_coeff, term_monomial) in terms.as_.iter().zip(&terms.ms) {
            self.as_.push(coeff * term_coeff);
            self.ms.push(tables.mul_monomials(monomial, *term_monomial));
        }
    }

    fn mk(&mut self, tables: &mut Tables) -> Polynomial {
        tables.mk_polynomial_core(mem::take(&mut self.as_), mem::take(&mut self.ms))
    }
}

/// constant * factors[0]^degrees[0] * ... * factors[n]^degrees[n].
pub struct Factors {
    pub constant: Int,
    pub factors: Vec<Polynomial>,
    pub degrees: Vec<u32>,
}

/// The result of a pseudo-division: the quotient, the remainder and the number of steps.
pub struct PseudoDivision {
    pub quotient: Polynomial,
    pub remainder: Polynomial,
    pub steps: u32,
}

pub struct PolynomialManager {
    tables: Tables,
    unit: Monomial,
    zero: Polynomial,
    one: Polynomial,
    um: UpolynomialManager,
    som: SomBuffer,
    som2: SomBuffer,
    cheap: CheapSomBuffer,
}

impl Default for PolynomialManager {
    fn default() -> PolynomialManager {
        PolynomialManager::new()
    }
}

impl PolynomialManager {
    pub fn new() -> PolynomialManager {
        let mut tables = Tables {
            monomials: Vec::new(),
            monomial_ids: HashMap::new(),
            next_polynomial_id: 0,
        };
        let unit = tables.mk_monomial(&[], &[]);
        let zero = tables.mk_polynomial_core(Vec::new(), Vec::new());
        let one = tables.mk_polynomial_core(vec![Int::one()], vec![unit]);
        PolynomialManager {
            tables,
            unit,
            zero,
            one,
            um: UpolynomialManager::new(None),
            som: SomBuffer::default(),
            som2: SomBuffer::default(),
            cheap: CheapSomBuffer::default(),
        }
    }

    pub fn unit(&self) -> Monomial {
        self.unit
    }

    pub fn zero(&self) -> Polynomial {
        self.zero.clone()
    }

    pub fn one(&self) -> Polynomial {
        self.one.clone()
    }

    // Monomials.

    pub fn monomial_vars(&self, monomial: Monomial) -> &[Var] {
        &self.tables.get(monomial).vars
    }

    pub fn monomial_degrees(&self, monomial: Monomial) -> &[u32] {
        &self.tables.get(monomial).degrees
    }

    pub fn monomial_total_degree(&self, monomial: Monomial) -> u32 {
        self.tables.get(monomial).total_degree
    }

    pub fn monomial_degree_of(&self, monomial: Monomial, variable: Var) -> u32 {
        self.tables.get(monomial).degree_of(variable)
    }

    pub fn mk_monomial(&mut self, vars: &[Var], degrees: &[u32]) -> Monomial {
        self.tables.mk_monomial(vars, degrees)
    }

    // rename: every variable x becomes permutation[x], in place in every monomial, as Z3 renames
    // its monomial table. Z3 then moves a maximal monomial first in every live polynomial. Here
    // that is the given polynomials, the ones nlsat keeps in its atoms. Others keep their order,
    // which matches again once the order is restored.
    pub fn rename<'a>(
        &mut self,
        permutation: &[Var],
        polynomials: impl IntoIterator<Item = &'a Polynomial>,
    ) {
        let mut monomial_ids = HashMap::new();
        for (id, monomial) in self.tables.monomials.iter_mut().enumerate() {
            let mut order: Vec<usize> = (0..monomial.vars.len()).collect();
            order.sort_by(|first, second| {
                permutation[monomial.vars[*first] as usize]
                    .cmp(&permutation[monomial.vars[*second] as usize])
            });
            monomial.degrees = order.iter().map(|index| monomial.degrees[*index]).collect();
            monomial.vars = order
                .iter()
                .map(|index| permutation[monomial.vars[*index] as usize])
                .collect();
            monomial_ids.insert(
                (monomial.vars.clone(), monomial.degrees.clone()),
                Monomial(id as u32),
            );
        }
        self.tables.monomial_ids = monomial_ids;
        for polynomial in polynomials {
            polynomial.make_first_maximal(&self.tables);
        }
    }

    // mk_monomial(x, k): x^k, the unit for k = 0.
    pub fn mk_power(&mut self, variable: Var, power: u32) -> Monomial {
        if power == 0 {
            self.unit
        } else {
            self.tables.mk_monomial(&[variable], &[power])
        }
    }

    pub fn mul_monomials(&mut self, first: Monomial, second: Monomial) -> Monomial {
        self.tables.mul_monomials(first, second)
    }

    // div: m1/m2, or None when m2 does not divide m1.
    pub fn div_monomials(&mut self, first: Monomial, second: Monomial) -> Option<Monomial> {
        self.tables.div_monomials(first, second)
    }

    // Construction.

    pub fn mk_polynomial_core(&mut self, as_: Vec<Int>, ms: Vec<Monomial>) -> Polynomial {
        self.tables.mk_polynomial_core(as_, ms)
    }

    pub fn mk_const(&mut self, value: &Int) -> Polynomial {
        if value.is_zero() {
            return self.zero();
        }
        if *value == Int::one() {
            return self.one();
        }
        self.tables
            .mk_polynomial_core(vec![value.clone()], vec![self.unit])
    }

    pub fn mk_var(&mut self, variable: Var, degree: u32) -> Polynomial {
        let monomial = self.tables.mk_monomial(&[variable], &[degree]);
        self.tables
            .mk_polynomial_core(vec![Int::one()], vec![monomial])
    }

    pub fn mk_polynomial(&mut self, as_: &[Int], ms: &[Monomial]) -> Polynomial {
        self.som.reset();
        for (coeff, monomial) in as_.iter().zip(ms) {
            self.som.add_term(coeff.clone(), *monomial);
        }
        self.som.mk(&mut self.tables, false)
    }

    // mk_linear: sum of as[i]*xs[i] plus c.
    pub fn mk_linear(&mut self, as_: &[Int], vars: &[Var], constant: &Int) -> Polynomial {
        let mut coeffs = Vec::new();
        let mut ms = Vec::new();
        for (coeff, variable) in as_.iter().zip(vars) {
            if coeff.is_zero() {
                continue;
            }
            coeffs.push(coeff.clone());
            ms.push(self.tables.mk_monomial(&[*variable], &[1]));
        }
        if !constant.is_zero() {
            coeffs.push(constant.clone());
            ms.push(self.unit);
        }
        self.mk_polynomial(&coeffs, &ms)
    }

    // Queries.

    pub fn is_zero(&self, polynomial: &Polynomial) -> bool {
        polynomial.size() == 0
    }

    pub fn is_const(&self, polynomial: &Polynomial) -> bool {
        let terms = polynomial.terms();
        terms.ms.is_empty() || (terms.ms.len() == 1 && self.tables.get(terms.ms[0]).size() == 0)
    }

    pub fn is_univariate(&self, polynomial: &Polynomial) -> bool {
        if self.is_const(polynomial) {
            return true;
        }
        let max_var = self.max_var(polynomial);
        for monomial in &polynomial.terms().ms {
            let data = self.tables.get(*monomial);
            if data.size() > 1 || (data.size() == 1 && data.vars[0] != max_var) {
                return false;
            }
        }
        true
    }

    pub fn max_var(&self, polynomial: &Polynomial) -> Var {
        let terms = polynomial.terms();
        if terms.ms.is_empty() {
            NULL_VAR
        } else {
            self.tables.get(terms.ms[0]).max_var()
        }
    }

    pub fn degree(&self, polynomial: &Polynomial, variable: Var) -> u32 {
        let mut result = 0;
        for monomial in &polynomial.terms().ms {
            result = result.max(self.tables.get(*monomial).degree_of(variable));
        }
        result
    }

    pub fn total_degree(&self, polynomial: &Polynomial) -> u32 {
        let mut result = 0;
        for monomial in &polynomial.terms().ms {
            result = result.max(self.tables.get(*monomial).total_degree);
        }
        result
    }

    // eq: the same monomials with the same coefficients, in any order.
    pub fn eq(&self, first: &Polynomial, second: &Polynomial) -> bool {
        if Rc::ptr_eq(first, second) {
            return true;
        }
        if first.size() != second.size() {
            return false;
        }
        if first.size() == 0 {
            return true;
        }
        if self.max_var(first) != self.max_var(second) {
            return false;
        }
        let mut coeffs = HashMap::new();
        let first_terms = first.terms();
        for (coeff, monomial) in first_terms.as_.iter().zip(&first_terms.ms) {
            coeffs.insert(*monomial, coeff);
        }
        let second_terms = second.terms();
        for (coeff, monomial) in second_terms.as_.iter().zip(&second_terms.ms) {
            if coeffs.get(monomial) != Some(&coeff) {
                return false;
            }
        }
        true
    }

    // The key of the hash-consing table. It lexicographically sorts the polynomial in place, as
    // Z3's hash does.
    pub fn get_key(&self, polynomial: &Polynomial) -> String {
        polynomial.lex_sort(&self.tables);
        debug_assert!(polynomial.is_lex_sorted.get());
        let mut key = String::new();
        let terms = polynomial.terms();
        for (coeff, monomial) in terms.as_.iter().zip(&terms.ms) {
            key.push_str(&format!("{coeff}:{};", monomial.0));
        }
        key
    }

    pub fn polynomial_to_string(&self, polynomial: &Polynomial) -> String {
        let terms = polynomial.terms();
        if terms.ms.is_empty() {
            return "0".to_string();
        }
        terms
            .ms
            .iter()
            .enumerate()
            .map(|(index, monomial)| {
                let data = self.tables.get(*monomial);
                let mut parts = vec![format!("{}", terms.as_[index])];
                for (variable, degree) in data.vars.iter().zip(&data.degrees) {
                    parts.push(if *degree == 1 {
                        format!("x{variable}")
                    } else {
                        format!("x{variable}^{degree}")
                    });
                }
                parts.join("*")
            })
            .collect::<Vec<_>>()
            .join(" + ")
    }

    // Arithmetic.

    fn addmul(
        &mut self,
        first_coeff: &Int,
        first: &Polynomial,
        second_coeff: &Int,
        second: &Polynomial,
    ) -> Polynomial {
        self.som.reset();
        self.som
            .addmul(&mut self.tables, first_coeff, self.unit, first);
        self.som
            .addmul(&mut self.tables, second_coeff, self.unit, second);
        self.som.mk(&mut self.tables, false)
    }

    pub fn add(&mut self, first: &Polynomial, second: &Polynomial) -> Polynomial {
        self.addmul(&Int::one(), first, &Int::one(), second)
    }

    pub fn sub(&mut self, first: &Polynomial, second: &Polynomial) -> Polynomial {
        self.addmul(&Int::one(), first, &Int::from(-1), second)
    }

    pub fn mul(&mut self, first: &Polynomial, second: &Polynomial) -> Polynomial {
        if first.size() == 0 || second.size() == 0 {
            return self.zero();
        }
        self.som.reset();
        let terms = first.terms();
        for (coeff, monomial) in terms.as_.iter().zip(&terms.ms) {
            self.som.addmul(&mut self.tables, coeff, *monomial, second);
        }
        self.som.mk(&mut self.tables, false)
    }

    // mul(a, m, p): a*m*p.
    pub fn mul_term(
        &mut self,
        coeff: &Int,
        monomial: Monomial,
        polynomial: &Polynomial,
    ) -> Polynomial {
        if coeff.is_zero() {
            return self.zero();
        }
        if *coeff == Int::one() && monomial == self.unit {
            return polynomial.clone();
        }
        self.cheap
            .addmul(&mut self.tables, coeff, monomial, polynomial);
        self.cheap.mk(&mut self.tables)
    }

    pub fn mul_const(&mut self, coeff: &Int, polynomial: &Polynomial) -> Polynomial {
        self.mul_term(coeff, self.unit, polynomial)
    }

    pub fn neg(&mut self, polynomial: &Polynomial) -> Polynomial {
        let terms = polynomial.terms();
        for (coeff, monomial) in terms.as_.iter().zip(&terms.ms) {
            self.cheap.add(-coeff, *monomial);
        }
        self.cheap.mk(&mut self.tables)
    }

    pub fn pw(&mut self, polynomial: &Polynomial, power: u32) -> Polynomial {
        if power == 0 {
            return self.one();
        }
        let mut result = polynomial.clone();
        for _ in 1..power {
            result = self.mul(&result, polynomial);
        }
        result
    }

    // coeff: the coefficient of x^k, a polynomial in the other variables.
    pub fn coeff(&mut self, polynomial: &Polynomial, variable: Var, power: u32) -> Polynomial {
        let terms = polynomial.terms();
        for (coeff, monomial) in terms.as_.iter().zip(&terms.ms) {
            if self.tables.get(*monomial).degree_of(variable) == power {
                let quotient = self.tables.div_x(*monomial, variable);
                self.cheap.add(coeff.clone(), quotient);
            }
        }
        self.cheap.mk(&mut self.tables)
    }

    // const_coeff: the coefficient of x^k when it is a number, else None.
    pub fn get_const_coeff(
        &self,
        polynomial: &Polynomial,
        variable: Var,
        power: u32,
    ) -> Option<Int> {
        let mut result = Int::zero();
        let terms = polynomial.terms();
        for (coeff, monomial) in terms.as_.iter().zip(&terms.ms) {
            let data = self.tables.get(*monomial);
            if data.degree_of(variable) != power {
                continue;
            }
            if (power > 0 && data.size() > 1) || (power == 0 && data.size() > 0) {
                return None;
            }
            result = coeff.clone();
        }
        Some(result)
    }

    pub fn lc(&mut self, polynomial: &Polynomial, variable: Var) -> Polynomial {
        let degree = self.degree(polynomial, variable);
        self.coeff(polynomial, variable, degree)
    }

    pub fn derivative(&mut self, polynomial: &Polynomial, variable: Var) -> Polynomial {
        let terms = polynomial.terms();
        for (coeff, monomial) in terms.as_.iter().zip(&terms.ms) {
            let degree = self.tables.get(*monomial).degree_of(variable);
            if degree > 0 {
                let quotient = self.tables.div_xk(*monomial, variable, 1);
                self.cheap.add(coeff * &Int::from(degree), quotient);
            }
        }
        self.cheap.mk(&mut self.tables)
    }

    // flip_sign_if_lm_neg: negates p when its graded-lex leading coefficient is negative.
    pub fn flip_sign_if_lm_neg(&mut self, polynomial: &Polynomial) -> Polynomial {
        let Some(max_pos) = polynomial.get_graded_lex_max_pos(&self.tables) else {
            return polynomial.clone();
        };
        if polynomial.coeff_at(max_pos).is_negative() {
            self.neg(polynomial)
        } else {
            polynomial.clone()
        }
    }

    // ic: the integer content, the gcd of the coefficients.
    fn get_ic(&self, polynomial: &Polynomial) -> Int {
        if polynomial.size() == 0 {
            return Int::zero();
        }
        if self.is_const(polynomial) {
            return polynomial.coeff_at(0);
        }
        let terms = polynomial.terms();
        let mut result = terms.as_[0].clone();
        for coeff in &terms.as_[1..] {
            if result == Int::one() {
                return result;
            }
            result = get_gcd(&result, coeff);
        }
        result
    }

    // ic(p, a, c): p = a*c, with the coefficients of c coprime.
    fn ic_with_content(&mut self, polynomial: &Polynomial) -> (Int, Polynomial) {
        if polynomial.size() == 0 {
            return (Int::zero(), polynomial.clone());
        }
        if self.is_const(polynomial) {
            return (polynomial.coeff_at(0), self.one());
        }
        let mut content = Int::zero();
        for coeff in &polynomial.terms().as_ {
            content = get_gcd(&content, coeff);
        }
        if content == Int::one() {
            return (Int::one(), polynomial.clone());
        }
        let terms = polynomial.terms();
        for (coeff, monomial) in terms.as_.iter().zip(&terms.ms) {
            self.cheap.add(coeff / &content, *monomial);
        }
        (content, self.cheap.mk(&mut self.tables))
    }

    // iccp: the integer content, the content and the primitive part of p with respect to x.
    pub fn iccp(
        &mut self,
        polynomial: &Polynomial,
        variable: Var,
    ) -> Result<(Int, Polynomial, Polynomial), SmtError> {
        if polynomial.size() == 0 {
            return Ok((Int::zero(), self.one(), polynomial.clone()));
        }
        if self.is_const(polynomial) {
            return Ok((polynomial.coeff_at(0), self.one(), self.one()));
        }
        let degree = self.degree(polynomial, variable);
        if degree == 0 {
            let (integer, content) = self.ic_with_content(polynomial);
            return Ok((integer, content, self.one()));
        }
        // The quick filter: a power of x that occurs only as a pure power means the content is 1.
        let mut filter = vec![0u32; degree as usize + 1];
        let mut powers: Vec<u32> = Vec::new();
        for monomial in &polynomial.terms().ms {
            let data = self.tables.get(*monomial);
            let power = data.degree_of(variable);
            if filter[power as usize] == 0 {
                powers.push(power);
            }
            filter[power as usize] += if data.size() == usize::from(power > 0) {
                1
            } else {
                2
            };
        }
        let (integer, primitive) = self.ic_with_content(polynomial);
        for power in &powers {
            if filter[*power as usize] == 1 {
                return Ok((integer, self.one(), primitive));
            }
        }
        let mut content = self.coeff(&primitive, variable, powers[0]);
        for power in &powers[1..] {
            let coeff = self.coeff(&primitive, variable, *power);
            content = self.gcd(&content, &coeff)?;
            if self.is_const(&content) {
                return Ok((integer, self.one(), primitive));
            }
        }
        content = self.flip_sign_if_lm_neg(&content);
        let quotient = self.exact_div(&primitive, &content)?;
        Ok((integer, content, quotient))
    }

    pub fn pp(&mut self, polynomial: &Polynomial, variable: Var) -> Result<Polynomial, SmtError> {
        Ok(self.iccp(polynomial, variable)?.2)
    }

    // square_free: the integer content times the square-free parts of the content and the
    // primitive part in the maximal variable, or p itself when it is square-free.
    pub fn square_free(&mut self, polynomial: &Polynomial) -> Result<Polynomial, SmtError> {
        if self.is_const(polynomial) {
            return Ok(polynomial.clone());
        }
        let variable = self.max_var(polynomial);
        let (integer, content, primitive) = self.iccp(polynomial, variable)?;
        let square_free_content = self.square_free(&content)?;
        let derivative = self.derivative(&primitive, variable);
        let g = self.gcd(&primitive, &derivative)?;
        if self.is_const(&g) && self.eq(&square_free_content, &content) {
            return Ok(polynomial.clone());
        }
        let square_free_primitive = if self.is_const(&g) {
            primitive
        } else {
            self.exact_div(&primitive, &g)?
        };
        let scaled = self.mul_const(&integer, &square_free_content);
        Ok(self.mul(&scaled, &square_free_primitive))
    }

    // normalize: p divided by the gcd of its coefficients.
    pub fn normalize(&mut self, polynomial: &Polynomial) -> Polynomial {
        if polynomial.size() == 0 {
            return polynomial.clone();
        }
        let mut g = Int::zero();
        for coeff in &polynomial.terms().as_ {
            g = get_gcd(&g, coeff);
        }
        if g == Int::one() {
            return polynomial.clone();
        }
        let terms = polynomial.terms();
        for (coeff, monomial) in terms.as_.iter().zip(&terms.ms) {
            self.cheap.add(coeff / &g, *monomial);
        }
        self.cheap.mk(&mut self.tables)
    }

    // nonzero_const_coeff: whether the coefficient of x^k is a nonzero number.
    pub fn is_nonzero_const_coeff(
        &self,
        polynomial: &Polynomial,
        variable: Var,
        power: u32,
    ) -> bool {
        self.get_const_coeff(polynomial, variable, power)
            .is_some_and(|coeff| !coeff.is_zero())
    }

    // exact_div: p/q, where q divides p.
    pub fn exact_div(
        &mut self,
        polynomial: &Polynomial,
        divisor: &Polynomial,
    ) -> Result<Polynomial, SmtError> {
        if polynomial.size() == 0 {
            return Ok(polynomial.clone());
        }
        // remainder is som, quotient is som2.
        self.som.reset();
        self.som2.reset();
        self.som.add(polynomial);
        // The TS reads past the end of a zero divisor and fails on it.
        let max_pos = divisor
            .get_graded_lex_max_pos(&self.tables)
            .ok_or_else(|| SmtError::Invariant("exact_div: division by zero".to_string()))?;
        let divisor_monomial = divisor.monomial_at(max_pos);
        let divisor_coeff = divisor.coeff_at(max_pos);
        loop {
            let Some(remainder_pos) = self.som.get_graded_lex_max_pos(&self.tables) else {
                self.som.reset();
                return Ok(self.som2.mk(&mut self.tables, false));
            };
            let Some(monomial) = self
                .tables
                .div_monomials(self.som.ms[remainder_pos], divisor_monomial)
            else {
                return Err(SmtError::Invariant(
                    "exact_div: the divisor does not divide".to_string(),
                ));
            };
            let coeff = &self.som.as_[remainder_pos] / &divisor_coeff;
            self.som2.add_term(coeff.clone(), monomial);
            self.som
                .addmul(&mut self.tables, &-coeff, monomial, divisor);
        }
    }

    // exact_pseudo_division: Q and R with lc(q)^(deg(p) - deg(q) + 1) * p = Q*q + R. The
    // quotient is only built when asked for, as in pseudo_division_core.
    pub fn exact_pseudo_division(
        &mut self,
        polynomial: &Polynomial,
        divisor: &Polynomial,
        variable: Var,
        is_quotient: bool,
    ) -> PseudoDivision {
        self.pseudo_division_core(polynomial, divisor, variable, true, is_quotient)
    }

    // pseudo_remainder: R with lc(q)^d * p = Q*q + R, where d counts the division steps.
    pub fn pseudo_remainder(
        &mut self,
        polynomial: &Polynomial,
        divisor: &Polynomial,
        variable: Var,
    ) -> PseudoDivision {
        self.pseudo_division_core(polynomial, divisor, variable, false, false)
    }

    fn pseudo_division_core(
        &mut self,
        polynomial: &Polynomial,
        divisor: &Polynomial,
        variable: Var,
        is_exact: bool,
        is_quotient: bool,
    ) -> PseudoDivision {
        let deg_a = self.degree(polynomial, variable);
        let deg_b = self.degree(divisor, variable);
        if deg_b == 0 {
            let steps = if is_exact { deg_a + 1 } else { 1 };
            if !is_quotient || !is_exact || deg_a == 0 {
                return PseudoDivision {
                    quotient: polynomial.clone(),
                    remainder: self.zero(),
                    steps,
                };
            }
            let power = self.pw(divisor, deg_a);
            return PseudoDivision {
                quotient: self.mul(polynomial, &power),
                remainder: self.zero(),
                steps,
            };
        }
        let lc_b = self.coeff(divisor, variable, deg_b);
        let reduct_b = self.reduct(divisor, variable, deg_b);
        let mut remainder = polynomial.clone();
        let mut quotient = self.zero();
        let mut steps = 0u32;
        loop {
            let deg_r = self.degree(&remainder, variable);
            if deg_b > deg_r {
                // exactSteps = degA - degB + 1; steps < exactSteps fails when it is not positive.
                if let Some(exact_steps) = (deg_a + 1).checked_sub(deg_b)
                    && is_exact
                    && steps < exact_steps
                {
                    let power = self.pw(&lc_b, exact_steps - steps);
                    if is_quotient {
                        quotient = self.mul(&power, &quotient);
                    }
                    remainder = self.mul(&power, &remainder);
                }
                return PseudoDivision {
                    quotient,
                    remainder,
                    steps,
                };
            }
            self.som.reset();
            self.som2.reset();
            {
                let terms = remainder.terms();
                for (coeff, monomial) in terms.as_.iter().zip(&terms.ms) {
                    if self.tables.get(*monomial).degree_of(variable) == deg_r {
                        let shifted = self.tables.div_xk(*monomial, variable, deg_b);
                        if is_quotient {
                            self.som2.add_term(coeff.clone(), shifted);
                        }
                        self.som
                            .addmul(&mut self.tables, &-coeff, shifted, &reduct_b);
                    } else {
                        self.som.addmul(&mut self.tables, coeff, *monomial, &lc_b);
                    }
                }
            }
            remainder = self.som.mk(&mut self.tables, false);
            if is_quotient {
                {
                    let terms = quotient.terms();
                    for (coeff, monomial) in terms.as_.iter().zip(&terms.ms) {
                        self.som2.addmul(&mut self.tables, coeff, *monomial, &lc_b);
                    }
                }
                quotient = self.som2.mk(&mut self.tables, false);
            }
            steps += 1;
        }
    }

    pub fn exact_pseudo_remainder(
        &mut self,
        polynomial: &Polynomial,
        divisor: &Polynomial,
        variable: Var,
    ) -> Polynomial {
        self.exact_pseudo_division(polynomial, divisor, variable, false)
            .remainder
    }

    // The reduct of coeff(p, x, k, reduct): p without its x^k monomials.
    pub fn reduct(&mut self, polynomial: &Polynomial, variable: Var, power: u32) -> Polynomial {
        let terms = polynomial.terms();
        for (coeff, monomial) in terms.as_.iter().zip(&terms.ms) {
            if self.tables.get(*monomial).degree_of(variable) != power {
                self.cheap.add(coeff.clone(), *monomial);
            }
        }
        self.cheap.mk(&mut self.tables)
    }

    // var_max_degrees, sorted by variable.
    fn get_var_max_degrees(&self, polynomial: &Polynomial) -> Vec<(Var, u32)> {
        let mut degrees: Vec<(Var, u32)> = Vec::new();
        for monomial in &polynomial.terms().ms {
            let data = self.tables.get(*monomial);
            for (variable, degree) in data.vars.iter().zip(&data.degrees) {
                match degrees.iter_mut().find(|entry| entry.0 == *variable) {
                    Some(entry) => entry.1 = entry.1.max(*degree),
                    None => degrees.push((*variable, *degree)),
                }
            }
        }
        degrees.sort_by_key(|entry| entry.0);
        degrees
    }

    // gcd: the greatest common divisor, with a positive integer content and leading coefficient.
    pub fn gcd(&mut self, first: &Polynomial, second: &Polynomial) -> Result<Polynomial, SmtError> {
        if first.size() == 0 {
            return Ok(self.flip_sign_if_lm_neg(second));
        }
        if second.size() == 0 {
            return Ok(self.flip_sign_if_lm_neg(first));
        }
        if Rc::ptr_eq(first, second) {
            return Ok(self.flip_sign_if_lm_neg(first));
        }
        if self.is_const(first) || self.is_const(second) {
            let gcd = get_gcd(&self.get_ic(second), &self.get_ic(first));
            return Ok(self.mk_const(&gcd));
        }
        let first_degrees = self.get_var_max_degrees(first);
        let second_degrees = self.get_var_max_degrees(second);
        let size = first_degrees.len().min(second_degrees.len());
        for (first_entry, second_entry) in first_degrees.iter().zip(&second_degrees) {
            let first_var = first_entry.0;
            let second_var = second_entry.0;
            if first_var < second_var {
                return self.gcd_content(first, first_var, second);
            }
            if first_var > second_var {
                return self.gcd_content(second, second_var, first);
            }
        }
        if size < first_degrees.len() {
            return self.gcd_content(first, first_degrees[size].0, second);
        }
        if size < second_degrees.len() {
            return self.gcd_content(second, second_degrees[size].0, first);
        }
        self.gcd_prs(first, second, first_degrees[size - 1].0)
    }

    // gcd_content: gcd(content(u, x), v).
    fn gcd_content(
        &mut self,
        polynomial: &Polynomial,
        variable: Var,
        other: &Polynomial,
    ) -> Result<Polynomial, SmtError> {
        let (integer, content, _) = self.iccp(polynomial, variable)?;
        let scaled = self.mul_const(&integer, &content);
        self.gcd(&scaled, other)
    }

    // gcd_prs: Collins' subresultant polynomial remainder sequence.
    fn gcd_prs(
        &mut self,
        first: &Polynomial,
        second: &Polynomial,
        variable: Var,
    ) -> Result<Polynomial, SmtError> {
        let (u, v) = if self.degree(first, variable) < self.degree(second, variable) {
            (second, first)
        } else {
            (first, second)
        };
        let (integer_u, content_u, primitive_u) = self.iccp(u, variable)?;
        let (integer_v, content_v, primitive_v) = self.iccp(v, variable)?;
        let content_gcd = self.gcd(&content_u, &content_v)?;
        let integer_gcd = get_gcd(&integer_u, &integer_v);
        let mut pp_u = primitive_u;
        let mut pp_v = primitive_v;
        let mut g = self.one();
        let mut h = self.one();
        loop {
            let delta =
                i64::from(self.degree(&pp_u, variable)) - i64::from(self.degree(&pp_v, variable));
            let remainder = self.exact_pseudo_remainder(&pp_u, &pp_v, variable);
            if remainder.size() == 0 {
                let flipped = self.flip_sign_if_lm_neg(&pp_v);
                let result = self.pp(&flipped, variable)?;
                let product = self.mul(&content_gcd, &result);
                return Ok(self.mul_const(&integer_gcd, &product));
            }
            if self.is_const(&remainder) {
                return Ok(self.mul_const(&integer_gcd, &content_gcd));
            }
            pp_u = pp_v;
            pp_v = self.exact_div(&remainder, &g)?;
            for _ in 0..delta {
                pp_v = self.exact_div(&pp_v, &h)?;
            }
            g = self.lc(&pp_u, variable);
            let mut new_h = self.one();
            for _ in 0..delta {
                new_h = self.mul(&new_h, &g);
            }
            for _ in 1..delta {
                new_h = self.exact_div(&new_h, &h)?;
            }
            h = new_h;
        }
    }

    // get_min_degree_var: the first variable, in order of occurrence, of minimal degree.
    fn get_min_degree_var(&self, polynomial: &Polynomial) -> Var {
        let mut degrees: Vec<(Var, u32)> = Vec::new();
        for monomial in &polynomial.terms().ms {
            let data = self.tables.get(*monomial);
            for (variable, degree) in data.vars.iter().zip(&data.degrees) {
                match degrees.iter_mut().find(|entry| entry.0 == *variable) {
                    Some(entry) => {
                        if *degree > entry.1 {
                            entry.1 = *degree;
                        }
                    }
                    None => {
                        if *degree > 0 {
                            degrees.push((*variable, *degree));
                        }
                    }
                }
            }
        }
        let mut result = NULL_VAR;
        let mut min_degree: Option<u32> = None;
        for (variable, degree) in degrees {
            if min_degree.is_none_or(|current| degree < current) {
                result = variable;
                min_degree = Some(degree);
            }
        }
        result
    }

    // factor: the constant and the irreducible factors, each with its multiplicity. A
    // square-free primitive part of degree 2 or more in its variable of minimal degree is out of
    // scope.
    pub fn factor(&mut self, polynomial: &Polynomial) -> Result<Factors, SmtError> {
        let mut result = Factors {
            constant: Int::one(),
            factors: Vec::new(),
            degrees: Vec::new(),
        };
        if polynomial.size() == 0 {
            result.constant = Int::zero();
        } else {
            self.factor_core(polynomial, &mut result)?;
        }
        Ok(result)
    }

    fn factor_core(
        &mut self,
        polynomial: &Polynomial,
        result: &mut Factors,
    ) -> Result<(), SmtError> {
        if self.is_const(polynomial) {
            result.constant = &result.constant * &polynomial.coeff_at(0);
            return Ok(());
        }
        let variable = self.get_min_degree_var(polynomial);
        let (integer, content, primitive) = self.iccp(polynomial, variable)?;
        result.constant = &result.constant * &integer;
        self.factor_core(&content, result)?;
        let derivative = self.derivative(&primitive, variable);
        let mut square = self.gcd(&primitive, &derivative)?;
        if self.is_const(&square) {
            return self.factor_sqf_pp(&primitive, variable, 1, result);
        }
        let mut product = self.exact_div(&primitive, &square)?;
        let mut multiplicity = 1;
        while !self.is_const(&product) {
            let next = self.gcd(&product, &square)?;
            let factor = self.exact_div(&product, &next)?;
            if !self.is_const(&factor) {
                self.factor_sqf_pp(&factor, variable, multiplicity, result)?;
            } else if factor.coeff_at(0) == Int::from(-1) && multiplicity % 2 == 1 {
                result.constant = -&result.constant;
            }
            square = self.exact_div(&square, &next)?;
            product = next;
            multiplicity += 1;
        }
        Ok(())
    }

    // factor_sqf_pp: the factors of a primitive square-free p of positive degree in x.
    fn factor_sqf_pp(
        &mut self,
        polynomial: &Polynomial,
        variable: Var,
        k: u32,
        result: &mut Factors,
    ) -> Result<(), SmtError> {
        let degree = self.degree(polynomial, variable);
        if degree == 1 {
            Self::push_factor(result, polynomial, k);
        } else if self.is_univariate(polynomial) {
            self.factor_sqf_pp_univ(polynomial, k, result)?;
        } else if degree == 2 {
            self.factor_quadratic(polynomial, variable, k, result)?;
        } else if !self.factor_multivariate(polynomial, variable, k, result)? {
            Self::push_factor(result, polynomial, k);
        }
        Ok(())
    }

    fn push_factor(result: &mut Factors, polynomial: &Polynomial, k: u32) {
        result.factors.push(polynomial.clone());
        result.degrees.push(k);
    }

    // to_numeral_vector: the coefficients of a univariate p by degree. Z3 normalizes p first but
    // reads the coefficients of p itself.
    // to_numeral_vector: a univariate p as its coefficients, low to high.
    pub fn to_coeffs(&mut self, polynomial: &Polynomial) -> Upolynomial {
        let mut coeffs = vec![Int::zero(); self.total_degree(polynomial) as usize + 1];
        let terms = polynomial.terms();
        for (coeff, monomial) in terms.as_.iter().zip(&terms.ms) {
            coeffs[self.tables.get(*monomial).total_degree as usize] = coeff.clone();
        }
        self.um.set(&coeffs)
    }

    // to_polynomial, mk_univariate: the monomials from the highest degree down.
    pub fn from_coeffs(&mut self, coeffs: &[Int], variable: Var) -> Polynomial {
        for (power, coeff) in coeffs.iter().enumerate().rev() {
            let monomial = self.mk_power(variable, power as u32);
            self.cheap.add(coeff.clone(), monomial);
        }
        self.cheap.mk(&mut self.tables)
    }

    // factor_sqf_pp_univ
    fn factor_sqf_pp_univ(
        &mut self,
        polynomial: &Polynomial,
        k: u32,
        result: &mut Factors,
    ) -> Result<(), SmtError> {
        let variable = self.max_var(polynomial);
        let mut fs = UpolynomialFactors {
            constant: Int::one(),
            factors: Vec::new(),
            degrees: Vec::new(),
        };
        let coeffs = self.to_coeffs(polynomial);
        factor_square_free(&mut self.um, &coeffs, &mut fs, 1, &DEFAULT_FACTOR_PARAMS)?;
        if fs.factors.len() == 1 && fs.degrees[0] == 1 {
            Self::push_factor(result, polynomial, k);
            return Ok(());
        }
        for (factor, degree) in fs.factors.iter().zip(&fs.degrees) {
            let factor = self.from_coeffs(factor, variable);
            Self::push_factor(result, &factor, k * degree);
        }
        if fs.constant == Int::from(-1) && k % 2 == 1 {
            result.constant = -&result.constant;
        }
        Ok(())
    }

    // factor_2_sqf_pp: a*x^2 + b*x + c splits into the primitive parts of 2*a*x + b -/+
    // sqrt(disc) when the discriminant b^2 - 4*a*c is a square.
    fn factor_quadratic(
        &mut self,
        polynomial: &Polynomial,
        variable: Var,
        k: u32,
        result: &mut Factors,
    ) -> Result<(), SmtError> {
        let mut a = self.coeff(polynomial, variable, 2);
        let mut b = self.coeff(polynomial, variable, 1);
        let mut c = self.coeff(polynomial, variable, 0);
        let is_flipped = a
            .get_graded_lex_max_pos(&self.tables)
            .is_some_and(|max_pos| a.coeff_at(max_pos).is_negative());
        if is_flipped {
            a = self.neg(&a);
            b = self.neg(&b);
            c = self.neg(&c);
        }
        let square = self.mul(&b, &b);
        let product = self.mul(&a, &c);
        let discriminant = self.addmul(&Int::one(), &square, &Int::from(-4), &product);
        let Some(root) = self.sqrt(&discriminant) else {
            Self::push_factor(result, polynomial, k);
            return Ok(());
        };
        if is_flipped && k % 2 == 1 {
            result.constant = -&result.constant;
        }
        let x = self.mk_power(variable, 1);
        let scaled = self.mul_term(&Int::from(2), x, &a);
        let linear = self.add(&scaled, &b);
        let difference = self.sub(&linear, &root);
        let first = self.pp(&difference, variable)?;
        Self::push_factor(result, &first, k);
        let sum = self.add(&linear, &root);
        let second = self.pp(&sum, variable)?;
        Self::push_factor(result, &second, k);
        Ok(())
    }

    // is_perfect_square for the monomial at a position: the square root of its coefficient when
    // the whole term is a square.
    fn get_term_square_root(&self, polynomial: &Polynomial, position: usize) -> Option<Int> {
        let monomial = polynomial.monomial_at(position);
        if self
            .tables
            .get(monomial)
            .degrees
            .iter()
            .any(|degree| degree % 2 == 1)
        {
            return None;
        }
        get_exact_square_root(&polynomial.coeff_at(position))
    }

    // sqrt: the square root of p with a positive graded-lex leading coefficient, or None.
    pub fn sqrt(&mut self, polynomial: &Polynomial) -> Option<Polynomial> {
        if polynomial.size() == 0 {
            return Some(polynomial.clone());
        }
        let min_pos = self.get_graded_lex_min_pos(polynomial);
        self.get_term_square_root(polynomial, min_pos)?;
        let max_pos = polynomial.get_graded_lex_max_pos(&self.tables)?;
        let a = self.get_term_square_root(polynomial, max_pos)?;
        let max_monomial = self.tables.get(polynomial.monomial_at(max_pos));
        let vars = max_monomial.vars.clone();
        let degrees: Vec<u32> = max_monomial
            .degrees
            .iter()
            .map(|degree| degree / 2)
            .collect();
        let m1 = self.tables.mk_monomial(&vars, &degrees);
        // root is som, rest is som2.
        self.som.reset();
        self.som2.reset();
        let two_a = &Int::from(2) * &a;
        self.som.add_term(a, m1);
        {
            let terms = polynomial.terms();
            for (index, (coeff, monomial)) in terms.as_.iter().zip(&terms.ms).enumerate() {
                if index != max_pos {
                    self.som2.add_term(coeff.clone(), *monomial);
                }
            }
        }
        loop {
            let Some(rest_max) = self.som2.get_graded_lex_max_pos(&self.tables) else {
                self.som2.reset();
                return Some(self.som.mk(&mut self.tables, false));
            };
            let monomial = self.tables.div_monomials(self.som2.ms[rest_max], m1);
            let monomial = match monomial {
                Some(monomial) if (&self.som2.as_[rest_max] % &two_a).is_zero() => monomial,
                _ => {
                    self.som.reset();
                    self.som2.reset();
                    return None;
                }
            };
            let coeff = floor_div(&self.som2.as_[rest_max], &two_a);
            let root_size = self.som.as_.len();
            for index in 0..root_size {
                if self.som.as_[index].is_zero() {
                    continue;
                }
                let term = -(&(&self.som.as_[index] * &coeff) * &Int::from(2));
                let product = self.tables.mul_monomials(self.som.ms[index], monomial);
                self.som2.add_term(term, product);
            }
            let square = self.tables.mul_monomials(monomial, monomial);
            self.som2.add_term(-(&coeff * &coeff), square);
            self.som.add_term(coeff, monomial);
        }
    }

    // graded_lex_min_pos
    fn get_graded_lex_min_pos(&self, polynomial: &Polynomial) -> usize {
        let terms = polynomial.terms();
        let mut min_pos = 0;
        for index in 1..terms.ms.len() {
            if self
                .tables
                .graded_lex_compare(terms.ms[index], terms.ms[min_pos])
                < 0
            {
                min_pos = index;
            }
        }
        min_pos
    }

    // vars: the variables of p in order of occurrence.
    // vars: the variables of p in the order they first occur.
    pub fn get_vars(&self, polynomial: &Polynomial) -> Vec<Var> {
        let mut vars: Vec<Var> = Vec::new();
        for monomial in &polynomial.terms().ms {
            for variable in &self.tables.get(*monomial).vars {
                if !vars.contains(variable) {
                    vars.push(*variable);
                }
            }
        }
        vars
    }

    // substitute: p with each xs[i] replaced by the integer values[i].
    pub fn substitute(
        &mut self,
        polynomial: &Polynomial,
        vars: &[Var],
        values: &[Int],
    ) -> Polynomial {
        self.som.reset();
        let terms = polynomial.terms();
        for (term_coeff, monomial) in terms.as_.iter().zip(&terms.ms) {
            let data = self.tables.get(*monomial);
            let mut coeff = term_coeff.clone();
            let mut kept_vars = Vec::new();
            let mut kept_degrees = Vec::new();
            for (variable, degree) in data.vars.iter().zip(&data.degrees) {
                match vars.iter().position(|current| current == variable) {
                    None => {
                        kept_vars.push(*variable);
                        kept_degrees.push(*degree);
                    }
                    Some(position) => coeff = &coeff * &values[position].pow(*degree),
                }
            }
            let kept = self.tables.mk_monomial(&kept_vars, &kept_degrees);
            self.som.add_term(coeff, kept);
        }
        self.som.mk(&mut self.tables, false)
    }

    // translate: p(x + v), by Horner on the coefficients of p in x.
    pub fn translate(&mut self, polynomial: &Polynomial, variable: Var, value: &Int) -> Polynomial {
        let degree = self.degree(polynomial, variable);
        if degree == 0 || value.is_zero() {
            return polynomial.clone();
        }
        let mut coeffs: Vec<SomBuffer> = (0..=degree).map(|_| SomBuffer::default()).collect();
        {
            let terms = polynomial.terms();
            for (coeff, monomial) in terms.as_.iter().zip(&terms.ms) {
                let power = self.tables.get(*monomial).degree_of(variable);
                let quotient = self.tables.div_x(*monomial, variable);
                coeffs[power as usize].add_term(coeff.clone(), quotient);
            }
        }
        for step in 1..=degree {
            for power in (degree - step)..degree {
                let (lower, upper) = coeffs.split_at_mut(power as usize + 1);
                lower[power as usize].addmul_buffer(&mut self.tables, value, self.unit, &upper[0]);
            }
        }
        self.som.reset();
        for (power, coeff) in coeffs.iter().enumerate() {
            let monomial = self.mk_power(variable, power as u32);
            self.som
                .addmul_buffer(&mut self.tables, &Int::one(), monomial, coeff);
        }
        self.som.mk(&mut self.tables, false)
    }

    // substitute(p, x2v): p with the rational values of its assigned variables, each term scaled
    // by the denominators to the maximal degree of their variable, and the content divided out. p
    // itself when it has no assigned variable.
    pub fn substitute_rational(
        &mut self,
        polynomial: &Polynomial,
        values: &[Option<Rational>],
    ) -> Polynomial {
        let get_value = |variable: Var| values.get(variable as usize).and_then(Option::as_ref);
        // The Vec keeps the order in which the variables first occur, as var_max_degree does.
        let mut max_degrees: Vec<(Var, u32)> = Vec::new();
        for monomial in &polynomial.terms().ms {
            let data = self.tables.get(*monomial);
            for (variable, degree) in data.vars.iter().zip(&data.degrees) {
                match max_degrees.iter_mut().find(|entry| entry.0 == *variable) {
                    Some(entry) => {
                        if *degree > entry.1 {
                            entry.1 = *degree;
                        }
                    }
                    None => {
                        if *degree > 0 {
                            max_degrees.push((*variable, *degree));
                        }
                    }
                }
            }
        }
        if !max_degrees.iter().any(|entry| get_value(entry.0).is_some()) {
            return polynomial.clone();
        }
        self.som.reset();
        let terms = polynomial.terms();
        for (term_coeff, monomial) in terms.as_.iter().zip(&terms.ms) {
            let data = self.tables.get(*monomial);
            let mut coeff = term_coeff.clone();
            let mut kept_vars = Vec::new();
            let mut kept_degrees = Vec::new();
            for (variable, degree) in data.vars.iter().zip(&data.degrees) {
                let Some(value) = get_value(*variable) else {
                    kept_vars.push(*variable);
                    kept_degrees.push(*degree);
                    continue;
                };
                coeff = &coeff * &value.num().pow(*degree);
                let max_degree = max_degrees
                    .iter()
                    .find(|entry| entry.0 == *variable)
                    .map_or(0, |entry| entry.1);
                if *degree < max_degree {
                    coeff = &coeff * &value.den().pow(max_degree - degree);
                }
            }
            for (variable, max_degree) in &max_degrees {
                if let Some(value) = get_value(*variable)
                    && data.degree_of(*variable) == 0
                {
                    coeff = &coeff * &value.den().pow(*max_degree);
                }
            }
            let kept = self.tables.mk_monomial(&kept_vars, &kept_degrees);
            self.som.add_term(coeff, kept);
        }
        self.som.mk(&mut self.tables, true)
    }

    // muladd: p*q + a.
    fn muladd(&mut self, first: &Polynomial, second: &Polynomial, constant: &Int) -> Polynomial {
        if first.size() == 0 || second.size() == 0 {
            return self.mk_const(constant);
        }
        self.som.reset();
        {
            let terms = first.terms();
            for (coeff, monomial) in terms.as_.iter().zip(&terms.ms) {
                self.som.addmul(&mut self.tables, coeff, *monomial, second);
            }
        }
        self.som.add_term(constant.clone(), self.unit);
        self.som.mk(&mut self.tables, false)
    }

    // compose: p(q) for a univariate p, by Horner.
    fn compose(&mut self, polynomial: &Polynomial, inner: &Polynomial) -> Polynomial {
        if self.is_const(polynomial) {
            return polynomial.clone();
        }
        let variable = self.max_var(polynomial);
        let degree = self.degree(polynomial, variable);
        let mut coeffs = vec![Int::zero(); degree as usize + 1];
        {
            let terms = polynomial.terms();
            for (coeff, monomial) in terms.as_.iter().zip(&terms.ms) {
                coeffs[self.tables.get(*monomial).degree_of(variable) as usize] = coeff.clone();
            }
        }
        let mut result = self.mk_const(&coeffs[degree as usize]);
        for power in (0..degree as usize).rev() {
            result = self.muladd(inner, &result, &coeffs[power]);
        }
        result
    }

    // compose_x_minus_y: p(x - y) for a univariate p in x.
    pub fn compose_x_minus_y(&mut self, polynomial: &Polynomial, variable: Var) -> Polynomial {
        let x = self.max_var(polynomial);
        if variable == x {
            return self.coeff(polynomial, x, 0);
        }
        let linear = self.mk_linear(&[Int::one(), Int::from(-1)], &[x, variable], &Int::zero());
        self.compose(polynomial, &linear)
    }

    // compose_x_div_y: y^n * p(x/y) for a univariate p in x of degree n.
    pub fn compose_x_div_y(&mut self, polynomial: &Polynomial, variable: Var) -> Polynomial {
        if self.is_const(polynomial) {
            return polynomial.clone();
        }
        let x = self.max_var(polynomial);
        let degree = self.degree(polynomial, x);
        let terms = polynomial.terms();
        for (coeff, monomial) in terms.as_.iter().zip(&terms.ms) {
            let power = self.tables.get(*monomial).degree_of(x);
            let powers = if x < variable {
                [(x, power), (variable, degree - power)]
            } else {
                [(variable, degree - power), (x, power)]
            };
            let kept: Vec<(Var, u32)> = powers.into_iter().filter(|entry| entry.1 > 0).collect();
            let vars: Vec<Var> = kept.iter().map(|entry| entry.0).collect();
            let degrees: Vec<u32> = kept.iter().map(|entry| entry.1).collect();
            let kept_monomial = self.tables.mk_monomial(&vars, &degrees);
            self.cheap.add(coeff.clone(), kept_monomial);
        }
        self.cheap.mk(&mut self.tables)
    }

    // resultant: Res(p, q) in x, by the subresultant PRS on the primitive parts, times the
    // contents.
    pub fn resultant(
        &mut self,
        first: &Polynomial,
        second: &Polynomial,
        variable: Var,
    ) -> Result<Polynomial, SmtError> {
        if first.size() == 0 || second.size() == 0 {
            return Ok(self.zero());
        }
        if self.is_const(first) {
            if self.is_const(second) {
                return Ok(self.one());
            }
            let degree = self.degree(second, variable);
            return Ok(self.pw(first, degree));
        }
        if self.is_const(second) {
            let degree = self.degree(first, variable);
            return Ok(self.pw(second, degree));
        }
        let (integer_a, content_a, pp_a) = self.iccp(first, variable)?;
        let (integer_b, content_b, pp_b) = self.iccp(second, variable)?;
        let scaled_a = self.mul_const(&integer_a, &content_a);
        let degree_second = self.degree(second, variable);
        let power_a = self.pw(&scaled_a, degree_second);
        let scaled_b = self.mul_const(&integer_b, &content_b);
        let degree_first = self.degree(first, variable);
        let power_b = self.pw(&scaled_b, degree_first);
        let scale = self.mul(&power_a, &power_b);
        let mut a = pp_a;
        let mut b = pp_b;
        let mut sign = 1;
        if self.degree(&a, variable) < self.degree(&b, variable) {
            if self.degree(&a, variable) % 2 == 1 && self.degree(&b, variable) % 2 == 1 {
                sign = -1;
            }
            mem::swap(&mut a, &mut b);
        }
        let mut g = self.one();
        let mut h = self.one();
        loop {
            let degree_a = self.degree(&a, variable);
            let degree_b = self.degree(&b, variable);
            let delta = i64::from(degree_a) - i64::from(degree_b);
            if degree_a % 2 == 1 && degree_b % 2 == 1 {
                sign = -sign;
            }
            let remainder = self.exact_pseudo_remainder(&a, &b, variable);
            a = b;
            b = self.exact_div(&remainder, &g)?;
            for _ in 0..delta {
                b = self.exact_div(&b, &h)?;
            }
            g = self.lc(&a, variable);
            let mut next_h = self.pw(&g, delta as u32);
            for _ in 1..delta {
                next_h = self.exact_div(&next_h, &h)?;
            }
            h = next_h;
            if self.degree(&b, variable) == 0 {
                let degree = self.degree(&a, variable);
                let lc_b = self.lc(&b, variable);
                let mut last_h = self.pw(&lc_b, degree);
                for _ in 1..degree {
                    last_h = self.exact_div(&last_h, &h)?;
                }
                let result = self.mul(&scale, &last_h);
                return Ok(if sign < 0 { self.neg(&result) } else { result });
            }
        }
    }

    fn is_square_free_in(
        &mut self,
        polynomial: &Polynomial,
        variable: Var,
    ) -> Result<bool, SmtError> {
        if self.is_const(polynomial) {
            return Ok(polynomial.size() > 0);
        }
        let derivative = self.derivative(polynomial, variable);
        let gcd = self.gcd(polynomial, &derivative)?;
        Ok(self.is_const(&gcd))
    }

    fn is_primitive(&mut self, polynomial: &Polynomial, variable: Var) -> Result<bool, SmtError> {
        let primitive = self.pp(polynomial, variable)?;
        Ok(self.eq(polynomial, &primitive))
    }

    // factor_n_sqf_pp, try_multivar_factor: reduces p to two variables by evaluating the others,
    // factors it at a point of the lifting variable, lifts a split of the univariate factors with
    // Hensel's lemma and keeps it when the lifted factors multiply back to p. Returns false when
    // no split lifts, leaving p unfactored.
    fn factor_multivariate(
        &mut self,
        polynomial: &Polynomial,
        x: Var,
        k: u32,
        result: &mut Factors,
    ) -> Result<bool, SmtError> {
        let all_vars = self.get_vars(polynomial);
        let mut entries: Vec<(u32, Var)> = all_vars
            .iter()
            .filter(|variable| **variable != x)
            .map(|variable| (self.degree(polynomial, *variable), *variable))
            .collect();
        entries.sort_by(|first, second| second.0.cmp(&first.0).then(second.1.cmp(&first.1)));
        let mut main_vars = vec![x];
        main_vars.extend(
            entries
                .iter()
                .filter(|entry| entry.0 > 1)
                .map(|entry| entry.1),
        );
        for main_var in main_vars {
            let deg_main = self.degree(polynomial, main_var);
            if deg_main <= 1 {
                continue;
            }
            for lift_var in all_vars.iter().copied() {
                if lift_var == main_var {
                    continue;
                }
                let eval_vars: Vec<Var> = all_vars
                    .iter()
                    .copied()
                    .filter(|variable| *variable != main_var && *variable != lift_var)
                    .collect();
                let max_combos: u64 = if eval_vars.is_empty() { 1 } else { 5 };
                for combo in 0..max_combos {
                    let bivariate = if eval_vars.is_empty() {
                        polynomial.clone()
                    } else {
                        let count = FACTOR_EVAL_VALUES.len() as u64;
                        let values: Vec<Int> = (0..eval_vars.len())
                            .map(|index| {
                                let digit = count
                                    .checked_pow(index as u32)
                                    .map_or(0, |power| combo / power)
                                    % count;
                                Int::from(FACTOR_EVAL_VALUES[digit as usize])
                            })
                            .collect();
                        self.substitute(polynomial, &eval_vars, &values)
                    };
                    if self.degree(&bivariate, main_var) != deg_main {
                        continue;
                    }
                    let deg_lift = self.degree(&bivariate, lift_var);
                    if deg_lift == 0 {
                        continue;
                    }
                    for point_value in FACTOR_EVAL_VALUES {
                        let point = Int::from(point_value);
                        let univariate =
                            self.substitute(&bivariate, &[lift_var], std::slice::from_ref(&point));
                        if !self.is_univariate(&univariate) {
                            continue;
                        }
                        if self.degree(&univariate, main_var) != deg_main {
                            continue;
                        }
                        if !self.is_square_free_in(&univariate, main_var)? {
                            continue;
                        }
                        let mut univariate_fs = UpolynomialFactors {
                            constant: Int::one(),
                            factors: Vec::new(),
                            degrees: Vec::new(),
                        };
                        let coeffs = self.to_coeffs(&univariate);
                        let primitive = self.um.get_primitive(&coeffs);
                        factor_square_free(
                            &mut self.um,
                            &primitive,
                            &mut univariate_fs,
                            1,
                            &DEFAULT_FACTOR_PARAMS,
                        )?;
                        let factor_count = univariate_fs.factors.len();
                        if factor_count <= 1 {
                            continue;
                        }
                        let translated = self.translate(&bivariate, lift_var, &point);
                        let lc_polynomial = self.coeff(&translated, main_var, deg_main);
                        let lc_at_zero = if self.is_const(&lc_polynomial) {
                            Some(if lc_polynomial.size() == 0 {
                                Int::zero()
                            } else {
                                lc_polynomial.coeff_at(0)
                            })
                        } else {
                            let substituted =
                                self.substitute(&lc_polynomial, &[lift_var], &[Int::zero()]);
                            self.get_const_value(&substituted)
                        };
                        let Some(lc_at_zero) = lc_at_zero else {
                            continue;
                        };
                        for prime_value in FACTOR_PRIMES {
                            let prime = Int::from(prime_value);
                            if get_gcd(&prime, &lc_at_zero) != Int::one() {
                                continue;
                            }
                            for split in 1..=factor_count / 2 {
                                let mut h1 = univariate_fs.factors[0].clone();
                                for factor in &univariate_fs.factors[1..split] {
                                    h1 = self.um.mul(&h1, factor);
                                }
                                let mut h2 = univariate_fs.factors[split].clone();
                                for factor in &univariate_fs.factors[split + 1..] {
                                    h2 = self.um.mul(&h2, factor);
                                }
                                let h1 = self.um.flip_sign_if_lm_neg(&h1);
                                let h2 = self.um.flip_sign_if_lm_neg(&h2);
                                let Some(lifted) = self.lift_bivariate(
                                    &translated,
                                    main_var,
                                    lift_var,
                                    deg_lift,
                                    &h1,
                                    &h2,
                                    &lc_at_zero,
                                    &prime,
                                )?
                                else {
                                    continue;
                                };
                                let negated = -&point;
                                let candidates: Vec<Polynomial> = lifted
                                    .iter()
                                    .map(|factor| self.translate(factor, lift_var, &negated))
                                    .collect();
                                if eval_vars.is_empty() {
                                    for candidate in &candidates {
                                        if self.is_const(candidate)
                                            || self.degree(candidate, x) == 0
                                        {
                                            continue;
                                        }
                                        self.push_small_factor(candidate, x, k, result)?;
                                    }
                                    return Ok(true);
                                }
                                for candidate in &candidates {
                                    if self.is_const(candidate) {
                                        continue;
                                    }
                                    let max_var = self.max_var(candidate);
                                    let division = self.exact_pseudo_division(
                                        polynomial, candidate, max_var, true,
                                    );
                                    if division.remainder.size() != 0 {
                                        continue;
                                    }
                                    let product = self.mul(candidate, &division.quotient);
                                    if !self.eq(&product, polynomial) {
                                        continue;
                                    }
                                    for part in [candidate, &division.quotient] {
                                        if self.is_const(part) {
                                            result.constant = &result.constant * &part.coeff_at(0);
                                        } else if self.degree(part, x) != 0 {
                                            self.push_small_factor(part, x, k, result)?;
                                        }
                                    }
                                    return Ok(true);
                                }
                            }
                        }
                    }
                }
            }
        }
        Ok(false)
    }

    // The factors of a lifted part, splitting only linear and quadratic ones further.
    fn push_small_factor(
        &mut self,
        polynomial: &Polynomial,
        x: Var,
        k: u32,
        result: &mut Factors,
    ) -> Result<(), SmtError> {
        let degree = self.degree(polynomial, x);
        if degree == 2
            && self.is_primitive(polynomial, x)?
            && self.is_square_free_in(polynomial, x)?
        {
            self.factor_quadratic(polynomial, x, k, result)
        } else {
            Self::push_factor(result, polynomial, k);
            Ok(())
        }
    }

    fn get_const_value(&self, polynomial: &Polynomial) -> Option<Int> {
        if !self.is_const(polynomial) {
            return None;
        }
        Some(if polynomial.size() == 0 {
            Int::zero()
        } else {
            polynomial.coeff_at(0)
        })
    }

    // try_bivar_hensel_lift: lifts q(x, 0) = lc * h1 * h2 to q = F1 * F2 in Z_p[x][y] by linear
    // Hensel lifting on the coefficients of y, then reads F1 and F2 back over Z. None when h1 and
    // h2 are not coprime in Z_p, q is not bivariate, or the product of the lifted factors is not
    // q.
    #[expect(clippy::too_many_arguments, reason = "the TS function's parameters")]
    fn lift_bivariate(
        &mut self,
        q: &Polynomial,
        x: Var,
        y: Var,
        deg_y: u32,
        h1: &[Int],
        h2: &[Int],
        lc: &Int,
        prime: &Int,
    ) -> Result<Option<[Polynomial; 2]>, SmtError> {
        let zp = UpolynomialManager::new(Some(prime.clone()));
        let f1 = zp.mk_monic(&zp.set(h1))?;
        let f2 = zp.mk_monic(&zp.set(h2))?;
        let ext = zp.ext_gcd(&f1, &f2)?;
        if ext.d.len() != 1 || ext.d[0] != Int::one() {
            return Ok(None);
        }
        let mut q_coeffs: Vec<Upolynomial> = Vec::new();
        for power in 0..=deg_y {
            let coeff = self.coeff(q, y, power);
            if coeff.size() != 0 && !self.is_univariate(&coeff) && !self.is_const(&coeff) {
                return Ok(None);
            }
            let coeffs = if coeff.size() == 0 {
                Vec::new()
            } else {
                self.to_coeffs(&coeff)
            };
            q_coeffs.push(zp.set(&coeffs));
        }
        let size = deg_y as usize + 1;
        let mut f1_coeffs: Vec<Upolynomial> = vec![Vec::new(); size];
        let mut f2_coeffs: Vec<Upolynomial> = vec![Vec::new(); size];
        f1_coeffs[0] = zp.set(&f1);
        f2_coeffs[0] = zp.mul_const(&f2, &zp.normalize_numeral(lc));
        let lc_inv = zp.inv(lc)?;
        for power in 1..size {
            let mut error = zp.set(&q_coeffs[power]);
            for (first, f1_coeff) in f1_coeffs.iter().enumerate().take(power + 1) {
                let second = power - first;
                if second >= size || second == 0 || first == 0 {
                    continue;
                }
                if f1_coeff.is_empty() || f2_coeffs[second].is_empty() {
                    continue;
                }
                let product = zp.mul(f1_coeff, &f2_coeffs[second]);
                error = zp.sub(&error, &product);
            }
            if error.is_empty() {
                continue;
            }
            let a = zp.div_rem(&zp.mul(&error, &ext.v), &f1).remainder;
            let b = zp.div_rem(&zp.mul(&error, &ext.u), &f2).remainder;
            f1_coeffs[power] = zp.mul_const(&a, &lc_inv);
            f2_coeffs[power] = zp.set(&b);
        }
        let to_polynomial = |pm: &mut PolynomialManager, coeffs: &[Upolynomial]| {
            let mut result = pm.zero();
            for (power, coeff) in coeffs.iter().enumerate() {
                if coeff.is_empty() {
                    continue;
                }
                let univariate = pm.from_coeffs(coeff, x);
                if univariate.size() == 0 {
                    continue;
                }
                let monomial = pm.mk_power(y, power as u32);
                let term = pm.mul_term(&Int::one(), monomial, &univariate);
                result = pm.add(&result, &term);
            }
            result
        };
        let first = to_polynomial(self, &f1_coeffs);
        let second = to_polynomial(self, &f2_coeffs);
        let product = self.mul(&first, &second);
        Ok(if self.eq(&product, q) {
            Some([first, second])
        } else {
            None
        })
    }

    // psc_chain: the nonzero principal subresultant coefficients of p and q in x, the resultant
    // first, or [0] when there are none. psc_chain_optimized: Ducos's subresultant chain with
    // Lazard's dichotomous S_e.
    pub fn psc_chain(
        &mut self,
        first: &Polynomial,
        second: &Polynomial,
        variable: Var,
    ) -> Result<Vec<Polynomial>, SmtError> {
        let mut chain = if self.degree(first, variable) >= self.degree(second, variable) {
            self.psc_chain_core(first, second, variable)?
        } else {
            self.psc_chain_core(second, first, variable)?
        };
        if chain.is_empty() {
            return Ok(vec![self.zero()]);
        }
        chain.reverse();
        Ok(chain)
    }

    fn psc_chain_core(
        &mut self,
        p: &Polynomial,
        q: &Polynomial,
        x: Var,
    ) -> Result<Vec<Polynomial>, SmtError> {
        let mut chain = Vec::new();
        let lc_q = self.lc(q, x);
        let mut s = self.pw(&lc_q, self.degree(p, x) - self.degree(q, x));
        let mut a = q.clone();
        let negated = self.neg(q);
        let mut b = self.exact_pseudo_remainder(p, &negated, x);
        while b.size() > 0 {
            let d = self.degree(&a, x);
            let e = self.degree(&b, x);
            // b is S_{d-1}.
            let principal = self.coeff(&b, x, d - 1);
            if principal.size() > 0 {
                chain.push(principal);
            }
            let mut c = b.clone();
            if d > e + 1 {
                c = self.get_se_lazard(d, &s, &b, x)?;
                let principal_e = self.coeff(&c, x, e);
                if principal_e.size() > 0 {
                    chain.push(principal_e);
                }
            }
            if e == 0 {
                break;
            }
            b = self.get_optimized_se1(d, e, &a, &b, &c, &s, x)?;
            a = c;
            s = self.lc(&a, x);
        }
        Ok(chain)
    }

    // Se_Lazard: S_e from S_{d-1} and lc(S_d) by dichotomous Lazard.
    fn get_se_lazard(
        &mut self,
        d: u32,
        lc_sd: &Polynomial,
        sd1: &Polynomial,
        x: Var,
    ) -> Result<Polynomial, SmtError> {
        let mut n = d - self.degree(sd1, x) - 1;
        if n == 0 {
            return Ok(sd1.clone());
        }
        let lc_sd1 = self.lc(sd1, x);
        let mut a = 1u32 << (31 - n.leading_zeros());
        let mut c = lc_sd1.clone();
        n -= a;
        while a != 1 {
            a /= 2;
            let square = self.mul(&c, &c);
            c = self.exact_div(&square, lc_sd)?;
            if n >= a {
                let product = self.mul(&c, &lc_sd1);
                c = self.exact_div(&product, lc_sd)?;
                n -= a;
            }
        }
        let product = self.mul(&c, sd1);
        self.exact_div(&product, lc_sd)
    }

    // optimized_S_e_1: S_{e-1} from A = S_{d+1}, S_{d-1}, S_e and s = lc(S_d).
    #[expect(clippy::too_many_arguments, reason = "the TS function's parameters")]
    fn get_optimized_se1(
        &mut self,
        d: u32,
        e: u32,
        a: &Polynomial,
        sd1: &Polynomial,
        se: &Polynomial,
        s: &Polynomial,
        x: Var,
    ) -> Result<Polynomial, SmtError> {
        let cd1 = self.lc(sd1, x);
        let lc_se = self.lc(se, x);
        let get_power = |pm: &mut PolynomialManager, power: u32| {
            if power == 0 {
                pm.one()
            } else {
                pm.mk_var(x, power)
            }
        };
        let mut h: Vec<Polynomial> = Vec::new();
        for j in 0..e {
            let power = get_power(self, j);
            h.push(self.mul(&lc_se, &power));
        }
        let power = get_power(self, e);
        let product = self.mul(&lc_se, &power);
        h.push(self.sub(&product, se));
        let x_polynomial = self.mk_var(x, 1);
        for j in (e + 1)..d {
            let xh = self.mul(&x_polynomial, &h[j as usize - 1]);
            let coeff = self.coeff(&xh, x, e);
            let product = self.mul(&coeff, sd1);
            let quotient = self.exact_div(&product, &cd1)?;
            h.push(self.sub(&xh, &quotient));
        }
        let mut sum = self.zero();
        for j in 0..d {
            let coeff = self.coeff(a, x, j);
            let product = self.mul(&coeff, &h[j as usize]);
            sum = self.add(&sum, &product);
        }
        let lc_a = self.lc(a, x);
        let d_polynomial = self.exact_div(&sum, &lc_a)?;
        let xh = self.mul(&x_polynomial, &h[d as usize - 1]);
        let added = self.add(&xh, &d_polynomial);
        let left = self.mul(&cd1, &added);
        let coeff = self.coeff(&xh, x, e);
        let right = self.mul(&coeff, sd1);
        let difference = self.sub(&left, &right);
        let result = self.exact_div(&difference, s)?;
        Ok(if (d - e + 1) % 2 == 1 {
            self.neg(&result)
        } else {
            result
        })
    }

    // Evaluation.

    // t_eval: p at the values of its variables, by Horner on the lexicographically sorted
    // monomials, which sorts p in place as Z3 does.
    pub fn evaluate_with<T, O, F>(
        &self,
        polynomial: &Polynomial,
        ops: &mut O,
        get_value: &mut F,
    ) -> Result<T, SmtError>
    where
        O: ValueOps<T> + ?Sized,
        F: FnMut(Var) -> Result<T, SmtError>,
    {
        if polynomial.size() == 0 {
            return Ok(ops.from_integer(&Int::zero()));
        }
        if self.is_const(polynomial) {
            return Ok(ops.from_integer(&polynomial.coeff_at(0)));
        }
        polynomial.lex_sort(&self.tables);
        self.evaluate_core(
            polynomial,
            ops,
            get_value,
            0,
            polynomial.size(),
            self.max_var(polynomial),
        )
    }

    // t_eval_core: the monomials in [start, end), ignoring the variables above x.
    fn evaluate_core<T, O, F>(
        &self,
        polynomial: &Polynomial,
        ops: &mut O,
        get_value: &mut F,
        start: usize,
        end: usize,
        x: Var,
    ) -> Result<T, SmtError>
    where
        O: ValueOps<T> + ?Sized,
        F: FnMut(Var) -> Result<T, SmtError>,
    {
        // The terms are read one at a time, not borrowed across the callbacks, as the TS reads
        // the arrays.
        if end == start + 1 {
            let mut result = ops.from_integer(&polynomial.coeff_at(start));
            let data = self.tables.get(polynomial.monomial_at(start));
            for (variable, degree) in data.vars.iter().zip(&data.degrees) {
                if *variable > x {
                    break;
                }
                let value = get_value(*variable)?;
                let power = ops.power(&value, *degree)?;
                result = ops.mul(&result, &power)?;
            }
            return Ok(result);
        }
        let value = get_value(x)?;
        let mut result = ops.from_integer(&Int::zero());
        let mut index = start;
        while index < end {
            let degree = self.tables.get(polynomial.monomial_at(index)).degree_of(x);
            if degree == 0 {
                let below = self.max_smaller_than(polynomial, index, end, x);
                let term = if below == NULL_VAR {
                    ops.from_integer(&polynomial.coeff_at(index))
                } else {
                    self.evaluate_core(polynomial, ops, get_value, index, end, below)?
                };
                result = ops.add(&result, &term)?;
                break;
            }
            let mut next = index + 1;
            let mut next_degree = 0;
            while next < end {
                let current = self.tables.get(polynomial.monomial_at(next)).degree_of(x);
                if current < degree {
                    next_degree = current;
                    break;
                }
                next += 1;
            }
            let below = self.max_smaller_than(polynomial, index, next, x);
            let term = if below == NULL_VAR {
                ops.from_integer(&polynomial.coeff_at(index))
            } else {
                self.evaluate_core(polynomial, ops, get_value, index, next, below)?
            };
            result = ops.add(&result, &term)?;
            let power = ops.power(&value, degree - next_degree)?;
            result = ops.mul(&result, &power)?;
            index = next;
        }
        Ok(result)
    }

    // max_smaller_than: the largest variable below x in the monomials in [start, end).
    fn max_smaller_than(&self, polynomial: &Polynomial, start: usize, end: usize, x: Var) -> Var {
        let terms = polynomial.terms();
        let mut max = NULL_VAR;
        for monomial in &terms.ms[start..end] {
            max = max.max(self.tables.get(*monomial).max_smaller_than(x));
        }
        max
    }

    pub fn evaluate(
        &self,
        polynomial: &Polynomial,
        values: &[Option<Rational>],
    ) -> Result<Rational, SmtError> {
        self.evaluate_with(polynomial, &mut RationalOps, &mut |variable: Var| {
            values
                .get(variable as usize)
                .cloned()
                .flatten()
                .ok_or_else(|| SmtError::Invariant(format!("x{variable} is unassigned")))
        })
    }

    pub fn get_sign(
        &self,
        polynomial: &Polynomial,
        values: &[Option<Rational>],
    ) -> Result<i32, SmtError> {
        let value = self.evaluate(polynomial, values)?;
        Ok(if value.is_zero() {
            0
        } else if value.is_positive() {
            1
        } else {
            -1
        })
    }
}

/// polynomial::cache: hash-conses polynomials and memoizes their subresultants and factors. It
/// does not hold the manager: each method takes it.
#[derive(Default)]
pub struct PolynomialCache {
    table: HashMap<String, Polynomial>,
    in_cache: HashSet<u32>,
    psc_chains: HashMap<(u32, u32, Var), Vec<Polynomial>>,
    factorizations: HashMap<u32, Vec<Polynomial>>,
}

impl PolynomialCache {
    pub fn new() -> PolynomialCache {
        PolynomialCache::default()
    }

    pub fn reset(&mut self) {
        self.table.clear();
        self.in_cache.clear();
        self.psc_chains.clear();
        self.factorizations.clear();
    }

    pub fn mk_unique(&mut self, pm: &mut PolynomialManager, polynomial: &Polynomial) -> Polynomial {
        if self.in_cache.contains(&polynomial.id()) {
            return polynomial.clone();
        }
        let key = pm.get_key(polynomial);
        if let Some(existing) = self.table.get(&key) {
            debug_assert!(pm.eq(existing, polynomial));
            return existing.clone();
        }
        self.table.insert(key, polynomial.clone());
        self.in_cache.insert(polynomial.id());
        polynomial.clone()
    }

    pub fn contains(&self, polynomial: &Polynomial) -> bool {
        self.in_cache.contains(&polynomial.id())
    }

    pub fn psc_chain(
        &mut self,
        pm: &mut PolynomialManager,
        first: &Polynomial,
        second: &Polynomial,
        variable: Var,
    ) -> Result<Vec<Polynomial>, SmtError> {
        let p = self.mk_unique(pm, first);
        let q = self.mk_unique(pm, second);
        let key = (p.id(), q.id(), variable);
        if let Some(cached) = self.psc_chains.get(&key) {
            return Ok(cached.clone());
        }
        let chain: Vec<Polynomial> = pm
            .psc_chain(&p, &q, variable)?
            .iter()
            .map(|element| self.mk_unique(pm, element))
            .collect();
        self.psc_chains.insert(key, chain.clone());
        Ok(chain)
    }

    // factor: the distinct factors, without the constant.
    pub fn factor(
        &mut self,
        pm: &mut PolynomialManager,
        polynomial: &Polynomial,
    ) -> Result<Vec<Polynomial>, SmtError> {
        let unique = self.mk_unique(pm, polynomial);
        if let Some(cached) = self.factorizations.get(&unique.id()) {
            return Ok(cached.clone());
        }
        let factors: Vec<Polynomial> = pm
            .factor(&unique)?
            .factors
            .iter()
            .map(|factor| self.mk_unique(pm, factor))
            .collect();
        self.factorizations.insert(unique.id(), factors.clone());
        Ok(factors)
    }
}

#[cfg(test)]
mod tests {
    use super::{PolynomialCache, PolynomialManager, SmtError, Var};
    use crate::nlsat::test_util::{parse_polynomial, read_fixture, show_polynomial};

    fn run_polynomial_command(input: &str) -> Result<String, SmtError> {
        let mut pm = PolynomialManager::new();
        let mut cache = PolynomialCache::new();
        let command = &input[..input.find(' ').expect("a command")];
        let rest = &input[command.len() + 1..];
        if command == "factor" {
            let polynomial = parse_polynomial(&mut pm, rest);
            let factors = cache.factor(&mut pm, &polynomial)?;
            let shown: String = factors
                .iter()
                .map(|factor| format!(" {}", show_polynomial(&pm, factor)))
                .collect();
            return Ok(format!("factors{shown}"));
        }
        if command == "psc" {
            let space = rest.find(' ').expect("a variable");
            let variable: Var = rest[..space].parse().expect("a variable");
            let operands: Vec<&str> = rest[space + 1..].split(" ; ").collect();
            let first = parse_polynomial(&mut pm, operands[0]);
            let second = parse_polynomial(&mut pm, operands[1]);
            let chain = cache.psc_chain(&mut pm, &first, &second, variable)?;
            let shown: String = chain
                .iter()
                .map(|element| format!(" {}", show_polynomial(&pm, element)))
                .collect();
            return Ok(format!("psc{shown}"));
        }
        let operands: Vec<&str> = rest.split(" ; ").collect();
        let first = parse_polynomial(&mut pm, operands[0]);
        let second = parse_polynomial(&mut pm, operands[1]);
        let gcd = pm.gcd(&first, &second)?;
        Ok(format!("gcd {}", show_polynomial(&pm, &gcd)))
    }

    fn check_fixture(name: &str) {
        let mut failures = Vec::new();
        for (input, expected) in read_fixture(name) {
            let actual = run_polynomial_command(&input);
            if actual.as_ref() != Ok(&expected) {
                failures.push(format!(
                    "{input}\n  expected {expected}\n  actual   {actual:?}"
                ));
            }
        }
        assert!(
            failures.is_empty(),
            "{} failures:\n{}",
            failures.len(),
            failures.join("\n")
        );
    }

    // nlsat polynomials: random polynomials of degree 2 or less, with the factors, subresultants
    // and gcds that Z3's polynomial manager computes for them, monomial order included.
    #[test]
    fn computes_the_polynomial_fixture() {
        check_fixture("polynomial.json");
    }

    #[test]
    fn returns_1_for_coprime_primitive_polynomials_where_z3_modular_gcd_returns_2() {
        assert_eq!(
            run_polynomial_command("gcd 2:0^1 -3: ; 2:0^1 -1:"),
            Ok("gcd [1:]".to_string())
        );
    }

    #[test]
    fn computes_the_subresultants_of_a_polynomial_of_degree_2_as_z3_does() {
        assert_eq!(
            run_polynomial_command("psc 0 1:0^2 -2: ; 1:0^1 -1:"),
            Ok("psc [-1:]".to_string())
        );
    }

    // nlsat polynomial factorization: products of random factors in two or three variables, up
    // to degree 2 in each variable per factor, factored as Z3 does: univariate factorization, the
    // square root of a discriminant, and bivariate Hensel lifting at evaluation points, monomial
    // order included.
    #[test]
    fn factors_the_polynomial_factorization_fixture() {
        check_fixture("polynomial-factorization.json");
    }
}
