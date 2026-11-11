// Ported from Z3 (src/nlsat/levelwise.cpp, src/nlsat/nlsat_common.cpp,
// src/util/index_sort_with_mutations.h), MIT license, see z3-license.txt. The levelwise single cell
// construction: around the sample, for each variable below the top one, the interval of root
// functions in which the projected polynomials keep their signs and orders.
//
// Deviation: Z3 breaks two ties by polynomial id: between root functions of equal value and degree,
// and in the order of the arguments of a top-level resultant. Z3 recycles the ids of freed
// polynomials (id_gen in polynomial.cpp), so its ids depend on its reference counting. Here ids
// follow creation order. Either choice bounds a valid cell, but the bounding polynomial can be a
// different one with the same root, such as x0 for -x0. Differential tests count these as ties.

use std::collections::HashSet;
use std::rc::Rc;

use super::SmtError;
use super::algebraic::{AlgebraicManager, Anum, AnumValue};
use super::polynomial::{NULL_VAR, Polynomial, PolynomialCache, PolynomialManager, Var};

// A section is the index-th root of lower. A sector lies between the lower_index-th root of lower
// and the upper_index-th root of upper, and a None bound is infinite.
#[derive(Clone, Default)]
pub struct CellInterval {
    pub is_section: bool,
    pub lower: Option<Polynomial>,
    pub lower_index: u32,
    pub upper: Option<Polynomial>,
    pub upper_index: u32,
}

// lws_spt_threshold, lws_witness_subs_lc and lws_witness_subs_disc.
struct LevelwiseParams {
    spanning_tree_threshold: u32,
    is_witness_subs_lc: bool,
    is_witness_subs_disc: bool,
}

const DEFAULT_LEVELWISE_PARAMS: LevelwiseParams = LevelwiseParams {
    spanning_tree_threshold: 4,
    is_witness_subs_lc: true,
    is_witness_subs_disc: true,
};

#[derive(Clone)]
struct RootFunction {
    value: Anum,
    polynomial: Polynomial,
    index: u32,
    ps_index: usize,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum ProjectionMode {
    Section,
    Sector,
    SpanningTree,
}

// m_side_mask: bit 0 for a root at or below the sample, bit 1 above, 3 for both.
const BOTH_SIDES: u32 = 3;

// stable_index_merge_sort: bottom-up, so each pair is compared once even though comparing refines
// the numbers.
fn sort_indices_stably(
    count: usize,
    mut is_less: impl FnMut(usize, usize) -> Result<bool, SmtError>,
) -> Result<Vec<usize>, SmtError> {
    let mut source: Vec<usize> = (0..count).collect();
    let mut width = 1;
    while width < count {
        let mut target = Vec::with_capacity(count);
        let mut low = 0;
        while low < count {
            let middle = (low + width).min(count);
            let high = (low + 2 * width).min(count);
            let mut left = low;
            let mut right = middle;
            while left < middle && right < high {
                if is_less(source[right], source[left])? {
                    target.push(source[right]);
                    right += 1;
                } else {
                    target.push(source[left]);
                    left += 1;
                }
            }
            target.extend_from_slice(&source[left..middle]);
            target.extend_from_slice(&source[right..high]);
            low += 2 * width;
        }
        source = target;
        width *= 2;
    }
    Ok(source)
}

// todo_set with canonicalization: the distinct primitive, sign-normalized polynomials still to
// project, in insertion order. A polynomial already in the cache goes in as it is.
#[derive(Default)]
pub struct TodoSet {
    pub polynomials: Vec<Polynomial>,
    in_set: HashSet<u32>,
}

impl TodoSet {
    pub fn new() -> TodoSet {
        TodoSet::default()
    }

    pub fn is_empty(&self) -> bool {
        self.polynomials.is_empty()
    }

    pub fn reset(&mut self) {
        self.polynomials = Vec::new();
        self.in_set.clear();
    }

    pub fn contains(&self, polynomial: &Polynomial) -> bool {
        self.in_set.contains(&polynomial.id())
    }

    pub fn insert(
        &mut self,
        pm: &mut PolynomialManager,
        cache: &mut PolynomialCache,
        polynomial: &Polynomial,
    ) -> Result<Polynomial, SmtError> {
        if self.in_set.contains(&polynomial.id()) {
            return Ok(polynomial.clone());
        }
        if cache.contains(polynomial) {
            self.in_set.insert(polynomial.id());
            self.polynomials.push(polynomial.clone());
            return Ok(polynomial.clone());
        }
        let primitive = if pm.is_zero(polynomial) || pm.is_const(polynomial) {
            polynomial.clone()
        } else {
            let variable = pm.max_var(polynomial);
            pm.pp(polynomial, variable)?
        };
        let normalized = pm.flip_sign_if_lm_neg(&primitive);
        let unique = cache.mk_unique(pm, &normalized);
        if !self.in_set.contains(&unique.id()) {
            self.in_set.insert(unique.id());
            self.polynomials.push(unique.clone());
        }
        Ok(unique)
    }

    pub fn get_max_var(&self, pm: &PolynomialManager) -> Var {
        let mut result = NULL_VAR;
        for polynomial in &self.polynomials {
            let variable = pm.max_var(polynomial);
            if result == NULL_VAR || variable > result {
                result = variable;
            }
        }
        result
    }

    // extract_max_polys: moves the polynomials of the maximal variable to out, after clearing it.
    pub fn extract_max_polys(&mut self, pm: &PolynomialManager, out: &mut Vec<Polynomial>) -> Var {
        out.clear();
        let variable = self.get_max_var(pm);
        self.extract_polys_at_level(pm, variable, out);
        variable
    }

    // extract_polys_at_level: moves the polynomials whose maximal variable is x to out.
    pub fn extract_polys_at_level(
        &mut self,
        pm: &PolynomialManager,
        variable: Var,
        out: &mut Vec<Polynomial>,
    ) {
        let mut kept = Vec::new();
        for polynomial in &self.polynomials {
            if pm.max_var(polynomial) != variable {
                kept.push(polynomial.clone());
                continue;
            }
            out.push(polynomial.clone());
            self.in_set.remove(&polynomial.id());
        }
        self.polynomials = kept;
    }
}

// A root function the TS marks as UNSET when absent: the bounds of a section or spanning tree
// projection are always there.
fn get_set_rf(rf: Option<usize>) -> Result<usize, SmtError> {
    rf.ok_or_else(|| SmtError::Invariant("a cell bound without its root function".to_string()))
}

struct Levelwise<'a> {
    pm: &'a mut PolynomialManager,
    am: &'a mut AlgebraicManager,
    cache: &'a mut PolynomialCache,
    sample: &'a [Option<Anum>],
    max_var: Var,
    is_linear: bool,
    params: &'a LevelwiseParams,
    intervals: Vec<CellInterval>,
    todo: TodoSet,
    level: Var,
    level_polys: Vec<Polynomial>,
    witnesses: Vec<Option<Polynomial>>,
    has_roots: Vec<bool>,
    root_functions: Vec<RootFunction>,
    // m_rel.m_pairs: pairs of level_polys indices, smaller first, iterated in insertion order.
    pairs: Vec<(usize, usize)>,
    pair_keys: HashSet<(usize, usize)>,
    side_mask: Vec<u32>,
    is_lc_omitted: Vec<bool>,
    lower_rf: Option<usize>,
    upper_rf: Option<usize>,
}

impl Levelwise<'_> {
    fn get_level(&self) -> usize {
        self.level as usize
    }

    fn get_sign(&mut self, polynomial: &Polynomial) -> Result<i32, SmtError> {
        self.am.eval_sign_at(self.pm, polynomial, self.sample)
    }

    fn get_values_without(&self, variable: Var) -> Vec<Option<Anum>> {
        self.sample
            .iter()
            .enumerate()
            .map(|(index, value)| {
                if index == variable as usize {
                    None
                } else {
                    value.clone()
                }
            })
            .collect()
    }

    fn request_factorized(&mut self, polynomial: Option<&Polynomial>) -> Result<(), SmtError> {
        let Some(polynomial) = polynomial else {
            return Ok(());
        };
        if self.pm.is_const(polynomial) {
            return Ok(());
        }
        for factor in self.cache.factor(self.pm, polynomial)? {
            if !self.pm.is_const(&factor) {
                self.todo.insert(self.pm, self.cache, &factor)?;
            }
        }
        Ok(())
    }

    // The first element of the subresultant chain that is not zero, or None when it is constant.
    fn get_first_psc(
        &mut self,
        first: &Polynomial,
        second: &Polynomial,
        variable: Var,
    ) -> Result<Option<Polynomial>, SmtError> {
        for element in self.cache.psc_chain(self.pm, first, second, variable)? {
            if self.pm.is_zero(&element) {
                continue;
            }
            return Ok(if self.pm.is_const(&element) {
                None
            } else {
                Some(element)
            });
        }
        Ok(None)
    }

    fn get_psc_discriminant(
        &mut self,
        polynomial: &Polynomial,
        variable: Var,
    ) -> Result<Option<Polynomial>, SmtError> {
        if self.pm.is_const(polynomial) || self.pm.degree(polynomial, variable) < 2 {
            return Ok(None);
        }
        let derivative = self.pm.derivative(polynomial, variable);
        self.get_first_psc(polynomial, &derivative, variable)
    }

    // handle_nullified_poly: p vanishes at the sample. Its coefficients, then its partial
    // derivatives level by level, in non-decreasing variable order, until one does not vanish.
    fn handle_nullified_poly(&mut self, polynomial: &Polynomial) -> Result<(), SmtError> {
        let degree = self.pm.degree(polynomial, self.level);
        for power in 0..=degree {
            let coeff = self.pm.coeff(polynomial, self.level, power);
            self.request_factorized(Some(&coeff))?;
        }
        let mut current = vec![(polynomial.clone(), 0)];
        while !current.is_empty() {
            let mut next = Vec::new();
            for (entry_polynomial, min_var) in &current {
                let max_var = self.pm.max_var(entry_polynomial);
                if max_var == NULL_VAR {
                    continue;
                }
                for variable in *min_var..=max_var {
                    if self.pm.degree(entry_polynomial, variable) == 0 {
                        continue;
                    }
                    let derivative = self.pm.derivative(entry_polynomial, variable);
                    if self.pm.is_const(&derivative) {
                        continue;
                    }
                    if self.get_sign(&derivative)? != 0 {
                        self.request_factorized(Some(&derivative))?;
                        return Ok(());
                    }
                    next.push((derivative, variable));
                }
            }
            for (entry_polynomial, _) in &next {
                self.request_factorized(Some(entry_polynomial))?;
            }
            current = next;
        }
        Ok(())
    }

    // choose_nonzero_coeff: a coefficient of p in x that is nonzero at the sample: a constant if
    // there is one, else the least by total degree, size and maximal variable. None when p
    // vanishes.
    fn choose_nonzero_coeff(
        &mut self,
        polynomial: &Polynomial,
        variable: Var,
    ) -> Result<Option<Polynomial>, SmtError> {
        let degree = self.pm.degree(polynomial, variable);
        for power in 0..=degree {
            let coeff = self.pm.coeff(polynomial, variable, power);
            if !self.pm.is_zero(&coeff) && self.pm.is_const(&coeff) {
                return Ok(Some(coeff));
            }
        }
        let mut best: Option<Polynomial> = None;
        for power in 0..=degree {
            let coeff = self.pm.coeff(polynomial, variable, power);
            if self.pm.is_zero(&coeff) || self.get_sign(&coeff)? == 0 {
                continue;
            }
            let total_degree = self.pm.total_degree(&coeff);
            let is_better = match &best {
                None => true,
                Some(current) => {
                    let best_degree = self.pm.total_degree(current);
                    total_degree < best_degree
                        || (total_degree == best_degree
                            && (coeff.size() < current.size()
                                || (coeff.size() == current.size()
                                    && self.pm.max_var(&coeff) < self.pm.max_var(current))))
                }
            };
            if is_better {
                best = Some(coeff);
            }
        }
        Ok(best)
    }

    fn add_projection_for_poly(
        &mut self,
        polynomial: &Polynomial,
        variable: Var,
        witness: Option<&Polynomial>,
        is_lc_added: bool,
        is_disc_added: bool,
    ) -> Result<(), SmtError> {
        let mut is_witness_added = witness.is_some_and(|witness| !self.pm.is_const(witness));
        if is_lc_added {
            let lc = self.pm.lc(polynomial, variable);
            self.request_factorized(Some(&lc))?;
            if is_witness_added && self.params.is_witness_subs_disc && self.get_sign(&lc)? != 0 {
                is_witness_added = false;
            }
        }
        if is_disc_added && let Some(disc) = self.get_psc_discriminant(polynomial, variable)? {
            self.request_factorized(Some(&disc))?;
            if is_witness_added && self.params.is_witness_subs_disc && self.get_sign(&disc)? != 0 {
                is_witness_added = false;
            }
        }
        if is_witness_added {
            self.request_factorized(witness)?;
        }
        Ok(())
    }

    fn add_pair(&mut self, first: usize, second: usize) {
        let first_index = self.root_functions[first].ps_index;
        let second_index = self.root_functions[second].ps_index;
        if first_index != second_index {
            self.add_ps_pair(first_index, second_index);
        }
    }

    fn add_ps_pair(&mut self, first: usize, second: usize) {
        let pair = if first < second {
            (first, second)
        } else {
            (second, first)
        };
        if self.pair_keys.insert(pair) {
            self.pairs.push(pair);
        }
    }

    fn get_sorted_pairs(&self) -> Vec<(usize, usize)> {
        let mut sorted = self.pairs.clone();
        sorted.sort_by(|first, second| {
            if first.0 == second.0 {
                first.1.cmp(&second.1)
            } else {
                first.0.cmp(&second.0)
            }
        });
        sorted
    }

    fn compute_side_mask(&mut self) {
        let Some(lower_rf) = self.lower_rf else {
            return;
        };
        while self.side_mask.len() < self.level_polys.len() {
            self.side_mask.push(0);
        }
        for (index, root_function) in self.root_functions.iter().enumerate() {
            self.side_mask[root_function.ps_index] |= if index <= lower_rf { 1 } else { 2 };
        }
    }

    fn get_bound_index(&self, rf: Option<usize>) -> Option<usize> {
        rf.map(|rf| self.root_functions[rf].ps_index)
    }

    // compute_omit_lc_both_sides: by projective delineability, the leading coefficient of a
    // polynomial with roots on both sides that does not bound the cell may be left out. With
    // is_leaf_required, only for the leaves of the resultant graph.
    fn compute_omit_lc_both_sides(&mut self, is_leaf_required: bool) {
        self.is_lc_omitted = vec![false; self.level_polys.len()];
        if self.root_functions.is_empty() || self.pairs.is_empty() || self.side_mask.is_empty() {
            return;
        }
        let mut degrees = vec![0; self.level_polys.len()];
        for pair in &self.pairs {
            degrees[pair.0] += 1;
            degrees[pair.1] += 1;
        }
        let lower_bound = self.get_bound_index(self.lower_rf);
        let upper_bound = self.get_bound_index(self.upper_rf);
        for (index, degree) in degrees.into_iter().enumerate() {
            if self.side_mask.get(index) != Some(&BOTH_SIDES) {
                continue;
            }
            if is_leaf_required && degree != 1 {
                continue;
            }
            if Some(index) == lower_bound || Some(index) == upper_bound {
                continue;
            }
            self.is_lc_omitted[index] = true;
        }
    }

    fn fill_relation_sector(&mut self) {
        if let Some(lower_rf) = self.lower_rf {
            for index in 0..lower_rf {
                self.add_pair(index, lower_rf);
            }
        }
        if let Some(upper_rf) = self.upper_rf {
            for index in upper_rf + 1..self.root_functions.len() {
                self.add_pair(upper_rf, index);
            }
        }
        if let (Some(lower_rf), Some(upper_rf)) = (self.lower_rf, self.upper_rf) {
            self.add_pair(lower_rf, upper_rf);
        }
    }

    fn fill_relation_section(&mut self) -> Result<(), SmtError> {
        let lower_rf = get_set_rf(self.lower_rf)?;
        for index in 0..lower_rf {
            self.add_pair(index, lower_rf);
        }
        for index in lower_rf + 1..self.root_functions.len() {
            self.add_pair(lower_rf, index);
        }
        Ok(())
    }

    // build_both_side_spanning_tree: by the reaching orders lemma, in order of the lower root, each
    // polynomial with roots on both sides is joined to the remaining one whose upper root is least.
    fn build_both_side_spanning_tree(&mut self) -> Result<(), SmtError> {
        let lower_rf = get_set_rf(self.lower_rf)?;
        let upper_rf = get_set_rf(self.upper_rf)?;
        let mut lower_rfs: Vec<Option<usize>> = vec![None; self.level_polys.len()];
        let mut upper_rfs: Vec<Option<usize>> = vec![None; self.level_polys.len()];
        for index in 0..=lower_rf {
            lower_rfs[self.root_functions[index].ps_index] = Some(index);
        }
        for index in upper_rf..self.root_functions.len() {
            upper_rfs[self.root_functions[index].ps_index] = Some(index);
        }
        // (ps_index, lower_rf, upper_rf); None sorts first, as the TS's UNSET of -1.
        let mut both: Vec<(usize, Option<usize>, Option<usize>)> = (0..self.level_polys.len())
            .map(|ps_index| (ps_index, lower_rfs[ps_index], upper_rfs[ps_index]))
            .filter(|info| self.side_mask.get(info.0) == Some(&BOTH_SIDES))
            .collect();
        both.sort_by_key(|info| info.1);
        for first in 0..both.len().saturating_sub(1) {
            let mut closest = first + 1;
            for index in first + 2..both.len() {
                if both[index].2 < both[closest].2 {
                    closest = index;
                }
            }
            self.add_ps_pair(both[first].0, both[closest].0);
        }
        Ok(())
    }

    fn is_both(&self, rf: usize) -> bool {
        self.side_mask.get(self.root_functions[rf].ps_index) == Some(&BOTH_SIDES)
    }

    fn fill_relation_spanning_tree(&mut self) -> Result<(), SmtError> {
        self.build_both_side_spanning_tree()?;
        let lower_rf = get_set_rf(self.lower_rf)?;
        let upper_rf = get_set_rf(self.upper_rf)?;
        // connect_non_tree_to_bounds
        for index in 0..lower_rf {
            if !self.is_both(index) {
                self.add_pair(index, lower_rf);
            }
        }
        for index in upper_rf + 1..self.root_functions.len() {
            if !self.is_both(index) {
                self.add_pair(upper_rf, index);
            }
        }
        // connect_tree_extremes_to_bounds
        let mut max_lower_both = None;
        for index in 0..lower_rf {
            if self.is_both(index) {
                max_lower_both = Some(index);
            }
        }
        let mut min_upper_both = None;
        for index in upper_rf + 1..self.root_functions.len() {
            if self.is_both(index) {
                min_upper_both = Some(index);
                break;
            }
        }
        if let Some(max_lower_both) = max_lower_both {
            self.add_pair(max_lower_both, lower_rf);
        }
        if let Some(min_upper_both) = min_upper_both {
            self.add_pair(upper_rf, min_upper_both);
        }
        self.add_pair(lower_rf, upper_rf);
        Ok(())
    }

    // isolate_roots_around_sample: the roots of p closest to v, at or below it in lower and above
    // it in upper, only the one at v for a section. Whether p has roots.
    fn isolate_roots_around_sample(
        &mut self,
        ps_index: usize,
        value: &Anum,
        lower: &mut Vec<RootFunction>,
        upper: &mut Vec<RootFunction>,
    ) -> Result<bool, SmtError> {
        let polynomial = self.level_polys[ps_index].clone();
        let values = self.get_values_without(self.level);
        let rational = match &*value.value() {
            AnumValue::Rational(rational) => Some(rational.clone()),
            AnumValue::Cell(_) => None,
        };
        if let Some(rational) = rational {
            let closest =
                self.am
                    .isolate_roots_closest(self.pm, &polynomial, &values, &rational)?;
            for (index, root) in closest.roots.iter().enumerate() {
                let side = if self.am.compare(root, value)? <= 0 {
                    &mut *lower
                } else {
                    &mut *upper
                };
                side.push(RootFunction {
                    value: self.am.copy(root),
                    polynomial: polynomial.clone(),
                    index: closest.indices[index],
                    ps_index,
                });
            }
            return Ok(!closest.roots.is_empty());
        }
        let roots = self.am.isolate_roots(self.pm, &polynomial, &values)?;
        let mut lower_index = None;
        let mut upper_index = None;
        let mut is_section = false;
        for (index, root) in roots.iter().enumerate() {
            let sign = self.am.compare(root, value)?;
            if sign > 0 {
                upper_index = Some(index);
                break;
            }
            lower_index = Some(index);
            if sign == 0 {
                is_section = true;
                break;
            }
        }
        if let Some(lower_index) = lower_index {
            lower.push(RootFunction {
                value: self.am.copy(&roots[lower_index]),
                polynomial: polynomial.clone(),
                index: (lower_index + 1) as u32,
                ps_index,
            });
            if is_section {
                return Ok(!roots.is_empty());
            }
        }
        if let Some(upper_index) = upper_index {
            upper.push(RootFunction {
                value: self.am.copy(&roots[upper_index]),
                polynomial,
                index: (upper_index + 1) as u32,
                ps_index,
            });
        }
        Ok(!roots.is_empty())
    }

    // root_function_lt: by value, ties by degree, descending for the lower partition, whose last
    // element bounds the cell, then by polynomial id.
    fn is_root_function_less(
        &mut self,
        first: &RootFunction,
        second: &RootFunction,
        is_degree_desc: bool,
    ) -> Result<bool, SmtError> {
        if Rc::ptr_eq(&first.polynomial, &second.polynomial) {
            return Ok(first.index < second.index);
        }
        let sign = self.am.compare(&first.value, &second.value)?;
        if sign != 0 {
            return Ok(sign < 0);
        }
        let first_degree = self.pm.degree(&first.polynomial, self.level);
        let second_degree = self.pm.degree(&second.polynomial, self.level);
        if first_degree != second_degree {
            return Ok(if is_degree_desc {
                first_degree > second_degree
            } else {
                first_degree < second_degree
            });
        }
        Ok(first.polynomial.id() < second.polynomial.id())
    }

    fn sort_root_functions(
        &mut self,
        root_functions: &[RootFunction],
        is_degree_desc: bool,
    ) -> Result<Vec<RootFunction>, SmtError> {
        let order = sort_indices_stably(root_functions.len(), |first, second| {
            self.is_root_function_less(
                &root_functions[first],
                &root_functions[second],
                is_degree_desc,
            )
        })?;
        Ok(order
            .into_iter()
            .map(|index| root_functions[index].clone())
            .collect())
    }

    fn set_interval_from_root_partition(
        &mut self,
        value: &Anum,
        middle: usize,
    ) -> Result<(), SmtError> {
        let level = self.get_level();
        if middle == 0 {
            self.lower_rf = None;
            self.upper_rf = Some(0);
            let interval = &mut self.intervals[level];
            interval.upper = Some(self.root_functions[0].polynomial.clone());
            interval.upper_index = self.root_functions[0].index;
            return Ok(());
        }
        self.lower_rf = Some(middle - 1);
        let interval = &mut self.intervals[level];
        interval.lower = Some(self.root_functions[middle - 1].polynomial.clone());
        interval.lower_index = self.root_functions[middle - 1].index;
        if self
            .am
            .compare(&self.root_functions[middle - 1].value, value)?
            == 0
        {
            self.intervals[level].is_section = true;
            self.upper_rf = self.lower_rf;
            return Ok(());
        }
        if middle < self.root_functions.len() {
            self.upper_rf = Some(middle);
            let interval = &mut self.intervals[level];
            interval.upper = Some(self.root_functions[middle].polynomial.clone());
            interval.upper_index = self.root_functions[middle].index;
        }
        Ok(())
    }

    fn add_linear_poly_from_root(
        &mut self,
        root: &Anum,
        is_lower: bool,
    ) -> Result<Polynomial, SmtError> {
        let value = match &*root.value() {
            AnumValue::Rational(value) => value.clone(),
            AnumValue::Cell(_) => {
                return Err(SmtError::Invariant(
                    "a linear cell bound at an irrational root".to_string(),
                ));
            }
        };
        let den = self.pm.mk_const(value.den());
        let variable = self.pm.mk_var(self.level, 1);
        let product = self.pm.mul(&den, &variable)?;
        let num = self.pm.mk_const(value.num());
        let polynomial = self.pm.sub(&product, &num);
        let level = self.get_level();
        let interval = &mut self.intervals[level];
        if is_lower {
            interval.lower = Some(polynomial.clone());
            interval.lower_index = 1;
        } else {
            interval.upper = Some(polynomial.clone());
            interval.upper_index = 1;
        }
        self.level_polys.push(polynomial.clone());
        self.has_roots.push(true);
        let witness = self.choose_nonzero_coeff(&polynomial, self.level)?;
        self.witnesses.push(witness);
        Ok(polynomial)
    }

    fn mk_linear_root_function(&mut self, polynomial: Polynomial, root: &Anum) -> RootFunction {
        RootFunction {
            value: self.am.copy(root),
            polynomial,
            index: 1,
            ps_index: self.level_polys.len() - 1,
        }
    }

    // add_linear_approximations: bounds of degree 2 or more are replaced by linear polynomials
    // whose roots lie between them and the sample, so the cell only shrinks.
    fn add_linear_approximations(&mut self, value: &Anum) -> Result<(), SmtError> {
        let level = self.get_level();
        if self.intervals[level].is_section {
            if !self.am.is_rational(value)? {
                // Z3's NOT_IMPLEMENTED_YET exits the process here.
                return Err(SmtError::NlsatUnsupported(
                    "a linear cell around an irrational section".to_string(),
                ));
            }
            let lower = self.intervals[level].lower.clone().ok_or_else(|| {
                SmtError::Invariant("a section without its polynomial".to_string())
            })?;
            if self.pm.total_degree(&lower) > 1 {
                let polynomial = self.add_linear_poly_from_root(value, true)?;
                let root_function = self.mk_linear_root_function(polynomial, value);
                let lower_rf = get_set_rf(self.lower_rf)?;
                self.root_functions.insert(lower_rf, root_function);
            }
            return Ok(());
        }
        let lower = self.intervals[level].lower.clone();
        if lower.is_some_and(|lower| self.pm.total_degree(&lower) > 1) {
            let lower_rf = get_set_rf(self.lower_rf)?;
            let bound = self.root_functions[lower_rf].value.clone();
            let between = self.am.select(&bound, value)?;
            let polynomial = self.add_linear_poly_from_root(&between, true)?;
            let root_function = self.mk_linear_root_function(polynomial, &between);
            self.root_functions.insert(lower_rf + 1, root_function);
            self.lower_rf = Some(lower_rf + 1);
            if let Some(upper_rf) = self.upper_rf {
                self.upper_rf = Some(upper_rf + 1);
            }
        }
        let upper = self.intervals[level].upper.clone();
        if upper.is_some_and(|upper| self.pm.total_degree(&upper) > 1) {
            let upper_rf = get_set_rf(self.upper_rf)?;
            let bound = self.root_functions[upper_rf].value.clone();
            let between = self.am.select(value, &bound)?;
            let polynomial = self.add_linear_poly_from_root(&between, false)?;
            let root_function = self.mk_linear_root_function(polynomial, &between);
            self.root_functions.insert(upper_rf, root_function);
        }
        Ok(())
    }

    // build_interval: the root functions around the sample, sorted, and the interval they bound.
    fn build_interval(&mut self) -> Result<bool, SmtError> {
        self.root_functions = Vec::new();
        self.pairs.clear();
        self.pair_keys.clear();
        let level = self.get_level();
        self.intervals[level] = CellInterval::default();
        self.lower_rf = None;
        self.upper_rf = None;
        let value = self
            .sample
            .get(level)
            .cloned()
            .flatten()
            .ok_or_else(|| SmtError::Invariant(format!("x{} is unassigned", self.level)))?;
        let mut lower = Vec::new();
        let mut upper = Vec::new();
        self.has_roots = (0..self.level_polys.len())
            .map(|ps_index| {
                self.isolate_roots_around_sample(ps_index, &value, &mut lower, &mut upper)
            })
            .collect::<Result<Vec<bool>, SmtError>>()?;
        if lower.is_empty() && upper.is_empty() {
            return Ok(false);
        }
        let middle = lower.len();
        let mut root_functions = self.sort_root_functions(&lower, true)?;
        root_functions.extend(self.sort_root_functions(&upper, false)?);
        self.root_functions = root_functions;
        self.set_interval_from_root_partition(&value, middle)?;
        if self.is_linear {
            self.add_linear_approximations(&value)?;
        }
        self.compute_side_mask();
        Ok(true)
    }

    fn add_relation_resultants(&mut self) -> Result<(), SmtError> {
        for pair in self.get_sorted_pairs() {
            let first = self.level_polys[pair.0].clone();
            let second = self.level_polys[pair.1].clone();
            let psc = self.get_first_psc(&first, &second, self.level)?;
            self.request_factorized(psc.as_ref())?;
        }
        Ok(())
    }

    // add_adjacent_root_resultants: at the top level, the resultants of the polynomials of
    // adjacent roots.
    fn add_adjacent_root_resultants(&mut self) -> Result<(), SmtError> {
        let mut root_values: Vec<(Anum, Polynomial)> = Vec::new();
        let values = self.get_values_without(self.max_var);
        let mut has_roots = Vec::with_capacity(self.level_polys.len());
        for polynomial in &self.level_polys {
            let roots = self.am.isolate_roots(self.pm, polynomial, &values)?;
            for root in &roots {
                root_values.push((self.am.copy(root), polynomial.clone()));
            }
            has_roots.push(!roots.is_empty());
        }
        self.has_roots = has_roots;
        if root_values.len() < 2 {
            return Ok(());
        }
        let order = sort_indices_stably(root_values.len(), |first, second| {
            Ok(self
                .am
                .compare(&root_values[first].0, &root_values[second].0)?
                < 0)
        })?;
        let mut added = HashSet::new();
        for index in 0..order.len() - 1 {
            let first = &root_values[order[index]].1;
            let second = &root_values[order[index + 1]].1;
            if Rc::ptr_eq(first, second) {
                continue;
            }
            let (low, high) = if first.id() < second.id() {
                (first, second)
            } else {
                (second, first)
            };
            if !added.insert((low.id(), high.id())) {
                continue;
            }
            let psc = self.get_first_psc(low, high, self.max_var)?;
            self.request_factorized(psc.as_ref())?;
        }
        Ok(())
    }

    // Polynomials with roots keep their order by resultants with the section's polynomial. Those
    // without need their leading coefficient and discriminant to stay without.
    fn add_section_projections(&mut self) -> Result<(), SmtError> {
        let section_polynomial = self.intervals[self.get_level()].lower.clone();
        let with_roots: HashSet<usize> = self
            .root_functions
            .iter()
            .map(|root_function| root_function.ps_index)
            .collect();
        for index in 0..self.level_polys.len() {
            let polynomial = self.level_polys[index].clone();
            let is_full = section_polynomial
                .as_ref()
                .is_some_and(|section| Rc::ptr_eq(&polynomial, section))
                || !with_roots.contains(&index);
            let witness = self.witnesses[index].clone();
            self.add_projection_for_poly(&polynomial, self.level, witness.as_ref(), is_full, true)?;
        }
        Ok(())
    }

    fn add_sector_projections(&mut self) -> Result<(), SmtError> {
        for index in 0..self.level_polys.len() {
            let polynomial = self.level_polys[index].clone();
            let is_lc_added = !self.is_lc_omitted.get(index).copied().unwrap_or(false);
            let mut witness = self.witnesses[index].clone();
            // coeffNonNull: a leading coefficient nonzero at the sample is its own witness.
            if is_lc_added
                && witness
                    .as_ref()
                    .is_some_and(|witness| !self.pm.is_const(witness))
                && self.params.is_witness_subs_lc
                && {
                    let lc = self.pm.lc(&polynomial, self.level);
                    self.get_sign(&lc)? != 0
                }
            {
                witness = None;
            }
            self.add_projection_for_poly(
                &polynomial,
                self.level,
                witness.as_ref(),
                is_lc_added,
                true,
            )?;
        }
        Ok(())
    }

    fn should_use_spanning_tree(&self) -> bool {
        if self.params.spanning_tree_threshold < 2 {
            return false;
        }
        if self.root_functions.len() < 4 || self.side_mask.is_empty() {
            return false;
        }
        if self.lower_rf.is_none() || self.upper_rf.is_none() {
            return false;
        }
        if self.get_bound_index(self.lower_rf) == self.get_bound_index(self.upper_rf) {
            return false;
        }
        let mut both_count = 0;
        for index in 0..self.level_polys.len() {
            if self.side_mask.get(index) == Some(&BOTH_SIDES) {
                both_count += 1;
                if both_count >= self.params.spanning_tree_threshold {
                    return true;
                }
            }
        }
        false
    }

    fn process_level_with_mode(
        &mut self,
        mode: ProjectionMode,
        has_interval: bool,
    ) -> Result<(), SmtError> {
        if has_interval {
            if mode == ProjectionMode::Section {
                self.fill_relation_section()?;
            } else {
                if mode == ProjectionMode::Sector {
                    self.fill_relation_sector();
                } else {
                    self.fill_relation_spanning_tree()?;
                }
                self.compute_side_mask();
                self.compute_omit_lc_both_sides(mode == ProjectionMode::SpanningTree);
            }
        }
        if mode == ProjectionMode::Section {
            self.add_section_projections()?;
        } else {
            self.add_sector_projections()?;
        }
        self.add_relation_resultants()
    }

    // collect_non_null_witnesses: a witness per polynomial, until handling the vanishing ones adds
    // no more polynomials at this level.
    fn collect_non_null_witnesses(&mut self) -> Result<(), SmtError> {
        self.witnesses = Vec::new();
        let mut index = 0;
        while index < self.level_polys.len() {
            let polynomial = self.level_polys[index].clone();
            let witness = self.choose_nonzero_coeff(&polynomial, self.level)?;
            if witness.is_none() {
                self.handle_nullified_poly(&polynomial)?;
            }
            self.witnesses.push(witness);
            if index + 1 == self.level_polys.len() {
                self.todo
                    .extract_polys_at_level(self.pm, self.level, &mut self.level_polys);
            }
            index += 1;
        }
        Ok(())
    }

    fn process_level(&mut self) -> Result<(), SmtError> {
        self.is_lc_omitted = Vec::new();
        self.pairs.clear();
        self.pair_keys.clear();
        self.side_mask = Vec::new();
        self.collect_non_null_witnesses()?;
        let has_interval = self.build_interval()?;
        let mode = if self.intervals[self.get_level()].is_section {
            ProjectionMode::Section
        } else if self.should_use_spanning_tree() {
            ProjectionMode::SpanningTree
        } else {
            ProjectionMode::Sector
        };
        self.process_level_with_mode(mode, has_interval)
    }

    // The top level is projected out without an interval. By projective delineability, a
    // polynomial without roots whose leading coefficient is nonzero needs only its discriminant.
    fn process_top_level(&mut self) -> Result<(), SmtError> {
        self.collect_non_null_witnesses()?;
        self.add_adjacent_root_resultants()?;
        for index in 0..self.level_polys.len() {
            let polynomial = self.level_polys[index].clone();
            let lc = self.pm.lc(&polynomial, self.max_var);
            let is_lc_added =
                self.has_roots[index] || self.pm.is_zero(&lc) || self.get_sign(&lc)? == 0;
            if !is_lc_added {
                self.witnesses[index] = None;
            }
            let witness = self.witnesses[index].clone();
            self.add_projection_for_poly(
                &polynomial,
                self.max_var,
                witness.as_ref(),
                is_lc_added,
                true,
            )?;
        }
        Ok(())
    }

    fn single_cell(mut self, polynomials: &[Polynomial]) -> Result<Vec<CellInterval>, SmtError> {
        if self.max_var == 0 {
            return Ok(self.intervals);
        }
        for polynomial in polynomials {
            self.request_factorized(Some(polynomial))?;
        }
        if self.todo.is_empty() {
            return Ok(self.intervals);
        }
        if self.todo.get_max_var(self.pm) == self.max_var {
            self.level = self.todo.extract_max_polys(self.pm, &mut self.level_polys);
            self.process_top_level()?;
        }
        while !self.todo.is_empty() {
            self.level = self.todo.extract_max_polys(self.pm, &mut self.level_polys);
            self.process_level()?;
        }
        Ok(self.intervals)
    }
}

// levelwise::single_cell: the cell intervals of the variables below max_var around the sample.
// is_linear forces linear bounds, for check_assignment's explanations.
pub fn get_single_cell(
    pm: &mut PolynomialManager,
    am: &mut AlgebraicManager,
    cache: &mut PolynomialCache,
    polynomials: &[Polynomial],
    max_var: Var,
    sample: &[Option<Anum>],
    is_linear: bool,
) -> Result<Vec<CellInterval>, SmtError> {
    let levelwise = Levelwise {
        pm,
        am,
        cache,
        sample,
        max_var,
        is_linear,
        params: &DEFAULT_LEVELWISE_PARAMS,
        intervals: (0..max_var).map(|_| CellInterval::default()).collect(),
        todo: TodoSet::new(),
        level: 0,
        level_polys: Vec::new(),
        witnesses: Vec::new(),
        has_roots: Vec::new(),
        root_functions: Vec::new(),
        pairs: Vec::new(),
        pair_keys: HashSet::new(),
        side_mask: Vec::new(),
        is_lc_omitted: Vec::new(),
        lower_rf: None,
        upper_rf: None,
    };
    levelwise.single_cell(polynomials)
}

#[cfg(test)]
mod tests {
    use super::{CellInterval, get_single_cell};
    use crate::nlsat::algebraic::{AlgebraicManager, Anum};
    use crate::nlsat::polynomial::{Polynomial, PolynomialCache, PolynomialManager, Var};
    use crate::nlsat::test_util::{
        parse_polynomial, parse_rational, read_fixture, show_anum, show_polynomial,
    };
    use crate::nlsat::{Int, SmtError};

    fn show_bound(
        pm: &PolynomialManager,
        polynomial: Option<&Polynomial>,
        index: u32,
        infinity: &str,
    ) -> String {
        polynomial.map_or_else(
            || infinity.to_string(),
            |polynomial| format!("{}#{index}", show_polynomial(pm, polynomial)),
        )
    }

    fn set_slot(slots: &mut Vec<Option<Anum>>, index: usize, anum: Anum) {
        if slots.len() <= index {
            slots.resize(index + 1, None);
        }
        slots[index] = Some(anum);
    }

    // The harness's lw programs: a sample of rationals and roots, then the cell intervals of the
    // levelwise single cell construction around it, and the sample its refinements left behind.
    fn run_levelwise_program(program: &str) -> Result<String, SmtError> {
        let mut am = AlgebraicManager::new();
        let mut pm = PolynomialManager::new();
        let mut cache = PolynomialCache::new();
        let mut sample: Vec<Option<Anum>> = Vec::new();
        let mut registers: Vec<Option<Anum>> = Vec::new();
        let mut variable_count = 0;
        let mut lines = Vec::new();
        for line in program.split('\n') {
            let words: Vec<&str> = line.split(' ').collect();
            let number = |index: usize| -> usize { words[index].parse().expect("a number") };
            let output = match words[0] {
                "vars" => {
                    variable_count = number(1);
                    String::new()
                }
                "q" => {
                    let anum = Anum::new(parse_rational(words[2]));
                    set_slot(&mut registers, number(1), anum.clone());
                    show_anum(&mut am, &anum)
                }
                "root" => {
                    let coeffs: Vec<Int> = words[3..]
                        .iter()
                        .map(|word| word.parse().expect("an integer"))
                        .collect();
                    let polynomial = pm.from_coeffs(&coeffs, 0);
                    let anum = am.isolate_roots(&mut pm, &polynomial, &[])?[number(2) - 1].clone();
                    set_slot(&mut registers, number(1), anum.clone());
                    show_anum(&mut am, &anum)
                }
                "set" => {
                    let register = registers[number(2)].clone().expect("a register");
                    let copy = am.copy(&register);
                    set_slot(&mut sample, number(1), copy);
                    String::new()
                }
                _ => {
                    let polynomials: Vec<Polynomial> = words[3..]
                        .join(" ")
                        .split(" ; ")
                        .map(|text| parse_polynomial(&mut pm, text))
                        .collect();
                    let cell = get_single_cell(
                        &mut pm,
                        &mut am,
                        &mut cache,
                        &polynomials,
                        Var::try_from(number(1)).expect("a variable"),
                        &sample,
                        number(2) == 1,
                    )?;
                    let intervals: String = cell
                        .iter()
                        .map(|interval: &CellInterval| {
                            if interval.is_section {
                                format!(
                                    " S{}",
                                    show_bound(
                                        &pm,
                                        interval.lower.as_ref(),
                                        interval.lower_index,
                                        ""
                                    )
                                )
                            } else {
                                format!(
                                    " ({},{})",
                                    show_bound(
                                        &pm,
                                        interval.lower.as_ref(),
                                        interval.lower_index,
                                        "-oo"
                                    ),
                                    show_bound(
                                        &pm,
                                        interval.upper.as_ref(),
                                        interval.upper_index,
                                        "+oo"
                                    )
                                )
                            }
                        })
                        .collect();
                    let values: String = (0..variable_count)
                        .map(|variable| match sample.get(variable).cloned().flatten() {
                            None => " _".to_string(),
                            Some(value) => show_anum(&mut am, &value),
                        })
                        .collect();
                    format!("{intervals} after{values}")
                }
            };
            lines.push(format!("{}{output}", words[0]));
        }
        Ok(lines.join("\n"))
    }

    // Random samples and polynomials, around the top variable left unassigned or, in the linear
    // mode of check_assignment, every variable assigned. The last cases have four polynomials with
    // roots on both sides of the sample, which take the spanning tree heuristic. Cases where Z3
    // breaks a tie between equal roots by its recycled polynomial ids are left out, see the port
    // header.
    #[test]
    fn levelwise() {
        let mut failures = Vec::new();
        for (program, expected) in read_fixture("levelwise.json") {
            let actual = run_levelwise_program(&program);
            if actual.as_ref() != Ok(&expected) {
                failures.push(format!(
                    "{program}\n  expected {expected}\n  actual {actual:?}"
                ));
            }
        }
        assert!(failures.is_empty(), "{}", failures.join("\n\n"));
    }
}
