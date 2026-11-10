// Ported from Z3 (src/math/lp/nex_creator.h, src/math/lp/nex_creator.cpp), MIT license, see
// z3-license.txt. Builds, orders, and simplifies nex expressions. The order compares variables by
// weight, then by index, and simplification sorts products and sums by it and merges like terms.
// Z3 keeps every expression it allocates so that it can free them; here the arena `nexes` does,
// until `clear`.
use std::cmp::Ordering;

use prove_num::Rational;

use crate::lp::nex::{
    Nex, NexId, NexMul, NexPow, NexSum, contains_var, get_degree, get_powers_from_mul,
    get_vars_of_expr, is_elementary, is_zero_scalar,
};

// occ: how many summands a variable divides, and its smallest power among them.
#[derive(Clone, Copy, Debug)]
pub struct Occ {
    pub occs: usize,
    pub power: u32,
}

/// A factor of `mk_mul`: a rational multiplies the coefficient, an expression is a factor.
pub enum NexFactor {
    Expr(NexId),
    Scalar(Rational),
}

#[derive(Default)]
pub struct NexCreator {
    /// The arena of every expression this creator made (nex.rs).
    pub nexes: Vec<Nex>,
    /// The TypeScript's insertion-ordered Map from a variable to its occurrences.
    pub occurences_map: Vec<(usize, Occ)>,
    /// The TypeScript's insertion-ordered Map from a variable to its power.
    pub powers: Vec<(usize, u32)>,
    active_vars_weights: Vec<u32>,
}

impl NexCreator {
    pub fn new() -> NexCreator {
        NexCreator::default()
    }

    // Z3's nex_creator::clear: drops every expression, so no id made before stays valid.
    pub fn clear(&mut self) {
        self.nexes.clear();
    }

    pub fn get_mul(&self, expr: NexId) -> &NexMul {
        match &self.nexes[expr] {
            Nex::Mul(mul) => mul,
            _ => panic!("nex {expr} is not a product"),
        }
    }

    pub fn get_mul_mut(&mut self, expr: NexId) -> &mut NexMul {
        match &mut self.nexes[expr] {
            Nex::Mul(mul) => mul,
            _ => panic!("nex {expr} is not a product"),
        }
    }

    pub fn get_sum(&self, expr: NexId) -> &NexSum {
        match &self.nexes[expr] {
            Nex::Sum(sum) => sum,
            _ => panic!("nex {expr} is not a sum"),
        }
    }

    pub fn get_sum_mut(&mut self, expr: NexId) -> &mut NexSum {
        match &mut self.nexes[expr] {
            Nex::Sum(sum) => sum,
            _ => panic!("nex {expr} is not a sum"),
        }
    }

    fn push(&mut self, expr: Nex) -> NexId {
        self.nexes.push(expr);
        self.nexes.len() - 1
    }

    // Assumes every variable is below k. Growing keeps the weights already set.
    pub fn set_number_of_vars(&mut self, count: usize) {
        self.active_vars_weights.resize(count, 0);
    }

    pub fn set_var_weight(&mut self, variable: usize, weight: u32) {
        self.active_vars_weights[variable] = weight;
    }

    pub fn mk_var(&mut self, variable: usize) -> NexId {
        self.push(Nex::Var(variable))
    }

    pub fn mk_scalar(&mut self, value: Rational) -> NexId {
        self.push(Nex::Scalar(value))
    }

    pub fn mk_sum(&mut self, children: &[NexId]) -> NexId {
        self.push(Nex::Sum(NexSum {
            children: children.to_vec(),
        }))
    }

    // mk_mul(e, es...): a rational multiplies the coefficient, an expression is a factor.
    pub fn mk_mul(&mut self, factors: &[NexFactor]) -> NexId {
        let mut children = Vec::new();
        let mut coeff = Rational::one();
        for factor in factors {
            match factor {
                NexFactor::Scalar(value) => coeff = coeff.mul(value),
                NexFactor::Expr(expr) => children.push(NexPow {
                    expr: *expr,
                    power: 1,
                }),
            }
        }
        self.mk_mul_with_powers(coeff, children)
    }

    pub fn mk_mul_with_powers(&mut self, coeff: Rational, children: Vec<NexPow>) -> NexId {
        self.push(Nex::Mul(NexMul { coeff, children }))
    }

    // mul_factory::mk_reduced.
    fn mk_reduced_mul(&mut self, coeff: Rational, children: Vec<NexPow>) -> NexId {
        if children.is_empty() {
            return self.mk_scalar(coeff);
        }
        if coeff == Rational::one() && children.len() == 1 && children[0].power == 1 {
            return children[0].expr;
        }
        self.mk_mul_with_powers(coeff, children)
    }

    // A weight past the weights set is the TypeScript's undefined, which no comparison favors.
    pub fn gt_var(&self, first: usize, second: usize) -> bool {
        let first_weight = self.active_vars_weights.get(first);
        let second_weight = self.active_vars_weights.get(second);
        if first_weight != second_weight {
            return match (first_weight, second_weight) {
                (Some(first_weight), Some(second_weight)) => first_weight > second_weight,
                _ => false,
            };
        }
        first > second
    }

    // Scalars are the smallest, and the coefficient of a product does not count. Z3's
    // gt_for_sort_join_sum is the same order.
    pub fn gt(&self, first: NexId, second: NexId) -> bool {
        if first == second {
            return false;
        }
        match &self.nexes[first] {
            Nex::Var(_) => self.gt_on_var_nex(first, second),
            Nex::Scalar(value) => matches!(
                &self.nexes[second],
                Nex::Scalar(second_value) if value.compare(second_value) == Ordering::Greater
            ),
            Nex::Mul(_) => self.gt_on_mul_nex(first, second),
            Nex::Sum(sum) => {
                if matches!(self.nexes[second], Nex::Sum(_)) {
                    return self.gt_on_sum_sum(first, second);
                }
                self.gt(sum.children[0], second)
            }
        }
    }

    fn gt_on_var_nex(&self, first: NexId, second: NexId) -> bool {
        let Nex::Var(variable) = self.nexes[first] else {
            panic!("nex {first} is not a variable");
        };
        match &self.nexes[second] {
            Nex::Scalar(_) => true,
            Nex::Var(second_variable) => self.gt_var(variable, *second_variable),
            Nex::Mul(mul) => {
                get_degree(&self.nexes, second) <= 1
                    && self.gt_on_var_nex(first, mul.children[0].expr)
            }
            Nex::Sum(sum) => {
                if self.gt(first, sum.children[0]) {
                    return true;
                }
                !self.gt(sum.children[0], first)
            }
        }
    }

    fn gt_on_mul_nex(&self, mul: NexId, second: NexId) -> bool {
        match &self.nexes[second] {
            Nex::Scalar(_) => false,
            Nex::Var(_) => {
                get_degree(&self.nexes, mul) > 1
                    || self.gt(self.get_mul(mul).children[0].expr, second)
            }
            Nex::Mul(_) => self.gt_on_mul_mul(mul, second),
            Nex::Sum(sum) => self.gt_on_mul_nex(mul, sum.children[0]),
        }
    }

    fn gt_on_mul_mul(&self, first: NexId, second: NexId) -> bool {
        let first_degree = get_degree(&self.nexes, first);
        let second_degree = get_degree(&self.nexes, second);
        if first_degree == second_degree {
            self.gt_on_powers_mul_same_degree(self.get_mul(first), self.get_mul(second))
        } else {
            first_degree > second_degree
        }
    }

    fn gt_on_powers_mul_same_degree(&self, first: &NexMul, second: &NexMul) -> bool {
        let mut first_power = first.children[0].power;
        let mut second_power = second.children[0].power;
        let mut first_index = 0;
        let mut second_index = 0;
        while first_index < first.children.len() && second_index < second.children.len() {
            if self.gt(
                first.children[first_index].expr,
                second.children[second_index].expr,
            ) {
                return true;
            }
            if self.gt(
                second.children[second_index].expr,
                first.children[first_index].expr,
            ) {
                return false;
            }
            if first_power > second_power {
                return true;
            }
            if first_power < second_power {
                return false;
            }
            first_index += 1;
            second_index += 1;
            if first_index < first.children.len() {
                first_power = first.children[first_index].power;
            }
            if second_index < second.children.len() {
                second_power = second.children[second_index].power;
            }
        }
        false
    }

    fn gt_on_sum_sum(&self, first: NexId, second: NexId) -> bool {
        let first = self.get_sum(first);
        let second = self.get_sum(second);
        let size = first.children.len().min(second.children.len());
        for index in 0..size {
            if self.gt(first.children[index], second.children[index]) {
                return true;
            }
            if self.gt(second.children[index], first.children[index]) {
                return false;
            }
        }
        first.children.len() > size
    }

    // A std::map ordered by gt, greatest first: the index of the key and whether it was there,
    // inserting it when absent.
    fn find_or_insert<Value>(
        &self,
        entries: &mut Vec<(NexId, Value)>,
        key: NexId,
        value: Value,
    ) -> (usize, bool) {
        let mut low = 0;
        let mut high = entries.len();
        while low < high {
            let middle = (low + high) >> 1;
            if self.gt(entries[middle].0, key) {
                low = middle + 1;
            } else {
                high = middle;
            }
        }
        if low < entries.len() && !self.gt(key, entries[low].0) {
            return (low, true);
        }
        entries.insert(low, (key, value));
        (low, false)
    }

    pub fn simplify(&mut self, expr: NexId) -> NexId {
        match self.nexes[expr] {
            Nex::Mul(_) => self.simplify_mul(expr),
            Nex::Sum(_) => self.simplify_sum(expr),
            _ => expr,
        }
    }

    // eat_scalar_pow: the coefficient times the factor raised to power when the factor is a
    // constant, else None.
    fn eat_scalar_pow(&self, coeff: &Rational, child: NexPow, power: u32) -> Option<Rational> {
        match &self.nexes[child.expr] {
            Nex::Mul(mul) if mul.children.is_empty() => Some(if mul.coeff == Rational::one() {
                coeff.clone()
            } else {
                coeff.mul(&mul.coeff.pow(child.power * power))
            }),
            Nex::Scalar(value) => Some(if *value == Rational::one() {
                coeff.clone()
            } else {
                coeff.mul(&value.pow(child.power * power))
            }),
            _ => None,
        }
    }

    // simplify_mul with simplify_children_of_mul: folds the constant factors into the
    // coefficient, flattens the product factors, and merges equal factors into powers.
    pub fn simplify_mul(&mut self, mul: NexId) -> NexId {
        let mut children = Vec::new();
        let mut to_promote = Vec::new();
        for child in self.get_mul(mul).children.clone() {
            if let Some(eaten) = self.eat_scalar_pow(&self.get_mul(mul).coeff, child, 1) {
                self.get_mul_mut(mul).coeff = eaten;
                continue;
            }
            let simplified = NexPow {
                expr: self.simplify(child.expr),
                power: child.power,
            };
            if matches!(self.nexes[simplified.expr], Nex::Mul(_)) {
                to_promote.push(simplified);
            } else {
                children.push(simplified);
            }
        }
        for child in to_promote {
            let Nex::Mul(promoted) = &self.nexes[child.expr] else {
                continue;
            };
            for grandchild in promoted.children.clone() {
                match self.eat_scalar_pow(&self.get_mul(mul).coeff, grandchild, child.power) {
                    Some(eaten) => self.get_mul_mut(mul).coeff = eaten,
                    None => children.push(NexPow {
                        expr: grandchild.expr,
                        power: grandchild.power * child.power,
                    }),
                }
            }
            let promoted_coeff = self.get_mul(child.expr).coeff.pow(child.power);
            let target = self.get_mul_mut(mul);
            target.coeff = target.coeff.mul(&promoted_coeff);
        }
        let powers = self.mul_to_powers(children);
        let target = self.get_mul_mut(mul);
        target.children = powers;
        if target.children.len() == 1
            && target.children[0].power == 1
            && target.coeff == Rational::one()
        {
            return target.children[0].expr;
        }
        if target.children.is_empty() || target.coeff.is_zero() {
            let coeff = target.coeff.clone();
            return self.mk_scalar(coeff);
        }
        mul
    }

    // The map already orders the factors by gt, so Z3's sort that follows changes nothing.
    fn mul_to_powers(&self, children: Vec<NexPow>) -> Vec<NexPow> {
        let mut entries: Vec<(NexId, u32)> = Vec::new();
        for child in children {
            let (index, is_found) = self.find_or_insert(&mut entries, child.expr, child.power);
            if is_found {
                entries[index].1 += child.power;
            }
        }
        entries
            .into_iter()
            .map(|entry| NexPow {
                expr: entry.0,
                power: entry.1,
            })
            .collect()
    }

    pub fn simplify_sum(&mut self, sum: NexId) -> NexId {
        self.simplify_children_of_sum(sum);
        let children = &self.get_sum(sum).children;
        if children.len() == 1 {
            return children[0];
        }
        if children.is_empty() {
            return self.mk_scalar(Rational::zero());
        }
        sum
    }

    fn simplify_children_of_sum(&mut self, sum: NexId) {
        let mut children = Vec::new();
        let mut to_promote = Vec::new();
        for child in self.get_sum(sum).children.clone() {
            let simplified = self.simplify(child);
            match &self.nexes[simplified] {
                Nex::Sum(_) => to_promote.push(simplified),
                _ if is_zero_scalar(&self.nexes, simplified) => {}
                Nex::Mul(mul) if mul.coeff.is_zero() => {}
                _ => children.push(simplified),
            }
        }
        for promoted in to_promote {
            for grandchild in &self.get_sum(promoted).children {
                if !is_zero_scalar(&self.nexes, *grandchild) {
                    children.push(*grandchild);
                }
            }
        }
        self.get_sum_mut(sum).children = children;
        self.sort_join_sum(sum);
    }

    // sort_join_sum: merges the summands that differ only in their coefficient, a + 3bc + 2bc into
    // a + 5bc, sorts them by gt, and puts the sum of the scalars last. Like Z3, a merged product
    // takes the new coefficient in place.
    fn sort_join_sum(&mut self, sum: NexId) {
        let mut entries: Vec<(NexId, Rational)> = Vec::new();
        let mut common_scalar = Rational::zero();
        for child in self.get_sum(sum).children.clone() {
            let coeff = match &self.nexes[child] {
                Nex::Scalar(value) => {
                    common_scalar = common_scalar.add(value);
                    continue;
                }
                Nex::Mul(mul) => mul.coeff.clone(),
                _ => Rational::one(),
            };
            let (index, is_found) = self.find_or_insert(&mut entries, child, coeff.clone());
            if is_found {
                entries[index].1 = entries[index].1.add(&coeff);
            }
        }
        let mut children = Vec::new();
        for (key, value) in entries {
            if value.is_zero() {
                continue;
            }
            if matches!(self.nexes[key], Nex::Mul(_)) {
                self.get_mul_mut(key).coeff = value;
                children.push(self.simplify(key));
            } else if value == Rational::one() {
                children.push(key);
            } else {
                children.push(self.mk_mul(&[NexFactor::Scalar(value), NexFactor::Expr(key)]));
            }
        }
        if !common_scalar.is_zero() {
            children.push(self.mk_scalar(common_scalar));
        }
        self.get_sum_mut(sum).children = children;
    }

    pub fn clone(&mut self, expr: NexId) -> NexId {
        match self.nexes[expr].clone() {
            Nex::Var(variable) => self.mk_var(variable),
            Nex::Scalar(value) => self.mk_scalar(value),
            Nex::Mul(mul) => {
                let children = mul
                    .children
                    .iter()
                    .map(|child| NexPow {
                        expr: self.clone(child.expr),
                        power: child.power,
                    })
                    .collect();
                self.mk_mul_with_powers(mul.coeff, children)
            }
            Nex::Sum(sum) => {
                let children: Vec<NexId> = sum
                    .children
                    .iter()
                    .map(|child| self.clone(*child))
                    .collect();
                self.mk_sum(&children)
            }
        }
    }

    // mk_div(a, j): a, a product or the variable itself, divided by the variable once.
    pub fn mk_div_by_var(&mut self, expr: NexId, variable: usize) -> NexId {
        let Nex::Mul(mul) = self.nexes[expr].clone() else {
            return self.mk_scalar(Rational::one());
        };
        let mut children = Vec::new();
        let mut is_seen = false;
        for child in mul.children {
            if is_seen || !contains_var(&self.nexes, child.expr, variable) {
                children.push(NexPow {
                    expr: self.clone(child.expr),
                    power: child.power,
                });
                continue;
            }
            if !matches!(self.nexes[child.expr], Nex::Var(_)) {
                children.push(NexPow {
                    expr: self.mk_div_by_var(child.expr, variable),
                    power: 1,
                });
            }
            if child.power != 1 {
                children.push(NexPow {
                    expr: self.clone(child.expr),
                    power: child.power - 1,
                });
            }
            is_seen = true;
        }
        self.mk_reduced_mul(mul.coeff, children)
    }

    // mk_div_by_mul: each summand, a product or a variable, divided by the product of powers.
    pub fn mk_div(&mut self, expr: NexId, divisor: NexId) -> NexId {
        let mul = match self.nexes[expr].clone() {
            Nex::Sum(sum) => {
                let children: Vec<NexId> = sum
                    .children
                    .iter()
                    .map(|child| self.mk_div(*child, divisor))
                    .collect();
                return self.mk_sum(&children);
            }
            Nex::Mul(mul) => mul,
            _ => return self.mk_scalar(Rational::one()),
        };
        let Nex::Mul(divisor_mul) = &self.nexes[divisor] else {
            panic!("the divisor {divisor} is not a product");
        };
        get_powers_from_mul(&self.nexes, divisor_mul, &mut self.powers);
        let divisor_coeff = divisor_mul.coeff.clone();
        let mut children = Vec::new();
        for child in mul.children {
            let Nex::Var(variable) = self.nexes[child.expr] else {
                children.push(NexPow {
                    expr: self.clone(child.expr),
                    power: child.power,
                });
                continue;
            };
            let Some(position) = self.powers.iter().position(|entry| entry.0 == variable) else {
                children.push(NexPow {
                    expr: self.clone(child.expr),
                    power: child.power,
                });
                continue;
            };
            let divisor_power = self.powers[position].1;
            if child.power > divisor_power {
                children.push(NexPow {
                    expr: self.mk_var(variable),
                    power: child.power - divisor_power,
                });
                self.powers.remove(position);
            } else if child.power == divisor_power {
                self.powers.remove(position);
            } else {
                // The factor is eaten by the divisor, whose variable keeps the rest of its power.
                self.powers[position].1 = divisor_power - child.power;
            }
        }
        self.mk_reduced_mul(mul.coeff.div(&divisor_coeff), children)
    }

    // canonize: a simplified copy with every product of a sum multiplied out. Z3's canonize_mul
    // drops the coefficient of the product; here the summands keep it.
    pub fn canonize(&mut self, expr: NexId) -> NexId {
        if is_elementary(&self.nexes, expr) {
            return self.clone(expr);
        }
        let copy = self.clone(expr);
        let simplified = self.simplify(copy);
        match &self.nexes[simplified] {
            Nex::Sum(sum) => {
                let children: Vec<NexId> = sum
                    .children
                    .clone()
                    .into_iter()
                    .map(|child| self.canonize(child))
                    .collect();
                self.get_sum_mut(simplified).children = children;
                self.simplify(simplified)
            }
            Nex::Mul(_) => self.canonize_mul(simplified),
            _ => simplified,
        }
    }

    fn canonize_mul(&mut self, mul: NexId) -> NexId {
        let mul_children = self.get_mul(mul).children.clone();
        let Some(sum_index) = mul_children
            .iter()
            .position(|child| matches!(self.nexes[child.expr], Nex::Sum(_)))
        else {
            return mul;
        };
        let sum_pow = mul_children[sum_index];
        let sum_clone = if sum_pow.power > 1 {
            Some(self.clone(sum_pow.expr))
        } else {
            None
        };
        let coeff = self.get_mul(mul).coeff.clone();
        let mut summands = Vec::new();
        for summand in self.get_sum(sum_pow.expr).children.clone() {
            let mut children = Vec::new();
            if let Some(sum_clone) = sum_clone {
                children.push(NexPow {
                    expr: sum_clone,
                    power: sum_pow.power - 1,
                });
            }
            children.push(NexPow {
                expr: summand,
                power: 1,
            });
            for (index, child) in mul_children.iter().enumerate() {
                if index != sum_index {
                    children.push(NexPow {
                        expr: self.clone(child.expr),
                        power: child.power,
                    });
                }
            }
            summands.push(self.mk_mul_with_powers(coeff.clone(), children));
        }
        let sum = self.mk_sum(&summands);
        self.canonize(sum)
    }

    // equal: whether the canonical forms agree when each variable weighs its index. The
    // TypeScript canonizes in a new creator; here the canonical forms go in this creator's arena,
    // under the index weights, and its own weights come back after.
    pub fn equal(&mut self, first: NexId, second: NexId) -> bool {
        let count = get_vars_of_expr(&self.nexes, first)
            .into_iter()
            .chain(get_vars_of_expr(&self.nexes, second))
            .map(|variable| variable + 1)
            .fold(0, usize::max);
        let weights = std::mem::take(&mut self.active_vars_weights);
        self.set_number_of_vars(count);
        for variable in 0..count {
            self.set_var_weight(variable, variable as u32);
        }
        let first_canonical = self.canonize(first);
        let second_canonical = self.canonize(second);
        let is_equal = !(self.gt(first_canonical, second_canonical)
            || self.gt(second_canonical, first_canonical));
        self.active_vars_weights = weights;
        is_equal
    }
}
