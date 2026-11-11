// Ported from Z3 (src/math/dd/dd_pdd.h, src/math/dd/dd_pdd.cpp, src/math/dd/pdd_eval.h), MIT
// license, see z3-license.txt. Polynomial decision diagrams over the rationals, which nla's Grobner
// solver works on: a node is x*hi + lo for the variable x at its level, lo has no x, and the leaves
// are values. Only the free semantics is ported, the one nla and dd::solver use: not mod2, mod2N or
// zero_one_vars, nor what only those or polysat use (the boolean operations, substitution of
// values, resolve, quot_rem, and division without the inverse). Nodes are never freed, so there is
// no garbage collection: node indices match Z3's until its first collection, and the node limit
// counts every node made. The op cache keys on both operands, where Z3's eq_entry compares the
// first operand of one entry with the second of the other.
//
// A Pdd is a node index, and its operations are the manager's methods, which take it by value.
use std::collections::{HashMap, HashSet};

use prove_num::{Rational, get_gcd};

use crate::util::error::SmtError;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Pdd(pub usize);

const ZERO_PDD: Pdd = Pdd(0);
const ONE_PDD: Pdd = Pdd(1);
const ADD_OP: u8 = 2;
const SUB_OP: u8 = 3;
const MINUS_OP: u8 = 4;
const MUL_OP: u8 = 5;
const REDUCE_OP: u8 = 6;
// Nodes below this index stand for the operations in the op cache, besides 0 and 1.
const NO_OP: usize = 10;
const INITIAL_FREE_NODES: usize = 1024;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PddMonomial {
    pub coeff: Rational,
    pub vars: Vec<usize>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PddCoefficient {
    pub coeff: Rational,
    pub is_constant: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PddPower {
    pub var: usize,
    pub degree: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PddFactor {
    pub lc: Pdd,
    pub rest: Pdd,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PddVarFactors {
    pub vars: Vec<usize>,
    pub poly: Pdd,
}

struct IteratorNode {
    is_first: bool,
    node: Pdd,
}

struct CommonFactors {
    first: Vec<usize>,
    second: Vec<usize>,
    first_coeff: Rational,
    second_coeff: Rational,
}

pub struct PddManager {
    levels: Vec<usize>,
    los: Vec<usize>,
    his: Vec<usize>,
    values: Vec<Rational>,
    node_table: HashMap<(usize, usize, usize), Pdd>,
    value_table: HashMap<Rational, Pdd>,
    op_cache: HashMap<(u8, usize, usize), Pdd>,
    factor_cache: HashMap<(usize, usize, u32), PddFactor>,
    degrees: Vec<Option<usize>>,
    num_allocated: usize,
    max_num_nodes: usize,
    is_applying: bool,
    pub var2pdd: Vec<Pdd>,
    pub var2level: Vec<usize>,
    pub level2var: Vec<usize>,
}

impl PddManager {
    pub fn new(num_vars: usize) -> PddManager {
        let mut manager = PddManager {
            levels: Vec::new(),
            los: Vec::new(),
            his: Vec::new(),
            values: Vec::new(),
            node_table: HashMap::new(),
            value_table: HashMap::new(),
            op_cache: HashMap::new(),
            factor_cache: HashMap::new(),
            degrees: Vec::new(),
            num_allocated: 0,
            max_num_nodes: 1 << 24,
            is_applying: false,
            var2pdd: Vec::new(),
            var2level: Vec::new(),
            level2var: Vec::new(),
        };
        manager.init_nodes(&(0..num_vars).collect::<Vec<_>>());
        manager
    }

    pub fn reset(&mut self, level2var: &[usize]) {
        self.levels.clear();
        self.los.clear();
        self.his.clear();
        self.values.clear();
        self.node_table.clear();
        self.value_table.clear();
        self.op_cache.clear();
        self.factor_cache.clear();
        self.degrees.clear();
        self.init_nodes(level2var);
    }

    fn init_nodes(&mut self, level2var: &[usize]) {
        for _ in 0..NO_OP {
            self.levels.push(0);
            self.los.push(0);
            self.his.push(0);
        }
        self.los[ONE_PDD.0] = 1;
        self.values.push(Rational::zero());
        self.values.push(Rational::one());
        self.num_allocated = NO_OP + INITIAL_FREE_NODES + level2var.len();
        self.var2pdd = vec![ZERO_PDD; level2var.len()];
        self.var2level = vec![0; level2var.len()];
        self.level2var = vec![0; level2var.len()];
        for (level, &variable) in level2var.iter().enumerate() {
            self.var2pdd[variable] = self
                .make_node(level, ZERO_PDD, ONE_PDD)
                .expect("the variables fit in the initial nodes");
            self.var2level[variable] = level;
            self.level2var[level] = variable;
        }
    }

    pub fn set_max_num_nodes(&mut self, limit: usize) {
        self.max_num_nodes = limit + self.level2var.len();
    }

    pub fn num_nodes(&self) -> usize {
        self.levels.len()
    }

    pub fn num_vars(&self) -> usize {
        self.var2pdd.len()
    }

    pub fn is_val(&self, node: Pdd) -> bool {
        self.his[node.0] == 0
    }

    pub fn level(&self, node: Pdd) -> usize {
        self.levels[node.0]
    }

    // A value node is at level 0, so its var is the lowest variable, as in Z3.
    pub fn var(&self, node: Pdd) -> usize {
        self.level2var[self.levels[node.0]]
    }

    pub fn lo(&self, node: Pdd) -> Pdd {
        Pdd(self.los[node.0])
    }

    pub fn hi(&self, node: Pdd) -> Pdd {
        Pdd(self.his[node.0])
    }

    pub fn val(&self, node: Pdd) -> &Rational {
        &self.values[self.los[node.0]]
    }

    pub fn offset(&self, node: Pdd) -> &Rational {
        let mut current = node;
        while !self.is_val(current) {
            current = self.lo(current);
        }
        self.val(current)
    }

    pub fn mk_var(&mut self, variable: usize) -> Result<Pdd, SmtError> {
        while self.var2level.len() <= variable {
            let next = self.var2level.len();
            let node = self.make_node(next, ZERO_PDD, ONE_PDD)?;
            self.var2pdd.push(node);
            self.var2level.push(next);
            self.level2var.push(next);
        }
        Ok(self.var2pdd[variable])
    }

    pub fn mk_val(&mut self, value: Rational) -> Result<Pdd, SmtError> {
        self.imk_val(value)
    }

    pub fn zero(&self) -> Pdd {
        ZERO_PDD
    }

    pub fn one(&self) -> Pdd {
        ONE_PDD
    }

    pub fn add(&mut self, first: Pdd, second: Pdd) -> Pdd {
        self.apply(first, second, ADD_OP)
    }

    pub fn sub(&mut self, first: Pdd, second: Pdd) -> Pdd {
        self.apply(first, second, SUB_OP)
    }

    pub fn mul(&mut self, first: Pdd, second: Pdd) -> Pdd {
        self.apply(first, second, MUL_OP)
    }

    pub fn reduce(&mut self, first: Pdd, second: Pdd) -> Pdd {
        self.apply(first, second, REDUCE_OP)
    }

    pub fn minus(&mut self, poly: Pdd) -> Pdd {
        self.while_applying(|manager| manager.minus_rec(poly))
    }

    pub fn pow(&mut self, poly: Pdd, exponent: u32) -> Result<Pdd, SmtError> {
        if exponent == 0 {
            return Ok(self.one());
        }
        if exponent == 1 || self.is_zero(poly) || self.is_one(poly) {
            return Ok(poly);
        }
        if self.is_val(poly) {
            let value = self.val(poly).pow(exponent);
            return self.mk_val(value);
        }
        // j even: pow(p,2*j') = pow(p*p,j'); j odd: pow(p,2*j'+1) = p*pow(p*p,j')
        let square = self.mul(poly, poly);
        let half = self.pow(square, exponent / 2)?;
        Ok(if exponent % 2 == 1 {
            self.mul(half, poly)
        } else {
            half
        })
    }

    // apply: operations grow the node limit where Z3 catches mem_out, collects garbage, retries and
    // then doubles the limit. Without garbage to collect, only the doubling matters.
    fn apply(&mut self, first: Pdd, second: Pdd, op: u8) -> Pdd {
        self.while_applying(|manager| manager.apply_rec(first, second, op))
    }

    fn while_applying(
        &mut self,
        compute: impl FnOnce(&mut PddManager) -> Result<Pdd, SmtError>,
    ) -> Pdd {
        self.is_applying = true;
        let result = compute(self);
        self.is_applying = false;
        result.expect("the node limit grows while applying")
    }

    fn apply_rec(&mut self, first: Pdd, second: Pdd, op: u8) -> Result<Pdd, SmtError> {
        match op {
            SUB_OP => {
                if second == ZERO_PDD {
                    return Ok(first);
                }
                if self.is_val(first) && self.is_val(second) {
                    let value = self.val(first).sub(self.val(second));
                    return self.imk_val(value);
                }
            }
            ADD_OP => {
                if first == ZERO_PDD {
                    return Ok(second);
                }
                if second == ZERO_PDD {
                    return Ok(first);
                }
                if self.is_val(first) && self.is_val(second) {
                    let value = self.val(first).add(self.val(second));
                    return self.imk_val(value);
                }
                if self.is_val(first)
                    || (!self.is_val(second) && self.level(first) < self.level(second))
                {
                    return self.apply_rec(second, first, op);
                }
            }
            MUL_OP => {
                if first == ZERO_PDD || second == ZERO_PDD {
                    return Ok(ZERO_PDD);
                }
                if first == ONE_PDD {
                    return Ok(second);
                }
                if second == ONE_PDD {
                    return Ok(first);
                }
                if self.is_val(first) && self.is_val(second) {
                    let value = self.val(first).mul(self.val(second));
                    return self.imk_val(value);
                }
                if self.is_val(first)
                    || (!self.is_val(second) && self.level(first) < self.level(second))
                {
                    return self.apply_rec(second, first, op);
                }
            }
            REDUCE_OP => {
                if second == ZERO_PDD || self.is_val(first) {
                    return Ok(first);
                }
                if self.degree(first) < self.degree(second) {
                    return Ok(first);
                }
                let leading = self.first_leading(second);
                if self.level(leading) > self.level(first) {
                    return Ok(first);
                }
            }
            _ => {}
        }
        let key = (op, first.0, second.0);
        if let Some(&cached) = self.op_cache.get(&key) {
            return Ok(cached);
        }
        let result = self.compute_apply(first, second, op)?;
        self.op_cache.insert(key, result);
        Ok(result)
    }

    fn compute_apply(&mut self, first: Pdd, second: Pdd, op: u8) -> Result<Pdd, SmtError> {
        let first_level = self.level(first);
        let second_level = self.level(second);
        let first_lo = self.lo(first);
        let first_hi = self.hi(first);
        match op {
            ADD_OP => {
                if self.is_val(second) || first_level != second_level {
                    let lo = self.apply_rec(first_lo, second, op)?;
                    return self.make_node(first_level, lo, first_hi);
                }
                let lo = self.apply_rec(first_lo, self.lo(second), op)?;
                let hi = self.apply_rec(first_hi, self.hi(second), op)?;
                self.make_node(first_level, lo, hi)
            }
            SUB_OP => {
                if self.is_val(first) || (!self.is_val(second) && first_level < second_level) {
                    // p - (ax + b) = -ax + (p - b)
                    let lo = self.apply_rec(first, self.lo(second), op)?;
                    let hi = self.minus_rec(self.hi(second))?;
                    return self.make_node(second_level, lo, hi);
                }
                if self.is_val(second) || first_level > second_level {
                    // (ax + b) - k = ax + (b - k)
                    let lo = self.apply_rec(first_lo, second, op)?;
                    return self.make_node(first_level, lo, first_hi);
                }
                // (ax + b) - (cx + d) = (a - c)x + (b - d)
                let lo = self.apply_rec(first_lo, self.lo(second), op)?;
                let hi = self.apply_rec(first_hi, self.hi(second), op)?;
                self.make_node(first_level, lo, hi)
            }
            MUL_OP => {
                if self.is_val(second) || first_level != second_level {
                    // (x*hi(p)+lo(p))*b = x*hi(p)*b + lo(p)*b
                    let lo = self.apply_rec(first_lo, second, op)?;
                    let hi = self.apply_rec(first_hi, second, op)?;
                    return self.make_node(first_level, lo, hi);
                }
                // (xa + b)(xc + d) = x(x*ac + ad + bc) + bd, where ad + bc may be x*e + f, so that the
                // hi child is x*(ac + e) + f.
                let ac = self.apply_rec(first_hi, self.hi(second), op)?;
                let ad = self.apply_rec(first_hi, self.lo(second), op)?;
                let bc = self.apply_rec(first_lo, self.hi(second), op)?;
                let bd = self.apply_rec(first_lo, self.lo(second), op)?;
                let sum = self.apply_rec(ad, bc, ADD_OP)?;
                if !self.is_val(sum) && self.level(sum) == first_level {
                    let hi = self.apply_rec(ac, self.hi(sum), ADD_OP)?;
                    let inner = self.make_node(first_level, self.lo(sum), hi)?;
                    return self.make_node(first_level, bd, inner);
                }
                let inner = self.make_node(first_level, sum, ac)?;
                self.make_node(first_level, bd, inner)
            }
            _ => {
                let leading = self.first_leading(second);
                if self.level(leading) >= first_level {
                    return self.reduce_on_match(first, second);
                }
                let lo = self.apply_rec(first_lo, second, op)?;
                let hi = self.apply_rec(first_hi, second, op)?;
                if lo == first_lo && hi == first_hi {
                    return Ok(first);
                }
                if self.level(lo) < first_level && self.level(hi) <= first_level {
                    return self.make_node(first_level, lo, hi);
                }
                let product = self.apply_rec(hi, self.var2pdd[self.var(first)], MUL_OP)?;
                self.apply_rec(product, lo, ADD_OP)
            }
        }
    }

    fn minus_rec(&mut self, node: Pdd) -> Result<Pdd, SmtError> {
        if node == ZERO_PDD {
            return Ok(ZERO_PDD);
        }
        if self.is_val(node) {
            let value = self.val(node).neg();
            return self.imk_val(value);
        }
        let key = (MINUS_OP, node.0, node.0);
        if let Some(&cached) = self.op_cache.get(&key) {
            return Ok(cached);
        }
        let lo = self.minus_rec(self.lo(node))?;
        let hi = self.minus_rec(self.hi(node))?;
        let result = self.make_node(self.level(node), lo, hi)?;
        self.op_cache.insert(key, result);
        Ok(result)
    }

    // reduce_on_match: the monomials of a that lm(b) divides become (b - lt(b))/lm(b).
    fn reduce_on_match(&mut self, first: Pdd, second: Pdd) -> Result<Pdd, SmtError> {
        let mut current = first;
        while self.lm_occurs(second, current) {
            let quotient = self.lt_quotient(second, current)?;
            let product = self.apply_rec(quotient, second, MUL_OP)?;
            current = self.apply_rec(current, product, ADD_OP)?;
        }
        Ok(current)
    }

    // lm_occurs: whether the leading monomial of p divides a monomial of q.
    fn lm_occurs(&mut self, first: Pdd, second: Pdd) -> bool {
        let mut divisor = self.first_leading(first);
        let mut target = second;
        loop {
            if self.is_val(divisor) {
                return true;
            }
            if self.is_val(target) {
                return false;
            }
            if self.level(divisor) > self.level(target) {
                return false;
            }
            if self.level(divisor) == self.level(target) {
                divisor = self.next_leading(divisor);
                target = self.hi(target);
            } else if self.lm_occurs(divisor, self.hi(target)) {
                return true;
            } else {
                target = self.lo(target);
            }
        }
    }

    // lt_quotient: minus the r such that lt(p)*r is a monomial of q, given lm_occurs(p, q).
    fn lt_quotient(&mut self, first: Pdd, second: Pdd) -> Result<Pdd, SmtError> {
        let mut divisor = self.first_leading(first);
        let mut target = second;
        while !self.is_val(divisor) {
            if self.level(divisor) == self.level(target) {
                divisor = self.next_leading(divisor);
                target = if self.lm_occurs(divisor, self.hi(target)) {
                    self.hi(target)
                } else {
                    self.lo(target)
                };
            } else if self.lm_occurs(divisor, self.hi(target)) {
                return self.lt_quotient_hi(divisor, target);
            } else {
                target = self.lo(target);
            }
        }
        if self.is_val(target) {
            let value = self.val(target).neg().div(self.val(divisor));
            return self.imk_val(value);
        }
        self.lt_quotient_hi(divisor, target)
    }

    fn lt_quotient_hi(&mut self, first: Pdd, second: Pdd) -> Result<Pdd, SmtError> {
        let quotient = self.lt_quotient(first, self.hi(second))?;
        self.apply_rec(self.var2pdd[self.var(second)], quotient, MUL_OP)
    }

    // try_spoly: a*q*qc - b*p*pc, where p = lcm(lm(a),lm(b))/lm(a), q = lcm(lm(a),lm(b))/lm(b) and pc
    // and qc are the leading coefficients of a and b, when the leading monomials share a variable.
    pub fn try_spoly(&mut self, first: Pdd, second: Pdd) -> Result<Option<Pdd>, SmtError> {
        let Some(factors) = self.common_factors(first, second) else {
            return Ok(None);
        };
        let mut first_multiplier = self.mk_val(factors.second_coeff)?;
        for &variable in factors.second.iter().rev() {
            let variable_pdd = self.mk_var(variable)?;
            first_multiplier = self.mul(first_multiplier, variable_pdd);
        }
        let mut second_multiplier = self.mk_val(factors.first_coeff.neg())?;
        for &variable in factors.first.iter().rev() {
            let variable_pdd = self.mk_var(variable)?;
            second_multiplier = self.mul(second_multiplier, variable_pdd);
        }
        let first_product = self.mul(first_multiplier, first);
        let second_product = self.mul(second_multiplier, second);
        Ok(Some(self.add(first_product, second_product)))
    }

    fn common_factors(&mut self, first: Pdd, second: Pdd) -> Option<CommonFactors> {
        let mut first_vars = Vec::new();
        let mut second_vars = Vec::new();
        let mut first_node = self.first_leading(first);
        let mut second_node = self.first_leading(second);
        let mut has_common = false;
        loop {
            if self.is_val(first_node) || self.is_val(second_node) {
                if !has_common {
                    return None;
                }
                while !self.is_val(second_node) {
                    second_vars.push(self.var(second_node));
                    second_node = self.next_leading(second_node);
                }
                while !self.is_val(first_node) {
                    first_vars.push(self.var(first_node));
                    first_node = self.next_leading(first_node);
                }
                let first_coeff = self.val(first_node).clone();
                let second_coeff = self.val(second_node).clone();
                if !first_coeff.is_int() || !second_coeff.is_int() {
                    return Some(CommonFactors {
                        first: first_vars,
                        second: second_vars,
                        first_coeff,
                        second_coeff,
                    });
                }
                let gcd = Rational::from_int(get_gcd(first_coeff.num(), second_coeff.num()));
                return Some(CommonFactors {
                    first: first_vars,
                    second: second_vars,
                    first_coeff: first_coeff.div(&gcd),
                    second_coeff: second_coeff.div(&gcd),
                });
            }
            if self.level(first_node) == self.level(second_node) {
                has_common = true;
                first_node = self.next_leading(first_node);
                second_node = self.next_leading(second_node);
            } else if self.level(first_node) > self.level(second_node) {
                first_vars.push(self.var(first_node));
                first_node = self.next_leading(first_node);
            } else {
                second_vars.push(self.var(second_node));
                second_node = self.next_leading(second_node);
            }
        }
    }

    // lm_lt: compares the leading monomials, then the monomials in degree-lex order.
    pub fn lm_lt(&mut self, first: Pdd, second: Pdd) -> bool {
        let mut first_node = self.first_leading(first);
        let mut second_node = self.first_leading(second);
        while first_node != second_node && !(self.is_val(first_node) && self.is_val(second_node)) {
            if self.is_val(first_node) {
                return true;
            }
            if self.is_val(second_node) {
                return false;
            }
            if self.level(first_node) != self.level(second_node) {
                return self.level(first_node) < self.level(second_node);
            }
            first_node = self.next_leading(first_node);
            second_node = self.next_leading(second_node);
        }
        let var2level = &self.var2level;
        let is_degree_lex_gt = |left: &[usize], right: &[usize]| {
            if left.len() != right.len() {
                return left.len() > right.len();
            }
            let mut index = 0;
            while index < left.len() && left[index] == right[index] {
                index += 1;
            }
            index < left.len() && var2level[left[index]] > var2level[right[index]]
        };
        let compare = |left: &Vec<usize>, right: &Vec<usize>| {
            if is_degree_lex_gt(left, right) {
                std::cmp::Ordering::Less
            } else if is_degree_lex_gt(right, left) {
                std::cmp::Ordering::Greater
            } else {
                std::cmp::Ordering::Equal
            }
        };
        let mut first_monomials: Vec<Vec<usize>> = self
            .monomials(first)
            .into_iter()
            .map(|monomial| monomial.vars)
            .collect();
        first_monomials.sort_by(compare);
        let mut second_monomials: Vec<Vec<usize>> = self
            .monomials(second)
            .into_iter()
            .map(|monomial| monomial.vars)
            .collect();
        second_monomials.sort_by(compare);
        let length = first_monomials.len().min(second_monomials.len());
        for index in 0..length {
            if is_degree_lex_gt(&second_monomials[index], &first_monomials[index]) {
                return true;
            }
            if is_degree_lex_gt(&first_monomials[index], &second_monomials[index]) {
                return false;
            }
        }
        first_monomials.len() == length && second_monomials.len() > length
    }

    pub fn different_leading_term(&mut self, first: Pdd, second: Pdd) -> bool {
        let mut first_node = self.first_leading(first);
        let mut second_node = self.first_leading(second);
        loop {
            if first_node == second_node {
                return false;
            }
            if self.is_val(first_node) || self.is_val(second_node) {
                return true;
            }
            if self.level(first_node) != self.level(second_node) {
                return true;
            }
            first_node = self.next_leading(first_node);
            second_node = self.next_leading(second_node);
        }
    }

    // first_leading: the first node with a term of the leading monomial, the monomial of highest
    // degree and then highest variables.
    fn first_leading(&mut self, node: Pdd) -> Pdd {
        let mut current = node;
        while !self.is_val(current)
            && self.degree(self.hi(current)) + 1 < self.degree(self.lo(current))
        {
            current = self.lo(current);
        }
        current
    }

    fn next_leading(&mut self, node: Pdd) -> Pdd {
        self.first_leading(self.hi(node))
    }

    pub fn degree(&mut self, node: Pdd) -> usize {
        if node == ZERO_PDD || node == ONE_PDD {
            return 0;
        }
        if let Some(Some(cached)) = self.degrees.get(node.0) {
            return *cached;
        }
        let degree = if self.is_val(node) {
            0
        } else {
            let lo_degree = self.degree(self.lo(node));
            lo_degree.max(self.degree(self.hi(node)) + 1)
        };
        if self.degrees.len() <= node.0 {
            self.degrees.resize(node.0 + 1, None);
        }
        self.degrees[node.0] = Some(degree);
        degree
    }

    // factor: p = lc*v^degree + rest, where the degree of v in rest is below degree.
    pub fn factor(
        &mut self,
        poly: Pdd,
        variable: usize,
        degree: u32,
    ) -> Result<PddFactor, SmtError> {
        let variable_level = self.var2level[variable];
        if degree == 0 || self.level(poly) < variable_level {
            return Ok(PddFactor {
                lc: self.zero(),
                rest: poly,
            });
        }
        let key = (poly.0, variable, degree);
        if let Some(&cached) = self.factor_cache.get(&key) {
            return Ok(cached);
        }
        let result = self.compute_factor(poly, variable, degree)?;
        self.factor_cache.insert(key, result);
        Ok(result)
    }

    fn compute_factor(
        &mut self,
        poly: Pdd,
        variable: usize,
        degree: u32,
    ) -> Result<PddFactor, SmtError> {
        let variable_level = self.var2level[variable];
        if self.level(poly) > variable_level {
            let node = self.mk_var(self.var(poly))?;
            let hi_factor = self.factor(self.hi(poly), variable, degree)?;
            let lo_factor = self.factor(self.lo(poly), variable, degree)?;
            let lc = self.mul(hi_factor.lc, node);
            let rest = self.mul(hi_factor.rest, node);
            return Ok(PddFactor {
                lc: self.add(lc, lo_factor.lc),
                rest: self.add(rest, lo_factor.rest),
            });
        }
        let mut found = 0;
        let mut lc = poly;
        while found < degree && !self.is_val(lc) && self.level(lc) == variable_level {
            found += 1;
            lc = self.hi(lc);
        }
        if found < degree {
            return Ok(PddFactor {
                lc: self.zero(),
                rest: poly,
            });
        }
        let mut rest = self.zero();
        let mut power = self.one();
        let mut current = poly;
        for _ in 0..degree {
            let term = self.mul(power, self.lo(current));
            rest = self.add(rest, term);
            current = self.hi(current);
            let variable_pdd = self.mk_var(variable)?;
            power = self.mul(power, variable_pdd);
        }
        Ok(PddFactor { lc, rest })
    }

    // is_binary: v1, x*v1 + v2 or x*v1 + y*v2 + v3, for values v1, v2 and v3.
    pub fn is_binary(&self, node: Pdd) -> bool {
        let lo = self.lo(node);
        self.is_val(node)
            || (self.is_val(self.hi(node))
                && (self.is_val(lo) || (self.is_val(self.hi(lo)) && self.is_val(self.lo(lo)))))
    }

    // get_powers: the variables with a power above 1. The var of a value node is the lowest
    // variable, so Z3 counts a value under that variable as one more power of it.
    pub fn get_powers(&self, poly: Pdd) -> Vec<PddPower> {
        let mut powers = Vec::new();
        let mut marked = HashSet::new();
        let mut todo = vec![poly];
        while let Some(node) = todo.pop() {
            if self.is_val(node) || marked.contains(&node) {
                continue;
            }
            marked.insert(node);
            let variable = self.var(node);
            let mut current = node;
            let mut degree = 1;
            while !self.is_val(current) && self.var(self.hi(current)) == variable {
                degree += 1;
                todo.push(self.lo(current));
                current = self.hi(current);
            }
            if degree > 1 {
                powers.push(PddPower {
                    var: variable,
                    degree,
                });
            }
            if !self.is_val(current) {
                todo.push(self.hi(current));
                todo.push(self.lo(current));
            }
        }
        powers
    }

    // var_is_leaf: whether every node of v has values as children.
    pub fn var_is_leaf(&self, poly: Pdd, variable: usize) -> bool {
        let mut marked = HashSet::new();
        let mut todo = vec![poly];
        while let Some(node) = todo.pop() {
            if self.is_val(node) || marked.contains(&node) {
                continue;
            }
            marked.insert(node);
            if self.var(node) == variable {
                if !self.is_val(self.lo(node)) || !self.is_val(self.hi(node)) {
                    return false;
                }
                continue;
            }
            if !marked.contains(&self.lo(node)) {
                todo.push(self.lo(node));
            }
            if !marked.contains(&self.hi(node)) {
                todo.push(self.hi(node));
            }
        }
        true
    }

    pub fn tree_size(&self, poly: Pdd) -> usize {
        fn get_size(manager: &PddManager, node: Pdd, sizes: &mut HashMap<Pdd, usize>) -> usize {
            if let Some(&cached) = sizes.get(&node) {
                return cached;
            }
            let size = if manager.is_val(node) {
                1
            } else {
                1 + get_size(manager, manager.lo(node), sizes)
                    + get_size(manager, manager.hi(node), sizes)
            };
            sizes.insert(node, size);
            size
        }
        get_size(self, poly, &mut HashMap::new())
    }

    pub fn free_vars(&self, poly: Pdd) -> Vec<usize> {
        let mut vars = Vec::new();
        let mut marked = HashSet::new();
        let mut todo = vec![poly];
        while let Some(node) = todo.pop() {
            if self.is_val(node) || marked.contains(&node) {
                continue;
            }
            let variable_node = self.var2pdd[self.var(node)];
            if !marked.contains(&variable_node) {
                vars.push(self.var(node));
            }
            marked.insert(node);
            marked.insert(variable_node);
            if !marked.contains(&self.lo(node)) {
                todo.push(self.lo(node));
            }
            if !marked.contains(&self.hi(node)) {
                todo.push(self.hi(node));
            }
        }
        vars
    }

    fn imk_val(&mut self, value: Rational) -> Result<Pdd, SmtError> {
        if value.is_zero() {
            return Ok(ZERO_PDD);
        }
        if value == Rational::one() {
            return Ok(ONE_PDD);
        }
        if let Some(&existing) = self.value_table.get(&value) {
            return Ok(existing);
        }
        let node = self.insert_node(0, self.values.len(), 0)?;
        self.values.push(value.clone());
        self.value_table.insert(value, node);
        Ok(node)
    }

    fn make_node(&mut self, level: usize, lo: Pdd, hi: Pdd) -> Result<Pdd, SmtError> {
        if hi == ZERO_PDD {
            Ok(lo)
        } else {
            self.insert_node(level, lo.0, hi.0)
        }
    }

    // insert_node: Z3 adds half as many free nodes again when they run out, and is out of memory
    // when the nodes already number more than the limit.
    fn insert_node(&mut self, level: usize, lo: usize, hi: usize) -> Result<Pdd, SmtError> {
        let key = (level, lo, hi);
        if let Some(&existing) = self.node_table.get(&key) {
            return Ok(existing);
        }
        if self.levels.len() == self.num_allocated {
            if self.num_allocated > self.max_num_nodes && !self.is_applying {
                return Err(SmtError::PddMemoryOut);
            }
            while self.num_allocated > self.max_num_nodes {
                self.max_num_nodes *= 2;
            }
            self.num_allocated += self.num_allocated / 2;
        }
        let node = Pdd(self.levels.len());
        self.levels.push(level);
        self.los.push(lo);
        self.his.push(hi);
        self.node_table.insert(key, node);
        Ok(node)
    }

    // The operations of TypeScript's Pdd class.

    pub fn is_zero(&self, poly: Pdd) -> bool {
        poly == ZERO_PDD
    }

    pub fn is_one(&self, poly: Pdd) -> bool {
        poly == ONE_PDD
    }

    pub fn is_linear(&mut self, poly: Pdd) -> bool {
        self.degree(poly) == 1
    }

    pub fn is_var(&self, poly: Pdd) -> bool {
        !self.is_val(poly) && self.is_zero(self.lo(poly)) && self.is_one(self.hi(poly))
    }

    // a*x for a value a.
    pub fn is_unary(&self, poly: Pdd) -> bool {
        !self.is_val(poly) && self.is_zero(self.lo(poly)) && self.is_val(self.hi(poly))
    }

    // x + b for a value b.
    pub fn is_offset(&self, poly: Pdd) -> bool {
        !self.is_val(poly) && self.is_val(self.lo(poly)) && self.is_one(self.hi(poly))
    }

    // Pdd.add(Rational).
    pub fn add_val(&mut self, poly: Pdd, value: Rational) -> Result<Pdd, SmtError> {
        let value_pdd = self.mk_val(value)?;
        Ok(self.add(value_pdd, poly))
    }

    // Pdd.sub(Rational).
    pub fn sub_val(&mut self, poly: Pdd, value: Rational) -> Result<Pdd, SmtError> {
        self.add_val(poly, value.neg())
    }

    // Pdd.mul(Rational).
    pub fn mul_val(&mut self, poly: Pdd, value: Rational) -> Result<Pdd, SmtError> {
        let value_pdd = self.mk_val(value)?;
        Ok(self.mul(value_pdd, poly))
    }

    // div: in the free semantics, multiplication by the inverse, which shares the op cache.
    pub fn div(&mut self, poly: Pdd, divisor: &Rational) -> Result<Pdd, SmtError> {
        self.mul_val(poly, Rational::one().div(divisor))
    }

    // var_factors: the variables that divide every monomial, with their product divided out.
    pub fn var_factors(&mut self, poly: Pdd) -> Result<PddVarFactors, SmtError> {
        let none = PddVarFactors {
            vars: Vec::new(),
            poly,
        };
        if self.is_val(poly) {
            return Ok(none);
        }
        let variable = self.var(poly);
        if self.is_val(self.lo(poly)) {
            if !self.is_zero(self.lo(poly)) {
                return Ok(none);
            }
            let mut factors = self.var_factors(self.hi(poly))?;
            factors.vars.push(variable);
            return Ok(factors);
        }
        let lo_factors = self.var_factors(self.lo(poly))?;
        let mut lo_vars = lo_factors.vars;
        if lo_vars.is_empty() {
            return Ok(none);
        }
        let mut lo_and_hi = Vec::new();
        let hi_factors = self.var_factors(self.hi(poly))?;
        let mut hi_vars = hi_factors.vars;
        if lo_vars.last() == Some(&variable) {
            lo_vars.pop();
            self.merge_var_factors(&mut lo_vars, &mut hi_vars, &mut lo_and_hi);
            lo_and_hi.push(variable);
            let lo_product = self.multiply_vars(&lo_vars, lo_factors.poly)?;
            let hi_product = self.multiply_vars(&hi_vars, hi_factors.poly)?;
            return Ok(PddVarFactors {
                vars: lo_and_hi,
                poly: self.add(lo_product, hi_product),
            });
        }
        if hi_vars.is_empty() {
            return Ok(none);
        }
        self.merge_var_factors(&mut lo_vars, &mut hi_vars, &mut lo_and_hi);
        hi_vars.push(variable);
        if lo_and_hi.is_empty() {
            return Ok(none);
        }
        let lo_product = self.multiply_vars(&lo_vars, lo_factors.poly)?;
        let hi_product = self.multiply_vars(&hi_vars, hi_factors.poly)?;
        Ok(PddVarFactors {
            vars: lo_and_hi,
            poly: self.add(lo_product, hi_product),
        })
    }

    // Moves the variables in both lists to lo_and_hi and keeps the rest in place, by level.
    fn merge_var_factors(
        &self,
        lo_vars: &mut Vec<usize>,
        hi_vars: &mut Vec<usize>,
        lo_and_hi: &mut Vec<usize>,
    ) {
        let mut lo_kept = 0;
        let mut hi_kept = 0;
        let mut lo_index = 0;
        let mut hi_index = 0;
        while lo_index < lo_vars.len() || hi_index < hi_vars.len() {
            if lo_index == lo_vars.len() {
                hi_vars[hi_kept] = hi_vars[hi_index];
                hi_kept += 1;
                hi_index += 1;
            } else if hi_index == hi_vars.len() {
                lo_vars[lo_kept] = lo_vars[lo_index];
                lo_kept += 1;
                lo_index += 1;
            } else if lo_vars[lo_index] == hi_vars[hi_index] {
                lo_and_hi.push(lo_vars[lo_index]);
                lo_index += 1;
                hi_index += 1;
            } else if self.var2level[lo_vars[lo_index]] > self.var2level[hi_vars[hi_index]] {
                hi_vars[hi_kept] = hi_vars[hi_index];
                hi_kept += 1;
                hi_index += 1;
            } else {
                lo_vars[lo_kept] = lo_vars[lo_index];
                lo_kept += 1;
                lo_index += 1;
            }
        }
        lo_vars.truncate(lo_kept);
        hi_vars.truncate(hi_kept);
    }

    fn multiply_vars(&mut self, vars: &[usize], poly: Pdd) -> Result<Pdd, SmtError> {
        let mut product = poly;
        for &variable in vars {
            let variable_pdd = self.mk_var(variable)?;
            product = self.mul(product, variable_pdd);
        }
        Ok(product)
    }

    // subst_pdd: replaces the variable by the polynomial, without the op cache.
    pub fn subst_pdd(
        &mut self,
        poly: Pdd,
        variable: usize,
        replacement: Pdd,
    ) -> Result<Pdd, SmtError> {
        if self.is_val(poly) || self.var2level[self.var(poly)] < self.var2level[variable] {
            return Ok(poly);
        }
        let lo = self.subst_pdd(self.lo(poly), variable, replacement)?;
        let hi = self.subst_pdd(self.hi(poly), variable, replacement)?;
        if self.var(poly) == variable {
            let product = self.mul(replacement, hi);
            return Ok(self.add(product, lo));
        }
        if lo == self.lo(poly) && hi == self.hi(poly) {
            return Ok(poly);
        }
        let variable_pdd = self.mk_var(self.var(poly))?;
        let product = self.mul(variable_pdd, hi);
        Ok(self.add(product, lo))
    }

    // The monomials, hi before lo, each with its variables from the highest level down.
    pub fn monomials(&self, poly: Pdd) -> Vec<PddMonomial> {
        let mut monomials = Vec::new();
        let mut nodes: Vec<IteratorNode> = Vec::new();
        let mut vars = Vec::new();
        let mut node = poly;
        while !self.is_val(node) {
            nodes.push(IteratorNode {
                is_first: true,
                node,
            });
            vars.push(self.var(node));
            node = self.hi(node);
        }
        if nodes.is_empty() {
            if !self.val(node).is_zero() {
                monomials.push(PddMonomial {
                    coeff: self.val(node).clone(),
                    vars: Vec::new(),
                });
            }
            return monomials;
        }
        monomials.push(PddMonomial {
            coeff: self.val(node).clone(),
            vars: vars.clone(),
        });
        while let Some(top) = nodes.last_mut() {
            if !top.is_first {
                nodes.pop();
                continue;
            }
            top.is_first = false;
            let mut next = self.lo(top.node);
            vars.pop();
            if next == ZERO_PDD {
                nodes.pop();
                continue;
            }
            while !self.is_val(next) {
                nodes.push(IteratorNode {
                    is_first: true,
                    node: next,
                });
                vars.push(self.var(next));
                next = self.hi(next);
            }
            monomials.push(PddMonomial {
                coeff: self.val(next).clone(),
                vars: vars.clone(),
            });
        }
        monomials
    }

    // The coefficients, each marked as the constant term or not. Zero yields one constant 0.
    pub fn coefficients(&self, poly: Pdd) -> Vec<PddCoefficient> {
        let mut coefficients = Vec::new();
        let mut nodes = Vec::new();
        let mut node = poly;
        while !self.is_val(node) {
            nodes.push(node);
            node = self.hi(node);
        }
        coefficients.push(PddCoefficient {
            coeff: self.val(node).clone(),
            is_constant: nodes.is_empty(),
        });
        while let Some(top) = nodes.pop() {
            let mut next = self.lo(top);
            if next == ZERO_PDD {
                continue;
            }
            while !self.is_val(next) {
                nodes.push(next);
                next = self.hi(next);
            }
            coefficients.push(PddCoefficient {
                coeff: self.val(next).clone(),
                is_constant: nodes.is_empty(),
            });
        }
        coefficients
    }

    // Pdd.toString.
    pub fn display(&self, poly: Pdd) -> String {
        let mut text = String::new();
        for monomial in self.monomials(poly) {
            if !text.is_empty() {
                text += " ";
            }
            if monomial.coeff.is_negative() {
                text += "- ";
            } else if !text.is_empty() {
                text += "+ ";
            }
            let coeff = monomial.coeff.abs();
            let vars = &monomial.vars;
            if coeff != Rational::one() || vars.is_empty() {
                text += &if vars.is_empty() {
                    format!("{coeff}")
                } else {
                    format!("{coeff}*")
                };
            }
            let mut factors = Vec::new();
            let mut start = 0;
            while start < vars.len() {
                let mut end = start;
                while end < vars.len() && vars[end] == vars[start] {
                    end += 1;
                }
                factors.push(if end - start > 1 {
                    format!("v{}^{}", vars[start], end - start)
                } else {
                    format!("v{}", vars[start])
                });
                start = end;
            }
            text += &factors.join("*");
        }
        if text.is_empty() {
            "0".to_string()
        } else {
            text
        }
    }
}

// pdd_eval: the value of the polynomial under the values of its variables.
pub fn evaluate_pdd(
    manager: &PddManager,
    poly: Pdd,
    get_value: &mut impl FnMut(usize) -> Rational,
) -> Rational {
    if manager.is_val(poly) {
        return manager.val(poly).clone();
    }
    evaluate_pdd(manager, manager.hi(poly), get_value)
        .mul(&get_value(manager.var(poly)))
        .add(&evaluate_pdd(manager, manager.lo(poly), get_value))
}

#[cfg(test)]
pub(crate) mod tests {
    use std::cell::RefCell;
    use std::fmt;
    use std::ops::{Add, Mul, Neg, Sub};

    use prove_num::Rational;

    use super::{Pdd, PddManager, PddPower, evaluate_pdd};
    use crate::util::error::SmtError;

    pub(crate) fn rational(value: i64) -> Rational {
        Rational::from(value)
    }

    // A pdd with its manager, so that the tests read as the TypeScript's method chains, in the
    // same order of operations.
    #[derive(Clone, Copy)]
    pub(crate) struct Poly<'m> {
        pub manager: &'m RefCell<PddManager>,
        pub pdd: Pdd,
    }

    impl<'m> Poly<'m> {
        fn wrap(&self, pdd: Pdd) -> Poly<'m> {
            Poly {
                manager: self.manager,
                pdd,
            }
        }

        pub fn pow(self, exponent: u32) -> Poly<'m> {
            let pdd = self.manager.borrow_mut().pow(self.pdd, exponent).unwrap();
            self.wrap(pdd)
        }

        pub fn reduce(self, other: Poly<'m>) -> Poly<'m> {
            let pdd = self.manager.borrow_mut().reduce(self.pdd, other.pdd);
            self.wrap(pdd)
        }
    }

    impl PartialEq for Poly<'_> {
        fn eq(&self, other: &Self) -> bool {
            self.pdd == other.pdd
        }
    }

    impl fmt::Display for Poly<'_> {
        fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            formatter.write_str(&self.manager.borrow().display(self.pdd))
        }
    }

    impl fmt::Debug for Poly<'_> {
        fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            fmt::Display::fmt(self, formatter)
        }
    }

    impl<'m> Add for Poly<'m> {
        type Output = Poly<'m>;
        fn add(self, other: Poly<'m>) -> Poly<'m> {
            let pdd = self.manager.borrow_mut().add(self.pdd, other.pdd);
            self.wrap(pdd)
        }
    }

    impl<'m> Add<i64> for Poly<'m> {
        type Output = Poly<'m>;
        fn add(self, other: i64) -> Poly<'m> {
            let pdd = self
                .manager
                .borrow_mut()
                .add_val(self.pdd, rational(other))
                .unwrap();
            self.wrap(pdd)
        }
    }

    impl<'m> Sub for Poly<'m> {
        type Output = Poly<'m>;
        fn sub(self, other: Poly<'m>) -> Poly<'m> {
            let pdd = self.manager.borrow_mut().sub(self.pdd, other.pdd);
            self.wrap(pdd)
        }
    }

    impl<'m> Sub<i64> for Poly<'m> {
        type Output = Poly<'m>;
        fn sub(self, other: i64) -> Poly<'m> {
            let pdd = self
                .manager
                .borrow_mut()
                .sub_val(self.pdd, rational(other))
                .unwrap();
            self.wrap(pdd)
        }
    }

    impl<'m> Mul for Poly<'m> {
        type Output = Poly<'m>;
        fn mul(self, other: Poly<'m>) -> Poly<'m> {
            let pdd = self.manager.borrow_mut().mul(self.pdd, other.pdd);
            self.wrap(pdd)
        }
    }

    impl<'m> Mul<i64> for Poly<'m> {
        type Output = Poly<'m>;
        fn mul(self, other: i64) -> Poly<'m> {
            self * rational(other)
        }
    }

    impl<'m> Mul<Rational> for Poly<'m> {
        type Output = Poly<'m>;
        fn mul(self, other: Rational) -> Poly<'m> {
            let pdd = self.manager.borrow_mut().mul_val(self.pdd, other).unwrap();
            self.wrap(pdd)
        }
    }

    impl<'m> Neg for Poly<'m> {
        type Output = Poly<'m>;
        fn neg(self) -> Poly<'m> {
            let pdd = self.manager.borrow_mut().minus(self.pdd);
            self.wrap(pdd)
        }
    }

    pub(crate) fn get_vars(manager: &RefCell<PddManager>, count: usize) -> Vec<Poly<'_>> {
        (0..count)
            .map(|index| Poly {
                manager,
                pdd: manager.borrow_mut().mk_var(index).unwrap(),
            })
            .collect()
    }

    fn wrap(manager: &RefCell<PddManager>, pdd: Pdd) -> Poly<'_> {
        Poly { manager, pdd }
    }

    // Ported from Z3's src/test/pdd.cpp.
    #[test]
    fn canonizes_sums_and_products() {
        let manager = RefCell::new(PddManager::new(3));
        let vars = get_vars(&manager, 3);
        let (v0, v1, v2) = (vars[0], vars[1], vars[2]);
        assert_eq!(v0 * v1 * v2, v2 * v0 * v1);
        assert_eq!(v0 + v1 + v2, v2 + v1 + v0);
        let product = (v0 + v1) * v2;
        assert_eq!(product, v0 * v2 + v1 * v2);
        assert_eq!(product + 3 + 1, v0 * v2 + v1 * v2 + 1 + 3);
        let a = wrap(&manager, manager.borrow_mut().mk_var(0).unwrap());
        let b = wrap(&manager, manager.borrow_mut().mk_var(1).unwrap());
        assert_eq!((a - b) * (a + b), a * a - b * b);
        let square = a * 2 - 3;
        let expanded = a * a * 4 - a * 12 + 9;
        assert_eq!(square * square, expanded);
    }

    #[test]
    fn forms_s_polynomials_of_overlapping_leading_monomials() {
        let manager = RefCell::new(PddManager::new(3));
        let vars = get_vars(&manager, 3);
        let (v0, v1, v2) = (vars[0], vars[1], vars[2]);
        let try_spoly = |first: Poly, second: Poly| {
            let spoly = manager
                .borrow_mut()
                .try_spoly(first.pdd, second.pdd)
                .unwrap();
            spoly.map(|pdd| manager.borrow().display(pdd))
        };
        assert_eq!(
            try_spoly(v1 * v2, v0 * v2 + v2 * v2).as_deref(),
            Some("- v2*v1*v0")
        );
        assert_eq!(
            try_spoly(v1 * v2, v0 * v2 + v1 * v1).as_deref(),
            Some("- v1^3")
        );
        assert_eq!(try_spoly(v1, v2), None);
        let reducer = v0 * v1 - v0 * v0;
        let reduced = (v0 * v1 * (v2 + v0) + v2).reduce(reducer);
        assert_eq!(reduced, reduced.reduce(reducer));
    }

    #[test]
    fn reduces_by_the_leading_monomial() {
        let manager = RefCell::new(PddManager::new(4));
        let vars = get_vars(&manager, 4);
        let (a, b, c, d) = (vars[0], vars[1], vars[2], vars[3]);
        let poly = a * b * b * c * d + a * b * c * 2 + b * c * d + b * c + c * d + 3;
        let bc = b * c;
        assert_eq!(poly.reduce(bc), c * d + 3);
        assert_eq!(bc.reduce(poly), bc);
        let bcd = b * c * d - d * d;
        let expected = a * b * d * d + a * b * c * 2 + d * d + b * c + c * d + 3;
        assert_eq!(poly.reduce(bcd), expected);
        let k = d * d + b * 3;
        assert_eq!(bcd.reduce(k), b * c * d + b * 3);
    }

    #[test]
    fn iterates_monomials_from_the_highest_variable() {
        let manager = RefCell::new(PddManager::new(4));
        let vars = get_vars(&manager, 4);
        let (a, b, c, d) = (vars[0], vars[1], vars[2], vars[3]);
        let count = |poly: Poly| manager.borrow().monomials(poly.pdd).len();
        let sum = a + b + 2;
        assert_eq!(count(sum * (c + d * 3 + 5) + 2), 9);
        assert_eq!(count((a + b) * (c + d * 3) + 2), 5);
        assert_eq!(count(a), 1);
        assert_eq!(count(a + 5), 2);
        let five = manager.borrow_mut().mk_val(rational(5)).unwrap();
        assert_eq!(count(wrap(&manager, five)), 1);
        let zero = manager.borrow().zero();
        assert_eq!(count(wrap(&manager, zero)), 0);
        let monomial_vars = |poly: Poly| -> Vec<Vec<usize>> {
            let monomials = manager.borrow().monomials(poly.pdd);
            monomials
                .into_iter()
                .map(|monomial| monomial.vars)
                .collect()
        };
        assert_eq!(monomial_vars(a + b), vec![vec![1], vec![0]]);
        let ccbbaa = c * c * b * b * a * a;
        let ccbbba = c * c * b * b * b * a;
        let fifth: Vec<usize> = monomial_vars(ccbbaa + ccbbba)
            .iter()
            .map(|vars| vars[4])
            .collect();
        assert_eq!(fifth, vec![1, 0]);
        let p0 = ccbbaa + ccbbba + d * d;
        let lm_lt = |first: Poly, second: Poly| manager.borrow_mut().lm_lt(first.pdd, second.pdd);
        assert!(lm_lt(ccbbaa + ccbbba, p0));
        assert!(lm_lt(p0 + a * b, p0 + b * b));
    }

    #[test]
    fn prints_monomials_in_the_order_of_the_levels() {
        let manager = RefCell::new(PddManager::new(4));
        fn product(vars: Vec<Poly<'_>>) -> Poly<'_> {
            (vars[0] + vars[1]) * (vars[2] + vars[3])
        }
        assert_eq!(
            product(get_vars(&manager, 4)).to_string(),
            "v3*v1 + v3*v0 + v2*v1 + v2*v0"
        );
        manager.borrow_mut().reset(&[3, 2, 1, 0]);
        assert_eq!(
            product(get_vars(&manager, 4)).to_string(),
            "v0*v2 + v0*v3 + v1*v2 + v1*v3"
        );
        assert_eq!(
            (-(get_vars(&manager, 2)[0] - 1) * rational(1).div(&rational(2))).to_string(),
            "- 1/2*v0 + 1/2"
        );
    }

    #[test]
    fn factors_out_a_power_of_a_variable() {
        let manager = RefCell::new(PddManager::new(4));
        let vars = get_vars(&manager, 4);
        let (a, b, c, d) = (vars[0], vars[1], vars[2], vars[3]);
        let get_degree = |poly: Poly, variable: usize| {
            let monomials = manager.borrow().monomials(poly.pdd);
            monomials
                .iter()
                .map(|monomial| {
                    monomial
                        .vars
                        .iter()
                        .filter(|&&inner_var| inner_var == variable)
                        .count()
                })
                .fold(0, usize::max)
        };
        let polys = [
            b,
            b.pow(3),
            b + c,
            a.pow(5) + a.pow(3) * b + a * a * b * b + c,
            c.pow(5) + b.pow(3) * c + b * c * c * 3 + a,
            (a + b) * (b + c) * (c + d) * (d + a),
        ];
        for poly in polys {
            for variable in [0, 1, 2, 3] {
                for degree in 0..=5 {
                    let factor = manager
                        .borrow_mut()
                        .factor(poly.pdd, variable, degree)
                        .unwrap();
                    let variable_pdd = manager.borrow_mut().mk_var(variable).unwrap();
                    let power = wrap(&manager, variable_pdd).pow(degree);
                    let lc = wrap(&manager, factor.lc);
                    let rest = wrap(&manager, factor.rest);
                    assert_eq!(lc * power + rest, poly);
                    if degree > 0 {
                        assert!(get_degree(rest, variable) < degree as usize);
                    } else {
                        assert!(manager.borrow().is_zero(factor.lc));
                    }
                }
            }
        }
    }

    #[test]
    fn raises_to_powers() {
        let manager = RefCell::new(PddManager::new(4));
        let vars = get_vars(&manager, 2);
        let (a, b) = (vars[0], vars[1]);
        let zeroth = a.pow(0);
        assert!(manager.borrow().is_one(zeroth.pdd));
        assert_eq!(a.pow(1), a);
        assert_eq!(a.pow(7), a * a * a * a * a * a * a);
        let cube = a * a * a * b * b * b * 27;
        assert_eq!((a * b * 3).pow(3), cube);
    }

    #[test]
    fn factors_out_the_variables_of_every_monomial() {
        let manager = RefCell::new(PddManager::new(3));
        let vars = get_vars(&manager, 5);
        let poly = vars[0] * vars[1] * vars[2] + vars[2] * vars[0] + vars[1];
        let c1 = poly + 1;
        let var_factors = |poly: Poly| manager.borrow_mut().var_factors(poly.pdd).unwrap();
        let none = var_factors(c1);
        assert!(none.poly == c1.pdd && none.vars.is_empty());
        for first in 0..5 {
            let single = var_factors(c1 * vars[first]);
            assert_eq!(single.poly, c1.pdd);
            assert_eq!(single.vars, vec![first]);
            for second in first..5 {
                for third in second..5 {
                    let triple = var_factors(c1 * vars[first] * vars[second] * vars[third]);
                    assert_eq!(triple.poly, c1.pdd);
                    let mut sorted = triple.vars.clone();
                    sorted.sort();
                    assert_eq!(sorted, vec![first, second, third]);
                }
            }
        }
    }

    #[test]
    fn evaluates_substitutes_and_reads_the_shape() {
        let manager = RefCell::new(PddManager::new(3));
        let vars = get_vars(&manager, 3);
        let (x, y, z) = (vars[0], vars[1], vars[2]);
        let poly = x * x * y + z * 3 - 4;
        let values = [rational(2), rational(5), rational(-1)];
        let value = evaluate_pdd(&manager.borrow(), poly.pdd, &mut |variable| {
            values[variable].clone()
        });
        assert_eq!(value, rational(13));
        let replacement = y + 1;
        let substituted = manager
            .borrow_mut()
            .subst_pdd(poly.pdd, 0, replacement.pdd)
            .unwrap();
        assert_eq!(wrap(&manager, substituted), (y + 1).pow(2) * y + z * 3 - 4);
        let mut free_vars = manager.borrow().free_vars(poly.pdd);
        free_vars.sort();
        assert_eq!(free_vars, vec![0, 1, 2]);
        let get_powers = |poly: Poly| manager.borrow().get_powers(poly.pdd);
        assert_eq!(
            get_powers(y * z * z + y),
            vec![PddPower { var: 2, degree: 2 }]
        );
        // As in Z3, a value under the lowest variable counts as one more power of it: x + 1 reports
        // x^2, and x^2*y reports x^3.
        assert_eq!(get_powers(x + 1), vec![PddPower { var: 0, degree: 2 }]);
        assert_eq!(get_powers(poly), vec![PddPower { var: 0, degree: 3 }]);
        assert_eq!(manager.borrow_mut().degree(poly.pdd), 3);
        assert!(!manager.borrow_mut().is_linear(poly.pdd));
        let sum = x + y;
        assert!(manager.borrow_mut().is_linear(sum.pdd));
        let double = x * 2;
        assert!(manager.borrow().is_unary(double.pdd));
        let offset = z + 2;
        assert!(manager.borrow().is_offset(offset.pdd));
        let coefficients: Vec<String> = manager
            .borrow()
            .coefficients(poly.pdd)
            .iter()
            .map(|value| format!("{}:{}", value.coeff, value.is_constant))
            .collect();
        assert_eq!(coefficients, vec!["3:false", "1:false", "-4:true"]);
    }

    #[test]
    fn runs_out_of_nodes_only_outside_an_operation() {
        let mut manager = PddManager::new(2);
        let a = manager.mk_var(0).unwrap();
        let b = manager.mk_var(1).unwrap();
        manager.set_max_num_nodes(0);
        let mut value = 2;
        while manager.num_nodes() < 1036 {
            manager.mk_val(rational(value)).unwrap();
            value += 1;
        }
        assert_eq!(manager.mk_val(rational(value)), Err(SmtError::PddMemoryOut));
        let product = manager.mul(a, b);
        assert_eq!(manager.display(product), "v1*v0");
        let node = manager.mk_val(rational(value)).unwrap();
        assert_eq!(manager.val(node), &rational(value));
    }
}
