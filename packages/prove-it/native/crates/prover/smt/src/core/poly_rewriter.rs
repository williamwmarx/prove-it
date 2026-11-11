//! Ported from Z3 (src/ast/rewriter/poly_rewriter.h, poly_rewriter_def.h), MIT license, through
//! `poly-rewriter.ts`. The rewrites of sums and products of monomials, which arith_rewriter extends.
//! Powers are not ported, as tlapm's encoding does not produce them.
//!
//! The TypeScript's rewrites return `number | Rewrite | undefined`, with undefined for BR_FAILED:
//! here [`Reduced`], whose `Failed` is undefined. Unlike what `reduce_app` returns, these results
//! come with no reference. The TypeScript's `PolyRewriter` keeps its manager; here each method
//! takes it.

use std::collections::HashMap;

use prove_num::Rational;

use crate::core::ast::{
    AstManager, Expr, KIND_APP, OP_ABS, OP_ADD, OP_DIV, OP_GE, OP_GT, OP_IDIV, OP_IS_INT, OP_LE,
    OP_LT, OP_MOD, OP_MUL, OP_NUM, OP_SUB, OP_TO_INT, OP_TO_REAL, OP_UMINUS, SORT_INT, Sort,
};
use crate::core::rewriter_tpl::{Reduced, Rewrite};
use crate::util::error::SmtError;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ArithRewriterOptions {
    /// poly_rewriter's som: distributes products over sums.
    pub is_som: bool,
    /// arith_rewriter's sort_sums: orders the monomials of a sum.
    pub is_sort_sums: bool,
    /// arith_rewriter's arith_ineq_lhs: moves the monomials of an inequality to the left-hand side.
    pub is_arith_ineq_lhs: bool,
    /// arith_rewriter's gcd_rounding: divides integer atoms by the gcd of their coefficients.
    pub is_gcd_rounding: bool,
}

// ARITH_OPS.
fn is_arith_op(op: i32) -> bool {
    matches!(
        op,
        OP_NUM
            | OP_ADD
            | OP_SUB
            | OP_UMINUS
            | OP_MUL
            | OP_IDIV
            | OP_MOD
            | OP_ABS
            | OP_LE
            | OP_GE
            | OP_LT
            | OP_GT
            | OP_DIV
            | OP_TO_REAL
            | OP_TO_INT
            | OP_IS_INT
    )
}

/// The value of a rewrite as the TypeScript's `number | Rewrite`.
pub(crate) fn get_reduced_expr(reduced: Reduced) -> Option<Expr> {
    match reduced {
        Reduced::Failed => None,
        Reduced::Done(expr) | Reduced::Rewrite(Rewrite { expr, .. }) => Some(expr),
    }
}

#[derive(Clone, Debug)]
pub struct PolyRewriter {
    /// m_curr_sort: the sort of the numerals and terms that the current rewrite makes.
    pub curr_sort: Sort,
    // The expr_fast_mark1 and expr_fast_mark2 of mk_nflat_add_core: Z3 marks the power products in
    // their nodes, and a stamp per expression marks them here for one call.
    visited_stamps: Vec<i32>,
    multiple_stamps: Vec<i32>,
    stamp: i32,
    pub options: ArithRewriterOptions,
}

impl PolyRewriter {
    pub fn new(options: ArithRewriterOptions) -> PolyRewriter {
        PolyRewriter {
            curr_sort: SORT_INT,
            visited_stamps: Vec::new(),
            multiple_stamps: Vec::new(),
            stamp: 0,
            options,
        }
    }

    pub(crate) fn reduce(&self, expr: Expr, depth: u32) -> Rewrite {
        Rewrite { expr, depth }
    }

    pub(crate) fn is_zero(&self, m: &AstManager, expr: Expr) -> bool {
        m.is_numeral(expr) && self.get_value(m, expr).is_zero()
    }

    /// The value of a numeral of either sort.
    pub(crate) fn get_value(&self, m: &AstManager, expr: Expr) -> Rational {
        m.get_rational_value(expr).clone()
    }

    pub(crate) fn mk_numeral(&self, m: &mut AstManager, value: &Rational) -> Expr {
        m.mk_numeral_of_sort(value, self.curr_sort)
    }

    pub(crate) fn is_add(&self, m: &AstManager, expr: Expr) -> bool {
        m.get_op(expr) == OP_ADD
    }

    pub(crate) fn is_mul(&self, m: &AstManager, expr: Expr) -> bool {
        m.get_op(expr) == OP_MUL
    }

    pub(crate) fn is_arith_term(&self, m: &AstManager, expr: Expr) -> bool {
        m.kinds[expr as usize] == KIND_APP && is_arith_op(m.get_op(expr))
    }

    /// get_monomials: the summands of a sum, and otherwise the term itself.
    pub(crate) fn get_num_monomials(&self, m: &AstManager, expr: Expr) -> usize {
        if self.is_add(m, expr) {
            m.get_num_args(expr)
        } else {
            1
        }
    }

    pub(crate) fn get_monomial(&self, m: &AstManager, expr: Expr, index: usize) -> Expr {
        if self.is_add(m, expr) {
            m.get_arg(expr, index)
        } else {
            expr
        }
    }

    /// get_power_product: the monomial without its coefficient.
    pub(crate) fn get_power_product(&self, m: &AstManager, expr: Expr) -> Expr {
        if self.is_mul(m, expr) && m.get_num_args(expr) == 2 && m.is_numeral(m.get_arg(expr, 0)) {
            m.get_arg(expr, 1)
        } else {
            expr
        }
    }

    pub(crate) fn get_coefficient(&self, m: &AstManager, expr: Expr) -> Rational {
        if self.is_mul(m, expr) && m.get_num_args(expr) == 2 && m.is_numeral(m.get_arg(expr, 0)) {
            self.get_value(m, m.get_arg(expr, 0))
        } else {
            Rational::one()
        }
    }

    /// mon_lt::ordinal, without powers.
    pub(crate) fn get_ordinal(&self, m: &AstManager, expr: Expr) -> i32 {
        if m.kinds[expr as usize] != KIND_APP || !is_arith_op(m.get_op(expr)) {
            return m.ids[expr as usize];
        }
        if self.is_mul(m, expr) {
            let target = if m.is_numeral(m.get_arg(expr, 0)) {
                m.get_arg(expr, 1)
            } else {
                expr
            };
            return m.ids[target as usize];
        }
        if m.is_numeral(expr) {
            -1
        } else {
            m.ids[expr as usize]
        }
    }

    /// std::sort with mon_lt, of the monomials from start, in place. Insertion sort is stable, as
    /// Array.prototype.sort is, and allocates nothing for the short sums that are the common case.
    pub(crate) fn sort_monomials(&self, m: &AstManager, monomials: &mut [Expr], start: usize) {
        for index in start + 1..monomials.len() {
            let monomial = monomials[index];
            let ordinal = self.get_ordinal(m, monomial);
            let mut position = index;
            while position > start && self.get_ordinal(m, monomials[position - 1]) > ordinal {
                monomials[position] = monomials[position - 1];
                position -= 1;
            }
            monomials[position] = monomial;
        }
    }

    pub fn mk_add_app(&self, m: &mut AstManager, args: &[Expr]) -> Result<Expr, SmtError> {
        match args {
            [] => Ok(self.mk_numeral(m, &Rational::zero())),
            [arg] => Ok(*arg),
            _ => m.mk_app(OP_ADD, args, self.curr_sort),
        }
    }

    /// mkMulApp: a product of more than two factors whose first is a numeral is that numeral times
    /// the product of the rest, which the TypeScript makes by recursion, innermost first.
    pub fn mk_mul_app(&self, m: &mut AstManager, args: &[Expr]) -> Result<Expr, SmtError> {
        match args {
            [] => return Ok(self.mk_numeral(m, &Rational::one())),
            [arg] => return Ok(*arg),
            _ => {}
        }
        let mut start = 0;
        while args.len() - start > 2 && m.is_numeral(args[start]) {
            start += 1;
        }
        let mut result = m.mk_app(OP_MUL, &args[start..], self.curr_sort)?;
        for index in (0..start).rev() {
            let coefficient = self.get_value(m, args[index]);
            result = self.mk_mul_app_with(m, &coefficient, result)?;
        }
        Ok(result)
    }

    pub(crate) fn mk_mul_app_with(
        &self,
        m: &mut AstManager,
        coefficient: &Rational,
        arg: Expr,
    ) -> Result<Expr, SmtError> {
        if *coefficient == Rational::one() || self.is_zero(m, arg) {
            return Ok(arg);
        }
        let numeral = self.mk_numeral(m, coefficient);
        self.mk_mul_app(m, &[numeral, arg])
    }

    /// The rewrites return None or `Reduced::Failed` when they do not apply, like BR_FAILED.
    pub fn mk_add(&mut self, m: &mut AstManager, args: &[Expr]) -> Result<Option<Expr>, SmtError> {
        if args.len() < 2 {
            return Ok(None);
        }
        self.curr_sort = m.sorts[args[0] as usize];
        if !args.iter().any(|arg| self.is_add(m, *arg)) {
            return self.mk_nflat_add(m, args);
        }
        let mut flat: Vec<Expr> = Vec::new();
        for arg in args {
            if self.is_add(m, *arg) {
                m.push_args(*arg, &mut flat);
            } else {
                flat.push(*arg);
            }
        }
        match self.mk_nflat_add(m, &flat)? {
            Some(result) => Ok(Some(result)),
            None => Ok(Some(self.mk_add_app(m, &flat)?)),
        }
    }

    fn mk_nflat_add(
        &mut self,
        m: &mut AstManager,
        args: &[Expr],
    ) -> Result<Option<Expr>, SmtError> {
        let is_sort_sums = self.options.is_sort_sums;
        let mut constant = Rational::zero();
        let mut num_coeffs = 0;
        let mut is_ordered = true;
        let mut previous = -1;
        let mut is_multiple = false;
        self.stamp = self.stamp.wrapping_add(1);
        let stamp = self.stamp;
        for (index, arg) in args.iter().copied().enumerate() {
            if m.is_numeral(arg) {
                num_coeffs += 1;
                constant = constant.add(m.get_rational_value(arg));
                is_ordered = !is_sort_sums || index == 0;
            } else if is_sort_sums && is_ordered {
                if previous != -1 && self.get_ordinal(m, arg) < self.get_ordinal(m, previous) {
                    is_ordered = false;
                }
                previous = arg;
            }
            let product = self.get_power_product(m, arg);
            if product as usize >= self.visited_stamps.len() {
                self.grow_stamps(product);
            }
            if self.visited_stamps[product as usize] == stamp {
                self.multiple_stamps[product as usize] = stamp;
                is_multiple = true;
            } else {
                self.visited_stamps[product as usize] = stamp;
            }
        }
        if is_multiple {
            let mut coeffs: HashMap<Expr, Rational> = HashMap::new();
            for arg in args.iter().copied() {
                if m.is_numeral(arg) {
                    continue;
                }
                let product = self.get_power_product(m, arg);
                if self.multiple_stamps[product as usize] == stamp {
                    let sum = coeffs
                        .get(&product)
                        .cloned()
                        .unwrap_or_else(Rational::zero)
                        .add(&self.get_coefficient(m, arg));
                    coeffs.insert(product, sum);
                }
            }
            let mut new_args: Vec<Expr> = if constant.is_zero() {
                Vec::new()
            } else {
                vec![self.mk_numeral(m, &constant)]
            };
            // visited.reset(): a new stamp marks the power products already copied.
            self.stamp = self.stamp.wrapping_add(1);
            let copied_stamp = self.stamp;
            for arg in args.iter().copied() {
                if m.is_numeral(arg) {
                    continue;
                }
                let product = self.get_power_product(m, arg);
                if self.multiple_stamps[product as usize] != stamp {
                    new_args.push(arg);
                } else if self.visited_stamps[product as usize] != copied_stamp {
                    self.visited_stamps[product as usize] = copied_stamp;
                    let coefficient = coeffs.get(&product).cloned().unwrap_or_else(Rational::zero);
                    if !coefficient.is_zero() {
                        new_args.push(self.mk_mul_app_with(m, &coefficient, product)?);
                    }
                }
            }
            if is_sort_sums {
                let start = if constant.is_zero() { 0 } else { 1 };
                self.sort_monomials(m, &mut new_args, start);
            }
            return Ok(Some(self.mk_add_app(m, &new_args)?));
        }
        if is_ordered {
            if num_coeffs == 0 {
                return Ok(None);
            }
            if num_coeffs == 1 && m.is_numeral(args[0]) && !self.get_value(m, args[0]).is_zero() {
                return Ok(None);
            }
        }
        let mut new_args: Vec<Expr> = if constant.is_zero() {
            Vec::new()
        } else {
            vec![self.mk_numeral(m, &constant)]
        };
        for arg in args {
            if !m.is_numeral(*arg) {
                new_args.push(*arg);
            }
        }
        if !is_ordered {
            let start = if constant.is_zero() { 0 } else { 1 };
            self.sort_monomials(m, &mut new_args, start);
        }
        Ok(Some(self.mk_add_app(m, &new_args)?))
    }

    fn grow_stamps(&mut self, expr: Expr) {
        let size = (2 * self.visited_stamps.len())
            .max(expr as usize + 1)
            .max(1024);
        self.visited_stamps.resize(size, 0);
        self.multiple_stamps.resize(size, 0);
    }

    pub fn mk_mul(&mut self, m: &mut AstManager, args: &[Expr]) -> Result<Reduced, SmtError> {
        if args.len() < 2 {
            return Ok(Reduced::Failed);
        }
        self.curr_sort = m.sorts[args[0] as usize];
        let is_flat_monomial = args.len() == 2
            && m.is_numeral(args[0])
            && !(self.is_mul(m, args[1]) && m.is_numeral(m.get_arg(args[1], 0)));
        if is_flat_monomial || !args.iter().any(|arg| self.is_mul(m, *arg)) {
            return self.mk_nflat_mul(m, args);
        }
        // collect: the factors of the nested products, in order, on a stack of the terms to visit.
        let mut flat: Vec<Expr> = Vec::new();
        let mut todo: Vec<Expr> = args.iter().rev().copied().collect();
        while let Some(arg) = todo.pop() {
            if self.is_mul(m, arg) {
                for index in (0..m.get_num_args(arg)).rev() {
                    todo.push(m.get_arg(arg, index));
                }
            } else {
                flat.push(arg);
            }
        }
        match self.mk_nflat_mul(m, &flat)? {
            Reduced::Failed => Ok(Reduced::Done(self.mk_mul_app(m, &flat)?)),
            reduced => Ok(reduced),
        }
    }

    fn mk_nflat_mul(&mut self, m: &mut AstManager, args: &[Expr]) -> Result<Reduced, SmtError> {
        if args.len() == 2
            && m.is_numeral(args[0])
            && self.get_value(m, args[0]) != Rational::one()
            && !self.get_value(m, args[0]).is_zero()
            && !self.is_arith_term(m, args[1])
        {
            return Ok(Reduced::Failed);
        }
        let mut coefficient = Rational::one();
        let mut num_coeffs = 0;
        let mut num_add = 0;
        let mut factor = -1;
        for arg in args.iter().copied() {
            if m.is_numeral(arg) {
                num_coeffs += 1;
                coefficient = coefficient.mul(m.get_rational_value(arg));
            } else {
                factor = arg;
                if self.is_add(m, arg) {
                    num_add += 1;
                }
            }
        }
        if num_coeffs == args.len() || coefficient.is_zero() {
            return Ok(Reduced::Done(self.mk_numeral(m, &coefficient)));
        }
        if num_coeffs == args.len() - 1 {
            if coefficient == Rational::one() {
                return Ok(Reduced::Done(factor));
            }
            if self.is_mul(m, factor) {
                if m.get_num_args(factor) != 2 || !m.is_numeral(m.get_arg(factor, 0)) {
                    return Ok(Reduced::Failed);
                }
                let product = coefficient.mul(m.get_rational_value(m.get_arg(factor, 0)));
                let result = self.mk_mul_app_with(m, &product, m.get_arg(factor, 1))?;
                return Ok(Reduced::Rewrite(self.reduce(result, 1)));
            }
            if num_add == 0 {
                if args.len() == 2 && args[1] == factor {
                    return Ok(Reduced::Failed);
                }
                return Ok(Reduced::Done(self.mk_mul_app_with(
                    m,
                    &coefficient,
                    factor,
                )?));
            }
            let mut summands = Vec::new();
            for index in 0..m.get_num_args(factor) {
                let arg = m.get_arg(factor, index);
                summands.push(self.mk_mul_app_with(m, &coefficient, arg)?);
            }
            let result = self.mk_add_app(m, &summands)?;
            return Ok(Reduced::Rewrite(self.reduce(result, 2)));
        }
        if num_coeffs > 1 || (num_coeffs == 1 && !m.is_numeral(args[0])) {
            let factors: Vec<Expr> = args
                .iter()
                .copied()
                .filter(|arg| !m.is_numeral(*arg))
                .collect();
            let product = self.mk_mul_app(m, &factors)?;
            let result = self.mk_mul_app_with(m, &coefficient, product)?;
            return Ok(Reduced::Rewrite(self.reduce(result, 2)));
        }
        if !self.options.is_som || num_add == 0 {
            let mut factors: Vec<Expr> = args
                .iter()
                .copied()
                .filter(|arg| !m.is_numeral(*arg))
                .collect();
            let is_ordered = (1..factors.len()).all(|index| {
                self.get_ordinal(m, factors[index]) >= self.get_ordinal(m, factors[index - 1])
            });
            if is_ordered && num_coeffs == 0 {
                return Ok(Reduced::Failed);
            }
            if !is_ordered {
                self.sort_monomials(m, &mut factors, 0);
            }
            let product = self.mk_mul_app(m, &factors)?;
            return Ok(Reduced::Done(self.mk_mul_app_with(
                m,
                &coefficient,
                product,
            )?));
        }
        let sums: Vec<Vec<Expr>> = args
            .iter()
            .map(|arg| {
                if self.is_add(m, *arg) {
                    m.get_args(*arg)
                } else {
                    vec![*arg]
                }
            })
            .collect();
        // Like som's expr_ref_buffer, the products are released in order when it returns.
        let (is_blown_up, products) = m.with_temporaries_keeping(
            |m| {
                let mut positions = vec![0; sums.len()];
                let mut products: Vec<Expr> = Vec::new();
                loop {
                    if products.len() > 10 * sums.len() {
                        return Ok((true, products));
                    }
                    let factors: Vec<Expr> = sums
                        .iter()
                        .enumerate()
                        .map(|(index, sum)| sum[positions[index]])
                        .collect();
                    products.push(self.mk_mul_app(m, &factors)?);
                    let mut index = 0;
                    while index < sums.len() {
                        positions[index] += 1;
                        if positions[index] < sums[index].len() {
                            break;
                        }
                        positions[index] = 0;
                        index += 1;
                    }
                    if index == sums.len() {
                        return Ok((false, products));
                    }
                }
            },
            |result| result.1.clone(),
        )?;
        let result = if is_blown_up {
            Reduced::Failed
        } else {
            let sum = self.mk_add_app(m, &products)?;
            Reduced::Rewrite(self.reduce(sum, 2))
        };
        for product in &products {
            m.dec_ref(*product)?;
        }
        Ok(result)
    }

    pub fn mk_sub(&mut self, m: &mut AstManager, args: &[Expr]) -> Result<Reduced, SmtError> {
        if args.len() == 1 {
            return Ok(Reduced::Done(args[0]));
        }
        self.curr_sort = m.sorts[args[0] as usize];
        let minus_one = self.mk_numeral(m, &Rational::minus_one());
        let mut new_args = vec![args[0]];
        for arg in &args[1..] {
            if !self.is_zero(m, *arg) {
                new_args.push(self.mk_mul_app(m, &[minus_one, *arg])?);
            }
        }
        let result = self.mk_add_app(m, &new_args)?;
        Ok(Reduced::Rewrite(self.reduce(result, 2)))
    }

    pub fn mk_uminus(&mut self, m: &mut AstManager, arg: Expr) -> Result<Reduced, SmtError> {
        self.curr_sort = m.sorts[arg as usize];
        if m.is_numeral(arg) {
            let value = self.get_value(m, arg).neg();
            return Ok(Reduced::Done(self.mk_numeral(m, &value)));
        }
        let result = self.mk_mul_app_with(m, &Rational::minus_one(), arg)?;
        Ok(Reduced::Rewrite(self.reduce(result, 1)))
    }

    /// poly_rewriter::cancel_monomials. The stamps stand for its visited, multiple and copied marks.
    pub(crate) fn cancel_monomials(
        &mut self,
        m: &mut AstManager,
        lhs: Expr,
        rhs: Expr,
        is_moving: bool,
    ) -> Result<Option<(Expr, Expr)>, SmtError> {
        self.curr_sort = m.sorts[lhs as usize];
        self.stamp = self.stamp.wrapping_add(1);
        let stamp = self.stamp;
        let mut constant = Rational::zero();
        let mut num_coeffs = 0;
        for index in 0..self.get_num_monomials(m, lhs) {
            let arg = self.get_monomial(m, lhs, index);
            if m.is_numeral(arg) {
                constant = constant.add(m.get_rational_value(arg));
                num_coeffs += 1;
                continue;
            }
            let product = self.get_power_product(m, arg);
            if product as usize >= self.visited_stamps.len() {
                self.grow_stamps(product);
            }
            self.visited_stamps[product as usize] = stamp;
        }
        if is_moving && num_coeffs == 0 && m.is_numeral(rhs) {
            return Ok(None);
        }
        let mut is_multiple = false;
        for index in 0..self.get_num_monomials(m, rhs) {
            let arg = self.get_monomial(m, rhs, index);
            if m.is_numeral(arg) {
                constant = constant.sub(m.get_rational_value(arg));
                num_coeffs += 1;
                continue;
            }
            let product = self.get_power_product(m, arg);
            if (product as usize) < self.visited_stamps.len()
                && self.visited_stamps[product as usize] == stamp
            {
                self.multiple_stamps[product as usize] = stamp;
                is_multiple = true;
            }
        }
        if !is_multiple && num_coeffs <= 1 {
            let is_failed = if is_moving {
                m.is_numeral(rhs)
            } else {
                num_coeffs == 0 || m.is_numeral(rhs)
            };
            if is_failed {
                return Ok(None);
            }
        }
        let is_multiple_product = |this: &PolyRewriter, product: Expr| {
            (product as usize) < this.multiple_stamps.len()
                && this.multiple_stamps[product as usize] == stamp
        };
        let mut coeffs: HashMap<Expr, Rational> = HashMap::new();
        if is_multiple {
            for index in 0..self.get_num_monomials(m, lhs) {
                let arg = self.get_monomial(m, lhs, index);
                if m.is_numeral(arg) {
                    continue;
                }
                let product = self.get_power_product(m, arg);
                if is_multiple_product(self, product) {
                    let sum = coeffs
                        .get(&product)
                        .cloned()
                        .unwrap_or_else(Rational::zero)
                        .add(&self.get_coefficient(m, arg));
                    coeffs.insert(product, sum);
                }
            }
            for index in 0..self.get_num_monomials(m, rhs) {
                let arg = self.get_monomial(m, rhs, index);
                if m.is_numeral(arg) {
                    continue;
                }
                let product = self.get_power_product(m, arg);
                if is_multiple_product(self, product) {
                    let difference = coeffs
                        .get(&product)
                        .cloned()
                        .unwrap_or_else(Rational::zero)
                        .sub(&self.get_coefficient(m, arg));
                    coeffs.insert(product, difference);
                }
            }
        }
        let mut new_lhs: Vec<Expr> = Vec::new();
        self.stamp = self.stamp.wrapping_add(1);
        let copied_stamp = self.stamp;
        for index in 0..self.get_num_monomials(m, lhs) {
            let arg = self.get_monomial(m, lhs, index);
            if m.is_numeral(arg) {
                continue;
            }
            let product = self.get_power_product(m, arg);
            if !is_multiple_product(self, product) {
                new_lhs.push(arg);
            } else if self.visited_stamps[product as usize] != copied_stamp {
                self.visited_stamps[product as usize] = copied_stamp;
                let coefficient = coeffs.get(&product).cloned().unwrap_or_else(Rational::zero);
                if !coefficient.is_zero() {
                    new_lhs.push(self.mk_mul_app_with(m, &coefficient, product)?);
                }
            }
        }
        let mut new_rhs: Vec<Expr> = Vec::new();
        for index in 0..self.get_num_monomials(m, rhs) {
            let arg = self.get_monomial(m, rhs, index);
            if m.is_numeral(arg) {
                continue;
            }
            let product = self.get_power_product(m, arg);
            if is_multiple_product(self, product) {
                continue;
            }
            if !is_moving {
                new_rhs.push(arg);
            } else {
                let coefficient = self.get_coefficient(m, arg);
                if coefficient == Rational::minus_one() {
                    new_lhs.push(product);
                } else if !coefficient.is_zero() {
                    let numeral = self.mk_numeral(m, &coefficient.neg());
                    new_lhs.push(self.mk_mul_app(m, &[numeral, product])?);
                }
            }
        }
        if is_moving && self.options.is_sort_sums {
            self.sort_monomials(m, &mut new_lhs, 0);
        }
        let is_constant_at_rhs = is_moving || new_rhs.is_empty() || !new_lhs.is_empty();
        let value = if is_constant_at_rhs {
            constant.neg()
        } else {
            constant
        };
        let is_lhs_constant = !is_constant_at_rhs && (new_lhs.is_empty() || !value.is_zero());
        let is_rhs_constant = is_constant_at_rhs && (new_rhs.is_empty() || !value.is_zero());
        if is_lhs_constant {
            new_lhs.insert(0, self.mk_numeral(m, &value));
        }
        if is_rhs_constant {
            new_rhs.insert(0, self.mk_numeral(m, &value));
        }
        let lhs_result = self.mk_add_app(m, &new_lhs)?;
        let rhs_result = self.mk_add_app(m, &new_rhs)?;
        Ok(Some((lhs_result, rhs_result)))
    }
}
