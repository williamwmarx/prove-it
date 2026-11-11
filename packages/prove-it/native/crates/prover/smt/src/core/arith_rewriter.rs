//! Ported from Z3 (src/ast/rewriter/arith_rewriter.cpp), MIT license, through `arith-rewriter.ts`.
//! Only linear arithmetic and nonlinear factoring are ported, without powers, algebraic numbers or
//! hoisting, which tlapm's encoding does not produce.
//!
//! `ArithRewriter extends PolyRewriter` in the TypeScript: here it holds its `PolyRewriter` and
//! dereferences to it. As in `poly_rewriter.rs`, `Reduced::Failed` is the TypeScript's undefined,
//! and the results come with no reference.

use std::collections::HashSet;
use std::ops::{Deref, DerefMut};

use prove_num::{Int, Rational, get_euclidean_div, get_euclidean_mod, get_gcd};

use crate::core::ast::{
    AstManager, Expr, OP_ADD, OP_GE, OP_IDIV, OP_ITE, OP_LE, OP_LT, OP_MOD, OP_MUL, OP_SUB,
    OP_TO_INT, OP_TO_REAL, OP_UMINUS, SORT_BOOL, SORT_INT, SORT_REAL, Sort,
};
use crate::core::poly_rewriter::{ArithRewriterOptions, PolyRewriter};
use crate::core::rewriter_tpl::{Reduced, UNBOUNDED_DEPTH};
use crate::util::error::SmtError;

/// The parameters that asserted_formulas gives the kernel's rewriter, which also simplifies
/// instances.
pub const KERNEL_ARITH_OPTIONS: ArithRewriterOptions = ArithRewriterOptions {
    is_som: true,
    is_sort_sums: true,
    is_arith_ineq_lhs: true,
    is_gcd_rounding: true,
};

/// The defaults, which the simplify tactic uses.
pub const TACTIC_ARITH_OPTIONS: ArithRewriterOptions = ArithRewriterOptions {
    is_som: false,
    is_sort_sums: false,
    is_arith_ineq_lhs: false,
    is_gcd_rounding: false,
};

// bigint division, which throws a RangeError on a zero divisor in the TypeScript.
fn check_divisor(divisor: &Int) -> Result<(), SmtError> {
    if divisor.is_zero() {
        return Err(SmtError::Invariant("Division by zero".into()));
    }
    Ok(())
}

// The ceiling of the quotient by a positive divisor.
fn get_ceil_div(dividend: &Int, divisor: &Int) -> Int {
    -get_euclidean_div(&-dividend, divisor)
}

// symmod: the remainder closest to zero, for a positive modulus.
fn get_symmetric_mod(value: &Int, modulus: &Int) -> Int {
    let remainder = get_euclidean_mod(value, modulus);
    if &Int::from(2) * &remainder > *modulus {
        remainder - modulus
    } else {
        remainder
    }
}

// The running gcd of the coefficients of an atom's sides, and the number of their constants.
struct GcdState {
    gcd: Int,
    is_first: bool,
    num_consts: usize,
}

const KIND_LE: u8 = 0;
const KIND_GE: u8 = 1;
const KIND_EQ: u8 = 2;

fn get_inverse(kind: u8) -> u8 {
    if kind == KIND_LE {
        KIND_GE
    } else if kind == KIND_GE {
        KIND_LE
    } else {
        KIND_EQ
    }
}

// The rounding of div_polynomial.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Rounding {
    Floor,
    Ceil,
    None,
}

#[derive(Clone, Debug)]
pub struct ArithRewriter {
    poly: PolyRewriter,
    // The buffer of is_non_negative's factors.
    factors: Vec<Expr>,
}

impl Deref for ArithRewriter {
    type Target = PolyRewriter;

    fn deref(&self) -> &PolyRewriter {
        &self.poly
    }
}

impl DerefMut for ArithRewriter {
    fn deref_mut(&mut self) -> &mut PolyRewriter {
        &mut self.poly
    }
}

impl ArithRewriter {
    pub fn new(options: ArithRewriterOptions) -> ArithRewriter {
        ArithRewriter {
            poly: PolyRewriter::new(options),
            factors: Vec::new(),
        }
    }

    pub fn mk_le(
        &mut self,
        m: &mut AstManager,
        left: Expr,
        right: Expr,
    ) -> Result<Reduced, SmtError> {
        self.mk_le_ge_eq(m, left, right, KIND_LE)
    }

    pub fn mk_ge(
        &mut self,
        m: &mut AstManager,
        left: Expr,
        right: Expr,
    ) -> Result<Reduced, SmtError> {
        self.mk_le_ge_eq(m, left, right, KIND_GE)
    }

    pub fn mk_lt(
        &mut self,
        m: &mut AstManager,
        left: Expr,
        right: Expr,
    ) -> Result<Reduced, SmtError> {
        let atom = self.mk_atom(m, right, left, KIND_LE)?;
        let negation = m.mk_not(atom)?;
        Ok(Reduced::Rewrite(self.reduce(negation, 2)))
    }

    pub fn mk_gt(
        &mut self,
        m: &mut AstManager,
        left: Expr,
        right: Expr,
    ) -> Result<Reduced, SmtError> {
        let atom = self.mk_atom(m, left, right, KIND_LE)?;
        let negation = m.mk_not(atom)?;
        Ok(Reduced::Rewrite(self.reduce(negation, 2)))
    }

    pub fn mk_eq(
        &mut self,
        m: &mut AstManager,
        left: Expr,
        right: Expr,
    ) -> Result<Reduced, SmtError> {
        if !self.is_arith_term(m, left) && !self.is_arith_term(m, right) {
            return Ok(Reduced::Failed);
        }
        self.mk_le_ge_eq(m, left, right, KIND_EQ)
    }

    // mk_idiv_core and mk_mod_core: SMT-LIB integer division, whose remainder is non-negative.
    fn mk_idiv_app(&self, m: &mut AstManager, left: Expr, right: Expr) -> Result<Expr, SmtError> {
        m.mk_app(OP_IDIV, &[left, right], SORT_INT)
    }

    fn mk_mod_app(&self, m: &mut AstManager, left: Expr, right: Expr) -> Result<Expr, SmtError> {
        m.mk_app(OP_MOD, &[left, right], SORT_INT)
    }

    // arith_util's mk_mul, which makes no product of one factor.
    fn mk_flat_mul_app(&self, m: &mut AstManager, args: &[Expr]) -> Result<Expr, SmtError> {
        if args.len() == 1 {
            Ok(args[0])
        } else {
            m.mk_app(OP_MUL, args, SORT_INT)
        }
    }

    fn mk_int_ite(
        &self,
        m: &mut AstManager,
        condition: Expr,
        then_expr: Expr,
        else_expr: Expr,
    ) -> Result<Expr, SmtError> {
        m.mk_app(OP_ITE, &[condition, then_expr, else_expr], SORT_INT)
    }

    // flat_mul: the factors of nested products, in Z3's order.
    fn get_flat_mul(&self, m: &AstManager, expr: Expr) -> Vec<Expr> {
        let mut args = vec![expr];
        let mut index = 0;
        while index < args.len() {
            if !self.is_mul(m, args[index]) {
                index += 1;
                continue;
            }
            m.push_args(args[index], &mut args);
            let last = args.len() - 1;
            args[index] = args[last];
            args.pop();
        }
        args
    }

    fn remove_factor(&self, factor: Expr, args: &mut Vec<Expr>) {
        // indexOf: -1 when absent, where the TypeScript's write to args[-1] changes no item.
        if let Some(index) = args.iter().position(|arg| *arg == factor) {
            let last = args.len() - 1;
            args[index] = args[last];
        }
        args.pop();
    }

    // remove_divisor: div ab ac is div b c when a is positive, and div -b -c when it is negative.
    fn remove_divisor(
        &self,
        m: &mut AstManager,
        factor: Expr,
        dividend: Expr,
        divisor: Expr,
    ) -> Result<Expr, SmtError> {
        let mut dividend_args = self.get_flat_mul(m, dividend);
        let mut divisor_args = self.get_flat_mul(m, divisor);
        self.remove_factor(factor, &mut dividend_args);
        self.remove_factor(factor, &mut divisor_args);
        let zero = m.mk_numeral(&Int::zero());
        let new_dividend = if dividend_args.is_empty() {
            m.mk_numeral(&Int::one())
        } else {
            self.mk_flat_mul_app(m, &dividend_args)?
        };
        let new_divisor = if divisor_args.is_empty() {
            m.mk_numeral(&Int::one())
        } else {
            self.mk_flat_mul_app(m, &divisor_args)?
        };
        let is_zero = m.mk_eq(zero, factor)?;
        let zero_div = self.mk_idiv_app(m, zero, zero)?;
        let is_positive = m.mk_app(OP_GE, &[factor, zero], SORT_BOOL)?;
        let positive_div = self.mk_idiv_app(m, new_dividend, new_divisor)?;
        let negated_dividend = m.mk_app(OP_UMINUS, &[new_dividend], SORT_INT)?;
        let negated_divisor = m.mk_app(OP_UMINUS, &[new_divisor], SORT_INT)?;
        let negative_div = self.mk_idiv_app(m, negated_dividend, negated_divisor)?;
        let inner = self.mk_int_ite(m, is_positive, positive_div, negative_div)?;
        self.mk_int_ite(m, is_zero, zero_div, inner)
    }

    // get_divides: div ab ac is div b c, and common numeral factors cancel.
    fn get_divides(
        &self,
        m: &mut AstManager,
        dividend: Expr,
        divisor: Expr,
    ) -> Result<Option<Expr>, SmtError> {
        let mut dividend_args = self.get_flat_mul(m, dividend);
        let mut divisor_args = self.get_flat_mul(m, divisor);
        let mut dividend_value = Int::one();
        let mut divisor_value = Int::one();
        let mut dividend_numeral: Option<Expr> = None;
        let mut divisor_numeral: Option<Expr> = None;
        let marked: HashSet<Expr> = dividend_args.iter().copied().collect();
        for arg in dividend_args.iter().copied() {
            let Some(value) = m.get_numeral(arg) else {
                continue;
            };
            dividend_value = value.clone();
            dividend_numeral = Some(arg);
        }
        for arg in divisor_args.iter().copied() {
            let value = m.get_numeral(arg).cloned();
            let is_minus_one = value.as_ref().is_some_and(|value| *value == -1);
            // A common factor of -1 stays, or the rewriting of (div (* -1 x) (* -1 y)) diverges.
            // Z3's check stores the -1 as the dividend's value.
            if marked.contains(&arg) && !is_minus_one {
                return Ok(Some(self.remove_divisor(m, arg, dividend, divisor)?));
            }
            if marked.contains(&arg) {
                dividend_value = Int::from(-1);
            }
            let Some(value) = value else {
                continue;
            };
            divisor_value = value;
            divisor_numeral = Some(arg);
        }
        let gcd = get_gcd(&dividend_value, &divisor_value);
        if gcd == 1 {
            return Ok(None);
        }
        let reduced = |m: &mut AstManager,
                       args: &mut Vec<Expr>,
                       numeral: Option<Expr>,
                       value: &Int|
         -> Result<Expr, SmtError> {
            let target = numeral.unwrap_or(-1);
            if let Some(index) = args.iter().position(|arg| *arg == target) {
                check_divisor(&gcd)?;
                args[index] = m.mk_numeral(&(value / &gcd));
            }
            self.mk_flat_mul_app(m, args)
        };
        let new_dividend = reduced(m, &mut dividend_args, dividend_numeral, &dividend_value)?;
        let new_divisor = reduced(m, &mut divisor_args, divisor_numeral, &divisor_value)?;
        Ok(Some(self.mk_idiv_app(m, new_dividend, new_divisor)?))
    }

    /// mk_idiv_core.
    pub fn mk_idiv(
        &mut self,
        m: &mut AstManager,
        left: Expr,
        right: Expr,
    ) -> Result<Reduced, SmtError> {
        self.curr_sort = SORT_INT;
        let dividend = m.get_numeral(left).cloned();
        let divisor = m.get_numeral(right).cloned();
        if let (Some(dividend), Some(divisor)) = (&dividend, &divisor)
            && !divisor.is_zero()
        {
            return Ok(Reduced::Done(
                m.mk_numeral(&get_euclidean_div(dividend, divisor)),
            ));
        }
        if divisor.as_ref().is_some_and(|divisor| *divisor == 1) {
            return Ok(Reduced::Done(left));
        }
        if divisor.as_ref().is_some_and(|divisor| *divisor == -1) {
            let minus_one = m.mk_numeral(&Int::from(-1));
            let product = self.mk_flat_mul_app(m, &[minus_one, left])?;
            return Ok(Reduced::Rewrite(self.reduce(product, 1)));
        }
        if divisor.as_ref().is_some_and(Int::is_zero) {
            return Ok(Reduced::Failed);
        }
        let zero = m.mk_numeral(&Int::zero());
        if left == right {
            let is_zero = m.mk_eq(left, zero)?;
            let zero_div = self.mk_idiv_app(m, zero, zero)?;
            let one = m.mk_numeral(&Int::one());
            let ite = self.mk_int_ite(m, is_zero, zero_div, one)?;
            return Ok(Reduced::Rewrite(self.reduce(ite, 3)));
        }
        if let Some(divisor) = &divisor
            && divisor.is_positive()
            && self.is_add(m, left)
        {
            let mut is_changed = false;
            let mut added = Int::zero();
            let mut args = Vec::new();
            for index in 0..m.get_num_args(left) {
                let arg = m.get_arg(left, index);
                let value = m.get_numeral(arg).cloned();
                let Some(value) = value.filter(|value| {
                    value.is_positive() && get_euclidean_mod(value, divisor) != *value
                }) else {
                    args.push(arg);
                    continue;
                };
                is_changed = true;
                added += get_euclidean_div(&value, divisor);
                args.push(m.mk_numeral(&get_euclidean_mod(&value, divisor)));
            }
            if is_changed {
                let added = m.mk_numeral(&added);
                let sum = m.mk_app(OP_ADD, &args, SORT_INT)?;
                let quotient = self.mk_idiv_app(m, sum, right)?;
                let result = self.mk_add_app(m, &[added, quotient])?;
                return Ok(Reduced::Rewrite(self.reduce(result, 3)));
            }
        }
        let Some(divided) = self.get_divides(m, left, right)? else {
            return Ok(Reduced::Failed);
        };
        let is_zero = m.mk_eq(zero, right)?;
        let zero_div = self.mk_idiv_app(m, left, zero)?;
        let ite = self.mk_int_ite(m, is_zero, zero_div, divided)?;
        Ok(Reduced::Rewrite(self.reduce(ite, UNBOUNDED_DEPTH)))
    }

    /// mk_mod_core.
    pub fn mk_mod(
        &mut self,
        m: &mut AstManager,
        left: Expr,
        right: Expr,
    ) -> Result<Reduced, SmtError> {
        self.curr_sort = SORT_INT;
        let dividend = m.get_numeral(left).cloned();
        let divisor = m.get_numeral(right).cloned();
        if let (Some(dividend), Some(divisor)) = (&dividend, &divisor)
            && !divisor.is_zero()
        {
            return Ok(Reduced::Done(
                m.mk_numeral(&get_euclidean_mod(dividend, divisor)),
            ));
        }
        if divisor
            .as_ref()
            .is_some_and(|divisor| *divisor == 1 || *divisor == -1)
        {
            return Ok(Reduced::Done(m.mk_numeral(&Int::zero())));
        }
        let zero = m.mk_numeral(&Int::zero());
        if left == right && divisor.is_none() {
            let is_zero = m.mk_eq(right, zero)?;
            let zero_mod = self.mk_mod_app(m, zero, zero)?;
            return Ok(Reduced::Done(self.mk_int_ite(m, is_zero, zero_mod, zero)?));
        }
        // mod is idempotent on a nonzero modulus.
        if m.get_op(left) == OP_MOD && m.get_arg(left, 1) == right {
            if divisor.as_ref().is_some_and(|divisor| !divisor.is_zero()) {
                return Ok(Reduced::Done(left));
            }
            if divisor.is_none() {
                let is_zero = m.mk_eq(right, zero)?;
                let inner = self.mk_mod_app(m, m.get_arg(left, 0), zero)?;
                let zero_mod = self.mk_mod_app(m, inner, zero)?;
                let ite = self.mk_int_ite(m, is_zero, zero_mod, left)?;
                return Ok(Reduced::Rewrite(self.reduce(ite, 2)));
            }
        }
        // Propagates mod inside a sum or product only if there is something to reduce.
        if let Some(divisor) = &divisor
            && divisor.is_positive()
            && (self.is_add(m, left) || self.is_mul(m, left))
        {
            let mut is_changed = false;
            let mut args = Vec::new();
            for index in 0..m.get_num_args(left) {
                let arg = m.get_arg(left, index);
                if let Some(value) = m.get_numeral(arg).cloned()
                    && get_euclidean_mod(&value, divisor) != value
                {
                    is_changed = true;
                    args.push(m.mk_numeral(&get_euclidean_mod(&value, divisor)));
                    continue;
                }
                if m.get_op(arg) == OP_MOD && m.get_arg(arg, 1) == right {
                    is_changed = true;
                    args.push(m.get_arg(arg, 0));
                    continue;
                }
                let coefficient = if self.is_mul(m, arg) && m.get_num_args(arg) == 2 {
                    m.get_numeral(m.get_arg(arg, 0)).cloned()
                } else {
                    None
                };
                if let Some(coefficient) = coefficient
                    && get_symmetric_mod(&coefficient, divisor) != coefficient
                {
                    is_changed = true;
                    let numeral = m.mk_numeral(&get_symmetric_mod(&coefficient, divisor));
                    args.push(m.mk_app(OP_MUL, &[numeral, m.get_arg(arg, 1)], SORT_INT)?);
                    continue;
                }
                args.push(arg);
            }
            if is_changed {
                let reduced = m.mk_app(m.decls[left as usize], &args, SORT_INT)?;
                let result = self.mk_mod_app(m, reduced, right)?;
                return Ok(Reduced::Rewrite(self.reduce(result, 3)));
            }
        }
        // For a symbolic modulus, the summands that are multiples of it go: mod (a + k*y) y = mod a y.
        if divisor.is_none() && self.is_add(m, left) {
            let mut args = Vec::new();
            for index in 0..m.get_num_args(left) {
                let arg = m.get_arg(left, index);
                let is_multiple = self.is_mul(m, arg)
                    && m.get_num_args(arg) == 2
                    && ((m.is_numeral(m.get_arg(arg, 0)) && m.get_arg(arg, 1) == right)
                        || (m.is_numeral(m.get_arg(arg, 1)) && m.get_arg(arg, 0) == right));
                if arg != right && !is_multiple {
                    args.push(arg);
                }
            }
            if args.len() < m.get_num_args(left) {
                let rest = if args.is_empty() {
                    zero
                } else {
                    self.mk_add_app(m, &args)?
                };
                let result = self.mk_mod_app(m, rest, right)?;
                return Ok(Reduced::Rewrite(self.reduce(result, 3)));
            }
        }
        let factor = if self.is_mul(m, left) && m.get_num_args(left) == 2 {
            m.get_numeral(m.get_arg(left, 0)).cloned()
        } else {
            None
        };
        if let (Some(divisor), Some(factor)) = (&divisor, &factor)
            && divisor.is_positive()
            && factor.is_positive()
            && (divisor % factor).is_zero()
        {
            let numeral = m.mk_numeral(factor);
            let modulus = m.mk_numeral(&(divisor / factor));
            let inner = self.mk_mod_app(m, m.get_arg(left, 1), modulus)?;
            let product = m.mk_app(OP_MUL, &[numeral, inner], SORT_INT)?;
            return Ok(Reduced::Rewrite(self.reduce(product, 1)));
        }
        // mod x -y = mod x y.
        if self.is_mul(m, right)
            && m.get_num_args(right) == 2
            && m.get_numeral(m.get_arg(right, 0))
                .is_some_and(|value| *value == -1)
        {
            let result = self.mk_mod_app(m, left, m.get_arg(right, 1))?;
            return Ok(Reduced::Rewrite(self.reduce(result, 1)));
        }
        if m.get_op(right) == OP_ITE {
            let then_mod = self.mk_mod_app(m, left, m.get_arg(right, 1))?;
            let else_mod = self.mk_mod_app(m, left, m.get_arg(right, 2))?;
            let ite = self.mk_int_ite(m, m.get_arg(right, 0), then_mod, else_mod)?;
            return Ok(Reduced::Rewrite(self.reduce(ite, 3)));
        }
        Ok(Reduced::Failed)
    }

    pub fn mk_abs(&mut self, m: &mut AstManager, arg: Expr) -> Result<Reduced, SmtError> {
        let sort = m.sorts[arg as usize];
        let zero = m.mk_numeral_of_sort(&Rational::zero(), sort);
        let condition = self.mk_atom(m, arg, zero, KIND_GE)?;
        let negation = m.mk_app(OP_UMINUS, &[arg], sort)?;
        let ite = m.mk_app(OP_ITE, &[condition, arg, negation], sort)?;
        Ok(Reduced::Rewrite(self.reduce(ite, 2)))
    }

    /// mk_div_core: division by a numeral other than 0 is a product.
    pub fn mk_div(
        &mut self,
        m: &mut AstManager,
        left: Expr,
        right: Expr,
    ) -> Result<Reduced, SmtError> {
        self.curr_sort = m.sorts[left as usize];
        if !m.is_numeral(right) || self.get_value(m, right).is_zero() {
            return Ok(Reduced::Failed);
        }
        let divisor = self.get_value(m, right);
        if m.is_numeral(left) {
            let value = self.get_value(m, left).div(&divisor);
            return Ok(Reduced::Done(m.mk_real_numeral(&value)));
        }
        let inverse = m.mk_real_numeral(&Rational::one().div(&divisor));
        let product = m.mk_app(OP_MUL, &[inverse, left], SORT_REAL)?;
        Ok(Reduced::Rewrite(self.reduce(product, 1)))
    }

    /// mk_to_int_core: (to_int (+ 1.0 (to_real x) y)) is (+ 1 x (to_int y)).
    pub fn mk_to_int(&mut self, m: &mut AstManager, arg: Expr) -> Result<Reduced, SmtError> {
        if m.is_int(arg) {
            return Ok(Reduced::Done(arg));
        }
        if m.is_numeral(arg) {
            let value = self.get_value(m, arg).floor();
            return Ok(Reduced::Done(m.mk_numeral(value.num())));
        }
        let op = m.get_op(arg);
        if op == OP_TO_REAL && m.is_int(m.get_arg(arg, 0)) {
            return Ok(Reduced::Done(m.get_arg(arg, 0)));
        }
        if op != OP_ADD && op != OP_MUL {
            return Ok(Reduced::Failed);
        }
        let mut int_args: Vec<Expr> = Vec::new();
        let mut real_args: Vec<Expr> = Vec::new();
        for index in 0..m.get_num_args(arg) {
            let child = m.get_arg(arg, index);
            if m.is_numeral(child) && self.get_value(m, child).is_int() {
                let value = self.get_value(m, child);
                int_args.push(m.mk_numeral(value.num()));
            } else if m.get_op(child) == OP_TO_REAL {
                int_args.push(m.get_arg(child, 0));
            } else {
                real_args.push(child);
            }
        }
        // Z3 makes a sum of one argument, which the manager leaves out.
        let mk_sum = |m: &mut AstManager, args: &[Expr], sort: Sort| {
            if args.len() == 1 {
                Ok(args[0])
            } else {
                m.mk_app(op, args, sort)
            }
        };
        if real_args.is_empty() {
            let sum = mk_sum(m, &int_args, SORT_INT)?;
            return Ok(Reduced::Rewrite(self.reduce(sum, 1)));
        }
        if int_args.is_empty() || op != OP_ADD {
            return Ok(Reduced::Failed);
        }
        let int_sum = mk_sum(m, &int_args, SORT_INT)?;
        let real_sum = mk_sum(m, &real_args, SORT_REAL)?;
        let to_int = m.mk_app(OP_TO_INT, &[real_sum], SORT_INT)?;
        let sum = m.mk_app(OP_ADD, &[int_sum, to_int], SORT_INT)?;
        Ok(Reduced::Rewrite(self.reduce(sum, 3)))
    }

    /// mk_to_real_core, with push_to_real: to_real distributes over sums and products.
    pub fn mk_to_real(&mut self, m: &mut AstManager, arg: Expr) -> Result<Reduced, SmtError> {
        if m.is_numeral(arg) {
            let value = self.get_value(m, arg);
            return Ok(Reduced::Done(m.mk_real_numeral(&value)));
        }
        if m.is_real(arg) {
            return Ok(Reduced::Done(arg));
        }
        let op = m.get_op(arg);
        if op != OP_ADD && op != OP_MUL {
            return Ok(Reduced::Failed);
        }
        let mut children = Vec::new();
        for index in 0..m.get_num_args(arg) {
            let child = m.get_arg(arg, index);
            children.push(m.mk_app(OP_TO_REAL, &[child], SORT_REAL)?);
        }
        let result = m.mk_app(op, &children, SORT_REAL)?;
        Ok(Reduced::Rewrite(self.reduce(result, 2)))
    }

    /// mk_is_int: a numeral is decided, and a term built from integers by sums and products is an
    /// integer. Any other term x is an integer when (to_real (to_int x)) is x.
    pub fn mk_is_int(&mut self, m: &mut AstManager, arg: Expr) -> Result<Reduced, SmtError> {
        if m.is_numeral(arg) {
            return Ok(Reduced::Done(if self.get_value(m, arg).is_int() {
                m.true_expr
            } else {
                m.false_expr
            }));
        }
        let mut todo = vec![arg];
        let mut visited: HashSet<Expr> = HashSet::new();
        let mut is_integral = true;
        while is_integral {
            let Some(current) = todo.pop() else {
                break;
            };
            if !visited.insert(current) {
                continue;
            }
            let op = m.get_op(current);
            if op == OP_TO_REAL {
                continue;
            }
            if m.is_numeral(current) {
                is_integral = self.get_value(m, current).is_int();
            } else if op == OP_MUL || op == OP_ADD || op == OP_SUB || op == OP_UMINUS {
                m.push_args(current, &mut todo);
            } else {
                is_integral = false;
            }
        }
        if is_integral {
            return Ok(Reduced::Done(m.true_expr));
        }
        let to_int = m.mk_app(OP_TO_INT, &[arg], SORT_INT)?;
        let to_real = m.mk_app(OP_TO_REAL, &[to_int], SORT_REAL)?;
        let eq = m.mk_eq(to_real, arg)?;
        Ok(Reduced::Rewrite(self.reduce(eq, 3)))
    }

    fn mk_atom(
        &self,
        m: &mut AstManager,
        left: Expr,
        right: Expr,
        kind: u8,
    ) -> Result<Expr, SmtError> {
        if kind == KIND_EQ {
            return m.mk_eq(left, right);
        }
        let op = if kind == KIND_LE { OP_LE } else { OP_GE };
        m.mk_app(op, &[left, right], SORT_BOOL)
    }

    // The factors of nested products, in order, on a stack of the terms to visit.
    fn flatten_mul(&self, m: &AstManager, expr: Expr, result: &mut Vec<Expr>) {
        let mut todo = vec![expr];
        while let Some(current) = todo.pop() {
            if self.is_mul(m, current) {
                for index in (0..m.get_num_args(current)).rev() {
                    todo.push(m.get_arg(current, index));
                }
            } else {
                result.push(current);
            }
        }
    }

    // is_non_negative, without powers and sequences. It counts each factor's occurrences by
    // scanning the factors, which are few, rather than by sorting them.
    fn is_non_negative(&mut self, m: &AstManager, expr: Expr) -> bool {
        if !self.is_mul(m, expr) {
            return false;
        }
        let mut factors = std::mem::take(&mut self.factors);
        factors.clear();
        self.flatten_mul(m, expr, &mut factors);
        let result = self.is_non_negative_factors(m, expr, &mut factors);
        self.factors = factors;
        result
    }

    fn is_non_negative_factors(&self, m: &AstManager, expr: Expr, factors: &mut [Expr]) -> bool {
        let mut is_negative = false;
        let mut num_factors = 0;
        for index in 0..factors.len() {
            let arg = factors[index];
            if !m.is_numeral(arg) {
                factors[num_factors] = arg;
                num_factors += 1;
            } else if m.get_rational_value(arg).is_negative() {
                is_negative = !is_negative;
            }
        }
        if is_negative {
            return false;
        }
        let mut num_odd = 0;
        let mut first_odd = -1;
        let mut second_odd = -1;
        for index in 0..num_factors {
            let factor = factors[index];
            if factors
                .iter()
                .position(|other| *other == factor)
                .is_some_and(|position| position < index)
            {
                continue;
            }
            let count = factors[index..num_factors]
                .iter()
                .filter(|other| **other == factor)
                .count();
            if count % 2 == 0 {
                continue;
            }
            num_odd += 1;
            if num_odd == 1 {
                first_odd = factor;
            } else if num_odd == 2 {
                second_odd = factor;
            } else {
                return false;
            }
        }
        if num_odd == 0 {
            return true;
        }
        // x * (x + 1) >= 0 holds for an integer x, as no integer lies strictly between -1 and 0,
        // but not for a real one.
        if num_odd != 2 || !m.is_int(expr) {
            return false;
        }
        self.is_successor(m, first_odd, second_odd) || self.is_successor(m, second_odd, first_odd)
    }

    // Whether sum is base plus or minus one.
    fn is_successor(&self, m: &AstManager, base: Expr, sum: Expr) -> bool {
        if !self.is_add(m, sum) {
            return false;
        }
        let mut offset = Rational::zero();
        let mut num_base = 0;
        for index in 0..m.get_num_args(sum) {
            let arg = m.get_arg(sum, index);
            if m.is_numeral(arg) {
                offset = offset.add(m.get_rational_value(arg));
            } else if arg == base {
                num_base += 1;
            } else {
                return false;
            }
        }
        num_base == 1 && (offset == Rational::one() || offset == Rational::minus_one())
    }

    fn negate_monomial(&self, m: &mut AstManager, expr: Expr) -> Result<Expr, SmtError> {
        if m.is_numeral(expr) {
            let value = self.get_value(m, expr).neg();
            return Ok(self.mk_numeral(m, &value));
        }
        if self.is_mul(m, expr) {
            let coefficient = m.get_arg(expr, 0);
            if !m.is_numeral(coefficient) {
                let minus_one = self.mk_numeral(m, &Rational::minus_one());
                return self.mk_mul_app(m, &[minus_one, expr]);
            }
            let value = self.get_value(m, coefficient);
            let mut factors = if value == Rational::minus_one() {
                Vec::new()
            } else {
                vec![self.mk_numeral(m, &value.neg())]
            };
            for index in 1..m.get_num_args(expr) {
                factors.push(m.get_arg(expr, index));
            }
            return if factors.len() == 1 {
                Ok(factors[0])
            } else {
                m.mk_app(OP_MUL, &factors, self.curr_sort)
            };
        }
        let minus_one = self.mk_numeral(m, &Rational::minus_one());
        m.mk_app(OP_MUL, &[minus_one, expr], self.curr_sort)
    }

    fn get_negated_polynomial(
        &self,
        m: &mut AstManager,
        expr: Expr,
    ) -> Result<Option<Expr>, SmtError> {
        let is_negative_monomial = |m: &AstManager, term: Expr| {
            self.is_mul(m, term)
                && m.is_numeral(m.get_arg(term, 0))
                && m.get_rational_value(m.get_arg(term, 0)).is_negative()
        };
        if is_negative_monomial(m, expr) {
            return Ok(Some(self.negate_monomial(m, expr)?));
        }
        if !self.is_add(m, expr) || !is_negative_monomial(m, m.get_arg(expr, 0)) {
            return Ok(None);
        }
        let mut args = Vec::new();
        for index in 0..m.get_num_args(expr) {
            let arg = m.get_arg(expr, index);
            args.push(self.negate_monomial(m, arg)?);
        }
        Ok(Some(m.mk_app(OP_ADD, &args, self.curr_sort)?))
    }

    // is_separated. Like narg, the last negated polynomial lives until is_separated returns.
    fn get_separated(
        &mut self,
        m: &mut AstManager,
        left: Expr,
        right: Expr,
        kind: u8,
    ) -> Result<Reduced, SmtError> {
        if kind == KIND_EQ || !m.is_numeral(right) {
            return Ok(Reduced::Failed);
        }
        let right_value = self.get_value(m, right);
        if kind == KIND_GE
            && right_value.is_zero()
            && self.is_mul(m, left)
            && self.is_non_negative(m, left)
        {
            return Ok(Reduced::Done(m.true_expr));
        }
        let mut bound = Rational::zero();
        let mut has_bound = true;
        let mut last_negated: Option<Expr> = None;
        for index in 0..self.get_num_monomials(m, left) {
            let arg = self.get_monomial(m, left, index);
            if m.is_numeral(arg) {
                bound = bound.add(m.get_rational_value(arg));
            } else if kind == KIND_LE && self.is_non_negative(m, arg) {
                continue;
            } else if kind == KIND_GE {
                let negated = m.with_temporaries_keeping(
                    |m| self.get_negated_polynomial(m, arg),
                    |result| result.iter().copied().collect(),
                )?;
                if let Some(negated) = negated {
                    if let Some(last) = last_negated {
                        m.dec_ref(last)?;
                    }
                    last_negated = Some(negated);
                }
                if negated.is_none_or(|negated| !self.is_non_negative(m, negated)) {
                    has_bound = false;
                }
            } else {
                has_bound = false;
            }
        }
        let result = if has_bound {
            self.mk_separated(m, left, kind, &bound, &right_value)?
        } else {
            Reduced::Failed
        };
        if let Some(last) = last_negated {
            m.dec_ref(last)?;
        }
        Ok(result)
    }

    fn mk_separated(
        &self,
        m: &mut AstManager,
        left: Expr,
        kind: u8,
        bound: &Rational,
        right_value: &Rational,
    ) -> Result<Reduced, SmtError> {
        let comparison = bound.compare(right_value);
        if kind == KIND_LE && comparison.is_lt() {
            return Ok(Reduced::Failed);
        }
        if kind == KIND_GE && comparison.is_gt() {
            return Ok(Reduced::Failed);
        }
        if kind == KIND_LE && comparison.is_gt() {
            return Ok(Reduced::Done(m.false_expr));
        }
        if kind == KIND_GE && comparison.is_lt() {
            return Ok(Reduced::Done(m.false_expr));
        }
        let zero = self.mk_numeral(m, &Rational::zero());
        if bound.is_zero() && self.is_mul(m, left) {
            let mut factors: Vec<Expr> = Vec::new();
            self.flatten_mul(m, left, &mut factors);
            let mut eqs = Vec::new();
            for arg in factors {
                if !m.is_numeral(arg) {
                    eqs.push(m.mk_eq(arg, zero)?);
                }
            }
            let disjunction = m.mk_or(&eqs)?;
            return Ok(Reduced::Rewrite(self.reduce(disjunction, 2)));
        }
        if !self.is_add(m, left) {
            return Ok(Reduced::Failed);
        }
        let mut atoms: Vec<Expr> = Vec::new();
        for index in 0..m.get_num_args(left) {
            let arg = m.get_arg(left, index);
            if !m.is_numeral(arg) {
                atoms.push(self.mk_atom(m, arg, zero, kind)?);
            }
        }
        let conjunction = m.mk_and(&atoms)?;
        Ok(Reduced::Rewrite(self.reduce(conjunction, 2)))
    }

    // is_bound.
    fn get_bound(
        &self,
        m: &mut AstManager,
        input_left: Expr,
        input_right: Expr,
        input_kind: u8,
    ) -> Result<Option<Expr>, SmtError> {
        if !self.is_add(m, input_left)
            && m.get_op(input_left) != OP_MOD
            && m.is_numeral(input_right)
        {
            let product = self.get_power_product(m, input_left);
            let coefficient = self.get_coefficient(m, input_left);
            let is_negative = coefficient.is_negative();
            let scale = coefficient.abs();
            let kind = if is_negative {
                get_inverse(input_kind)
            } else {
                input_kind
            };
            if coefficient.is_zero() || (!is_negative && scale == Rational::one()) {
                return Ok(None);
            }
            let value = self.get_value(m, input_right);
            let bound = if is_negative { value.neg() } else { value }.div(&scale);
            let is_int = m.is_int(input_left);
            if !is_int || bound.is_int() {
                let numeral = m.mk_numeral_of_sort(&bound, m.sorts[input_left as usize]);
                return Ok(Some(self.mk_atom(m, product, numeral, kind)?));
            }
            if kind == KIND_EQ {
                return Ok(Some(m.false_expr));
            }
            let rounded = if kind == KIND_LE {
                bound.floor()
            } else {
                bound.ceil()
            };
            let numeral = m.mk_numeral(rounded.num());
            return Ok(Some(self.mk_atom(m, product, numeral, kind)?));
        }
        let is_swapped = m.get_op(input_right) == OP_MOD;
        let left = if is_swapped { input_right } else { input_left };
        let right = if is_swapped { input_left } else { input_right };
        let kind = if is_swapped {
            get_inverse(input_kind)
        } else {
            input_kind
        };
        if m.get_numeral(right).is_none() || m.get_op(left) != OP_MOD {
            return Ok(None);
        }
        let divisor = m.get_arg(left, 1);
        if !m.is_numeral(divisor) || m.get_numeral_value(divisor).is_zero() {
            return Ok(None);
        }
        let value = m.get_numeral_value(right).clone();
        let modulus = m.get_numeral_value(divisor).abs();
        if value.is_negative() {
            return Ok(Some(if kind == KIND_GE {
                m.true_expr
            } else {
                m.false_expr
            }));
        }
        if value.is_zero() && kind == KIND_GE {
            return Ok(Some(m.true_expr));
        }
        if value.is_positive() && value >= modulus {
            return Ok(Some(if kind == KIND_LE {
                m.true_expr
            } else {
                m.false_expr
            }));
        }
        if &value + &Int::one() == modulus && kind == KIND_LE {
            return Ok(Some(m.true_expr));
        }
        Ok(None)
    }

    // div_polynomial: the quotient, with a reference the caller owns, or None when a constant is
    // not divisible and the atom is an equality. new_args is an expr_ref_buffer, which Z3 releases
    // first to last as it returns.
    fn divide_polynomial(
        &self,
        m: &mut AstManager,
        expr: Expr,
        divisor: &Int,
        rounding: Rounding,
    ) -> Result<Option<Expr>, SmtError> {
        check_divisor(divisor)?;
        let mut new_args: Vec<Expr> = Vec::new();
        let quotient = m.without_temporaries(|m| {
            for index in 0..self.get_num_monomials(m, expr) {
                let arg = self.get_monomial(m, expr, index);
                if m.is_numeral(arg) {
                    let value = m.get_numeral_value(arg).clone();
                    let is_divisible = (&value % divisor).is_zero();
                    if !is_divisible && rounding == Rounding::None {
                        return Ok(None);
                    }
                    let rounded = if is_divisible || rounding == Rounding::Floor {
                        get_euclidean_div(&value, divisor)
                    } else {
                        get_ceil_div(&value, divisor)
                    };
                    if !rounded.is_zero() {
                        let numeral = m.mk_numeral(&rounded);
                        m.inc_ref(numeral);
                        new_args.push(numeral);
                    }
                    continue;
                }
                let coefficient = self.get_coefficient(m, arg).num() / divisor;
                let product = self.get_power_product(m, arg);
                if coefficient == 1 {
                    m.inc_ref(product);
                    new_args.push(product);
                } else if !coefficient.is_zero() {
                    let numeral = m.mk_numeral(&coefficient);
                    let monomial = m.mk_app(OP_MUL, &[numeral, product], SORT_INT)?;
                    m.inc_ref(monomial);
                    new_args.push(monomial);
                }
            }
            Ok(Some(self.mk_add_app(m, &new_args)?))
        })?;
        if let Some(quotient) = quotient {
            m.inc_ref(quotient);
        }
        for arg in &new_args {
            m.dec_ref(*arg)?;
        }
        Ok(quotient)
    }

    // get_coeffs_gcd: the gcd of the coefficients, or 0 when there is no monomial, and the number
    // of non-zero constants.
    fn get_coeffs_gcd(&self, m: &AstManager, expr: Expr, state: &mut GcdState) {
        for index in 0..self.get_num_monomials(m, expr) {
            let arg = self.get_monomial(m, expr, index);
            if m.is_numeral(arg) {
                if !m.get_numeral_value(arg).is_zero() {
                    state.num_consts += 1;
                }
                continue;
            }
            state.gcd = if state.is_first {
                self.get_coefficient(m, arg).num().clone()
            } else {
                get_gcd(self.get_coefficient(m, arg).num(), &state.gcd)
            };
            state.is_first = false;
            if state.gcd == 1 {
                return;
            }
        }
    }

    fn is_holding(&self, left: &Rational, right: &Rational, kind: u8) -> bool {
        let comparison = left.compare(right);
        if kind == KIND_LE {
            comparison.is_le()
        } else if kind == KIND_GE {
            comparison.is_ge()
        } else {
            comparison.is_eq()
        }
    }

    // mk_le_ge_eq_core. Z3 holds the rewritten sides, new_arg1 and new_arg2, until it returns.
    fn mk_le_ge_eq(
        &mut self,
        m: &mut AstManager,
        original_left: Expr,
        original_right: Expr,
        kind: u8,
    ) -> Result<Reduced, SmtError> {
        let mut sides: Vec<Expr> = Vec::new();
        let result = self.mk_le_ge_eq_core(m, original_left, original_right, kind, &mut sides)?;
        for side in sides.iter().rev() {
            m.dec_ref(*side)?;
        }
        Ok(result)
    }

    fn mk_le_ge_eq_core(
        &mut self,
        m: &mut AstManager,
        original_left: Expr,
        original_right: Expr,
        kind: u8,
        sides: &mut Vec<Expr>,
    ) -> Result<Reduced, SmtError> {
        self.curr_sort = m.sorts[original_left as usize];
        let set_side = |m: &mut AstManager, sides: &mut Vec<Expr>, index: usize, expr: Expr| {
            m.inc_ref(expr);
            if index < sides.len() {
                m.dec_ref(sides[index])?;
                sides[index] = expr;
            } else {
                sides.push(expr);
            }
            Ok::<(), SmtError>(())
        };
        let is_arith_ineq_lhs = self.options.is_arith_ineq_lhs;
        let cancelled = m.with_temporaries_keeping(
            |m| self.cancel_monomials(m, original_left, original_right, is_arith_ineq_lhs),
            |result| match result {
                Some((lhs, rhs)) => vec![*lhs, *rhs],
                None => Vec::new(),
            },
        )?;
        if let Some((lhs, rhs)) = cancelled {
            sides.push(lhs);
            sides.push(rhs);
        }
        let mut is_changed = cancelled.is_some();
        let (mut left, mut right) = cancelled.unwrap_or((original_left, original_right));
        if m.is_numeral(left) && m.is_numeral(right) {
            let is_holding = self.is_holding(
                m.get_rational_value(left),
                m.get_rational_value(right),
                kind,
            );
            return Ok(Reduced::Done(if is_holding {
                m.true_expr
            } else {
                m.false_expr
            }));
        }
        let separated = self.get_separated(m, left, right, kind)?;
        if separated != Reduced::Failed {
            return Ok(separated);
        }
        let bound = match self.get_bound(m, left, right, kind)? {
            Some(bound) => Some(bound),
            None => self.get_bound(m, right, left, get_inverse(kind))?,
        };
        if let Some(bound) = bound {
            return Ok(Reduced::Done(bound));
        }
        if m.is_int(left) && self.options.is_gcd_rounding {
            let mut state = GcdState {
                gcd: Int::zero(),
                is_first: true,
                num_consts: 0,
            };
            self.get_coeffs_gcd(m, left, &mut state);
            if (state.is_first || state.gcd != 1) && state.num_consts <= 1 {
                self.get_coeffs_gcd(m, right, &mut state);
            }
            let divisor = state.gcd.abs();
            if !state.is_first && divisor != 1 && state.num_consts <= 1 {
                let left_rounding = if kind == KIND_LE {
                    Rounding::Ceil
                } else if kind == KIND_GE {
                    Rounding::Floor
                } else {
                    Rounding::None
                };
                let Some(new_left) = self.divide_polynomial(m, left, &divisor, left_rounding)?
                else {
                    return Ok(Reduced::Done(m.false_expr));
                };
                set_side(m, sides, 0, new_left)?;
                m.dec_ref(new_left)?;
                let right_rounding = if kind == KIND_LE {
                    Rounding::Floor
                } else if kind == KIND_GE {
                    Rounding::Ceil
                } else {
                    Rounding::None
                };
                let Some(new_right) = self.divide_polynomial(m, right, &divisor, right_rounding)?
                else {
                    return Ok(Reduced::Done(m.false_expr));
                };
                set_side(m, sides, 1, new_right)?;
                m.dec_ref(new_right)?;
                left = new_left;
                right = new_right;
                is_changed = true;
            }
        }
        if m.get_op(left) == OP_ITE && m.is_numeral(right) {
            let condition = m.get_arg(left, 0);
            let right_value = self.get_value(m, right);
            // Z3 makes the negated condition before it knows whether the result uses it, and its
            // conjunctions build an equality with arith_util::mk_eq but its disjunctions with
            // m.mk_eq.
            for (branch, other) in [(1, 2), (2, 1)] {
                if !m.is_numeral(m.get_arg(left, branch)) {
                    continue;
                }
                let negated = m.mk_not(condition)?;
                let value = self.get_value(m, m.get_arg(left, branch));
                let other = m.get_arg(left, other);
                let (holding, conjoined) = if branch == 1 {
                    (condition, negated)
                } else {
                    (negated, condition)
                };
                let result = if self.is_holding(&value, &right_value, kind) {
                    let atom = self.mk_atom(m, other, right, kind)?;
                    m.mk_or(&[holding, atom])?
                } else {
                    let conjunct = if kind == KIND_EQ {
                        self.mk_arith_eq(m, other, right)?
                    } else {
                        self.mk_atom(m, other, right, kind)?
                    };
                    m.mk_and(&[conjoined, conjunct])?
                };
                return Ok(Reduced::Rewrite(self.reduce(result, 2)));
            }
        }
        let is_to_int_right = m.get_op(right) == OP_TO_INT && m.is_numeral(left);
        let to_int_term = if is_to_int_right { right } else { left };
        let to_int_arg = if m.get_op(to_int_term) == OP_TO_INT {
            Some(m.get_arg(to_int_term, 0))
        } else {
            None
        };
        let to_int_bound = if is_to_int_right { left } else { right };
        if let Some(to_int_arg) = to_int_arg
            && m.is_numeral(to_int_bound)
        {
            let to_int_kind = if is_to_int_right {
                get_inverse(kind)
            } else {
                kind
            };
            let value = self.get_value(m, to_int_bound);
            let mk_lower = |m: &mut AstManager| {
                let numeral = m.mk_real_numeral(&value);
                m.mk_app(OP_GE, &[to_int_arg, numeral], SORT_BOOL)
            };
            let mk_upper = |m: &mut AstManager| {
                let numeral = m.mk_real_numeral(&value.add(&Rational::one()));
                m.mk_app(OP_LT, &[to_int_arg, numeral], SORT_BOOL)
            };
            if to_int_kind == KIND_LE {
                let upper = mk_upper(m)?;
                return Ok(Reduced::Rewrite(self.reduce(upper, 1)));
            }
            if to_int_kind == KIND_GE {
                let lower = mk_lower(m)?;
                return Ok(Reduced::Rewrite(self.reduce(lower, 1)));
            }
            let lower = mk_lower(m)?;
            let upper = mk_upper(m)?;
            let conjunction = m.mk_and(&[upper, lower])?;
            return Ok(Reduced::Rewrite(self.reduce(conjunction, 3)));
        }
        let negated = if self.options.is_arith_ineq_lhs && m.is_numeral(right) {
            self.get_negated_polynomial(m, left)?
        } else {
            None
        };
        if let Some(negated) = negated {
            set_side(m, sides, 0, negated)?;
            let value = self.get_value(m, right).neg();
            let negated_right = self.mk_numeral(m, &value);
            set_side(m, sides, 1, negated_right)?;
            return Ok(Reduced::Done(self.mk_atom(
                m,
                negated,
                negated_right,
                get_inverse(kind),
            )?));
        }
        if is_changed && left == original_left && right == original_right {
            return Ok(Reduced::Failed);
        }
        if is_changed {
            return Ok(Reduced::Done(self.mk_atom(m, left, right, kind)?));
        }
        self.factor_le_ge_eq(m, left, right, kind)
    }

    // factor_le_ge_eq: a sum with a nonlinear factor f, fg >= 0, splits on the signs of f and g.
    fn factor_le_ge_eq(
        &self,
        m: &mut AstManager,
        left: Expr,
        right: Expr,
        kind: u8,
    ) -> Result<Reduced, SmtError> {
        if !self.is_zero(m, right) {
            return Ok(Reduced::Failed);
        }
        let Some(factor) = self.find_nl_factor(m, left) else {
            return Ok(Reduced::Failed);
        };
        let rest = self.remove_nl_factor(m, factor, left)?;
        let zero = m.mk_numeral_of_sort(&Rational::zero(), m.sorts[left as usize]);
        let factor_eq = self.mk_arith_eq(m, factor, zero)?;
        let rest_eq = self.mk_arith_eq(m, rest, zero)?;
        let is_zero_product = m.mk_or(&[factor_eq, rest_eq])?;
        if kind == KIND_EQ {
            return Ok(Reduced::Rewrite(self.reduce(is_zero_product, 3)));
        }
        let factor_ge = m.mk_app(OP_GE, &[factor, zero], SORT_BOOL)?;
        let rest_ge = m.mk_app(OP_GE, &[rest, zero], SORT_BOOL)?;
        let is_same_sign = m.mk_eq(factor_ge, rest_ge)?;
        let sign = if kind == KIND_GE {
            is_same_sign
        } else {
            m.mk_not(is_same_sign)?
        };
        let result = m.mk_or(&[sign, is_zero_product])?;
        Ok(Reduced::Rewrite(self.reduce(result, 3)))
    }

    // arith_util::mk_eq: a numeral goes right, and otherwise the side with the smaller id goes
    // left.
    fn mk_arith_eq(&self, m: &mut AstManager, left: Expr, right: Expr) -> Result<Expr, SmtError> {
        let is_swapped = m.is_numeral(left)
            || (!m.is_numeral(right) && m.ids[left as usize] > m.ids[right as usize]);
        let lhs = if is_swapped { right } else { left };
        let rhs = if is_swapped { left } else { right };
        if lhs == rhs {
            return Ok(m.true_expr);
        }
        if m.is_numeral(lhs) && m.is_numeral(rhs) {
            return Ok(m.false_expr);
        }
        m.mk_eq(lhs, rhs)
    }

    // find_nl_factor: a factor of the first nonlinear product of a sum that divides every
    // monomial.
    fn find_nl_factor(&self, m: &AstManager, expr: Expr) -> Option<Expr> {
        let mut sum = vec![expr];
        let mut index = 0;
        while index < sum.len() {
            let arg = sum[index];
            index += 1;
            if self.is_add(m, arg) {
                m.push_args(arg, &mut sum);
                continue;
            }
            if !self.is_mul(m, arg) {
                continue;
            }
            let mut muls: Vec<Expr> = Vec::new();
            self.get_nl_muls(m, arg, &mut muls);
            if muls.len() <= 1 {
                continue;
            }
            return muls
                .into_iter()
                .find(|mul| self.is_add_factor(m, *mul, expr));
        }
        None
    }

    // get_nl_muls: the factors of a product that are not numerals, in order.
    fn get_nl_muls(&self, m: &AstManager, expr: Expr, muls: &mut Vec<Expr>) {
        let mut todo = vec![expr];
        while let Some(current) = todo.pop() {
            if self.is_mul(m, current) {
                for index in (0..m.get_num_args(current)).rev() {
                    todo.push(m.get_arg(current, index));
                }
            } else if !m.is_numeral(current) {
                muls.push(current);
            }
        }
    }

    // isMulFactor: some factor of the nested products is factor.
    fn is_mul_factor(&self, m: &AstManager, factor: Expr, expr: Expr) -> bool {
        let mut todo = vec![expr];
        while let Some(current) = todo.pop() {
            if self.is_mul(m, current) {
                for index in (0..m.get_num_args(current)).rev() {
                    todo.push(m.get_arg(current, index));
                }
            } else if factor == current {
                return true;
            }
        }
        false
    }

    // isAddFactor: factor is a factor of every summand of the nested sums.
    fn is_add_factor(&self, m: &AstManager, factor: Expr, expr: Expr) -> bool {
        let mut todo = vec![expr];
        while let Some(current) = todo.pop() {
            if self.is_add(m, current) {
                for index in (0..m.get_num_args(current)).rev() {
                    todo.push(m.get_arg(current, index));
                }
            } else if !self.is_mul_factor(m, factor, current) {
                return false;
            }
        }
        true
    }

    // remove_factor: the sum or product without one occurrence of the factor in each monomial.
    fn remove_nl_factor(
        &self,
        m: &mut AstManager,
        factor: Expr,
        expr: Expr,
    ) -> Result<Expr, SmtError> {
        let sort = m.sorts[expr as usize];
        if self.is_mul(m, expr) {
            let mut rest = vec![expr];
            let mut index = 0;
            while index < rest.len() {
                let arg = rest[index];
                if self.is_mul(m, arg) {
                    m.push_args(arg, &mut rest);
                    let last = rest.len() - 1;
                    rest[index] = rest[last];
                    rest.pop();
                    continue;
                }
                if arg == factor {
                    let last = rest.len() - 1;
                    rest[index] = rest[last];
                    rest.pop();
                    break;
                }
                index += 1;
            }
            if rest.is_empty() {
                return Ok(m.mk_numeral_of_sort(&Rational::one(), sort));
            }
            return if rest.len() == 1 {
                Ok(rest[0])
            } else {
                m.mk_app(OP_MUL, &rest, sort)
            };
        }
        if self.is_add(m, expr) {
            let mut sum = vec![expr];
            let mut index = 0;
            while index < sum.len() {
                let arg = sum[index];
                if self.is_add(m, arg) {
                    m.push_args(arg, &mut sum);
                    let last = sum.len() - 1;
                    sum[index] = sum[last];
                    sum.pop();
                    continue;
                }
                // A summand is a product or a term, whose removal does not recurse further.
                sum[index] = self.remove_nl_factor(m, factor, arg)?;
                index += 1;
            }
            return if sum.len() == 1 {
                Ok(sum[0])
            } else {
                m.mk_app(OP_ADD, &sum, sort)
            };
        }
        Ok(m.mk_numeral_of_sort(&Rational::one(), sort))
    }
}
