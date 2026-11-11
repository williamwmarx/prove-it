//! Ported from Z3 (src/qe/lite/qe_lite_tactic.cpp), MIT license, through `qe-lite-fm.ts`. The fm
//! of qe-lite: Fourier-Motzkin elimination of the integer variables of a quantifier that only occur
//! in clauses with one linear inequality.
//!
//! The TypeScript's constraints are objects that several lists share, compared by identity; here
//! they live in an arena of the `Fm`, cleared by each run, and the lists hold their indices.

use std::collections::{HashMap, HashSet};

use prove_num::{Int, get_gcd};

use crate::core::ast::{
    AstManager, Expr, KIND_QUANTIFIER, KIND_VAR, OP_ADD, OP_GE, OP_LE, OP_MUL, OP_NOT, OP_OR,
    SORT_BOOL, SORT_INT,
};
use crate::core::ref_vector::RefVector;
use crate::util::error::SmtError;

// fm's parameters.
const FM_LIMIT: u64 = 5_000_000;
const FM_CUTOFF1: usize = 8;
const FM_CUTOFF2: usize = 256;
const FM_EXTRA: usize = 0;

// A clause of Boolean literals and one linear inequality, a1*x1 + ... + an*xn <= c, or < c when
// strict. A literal is the index of a Boolean constant, negative when negated.
#[derive(Clone, Debug)]
struct Constraint {
    lits: Vec<i32>,
    xs: Vec<usize>,
    coefficients: Vec<Int>,
    c: Int,
    is_strict: bool,
    is_dead: bool,
}

// A constraint's index in the arena.
type ConstraintId = usize;

fn get_lit_index(lit: i32) -> usize {
    lit.unsigned_abs() as usize
}

fn get_lit_sign(lit: i32) -> i32 {
    if lit < 0 { -1 } else { 1 }
}

/// fm: Fourier-Motzkin elimination of the integer variables that only occur in clauses with one
/// linear inequality.
#[derive(Clone, Debug, Default)]
pub struct Fm {
    arena: Vec<Constraint>,
    constraints: Vec<ConstraintId>,
    bvar2expr: RefVector,
    bvar2sign: Vec<i32>,
    expr2bvar: HashMap<Expr, i32>,
    is_int: Vec<bool>,
    forbidden: Vec<bool>,
    var2expr: RefVector,
    expr2var: HashMap<Expr, usize>,
    var2pos: Vec<i64>,
    lowers: Vec<Vec<ConstraintId>>,
    uppers: Vec<Vec<ConstraintId>>,
    forbidden_set: HashSet<i32>,
    new_fmls: RefVector,
    counter: u64,
    is_inconsistent: bool,
    // m_sub_todo: the constraints to check for backward subsumption.
    sub_todo: Vec<ConstraintId>,
    pub num_vars: i32,
}

impl Fm {
    pub fn new() -> Fm {
        Fm::default()
    }

    /// ~fm.
    pub fn release(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.reset_constraints();
        self.new_fmls.reset(m)?;
        self.var2expr.reset(m)?;
        self.bvar2expr.reset(m)
    }

    pub fn apply(&mut self, m: &mut AstManager, fmls: &mut RefVector) -> Result<(), SmtError> {
        self.init(m, &fmls.items)?;
        self.init_use_list(m, &fmls.items)?;
        if fmls
            .items
            .iter()
            .any(|fml| m.has_quantifier_flags[*fml as usize] != 0)
        {
            return Ok(());
        }
        if self.is_inconsistent {
            self.set_false(m)?;
        } else {
            self.subsume();
            for variable in self.sort_candidates() {
                m.limit.checkpoint()?;
                if self.counter > FM_LIMIT {
                    break;
                }
                self.counter += 1;
                self.try_eliminate(m, variable)?;
                if self.is_inconsistent {
                    self.set_false(m)?;
                    break;
                }
            }
            if !self.is_inconsistent {
                self.copy_remaining(m)?;
            }
        }
        self.reset_constraints();
        fmls.reset(m)?;
        for fml in &self.new_fmls.items {
            fmls.push(m, *fml);
        }
        Ok(())
    }

    fn set_false(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        self.new_fmls.reset(m)?;
        self.new_fmls.push(m, m.false_expr);
        Ok(())
    }

    // Z3 keeps m_expr2bvar from the previous run, whose indices then point into the new, shorter
    // m_bvar2expr. This port clears it.
    fn init(&mut self, m: &mut AstManager, fmls: &[Expr]) -> Result<(), SmtError> {
        self.sub_todo.clear();
        self.reset_constraints();
        self.arena.clear();
        self.bvar2expr.reset(m)?;
        self.bvar2sign = vec![0];
        self.bvar2expr.push(m, -1);
        self.expr2bvar.clear();
        self.expr2var.clear();
        self.is_int.clear();
        self.var2pos.clear();
        self.forbidden.clear();
        self.var2expr.reset(m)?;
        self.lowers.clear();
        self.uppers.clear();
        self.new_fmls.reset(m)?;
        self.counter = 0;
        self.is_inconsistent = false;
        self.init_forbidden_set(m, fmls)
    }

    fn is_variable(&self, m: &AstManager, expr: Expr) -> bool {
        m.kinds[expr as usize] == KIND_VAR && m.values[expr as usize] < self.num_vars
    }

    fn is_literal(&self, m: &AstManager, expr: Expr) -> bool {
        m.is_uninterpreted_const(expr)
            || (m.is_not(expr) && m.is_uninterpreted_const(m.get_arg(expr, 0)))
    }

    // is_linear_mon_core: the variable of x or c*x, or -1.
    fn get_monomial_var(&self, m: &AstManager, expr: Expr) -> Expr {
        if m.get_op(expr) == OP_MUL && m.get_num_args(expr) == 2 {
            let coefficient = m.get_arg(expr, 0);
            let variable = m.get_arg(expr, 1);
            if m.is_numeral(coefficient) && self.is_variable(m, variable) {
                return variable;
            }
        }
        if self.is_variable(m, expr) { expr } else { -1 }
    }

    fn is_linear_pol(&self, m: &AstManager, expr: Expr) -> bool {
        let is_sum = m.get_op(expr) == OP_ADD;
        let num_monomials = if is_sum { m.get_num_args(expr) } else { 1 };
        let mut visited = HashSet::new();
        let mut is_all_forbidden = true;
        for index in 0..num_monomials {
            let monomial = if is_sum { m.get_arg(expr, index) } else { expr };
            let variable = self.get_monomial_var(m, monomial);
            if variable == -1 || !visited.insert(variable) {
                return false;
            }
            if !self.forbidden_set.contains(&m.values[variable as usize]) {
                is_all_forbidden = false;
            }
        }
        !is_all_forbidden
    }

    fn is_linear_ineq(&self, m: &AstManager, expr: Expr) -> bool {
        let atom = if m.is_not(expr) {
            m.get_arg(expr, 0)
        } else {
            expr
        };
        let op = m.get_op(atom);
        if (op != OP_LE && op != OP_GE) || m.get_num_args(atom) != 2 {
            return false;
        }
        let lhs = m.get_arg(atom, 0);
        let rhs = m.get_arg(atom, 1);
        // Z3's fm also eliminates Real variables, whose rational coefficients the port does not
        // keep.
        m.is_int(lhs) && m.is_numeral(rhs) && self.is_linear_pol(m, lhs)
    }

    // is_occ: a clause of literals with one linear inequality.
    fn is_occ(&self, m: &AstManager, expr: Expr) -> bool {
        if m.get_op(expr) != OP_OR {
            return self.is_linear_ineq(m, expr);
        }
        let mut is_found = false;
        for index in 0..m.get_num_args(expr) {
            let arg = m.get_arg(expr, index);
            if self.is_literal(m, arg) {
                continue;
            }
            if !self.is_linear_ineq(m, arg) || is_found {
                return false;
            }
            is_found = true;
        }
        is_found
    }

    // init_forbidden_set: the integer variables that occur outside the clauses are not
    // eliminated.
    fn init_forbidden_set(&mut self, m: &AstManager, fmls: &[Expr]) -> Result<(), SmtError> {
        self.forbidden_set.clear();
        let mut visited = HashSet::new();
        for fml in fmls {
            if self.is_occ(m, *fml) {
                continue;
            }
            let mut todo = vec![*fml];
            while let Some(expr) = todo.pop() {
                if !visited.insert(expr) {
                    continue;
                }
                let kind = m.kinds[expr as usize];
                if kind == KIND_VAR {
                    if self.is_variable(m, expr) && m.sorts[expr as usize] == SORT_INT {
                        self.forbidden_set.insert(m.values[expr as usize]);
                    }
                } else if kind == KIND_QUANTIFIER {
                    let data = m.get_quantifier(expr)?;
                    todo.push(data.body);
                    todo.extend(data.patterns.iter().copied());
                } else {
                    m.push_args(expr, &mut todo);
                }
            }
        }
        Ok(())
    }

    fn init_use_list(&mut self, m: &mut AstManager, fmls: &[Expr]) -> Result<(), SmtError> {
        for fml in fmls {
            if self.is_inconsistent {
                break;
            }
            if self.is_occ(m, *fml) {
                self.add_constraint(m, *fml)?;
            } else {
                self.new_fmls.push(m, *fml);
            }
        }
        Ok(())
    }

    // toVar.
    fn get_var(&mut self, m: &mut AstManager, expr: Expr) -> usize {
        if let Some(existing) = self.expr2var.get(&expr) {
            return *existing;
        }
        let variable = self.var2expr.len();
        self.var2expr.push(m, expr);
        self.is_int.push(m.sorts[expr as usize] == SORT_INT);
        self.var2pos.push(-1);
        self.expr2var.insert(expr, variable);
        self.lowers.push(Vec::new());
        self.uppers.push(Vec::new());
        self.forbidden
            .push(self.forbidden_set.contains(&m.values[expr as usize]));
        variable
    }

    // toLiteral.
    fn get_literal(&mut self, m: &mut AstManager, expr: Expr) -> i32 {
        let is_negated = m.is_not(expr);
        let atom = if is_negated { m.get_arg(expr, 0) } else { expr };
        let bvar = match self.expr2bvar.get(&atom) {
            Some(bvar) => *bvar,
            None => {
                let bvar = self.bvar2expr.len() as i32;
                self.bvar2expr.push(m, atom);
                self.bvar2sign.push(0);
                self.expr2bvar.insert(atom, bvar);
                bvar
            }
        };
        if is_negated { -bvar } else { bvar }
    }

    fn add_constraint(&mut self, m: &mut AstManager, fml: Expr) -> Result<(), SmtError> {
        let is_clause = m.get_op(fml) == OP_OR;
        let num_args = if is_clause { m.get_num_args(fml) } else { 1 };
        let mut lits = Vec::new();
        let mut xs = Vec::new();
        let mut coefficients = Vec::new();
        let mut c = Int::zero();
        let mut is_strict = false;
        for arg_index in 0..num_args {
            let arg = if is_clause {
                m.get_arg(fml, arg_index)
            } else {
                fml
            };
            if self.is_literal(m, arg) {
                lits.push(self.get_literal(m, arg));
                continue;
            }
            let is_negated = m.is_not(arg);
            let atom = if is_negated { m.get_arg(arg, 0) } else { arg };
            is_strict = is_negated;
            let is_flipped = if m.get_op(atom) == OP_GE {
                !is_negated
            } else {
                is_negated
            };
            let lhs = m.get_arg(atom, 0);
            let rhs = m.get_arg(atom, 1);
            c = if is_flipped {
                -m.get_numeral_value(rhs)
            } else {
                m.get_numeral_value(rhs).clone()
            };
            let is_sum = m.get_op(lhs) == OP_ADD;
            let num_monomials = if is_sum { m.get_num_args(lhs) } else { 1 };
            let mut is_all_int = true;
            for index in 0..num_monomials {
                let monomial = if is_sum { m.get_arg(lhs, index) } else { lhs };
                let is_scaled = m.get_op(monomial) == OP_MUL && m.get_num_args(monomial) == 2;
                let coefficient = if is_scaled {
                    m.get_numeral_value(m.get_arg(monomial, 0)).clone()
                } else {
                    Int::from(1)
                };
                let variable = self.get_var(
                    m,
                    if is_scaled {
                        m.get_arg(monomial, 1)
                    } else {
                        monomial
                    },
                );
                xs.push(variable);
                coefficients.push(if is_flipped {
                    -coefficient
                } else {
                    coefficient
                });
                if !self.is_int[variable] {
                    is_all_int = false;
                }
            }
            if is_all_int && is_strict {
                is_strict = false;
                c -= Int::from(1);
            }
        }
        let constraint = self.mk_constraint(Constraint {
            lits,
            xs,
            coefficients,
            c,
            is_strict,
            is_dead: false,
        });
        self.register_constraint(m, constraint)
    }

    fn mk_constraint(&mut self, constraint: Constraint) -> ConstraintId {
        self.arena.push(constraint);
        self.arena.len() - 1
    }

    // normalize_coeffs: divides by the gcd of the coefficients and the constant.
    fn normalize_coeffs(&mut self, id: ConstraintId) -> Result<(), SmtError> {
        let constraint = &mut self.arena[id];
        if constraint.xs.is_empty() {
            return Ok(());
        }
        let mut divisor = constraint.c.abs();
        for coefficient in &constraint.coefficients {
            if divisor == 1 {
                break;
            }
            divisor = get_gcd(coefficient, &divisor);
        }
        if divisor == 1 {
            return Ok(());
        }
        // The TypeScript throws a RangeError when every coefficient and the constant are 0.
        if divisor.is_zero() {
            return Err(SmtError::Invariant(
                "fm divides a constraint by zero".into(),
            ));
        }
        constraint.c = &constraint.c / &divisor;
        for coefficient in &mut constraint.coefficients {
            *coefficient = &*coefficient / &divisor;
        }
        Ok(())
    }

    fn is_false_constraint(&self, id: ConstraintId) -> bool {
        let constraint = &self.arena[id];
        constraint.lits.is_empty()
            && constraint.xs.is_empty()
            && (constraint.c < 0 || (constraint.is_strict && constraint.c.is_zero()))
    }

    fn register_constraint(
        &mut self,
        m: &mut AstManager,
        id: ConstraintId,
    ) -> Result<(), SmtError> {
        self.normalize_coeffs(id)?;
        if self.is_false_constraint(id) {
            self.del_constraint(id);
            self.is_inconsistent = true;
            return Ok(());
        }
        let mut is_indexed = false;
        for index in 0..self.arena[id].xs.len() {
            let variable = self.arena[id].xs[index];
            if self.forbidden[variable] {
                continue;
            }
            is_indexed = true;
            if self.arena[id].coefficients[index] < 0 {
                self.lowers[variable].push(id);
            } else {
                self.uppers[variable].push(id);
            }
        }
        if is_indexed {
            if !self.sub_todo.contains(&id) {
                self.sub_todo.push(id);
            }
            self.constraints.push(id);
            return Ok(());
        }
        let expr = self.to_expr(m, id)?;
        self.new_fmls.push(m, expr);
        self.del_constraint(id);
        Ok(())
    }

    fn del_constraint(&mut self, id: ConstraintId) {
        if let Some(position) = self.sub_todo.iter().position(|other| *other == id) {
            self.sub_todo.swap_remove(position);
        }
    }

    fn reset_constraints(&mut self) {
        for id in std::mem::take(&mut self.constraints) {
            self.del_constraint(id);
        }
    }

    // to_expr: the constraint as a formula, with a raw reference like Z3's.
    fn to_expr(&self, m: &mut AstManager, id: ConstraintId) -> Result<Expr, SmtError> {
        let constraint = &self.arena[id];
        let mut ineq = -1;
        if constraint.xs.is_empty() {
            if constraint.c > 0 || (!constraint.is_strict && constraint.c.is_zero()) {
                return Ok(m.true_expr);
            }
        } else {
            let mut monomials = Vec::with_capacity(constraint.xs.len());
            for (index, variable) in constraint.xs.iter().enumerate() {
                let expr = self.var2expr.items[*variable];
                let coefficient = &constraint.coefficients[index];
                monomials.push(if *coefficient == 1 {
                    expr
                } else {
                    let numeral = m.mk_numeral(coefficient);
                    m.mk_app(OP_MUL, &[numeral, expr], SORT_INT)?
                });
            }
            let lhs = if monomials.len() == 1 {
                monomials[0]
            } else {
                m.mk_app(OP_ADD, &monomials, SORT_INT)?
            };
            let rhs = m.mk_numeral(&constraint.c);
            ineq = if constraint.is_strict {
                let atom = m.mk_app(OP_GE, &[lhs, rhs], SORT_BOOL)?;
                m.mk_app(OP_NOT, &[atom], SORT_BOOL)?
            } else {
                m.mk_app(OP_LE, &[lhs, rhs], SORT_BOOL)?
            };
        }
        if constraint.lits.is_empty() {
            return Ok(if ineq == -1 { m.false_expr } else { ineq });
        }
        let mut lits = Vec::with_capacity(constraint.lits.len() + 1);
        for lit in &constraint.lits {
            let atom = self.bvar2expr.items[get_lit_index(*lit)];
            lits.push(if *lit < 0 {
                m.mk_app(OP_NOT, &[atom], SORT_BOOL)?
            } else {
                atom
            });
        }
        if ineq != -1 {
            lits.push(ineq);
        }
        if lits.len() == 1 {
            Ok(lits[0])
        } else {
            m.mk_app(OP_OR, &lits, SORT_BOOL)
        }
    }

    // subsumes: c1's literals are among c2's, the polynomials are the same, and c1's bound is at
    // most c2's.
    fn is_subsuming(&mut self, first_id: ConstraintId, second_id: ConstraintId) -> bool {
        if first_id == second_id {
            return false;
        }
        let first = &self.arena[first_id];
        let second = &self.arena[second_id];
        if first.lits.len() > second.lits.len() || first.xs.len() != second.xs.len() {
            return false;
        }
        if first.c > second.c {
            return false;
        }
        if !first.is_strict && second.is_strict && first.c == second.c {
            return false;
        }
        self.counter += (first.lits.len() + second.lits.len()) as u64;
        for (index, variable) in first.xs.iter().enumerate() {
            self.var2pos[*variable] = index as i64;
        }
        let is_same_pol = second.xs.iter().enumerate().all(|(index, variable)| {
            let position = self.var2pos[*variable];
            position != -1 && first.coefficients[position as usize] == second.coefficients[index]
        });
        for variable in &first.xs {
            self.var2pos[*variable] = -1;
        }
        if !is_same_pol {
            return false;
        }
        for lit in &second.lits {
            self.bvar2sign[get_lit_index(*lit)] = get_lit_sign(*lit);
        }
        let is_subset = first
            .lits
            .iter()
            .all(|lit| self.bvar2sign[get_lit_index(*lit)] == get_lit_sign(*lit));
        for lit in &second.lits {
            self.bvar2sign[get_lit_index(*lit)] = 0;
        }
        is_subset
    }

    fn backward_subsumption(&mut self, id: ConstraintId) {
        if self.arena[id].xs.is_empty() {
            return;
        }
        let mut best: Option<usize> = None;
        let mut best_size = usize::MAX;
        let mut is_best_lower = false;
        for (index, variable) in self.arena[id].xs.iter().enumerate() {
            if self.forbidden[*variable] {
                continue;
            }
            let is_lower = self.arena[id].coefficients[index] < 0;
            let candidates = if is_lower {
                &self.lowers[*variable]
            } else {
                &self.uppers[*variable]
            };
            if candidates.len() < best_size {
                best = Some(*variable);
                best_size = candidates.len();
                is_best_lower = is_lower;
            }
        }
        let Some(best) = best else {
            return;
        };
        if best_size == 0 {
            return;
        }
        let list = std::mem::take(if is_best_lower {
            &mut self.lowers[best]
        } else {
            &mut self.uppers[best]
        });
        self.counter += list.len() as u64;
        let mut kept = Vec::with_capacity(list.len());
        for other in list {
            if self.arena[other].is_dead {
                continue;
            }
            if !self.is_subsuming(id, other) {
                kept.push(other);
                continue;
            }
            self.arena[other].is_dead = true;
        }
        if is_best_lower {
            self.lowers[best] = kept;
        } else {
            self.uppers[best] = kept;
        }
    }

    fn subsume(&mut self) {
        while let Some(id) = self.sub_todo.pop() {
            if !self.arena[id].is_dead {
                self.backward_subsumption(id);
            }
        }
    }

    // sort_candidates: the variables without a lower or upper bound first, then by the number of
    // constraints they would create.
    fn sort_candidates(&self) -> Vec<usize> {
        let mut costs: Vec<(usize, usize)> = Vec::new();
        for (variable, is_forbidden) in self.forbidden.iter().enumerate() {
            if !is_forbidden {
                costs.push((
                    variable,
                    self.lowers[variable].len() * self.uppers[variable].len(),
                ));
            }
        }
        let is_less = |first: &(usize, usize), second: &(usize, usize)| {
            if first.1 == 0 {
                return second.1 > 0 || first.0 < second.0;
            }
            if second.1 == 0 {
                return false;
            }
            let is_first_int = self.is_int[first.0];
            let is_second_int = self.is_int[second.0];
            (!is_first_int && is_second_int)
                || (is_first_int == is_second_int && first.1 < second.1)
        };
        costs.sort_by(|first, second| {
            if is_less(first, second) {
                std::cmp::Ordering::Less
            } else if is_less(second, first) {
                std::cmp::Ordering::Greater
            } else {
                std::cmp::Ordering::Equal
            }
        });
        costs.into_iter().map(|cost| cost.0).collect()
    }

    // analyze: whether every variable is an integer, and whether x's coefficients are all 1 or
    // -1.
    fn analyze(&self, constraints: &[ConstraintId], variable: usize) -> (bool, bool) {
        let mut is_unit = true;
        for id in constraints {
            let constraint = &self.arena[*id];
            for (index, other) in constraint.xs.iter().enumerate() {
                if !self.is_int[*other] {
                    return (false, is_unit);
                }
                let coefficient = &constraint.coefficients[index];
                if *other == variable && *coefficient != 1 && *coefficient != -1 {
                    is_unit = false;
                }
            }
        }
        (true, is_unit)
    }

    fn can_eliminate(&self, variable: usize) -> bool {
        if !self.is_int[variable] {
            return true;
        }
        let (is_lower_all_int, is_lower_unit) = self.analyze(&self.lowers[variable], variable);
        if !is_lower_all_int {
            return false;
        }
        let (is_upper_all_int, is_upper_unit) = self.analyze(&self.uppers[variable], variable);
        is_upper_all_int && (is_lower_unit || is_upper_unit)
    }

    fn mark_dead(&mut self, variable: usize) {
        for id in &self.lowers[variable] {
            self.arena[*id].is_dead = true;
        }
        for id in &self.uppers[variable] {
            self.arena[*id].is_dead = true;
        }
    }

    // resolve: the combination of a lower and an upper bound of x without x, or None when it
    // holds.
    fn resolve(
        &mut self,
        lower_id: ConstraintId,
        upper_id: ConstraintId,
        variable: usize,
    ) -> Result<Option<ConstraintId>, SmtError> {
        let lower = &self.arena[lower_id];
        let upper = &self.arena[upper_id];
        self.counter +=
            (lower.xs.len() + upper.xs.len() + lower.lits.len() + upper.lits.len()) as u64;
        let get_coefficient = |constraint: &Constraint| {
            constraint
                .xs
                .iter()
                .position(|other| *other == variable)
                .map(|position| constraint.coefficients[position].clone())
                .ok_or_else(|| SmtError::Invariant("fm resolves on a missing variable".into()))
        };
        let a = -get_coefficient(lower)?;
        let b = get_coefficient(upper)?;
        let mut c = &(&lower.c * &b) + &(&upper.c * &a);
        let mut is_strict = lower.is_strict || upper.is_strict;
        let mut xs: Vec<usize> = Vec::new();
        let mut coefficients: Vec<Int> = Vec::new();
        for (index, other) in lower.xs.iter().enumerate() {
            if *other == variable {
                continue;
            }
            self.var2pos[*other] = xs.len() as i64;
            xs.push(*other);
            coefficients.push(&lower.coefficients[index] * &b);
        }
        for (index, other) in upper.xs.iter().enumerate() {
            if *other == variable {
                continue;
            }
            let position = self.var2pos[*other];
            if position == -1 {
                xs.push(*other);
                coefficients.push(&upper.coefficients[index] * &a);
            } else {
                let position = position as usize;
                coefficients[position] =
                    &coefficients[position] + &(&upper.coefficients[index] * &a);
            }
        }
        let mut new_xs = Vec::new();
        let mut new_coefficients = Vec::new();
        for (index, coefficient) in coefficients.into_iter().enumerate() {
            if !coefficient.is_zero() {
                new_xs.push(xs[index]);
                new_coefficients.push(coefficient);
            }
        }
        if is_strict && new_xs.iter().all(|other| self.is_int[*other]) {
            is_strict = false;
            c -= Int::from(1);
        }
        for other in &lower.xs {
            self.var2pos[*other] = -1;
        }
        if new_xs.is_empty() && (c > 0 || (!is_strict && c.is_zero())) {
            return Ok(None);
        }
        for lit in &lower.lits {
            self.bvar2sign[get_lit_index(*lit)] = get_lit_sign(*lit);
        }
        let mut lits = lower.lits.clone();
        let mut is_tautology = false;
        for lit in &upper.lits {
            if is_tautology {
                break;
            }
            let sign = self.bvar2sign[get_lit_index(*lit)];
            if sign == 0 {
                lits.push(*lit);
            } else if if sign == -1 { *lit > 0 } else { *lit < 0 } {
                is_tautology = true;
            }
        }
        for lit in &lower.lits {
            self.bvar2sign[get_lit_index(*lit)] = 0;
        }
        if is_tautology {
            return Ok(None);
        }
        if lits.is_empty() && new_xs.is_empty() && (c < 0 || (is_strict && c.is_zero())) {
            self.is_inconsistent = true;
            return Ok(None);
        }
        Ok(Some(self.mk_constraint(Constraint {
            lits,
            xs: new_xs,
            coefficients: new_coefficients,
            c,
            is_strict,
            is_dead: false,
        })))
    }

    fn try_eliminate(&mut self, m: &mut AstManager, variable: usize) -> Result<(), SmtError> {
        let lowers: Vec<ConstraintId> = self.lowers[variable]
            .iter()
            .copied()
            .filter(|id| !self.arena[*id].is_dead)
            .collect();
        let uppers: Vec<ConstraintId> = self.uppers[variable]
            .iter()
            .copied()
            .filter(|id| !self.arena[*id].is_dead)
            .collect();
        self.lowers[variable] = lowers.clone();
        self.uppers[variable] = uppers.clone();
        if lowers.is_empty() || uppers.is_empty() {
            self.mark_dead(variable);
            return Ok(());
        }
        if lowers.len() > FM_CUTOFF1 && uppers.len() > FM_CUTOFF1 {
            return Ok(());
        }
        if lowers.len() * uppers.len() > FM_CUTOFF2 {
            return Ok(());
        }
        if !self.can_eliminate(variable) {
            return Ok(());
        }
        self.counter += (lowers.len() * uppers.len()) as u64;
        let limit = lowers.len() + uppers.len() + FM_EXTRA;
        let mut created = Vec::new();
        for lower in &lowers {
            for upper in &uppers {
                if self.is_inconsistent || created.len() > limit {
                    return Ok(());
                }
                if let Some(resolved) = self.resolve(*lower, *upper, variable)? {
                    created.push(resolved);
                }
            }
        }
        self.mark_dead(variable);
        self.counter += created.len() as u64;
        for id in created {
            self.backward_subsumption(id);
            self.register_constraint(m, id)?;
        }
        Ok(())
    }

    // copy_remaining: the live constraints of the upper bounds, then of the lower bounds.
    fn copy_remaining(&mut self, m: &mut AstManager) -> Result<(), SmtError> {
        let uppers = std::mem::take(&mut self.uppers);
        let lowers = std::mem::take(&mut self.lowers);
        for lists in [&uppers, &lowers] {
            for constraints in lists {
                for id in constraints {
                    if self.arena[*id].is_dead {
                        continue;
                    }
                    self.arena[*id].is_dead = true;
                    let expr = self.to_expr(m, *id)?;
                    self.new_fmls.push(m, expr);
                }
            }
        }
        Ok(())
    }
}
