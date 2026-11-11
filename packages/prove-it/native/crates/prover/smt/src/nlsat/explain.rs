//! Ported from Z3 (src/nlsat/nlsat_explain.cpp), MIT license, see z3-license.txt. Explains a set of
//! literals that is infeasible at the sample: the literals of a lemma that exclude a cell around
//! the sample in which the set stays infeasible. Only Z3's default nlsat parameters are ported:
//! simplify_conflicts and factor on, minimize_conflicts, add_all_coeffs and zero_disc off, and lws
//! on. So the cell always comes from the levelwise construction, and Z3's fallback projection
//! (project with cac_add_cell_lits, add_lcs and the psc_* helpers) is not ported.

use std::collections::HashSet;

use super::algebraic::{AlgebraicManager, Anum};
use super::atoms::{
    AtomTable, BoolVarHooks, FALSE_LITERAL, ScopedLiteral, ScopedLiterals, TRUE_BOOL_VAR,
    TRUE_LITERAL, flip_kind,
};
use super::evaluator::{Evaluator, get_literal_value};
use super::levelwise::{TodoSet, get_single_cell};
use super::polynomial::{NULL_VAR, Polynomial, PolynomialCache, PolynomialManager, Var};
use super::types::{Atom, AtomRef, IneqAtom, IneqKind, RootKind};
use super::{Int, L_TRUE, SmtError};

/// The solver state an explanation reads.
pub struct ExplainContext<'a> {
    pub pm: &'a mut PolynomialManager,
    pub am: &'a mut AlgebraicManager,
    pub cache: &'a mut PolynomialCache,
    pub atoms: &'a mut AtomTable,
    /// sample(): the solver's assignment, refined in place.
    pub sample: &'a mut Vec<Option<Anum>>,
    /// With the Boolean values of `hooks`, what value(l) reads: l_true, l_false or l_undef.
    pub evaluator: &'a mut Evaluator,
    /// The solver's onMk and onDelete, which the atoms Explain makes and frees fire, and its
    /// Boolean values, which they reset.
    pub hooks: &'a mut dyn BoolVarHooks,
    /// m_var2eq: the equation of least degree assigned for each variable.
    pub var2eq: &'a [Option<AtomRef>],
}

// add_all_coeffs_restart: every coefficient of a polynomial vanished, so the explanation starts
// over adding all coefficients. It travels as an error beside the solver's own, and
// compute_conflict_explanation catches it.
enum ExplainError {
    AddAllCoeffsRestart,
    Smt(SmtError),
}

impl From<SmtError> for ExplainError {
    fn from(error: SmtError) -> ExplainError {
        ExplainError::Smt(error)
    }
}

// eq_info: an equation used to rewrite the core, and what its leading coefficient must satisfy.
struct EqInfo {
    eq: Polynomial,
    variable: Var,
    degree: u32,
    lc: Polynomial,
    lc_sign: i32,
    is_lc_const: bool,
    is_lc_added: bool,
    is_lc_ineq_added: bool,
}

// ROOT_TO_INEQ: the inequality kind, and whether it is negated, of a linear root atom.
fn get_root_to_ineq(kind: RootKind) -> (IneqKind, bool) {
    match kind {
        RootKind::RootEq => (IneqKind::Eq, false),
        RootKind::RootLt => (IneqKind::Lt, false),
        RootKind::RootGt => (IneqKind::Gt, false),
        RootKind::RootLe => (IneqKind::Gt, true),
        RootKind::RootGe => (IneqKind::Lt, true),
    }
}

fn add_lc_ineq(info: &mut EqInfo) {
    info.is_lc_added = true;
    info.is_lc_ineq_added = true;
}

fn add_lc_diseq(info: &mut EqInfo) {
    if info.is_lc_added {
        return;
    }
    info.is_lc_added = true;
    info.is_lc_ineq_added = false;
}

fn get_kind_for_sign(sign: i32) -> IneqKind {
    if sign == 0 {
        IneqKind::Eq
    } else if sign < 0 {
        IneqKind::Lt
    } else {
        IneqKind::Gt
    }
}

// The equation var2eq keeps for a variable, an inequality atom.
fn get_eq_atom(eq: &Atom) -> Result<&IneqAtom, SmtError> {
    match eq {
        Atom::Ineq(atom) => Ok(atom),
        Atom::Root(_) => Err(SmtError::Invariant("var2eq holds a root atom".to_string())),
    }
}

pub struct Explain {
    // The caller's result while an explanation runs: swapped in from the caller and back out by
    // reset_result, since the explanation cannot keep the caller's reference.
    result: ScopedLiterals,
    added: HashSet<u32>,
    todo: TodoSet,
    lower_stage_polys: Vec<Polynomial>,
    core: ScopedLiterals,
    is_add_all_coeffs: bool,
    /// m_full_dimensional: the solver sets it when every clause is full dimensional, and the cell
    /// bounds are then closed.
    pub is_full_dimensional: bool,
}

impl Default for Explain {
    fn default() -> Explain {
        Explain::new()
    }
}

impl Explain {
    pub fn new() -> Explain {
        Explain {
            result: ScopedLiterals::new(),
            added: HashSet::new(),
            todo: TodoSet::new(),
            lower_stage_polys: Vec::new(),
            core: ScopedLiterals::new(),
            is_add_all_coeffs: false,
            is_full_dimensional: false,
        }
    }

    fn get_sign(ctx: &mut ExplainContext<'_>, polynomial: &Polynomial) -> Result<i32, SmtError> {
        ctx.am.eval_sign_at(ctx.pm, polynomial, ctx.sample)
    }

    fn get_atom(ctx: &ExplainContext<'_>, literal: u32) -> Result<AtomRef, SmtError> {
        ctx.atoms
            .get_atom(literal)
            .cloned()
            .ok_or_else(|| SmtError::Invariant(format!("literal {literal} has no atom")))
    }

    fn add_literal(&mut self, ctx: &mut ExplainContext<'_>, literal: u32) {
        if literal == FALSE_LITERAL || self.added.contains(&literal) {
            return;
        }
        self.added.insert(literal);
        self.result.push(ctx.atoms, literal);
    }

    fn reset_result(&mut self, result: &mut ScopedLiterals) {
        self.added.clear();
        std::mem::swap(&mut self.result, result);
    }

    fn collect_polys(
        ctx: &ExplainContext<'_>,
        literals: &[u32],
    ) -> Result<Vec<Polynomial>, SmtError> {
        let mut polynomials = Vec::new();
        for &literal in literals {
            match &*Self::get_atom(ctx, literal)? {
                Atom::Ineq(atom) => polynomials.extend(atom.polynomials.iter().cloned()),
                Atom::Root(atom) => polynomials.push(atom.polynomial.clone()),
            }
        }
        Ok(polynomials)
    }

    fn get_max_var_of_polys(pm: &PolynomialManager, polynomials: &[Polynomial]) -> Var {
        let mut result = NULL_VAR;
        for polynomial in polynomials {
            let variable = pm.max_var(polynomial);
            if result == NULL_VAR || variable > result {
                result = variable;
            }
        }
        result
    }

    fn get_max_var_of_literals(atoms: &AtomTable, literals: &[u32]) -> Var {
        let mut result = NULL_VAR;
        for &literal in literals {
            if let Some(atom) = atoms.get_atom(literal)
                && (result == NULL_VAR || atom.max_var() > result)
            {
                result = atom.max_var();
            }
        }
        result
    }

    // add_assumption: the negation of p kind 0, or of p != 0 when is_neg, into the lemma.
    fn add_assumption(
        &mut self,
        ctx: &mut ExplainContext<'_>,
        kind: IneqKind,
        polynomial: &Polynomial,
        is_neg: bool,
    ) {
        let bool_var = ctx.atoms.mk_ineq_atom(
            ctx.pm,
            ctx.cache,
            Some(&mut *ctx.hooks),
            kind,
            std::slice::from_ref(polynomial),
            &[false],
        );
        self.add_literal(ctx, 2 * bool_var + if is_neg { 0 } else { 1 });
    }

    // find_cell_roots for one polynomial: the root equal to the sample of its maximal variable.
    fn find_section_root(
        ctx: &mut ExplainContext<'_>,
        polynomial: &Polynomial,
        variable: Var,
    ) -> Result<Option<u32>, SmtError> {
        let value = ctx
            .sample
            .get(variable as usize)
            .cloned()
            .flatten()
            .ok_or_else(|| SmtError::Invariant(format!("x{variable} is unassigned")))?;
        let values: Vec<Option<Anum>> = ctx
            .sample
            .iter()
            .enumerate()
            .map(|(index, current)| {
                if index == variable as usize {
                    None
                } else {
                    current.clone()
                }
            })
            .collect();
        let roots = ctx.am.isolate_roots(ctx.pm, polynomial, &values)?;
        for (index, root) in roots.iter().enumerate() {
            let sign = ctx.am.compare(&value, root)?;
            if sign == 0 {
                return Ok(Some(index as u32 + 1));
            }
            if sign < 0 {
                return Ok(None);
            }
        }
        Ok(None)
    }

    // add_zero_assumption: p vanishes at the sample, so the sample lies on a root of its
    // square-free part, which becomes a section literal.
    fn add_zero_assumption(
        &mut self,
        ctx: &mut ExplainContext<'_>,
        polynomial: &Polynomial,
    ) -> Result<(), ExplainError> {
        let square_free = ctx.pm.square_free(polynomial)?;
        if ctx.pm.is_const(&square_free) {
            return Ok(());
        }
        let variable = ctx.pm.max_var(&square_free);
        if let Some(index) = Self::find_section_root(ctx, &square_free, variable)? {
            self.add_root_literal(ctx, RootKind::RootEq, variable, index, &square_free)?;
        }
        Ok(())
    }

    // elim_vanishing: p without its leading coefficients that vanish at the sample, each of which
    // becomes an assumption. Zero when all do.
    fn elim_vanishing(
        &mut self,
        ctx: &mut ExplainContext<'_>,
        polynomial: &Polynomial,
    ) -> Result<Polynomial, ExplainError> {
        let mut p = polynomial.clone();
        let mut variable = ctx.pm.max_var(&p);
        let mut degree = ctx.pm.degree(&p, variable);
        loop {
            if ctx.pm.is_const(&p) {
                return Ok(p);
            }
            if degree == 0 {
                variable = ctx.pm.max_var(&p);
                degree = ctx.pm.degree(&p, variable);
            }
            if ctx.pm.is_nonzero_const_coeff(&p, variable, degree) {
                return Ok(p);
            }
            // Z3 passes lc to insert_fresh_factors_in_todo by reference, so from here on lc is
            // without its own vanishing coefficients, which equals it given the assumptions that
            // removed them.
            let coeff = ctx.pm.coeff(&p, variable, degree);
            let lc = self.insert_fresh_factors_in_todo(ctx, &coeff)?;
            let reduct = ctx.pm.reduct(&p, variable, degree);
            if !ctx.pm.is_zero(&lc) && Self::get_sign(ctx, &lc)? != 0 {
                return Ok(p);
            }
            if degree == 0 {
                if self.is_add_all_coeffs {
                    self.add_zero_assumption(ctx, &lc)?;
                    return Ok(ctx.pm.zero());
                }
                self.is_add_all_coeffs = true;
                return Err(ExplainError::AddAllCoeffsRestart);
            }
            self.add_zero_assumption(ctx, &lc)?;
            degree -= 1;
            p = reduct;
        }
    }

    fn elim_vanishing_all(
        &mut self,
        ctx: &mut ExplainContext<'_>,
        polynomials: &[Polynomial],
    ) -> Result<Vec<Polynomial>, ExplainError> {
        let eliminated = polynomials
            .iter()
            .map(|polynomial| self.elim_vanishing(ctx, polynomial))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(eliminated
            .into_iter()
            .filter(|polynomial| !ctx.pm.is_const(polynomial))
            .collect())
    }

    // insert_fresh_factors_in_todo: the factors of p, without their vanishing coefficients.
    // Returns p without its vanishing coefficients, which Z3 writes back to its argument.
    fn insert_fresh_factors_in_todo(
        &mut self,
        ctx: &mut ExplainContext<'_>,
        polynomial: &Polynomial,
    ) -> Result<Polynomial, ExplainError> {
        if ctx.pm.is_const(polynomial) {
            return Ok(polynomial.clone());
        }
        let p = self.elim_vanishing(ctx, polynomial)?;
        if ctx.pm.is_const(&p) {
            return Ok(p);
        }
        for factor in ctx.cache.factor(ctx.pm, &p)? {
            let reduced = self.elim_vanishing(ctx, &factor)?;
            if !ctx.pm.is_const(&reduced) {
                self.todo.insert(ctx.pm, ctx.cache, &reduced)?;
            }
        }
        Ok(p)
    }

    // normalize: the literal without the vanishing coefficients of max and the factors of lower
    // stages, which become assumptions. True or false when nothing is left.
    fn normalize_literal(
        &mut self,
        ctx: &mut ExplainContext<'_>,
        literal: u32,
        max: Var,
    ) -> Result<u32, ExplainError> {
        if literal >> 1 == TRUE_BOOL_VAR {
            return Ok(literal);
        }
        let atom_ref = Self::get_atom(ctx, literal)?;
        let Atom::Ineq(atom) = &*atom_ref else {
            return Ok(literal);
        };
        let is_neg = literal & 1 == 1;
        let mut polynomials = Vec::new();
        let mut is_even = Vec::new();
        let mut atom_sign = 1;
        let mut is_normalized = false;
        for (index, factor) in atom.polynomials.iter().enumerate() {
            let p = if ctx.pm.max_var(factor) == max {
                self.elim_vanishing(ctx, factor)?
            } else {
                factor.clone()
            };
            if ctx.pm.is_const(&p) || ctx.pm.max_var(&p) < max {
                let sign = Self::get_sign(ctx, &p)?;
                if !ctx.pm.is_const(&p) {
                    self.lower_stage_polys.push(p.clone());
                    if sign == 0 {
                        self.add_assumption(ctx, IneqKind::Eq, &p, false);
                    } else if atom.is_even[index] {
                        self.add_assumption(ctx, IneqKind::Eq, &p, true);
                    } else {
                        self.add_assumption(ctx, get_kind_for_sign(sign), &p, false);
                    }
                }
                if sign == 0 {
                    return Ok(if (atom.kind == IneqKind::Eq) != is_neg {
                        TRUE_LITERAL
                    } else {
                        FALSE_LITERAL
                    });
                }
                if sign < 0 && !atom.is_even[index] {
                    atom_sign = -atom_sign;
                }
                is_normalized = true;
                continue;
            }
            if p.id() != factor.id() {
                is_normalized = true;
            }
            is_even.push(atom.is_even[index]);
            polynomials.push(p);
        }
        if polynomials.is_empty() {
            let is_true = match atom.kind {
                IneqKind::Eq => false,
                IneqKind::Lt => atom_sign < 0,
                IneqKind::Gt => atom_sign > 0,
            };
            return Ok(if is_true != is_neg {
                TRUE_LITERAL
            } else {
                FALSE_LITERAL
            });
        }
        if !is_normalized {
            return Ok(literal);
        }
        let kind = if atom_sign < 0 {
            flip_kind(atom.kind)
        } else {
            atom.kind
        };
        Ok(ctx.atoms.mk_ineq_literal(
            ctx.pm,
            ctx.cache,
            Some(&mut *ctx.hooks),
            kind,
            &polynomials,
            &is_even,
        ) ^ u32::from(is_neg))
    }

    fn normalize_core(
        &mut self,
        ctx: &mut ExplainContext<'_>,
        core: &mut ScopedLiterals,
        max: Var,
    ) -> Result<(), ExplainError> {
        let mut kept = 0;
        for index in 0..core.literals.len() {
            let literal = core.literals[index];
            let normalized = self.normalize_literal(ctx, literal, max)?;
            if normalized == TRUE_LITERAL {
                continue;
            }
            if normalized == FALSE_LITERAL {
                core.reset(ctx.atoms, Some(&mut *ctx.hooks));
                return Ok(());
            }
            core.set(ctx.atoms, Some(&mut *ctx.hooks), kept, normalized);
            kept += 1;
        }
        core.shrink(ctx.atoms, Some(&mut *ctx.hooks), kept);
        Ok(())
    }

    // simplify(l, info, max, new_lit): rewrites the factors of degree at least the equation's by
    // their pseudo-remainders, recording the condition on the equation's leading coefficient.
    fn simplify_literal(
        &mut self,
        ctx: &mut ExplainContext<'_>,
        literal: u32,
        info: &mut EqInfo,
        max: Var,
        new_literal: &mut ScopedLiteral,
    ) -> Result<(), ExplainError> {
        fn add_lc_condition(info: &mut EqInfo, kind: IneqKind, steps: u32, is_factor_even: bool) {
            if info.is_lc_const {
                return;
            }
            if steps.is_multiple_of(2) || is_factor_even || kind == IneqKind::Eq {
                add_lc_diseq(info);
            } else {
                add_lc_ineq(info);
            }
        }
        let atom_ref = Self::get_atom(ctx, literal)?;
        let atom = match &*atom_ref {
            Atom::Ineq(atom)
                if !(atom.polynomials.len() == 1 && atom.polynomials[0].id() == info.eq.id()) =>
            {
                atom
            }
            _ => {
                new_literal.set(ctx.atoms, Some(&mut *ctx.hooks), literal);
                return Ok(());
            }
        };
        let is_neg = literal & 1 == 1;
        let mut factors = Vec::new();
        let mut is_even = Vec::new();
        let mut atom_sign = 1;
        let mut is_modified = false;
        for (index, factor) in atom.polynomials.iter().enumerate() {
            let is_factor_even = atom.is_even[index];
            if ctx.pm.degree(factor, info.variable) < info.degree {
                factors.push(factor.clone());
                is_even.push(is_factor_even);
                continue;
            }
            is_modified = true;
            let division = ctx.pm.pseudo_remainder(factor, &info.eq, info.variable)?;
            if division.steps % 2 == 1 && !is_factor_even && info.lc_sign < 0 {
                atom_sign = -atom_sign;
            }
            let remainder = division.remainder;
            if !ctx.pm.is_const(&remainder) {
                factors.push(remainder);
                is_even.push(is_factor_even);
                add_lc_condition(info, atom.kind, division.steps, is_factor_even);
                continue;
            }
            let sign = Self::get_sign(ctx, &remainder)?;
            if sign == 0 {
                new_literal.set(
                    ctx.atoms,
                    Some(&mut *ctx.hooks),
                    if (atom.kind == IneqKind::Eq) != is_neg {
                        TRUE_LITERAL
                    } else {
                        FALSE_LITERAL
                    },
                );
                if !info.is_lc_const {
                    add_lc_diseq(info);
                }
                return Ok(());
            }
            add_lc_condition(info, atom.kind, division.steps, is_factor_even);
            if sign < 0 && !is_factor_even {
                atom_sign = -atom_sign;
            }
        }
        if !is_modified {
            new_literal.set(ctx.atoms, Some(&mut *ctx.hooks), literal);
            return Ok(());
        }
        let kind = if atom_sign < 0 {
            flip_kind(atom.kind)
        } else {
            atom.kind
        };
        let simplified = ctx.atoms.mk_ineq_literal(
            ctx.pm,
            ctx.cache,
            Some(&mut *ctx.hooks),
            kind,
            &factors,
            &is_even,
        ) ^ u32::from(is_neg);
        new_literal.set(ctx.atoms, Some(&mut *ctx.hooks), simplified);
        // Z3's null_var is the largest unsigned, so true and false never count as lower stage.
        let max_var = ctx.atoms.get_max_var(new_literal.literal);
        if max_var == NULL_VAR || max_var >= max {
            let normalized = self.normalize_literal(ctx, new_literal.literal, max)?;
            new_literal.set(ctx.atoms, Some(&mut *ctx.hooks), normalized);
            return Ok(());
        }
        let value = get_literal_value(
            ctx.evaluator,
            ctx.pm,
            ctx.am,
            ctx.atoms,
            ctx.hooks.bvalues(),
            ctx.sample,
            new_literal.literal,
        )?;
        if value == L_TRUE {
            new_literal.set(ctx.atoms, Some(&mut *ctx.hooks), literal);
            return Ok(());
        }
        self.add_literal(ctx, new_literal.literal);
        new_literal.set(ctx.atoms, Some(&mut *ctx.hooks), TRUE_LITERAL);
        Ok(())
    }

    // simplify(C, eq, max): the core rewritten by eq. Like Z3's scoped_literal, new_literal keeps a
    // reference until the next literal or the end, also when an elimination restarts.
    fn simplify_with_eq(
        &mut self,
        ctx: &mut ExplainContext<'_>,
        core: &mut ScopedLiterals,
        eq: &Polynomial,
        max: Var,
    ) -> Result<bool, ExplainError> {
        let variable = ctx.pm.max_var(eq);
        let degree = ctx.pm.degree(eq, variable);
        let lc = ctx.pm.coeff(eq, variable, degree);
        let mut info = EqInfo {
            eq: eq.clone(),
            variable,
            degree,
            lc_sign: Self::get_sign(ctx, &lc)?,
            is_lc_const: ctx.pm.is_const(&lc),
            lc,
            is_lc_added: false,
            is_lc_ineq_added: false,
        };
        let mut new_literal = ScopedLiteral::new();
        let outcome = (|| {
            let mut is_modified = false;
            let mut kept = 0;
            for index in 0..core.literals.len() {
                let literal = core.literals[index];
                new_literal.set(ctx.atoms, Some(&mut *ctx.hooks), TRUE_LITERAL);
                self.simplify_literal(ctx, literal, &mut info, max, &mut new_literal)?;
                if new_literal.literal == literal {
                    core.set(ctx.atoms, Some(&mut *ctx.hooks), kept, literal);
                    kept += 1;
                    continue;
                }
                is_modified = true;
                if new_literal.literal == TRUE_LITERAL {
                    continue;
                }
                if new_literal.literal == FALSE_LITERAL {
                    kept = 0;
                    break;
                }
                core.set(ctx.atoms, Some(&mut *ctx.hooks), kept, new_literal.literal);
                kept += 1;
            }
            core.shrink(ctx.atoms, Some(&mut *ctx.hooks), kept);
            if info.is_lc_added {
                if info.is_lc_ineq_added {
                    let kind = if info.lc_sign < 0 {
                        IneqKind::Lt
                    } else {
                        IneqKind::Gt
                    };
                    self.add_assumption(ctx, kind, &info.lc, false);
                } else {
                    self.add_assumption(ctx, IneqKind::Eq, &info.lc, true);
                }
            }
            Ok(is_modified)
        })();
        new_literal.set(ctx.atoms, Some(&mut *ctx.hooks), TRUE_LITERAL);
        outcome
    }

    // select_eq: the positive single-factor odd equation of least degree in max.
    fn select_eq(
        ctx: &ExplainContext<'_>,
        core: &ScopedLiterals,
        max: Var,
    ) -> Result<Option<Polynomial>, SmtError> {
        let mut result = None;
        let mut min_degree = u32::MAX;
        for &literal in &core.literals {
            if literal & 1 == 1 {
                continue;
            }
            let atom_ref = Self::get_atom(ctx, literal)?;
            let Atom::Ineq(atom) = &*atom_ref else {
                continue;
            };
            if atom.kind != IneqKind::Eq || atom.polynomials.len() > 1 || atom.is_even[0] {
                continue;
            }
            let degree = ctx.pm.degree(&atom.polynomials[0], max);
            if degree < min_degree {
                result = Some(atom.polynomials[0].clone());
                min_degree = degree;
                if min_degree == 1 {
                    break;
                }
            }
        }
        Ok(result)
    }

    // select_lower_stage_eq: an assigned equation of a lower variable with a constant leading
    // coefficient that can rewrite a literal of the core.
    fn select_lower_stage_eq(
        ctx: &ExplainContext<'_>,
        core: &ScopedLiterals,
        max: Var,
    ) -> Result<Option<AtomRef>, SmtError> {
        for &literal in &core.literals {
            let atom_ref = Self::get_atom(ctx, literal)?;
            let Atom::Ineq(atom) = &*atom_ref else {
                continue;
            };
            for factor in &atom.polynomials {
                let mut variables: Vec<Var> = Vec::new();
                for &monomial in &factor.terms().ms {
                    for &variable in ctx.pm.monomial_vars(monomial) {
                        if !variables.contains(&variable) {
                            variables.push(variable);
                        }
                    }
                }
                for variable in variables {
                    if variable >= max {
                        continue;
                    }
                    let Some(eq) = ctx.var2eq.get(variable as usize).cloned().flatten() else {
                        continue;
                    };
                    let eq_polynomial = &get_eq_atom(&eq)?.polynomials[0];
                    let eq_degree = ctx.pm.degree(eq_polynomial, variable);
                    if !ctx
                        .pm
                        .is_nonzero_const_coeff(eq_polynomial, variable, eq_degree)
                    {
                        continue;
                    }
                    if ctx.pm.degree(factor, variable) >= eq_degree {
                        return Ok(Some(eq));
                    }
                }
            }
        }
        Ok(None)
    }

    fn simplify_core(
        &mut self,
        ctx: &mut ExplainContext<'_>,
        core: &mut ScopedLiterals,
        max: Var,
    ) -> Result<(), ExplainError> {
        while core.size() > 0 {
            let Some(eq) = Self::select_eq(ctx, core, max)? else {
                break;
            };
            if !self.simplify_with_eq(ctx, core, &eq, max)? {
                break;
            }
        }
        while core.size() > 0 {
            let Some(eq) = Self::select_lower_stage_eq(ctx, core, max)? else {
                break;
            };
            let eq_atom = get_eq_atom(&eq)?;
            self.simplify_with_eq(ctx, core, &eq_atom.polynomials[0], max)?;
            self.add_literal(ctx, 2 * eq_atom.bool_var + 1);
        }
        Ok(())
    }

    // add_root_literal: the negation of y kind root[i](p), as an inequality when p is linear or
    // quadratic in y, else as a root atom.
    fn add_root_literal(
        &mut self,
        ctx: &mut ExplainContext<'_>,
        kind: RootKind,
        variable: Var,
        index: u32,
        polynomial: &Polynomial,
    ) -> Result<(), ExplainError> {
        if self.mk_linear_root(ctx, kind, variable, polynomial) {
            return Ok(());
        }
        if self.mk_quadratic_root(ctx, kind, variable, index, polynomial)? {
            return Ok(());
        }
        let bool_var = ctx.atoms.mk_root_atom(
            ctx.pm,
            ctx.cache,
            Some(&mut *ctx.hooks),
            kind,
            variable,
            index,
            polynomial,
        );
        self.add_literal(ctx, 2 * bool_var + 1);
        Ok(())
    }

    fn mk_linear_root(
        &mut self,
        ctx: &mut ExplainContext<'_>,
        kind: RootKind,
        variable: Var,
        polynomial: &Polynomial,
    ) -> bool {
        let coeff = ctx.pm.get_const_coeff(polynomial, variable, 1);
        if ctx.pm.degree(polynomial, variable) != 1 {
            return false;
        }
        let Some(coeff) = coeff else {
            return false;
        };
        self.add_linear_root(ctx, kind, polynomial, coeff.is_negative());
        true
    }

    fn add_linear_root(
        &mut self,
        ctx: &mut ExplainContext<'_>,
        kind: RootKind,
        polynomial: &Polynomial,
        is_negated: bool,
    ) {
        let (ineq_kind, is_neg) = get_root_to_ineq(kind);
        let p = if is_negated {
            ctx.pm.neg(polynomial)
        } else {
            polynomial.clone()
        };
        self.add_assumption(ctx, ineq_kind, &p, is_neg);
    }

    // mk_plinear_root: a root of p linear in y whose coefficient keeps its sign.
    fn mk_plinear_root(
        &mut self,
        ctx: &mut ExplainContext<'_>,
        kind: RootKind,
        variable: Var,
        polynomial: &Polynomial,
    ) -> Result<bool, ExplainError> {
        if ctx.pm.degree(polynomial, variable) != 1 {
            return Ok(false);
        }
        let coeff = ctx.pm.coeff(polynomial, variable, 1);
        let sign = Self::get_sign(ctx, &coeff)?;
        if sign == 0 {
            return Ok(false);
        }
        self.ensure_sign(ctx, &coeff)?;
        self.add_linear_root(ctx, kind, polynomial, sign < 0);
        Ok(true)
    }

    // mk_quadratic_root: by Thom's lemma, the signs of the discriminant, the leading coefficient,
    // the derivative and p characterize the sample's position among the roots of a quadratic.
    fn mk_quadratic_root(
        &mut self,
        ctx: &mut ExplainContext<'_>,
        kind: RootKind,
        variable: Var,
        index: u32,
        polynomial: &Polynomial,
    ) -> Result<bool, ExplainError> {
        if ctx.pm.degree(polynomial, variable) != 2 || (index != 1 && index != 2) {
            return Ok(false);
        }
        let a = ctx.pm.coeff(polynomial, variable, 2);
        let b = ctx.pm.coeff(polynomial, variable, 1);
        let c = ctx.pm.coeff(polynomial, variable, 0);
        let b_squared = ctx.pm.mul(&b, &b)?;
        let four_a = ctx.pm.mul_const(&Int::from(4_i64), &a);
        let four_a_c = ctx.pm.mul(&four_a, &c)?;
        let discriminant = ctx.pm.sub(&b_squared, &four_a_c);
        let y = ctx.pm.mk_var(variable, 1);
        let two_a = ctx.pm.mul_const(&Int::from(2_i64), &a);
        let two_a_y = ctx.pm.mul(&two_a, &y)?;
        let sum = ctx.pm.add(&two_a_y, &b);
        let derivative = ctx.pm.normalize(&sum);
        if self.ensure_sign_quad(ctx, &discriminant)? < 0 {
            return Ok(false);
        }
        if self.ensure_sign_quad(ctx, &a)? == 0 {
            let b_y = ctx.pm.mul(&b, &y)?;
            let linear = ctx.pm.add(&b_y, &c);
            return self.mk_plinear_root(ctx, kind, variable, &linear);
        }
        self.ensure_sign(ctx, &derivative)?;
        if Self::get_sign(ctx, &discriminant)? > 0 {
            self.ensure_sign(ctx, polynomial)?;
        }
        Ok(true)
    }

    fn ensure_sign(
        &mut self,
        ctx: &mut ExplainContext<'_>,
        polynomial: &Polynomial,
    ) -> Result<(), ExplainError> {
        if ctx.pm.is_const(polynomial) {
            return Ok(());
        }
        let sign = Self::get_sign(ctx, polynomial)?;
        self.add_assumption(ctx, get_kind_for_sign(sign), polynomial, false);
        self.insert_fresh_factors_in_todo(ctx, polynomial)?;
        Ok(())
    }

    fn ensure_sign_quad(
        &mut self,
        ctx: &mut ExplainContext<'_>,
        polynomial: &Polynomial,
    ) -> Result<i32, ExplainError> {
        let sign = Self::get_sign(ctx, polynomial)?;
        if !ctx.pm.is_const(polynomial) {
            self.add_assumption(ctx, get_kind_for_sign(sign), polynomial, false);
            self.insert_fresh_factors_in_todo(ctx, polynomial)?;
        }
        Ok(sign)
    }

    // levelwise_single_cell: the literals that bound the cell.
    fn add_cell_literals(
        &mut self,
        ctx: &mut ExplainContext<'_>,
        polynomials: &[Polynomial],
        max_var: Var,
        is_linear: bool,
    ) -> Result<(), ExplainError> {
        let cell = get_single_cell(
            ctx.pm,
            ctx.am,
            ctx.cache,
            polynomials,
            max_var,
            ctx.sample,
            is_linear,
        )?;
        let is_full = self.is_full_dimensional;
        for interval in &cell {
            if interval.is_section {
                let lower = interval.lower.as_ref().ok_or_else(|| {
                    SmtError::Invariant("a section without its polynomial".to_string())
                })?;
                let variable = ctx.pm.max_var(lower);
                self.add_root_literal(
                    ctx,
                    RootKind::RootEq,
                    variable,
                    interval.lower_index,
                    lower,
                )?;
                continue;
            }
            if let Some(lower) = &interval.lower {
                let variable = ctx.pm.max_var(lower);
                let kind = if is_full {
                    RootKind::RootGe
                } else {
                    RootKind::RootGt
                };
                self.add_root_literal(ctx, kind, variable, interval.lower_index, lower)?;
            }
            if let Some(upper) = &interval.upper {
                let variable = ctx.pm.max_var(upper);
                let kind = if is_full {
                    RootKind::RootLe
                } else {
                    RootKind::RootLt
                };
                self.add_root_literal(ctx, kind, variable, interval.upper_index, upper)?;
            }
        }
        Ok(())
    }

    // project: the factors of the polynomials, then the cell around the sample.
    fn project(
        &mut self,
        ctx: &mut ExplainContext<'_>,
        polynomials: &[Polynomial],
        max_var: Var,
    ) -> Result<(), ExplainError> {
        if polynomials.is_empty() {
            return Ok(());
        }
        self.todo.reset();
        for polynomial in polynomials {
            self.insert_fresh_factors_in_todo(ctx, polynomial)?;
        }
        let todo_polys = self.todo.polynomials.clone();
        self.add_cell_literals(ctx, &todo_polys, max_var, false)
    }

    fn explain_core(
        &mut self,
        ctx: &mut ExplainContext<'_>,
        literals: &[u32],
    ) -> Result<(), ExplainError> {
        if literals.is_empty() {
            return Ok(());
        }
        let mut polynomials = Self::collect_polys(ctx, literals)?;
        polynomials.extend(self.lower_stage_polys.iter().cloned());
        let max_var = Self::get_max_var_of_polys(ctx.pm, &polynomials);
        let eliminated = self.elim_vanishing_all(ctx, &polynomials)?;
        self.project(ctx, &eliminated, max_var)
    }

    // process2: with simplify_conflicts, the core normalized and rewritten by its equations first.
    // As in Z3, a restart leaves the core holding its literals until the next attempt: the core
    // is out of self while the steps borrow self, and back in also on a restart.
    fn process(
        &mut self,
        ctx: &mut ExplainContext<'_>,
        literals: &[u32],
    ) -> Result<(), ExplainError> {
        self.lower_stage_polys.clear();
        let mut core = std::mem::take(&mut self.core);
        let outcome = (|| {
            core.reset(ctx.atoms, Some(&mut *ctx.hooks));
            for &literal in literals {
                core.push(ctx.atoms, literal);
            }
            let max = Self::get_max_var_of_literals(ctx.atoms, literals);
            self.normalize_core(ctx, &mut core, max)?;
            self.simplify_core(ctx, &mut core, max)?;
            let core_literals = core.literals.clone();
            self.explain_core(ctx, &core_literals)?;
            core.reset(ctx.atoms, Some(&mut *ctx.hooks));
            Ok(())
        })();
        self.core = core;
        outcome
    }

    /// compute_conflict_explanation: the literals, appended to result, that with the negations of
    /// literals make a valid lemma.
    pub fn compute_conflict_explanation(
        &mut self,
        ctx: &mut ExplainContext<'_>,
        literals: &[u32],
        result: &mut ScopedLiterals,
    ) -> Result<(), SmtError> {
        if Self::get_max_var_of_literals(ctx.atoms, literals) == 0
            && matches!(ctx.sample.first(), None | Some(None))
        {
            result.reset(ctx.atoms, Some(&mut *ctx.hooks));
            return Ok(());
        }
        let saved_add_all_coeffs = self.is_add_all_coeffs;
        let base = result.size();
        let outcome = loop {
            std::mem::swap(&mut self.result, result);
            let attempt = self.process(ctx, literals);
            self.reset_result(result);
            match attempt {
                Ok(()) => break Ok(()),
                Err(ExplainError::AddAllCoeffsRestart) => {
                    result.shrink(ctx.atoms, Some(&mut *ctx.hooks), base)
                }
                Err(ExplainError::Smt(error)) => break Err(error),
            }
        };
        self.is_add_all_coeffs = saved_add_all_coeffs;
        outcome
    }

    /// compute_linear_explanation: the literals of a linear cell around a sample of every
    /// variable.
    pub fn compute_linear_explanation(
        &mut self,
        ctx: &mut ExplainContext<'_>,
        literals: &[u32],
        result: &mut ScopedLiterals,
    ) -> Result<(), SmtError> {
        std::mem::swap(&mut self.result, result);
        self.lower_stage_polys.clear();
        let outcome = (|| {
            let polynomials = Self::collect_polys(ctx, literals)?;
            if !polynomials.is_empty() {
                let max_var = Self::get_max_var_of_polys(ctx.pm, &polynomials) + 1;
                self.add_cell_literals(ctx, &polynomials, max_var, true)?;
            }
            Ok(())
        })();
        self.reset_result(result);
        // The TS lets the restart escape here, where only an elimination with every coefficient
        // vanishing could raise it; the Rust names it an invariant failure.
        outcome.map_err(|error| match error {
            ExplainError::Smt(error) => error,
            ExplainError::AddAllCoeffsRestart => SmtError::Invariant(
                "add_all_coeffs_restart outside compute_conflict_explanation".to_string(),
            ),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::super::algebraic::{AlgebraicManager, Anum};
    use super::super::atoms::{AtomTable, BoolVarHooks, ScopedLiterals};
    use super::super::evaluator::Evaluator;
    use super::super::polynomial::{PolynomialCache, PolynomialManager};
    use super::super::test_util::{
        parse_polynomial, parse_rational, read_fixture, show_anum, show_polynomial,
    };
    use super::super::types::{Atom, AtomRef, IneqKind, RootKind};
    use super::super::{Int, L_UNDEF, LBool, SmtError};
    use super::{Explain, ExplainContext};

    const INEQ_KINDS: [(IneqKind, &str); 3] = [
        (IneqKind::Eq, "EQ"),
        (IneqKind::Lt, "LT"),
        (IneqKind::Gt, "GT"),
    ];

    const ROOT_KINDS: [(RootKind, &str); 5] = [
        (RootKind::RootEq, "ROOT_EQ"),
        (RootKind::RootLt, "ROOT_LT"),
        (RootKind::RootGt, "ROOT_GT"),
        (RootKind::RootLe, "ROOT_LE"),
        (RootKind::RootGe, "ROOT_GE"),
    ];

    // The harness's table has no hooks, and its getValue reads no Boolean values: they stay
    // l_undef.
    #[derive(Default)]
    struct UndefHooks {
        bvalues: Vec<LBool>,
    }

    impl BoolVarHooks for UndefHooks {
        fn on_mk(&mut self, bool_var: u32) {
            let size = (bool_var as usize + 1).max(self.bvalues.len());
            self.bvalues.resize(size, L_UNDEF);
        }

        fn on_delete(&mut self, _bool_var: u32) {}

        fn bvalues(&self) -> &[LBool] {
            &self.bvalues
        }
    }

    fn show_atom(pm: &PolynomialManager, table: &AtomTable, bool_var: u32) -> String {
        match &**table.atoms[bool_var as usize].as_ref().expect("an atom") {
            Atom::Ineq(atom) => {
                let kind = INEQ_KINDS
                    .iter()
                    .find(|entry| entry.0 == atom.kind)
                    .expect("a kind");
                let body: String = atom
                    .polynomials
                    .iter()
                    .enumerate()
                    .map(|(index, polynomial)| {
                        let parity = if atom.is_even[index] { "e" } else { "o" };
                        format!(" {parity}{}", show_polynomial(pm, polynomial))
                    })
                    .collect();
                format!(" b{bool_var} {} {}{body}", kind.1, atom.max_var.get())
            }
            Atom::Root(atom) => {
                let kind = ROOT_KINDS
                    .iter()
                    .find(|entry| entry.0 == atom.kind)
                    .expect("a kind");
                format!(
                    " b{bool_var} {} {} i{} {}",
                    kind.1,
                    atom.max_var.get(),
                    atom.index,
                    show_polynomial(pm, &atom.polynomial)
                )
            }
        }
    }

    fn set_at<T: Clone>(vector: &mut Vec<Option<T>>, index: usize, value: T) {
        if vector.len() <= index {
            vector.resize(index + 1, None);
        }
        vector[index] = Some(value);
    }

    // The harness's explain programs: a sample with the top variable unassigned, or every
    // variable assigned for the linear variant, atoms made by the solver's atom table, the
    // equations Z3's solver keeps for some assigned variables, then the explanations of sets of
    // literals. Each explanation prints its literals with their atoms, numbered as Z3 numbers
    // them.
    fn run_explain_program(program: &str) -> Result<String, SmtError> {
        let mut am = AlgebraicManager::new();
        let mut pm = PolynomialManager::new();
        let mut cache = PolynomialCache::new();
        let mut hooks = UndefHooks::default();
        let mut table = AtomTable::new(Some(&mut hooks));
        let mut sample: Vec<Option<Anum>> = Vec::new();
        let mut var2eq: Vec<Option<AtomRef>> = Vec::new();
        let mut evaluator = Evaluator::new();
        let mut explain = Explain::new();
        let mut registers: Vec<Option<Anum>> = Vec::new();
        let mut atoms: Vec<u32> = Vec::new();
        let mut lines = Vec::new();
        for line in program.split('\n') {
            let words: Vec<&str> = line.split(' ').collect();
            let numbers: Vec<Option<i64>> =
                words[1..].iter().map(|word| word.parse().ok()).collect();
            let number = |index: usize| -> usize {
                usize::try_from(numbers[index].expect("a number")).expect("a natural number")
            };
            let output = match words[0] {
                "q" => {
                    let anum = Anum::new(parse_rational(words[2]));
                    set_at(&mut registers, number(0), anum.clone());
                    show_anum(&mut am, &anum)
                }
                "root" => {
                    let coeffs: Vec<Int> = words[3..]
                        .iter()
                        .map(|word| word.parse().expect("a coefficient"))
                        .collect();
                    let polynomial = pm.from_coeffs(&coeffs, 0);
                    let anum = am.isolate_roots(&mut pm, &polynomial, &[])?[number(1) - 1].clone();
                    set_at(&mut registers, number(0), anum.clone());
                    show_anum(&mut am, &anum)
                }
                "set" => {
                    let copy = am.copy(registers[number(1)].as_ref().expect("a register"));
                    set_at(&mut sample, number(0), copy);
                    String::new()
                }
                "ineq" => {
                    let count = number(1);
                    let polynomials: Vec<_> = words[3 + count..]
                        .join(" ")
                        .split(" ; ")
                        .map(|text| parse_polynomial(&mut pm, text))
                        .collect();
                    let is_even: Vec<bool> =
                        (2..2 + count).map(|index| number(index) == 1).collect();
                    let kind = INEQ_KINDS
                        .iter()
                        .find(|entry| entry.1 == words[1])
                        .expect("a kind");
                    atoms.push(table.mk_ineq_atom(
                        &mut pm,
                        &mut cache,
                        Some(&mut hooks),
                        kind.0,
                        &polynomials,
                        &is_even,
                    ));
                    // The harness holds a reference to each atom it makes, as a clause would.
                    let bool_var = atoms[atoms.len() - 1];
                    table.inc_ref(2 * bool_var);
                    show_atom(&pm, &table, bool_var)
                }
                "rootatom" => {
                    let polynomial = parse_polynomial(&mut pm, &words[4..].join(" "));
                    let kind = ROOT_KINDS
                        .iter()
                        .find(|entry| entry.1 == words[1])
                        .expect("a kind");
                    let variable = i32::try_from(number(1)).expect("a variable");
                    let index = u32::try_from(number(2)).expect("a root index");
                    atoms.push(table.mk_root_atom(
                        &mut pm,
                        &mut cache,
                        Some(&mut hooks),
                        kind.0,
                        variable,
                        index,
                        &polynomial,
                    ));
                    let bool_var = atoms[atoms.len() - 1];
                    table.inc_ref(2 * bool_var);
                    show_atom(&pm, &table, bool_var)
                }
                "eq" => {
                    let atom = table.atoms[atoms[number(1)] as usize]
                        .clone()
                        .expect("an atom");
                    set_at(&mut var2eq, number(0), atom);
                    String::new()
                }
                "explain" => {
                    let literals: Vec<u32> = (0..(numbers.len() - 1) / 2)
                        .map(|index| {
                            2 * atoms[number(1 + 2 * index)]
                                + u32::try_from(number(2 + 2 * index)).expect("a sign")
                        })
                        .collect();
                    let mut result = ScopedLiterals::new();
                    let mut ctx = ExplainContext {
                        pm: &mut pm,
                        am: &mut am,
                        cache: &mut cache,
                        atoms: &mut table,
                        sample: &mut sample,
                        evaluator: &mut evaluator,
                        hooks: &mut hooks,
                        var2eq: &var2eq,
                    };
                    if number(0) == 1 {
                        explain.compute_linear_explanation(&mut ctx, &literals, &mut result)?;
                    } else {
                        explain.compute_conflict_explanation(&mut ctx, &literals, &mut result)?;
                    }
                    let output: String = result
                        .literals
                        .iter()
                        .map(|&literal| {
                            format!(" {literal}{}", show_atom(&pm, &table, literal >> 1))
                        })
                        .collect();
                    result.reset(&mut table, Some(&mut hooks));
                    output
                }
                _ => String::new(),
            };
            lines.push(format!("{}{output}", words[0]));
        }
        Ok(lines.join("\n"))
    }

    // Random samples, atoms and cores, with lower stage equations, leading coefficients that
    // vanish at the sample, and factors whose every coefficient does, which restarts the
    // explanation with all coefficients. Each program explains one or two cores, so the second
    // reuses the Boolean variables the first freed.
    #[test]
    fn explains_the_fixture_cores() {
        let mut failures = Vec::new();
        for (program, expected) in read_fixture("explain.json") {
            match run_explain_program(&program) {
                Ok(actual) if actual == expected => {}
                actual => failures.push(format!(
                    "{program}\nexpected:\n{expected}\nactual:\n{actual:?}"
                )),
            }
        }
        assert!(failures.is_empty(), "{}", failures.join("\n\n"));
    }

    #[test]
    fn throws_a_named_error_for_a_linear_cell_around_an_irrational_section() {
        // x0 is the root sqrt(2) of the equation x0^2 - 2, so the cell at x0 is an irrational
        // section, where Z3 exits.
        let program = [
            "vars 2",
            "root 0 2 -2 0 1",
            "set 0 0",
            "q 1 10/2",
            "set 1 1",
            "ineq EQ 1 0 -2: 1:0^2",
            "explain 1 0 0",
        ]
        .join("\n");
        assert!(matches!(
            run_explain_program(&program),
            Err(SmtError::NlsatUnsupported(_))
        ));
    }
}
