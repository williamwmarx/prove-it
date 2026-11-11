// Ported from Z3 (src/math/lp/nra_solver.cpp, src/math/lp/nla_coi.cpp), MIT license, see
// z3-license.txt. nla's bridge to nlsat. The constraints in the cone of influence of the monomials
// to refine go to nlsat, with every monomial and term column replaced by its polynomial. check runs
// nlsat's search on them: a model becomes nla's, and a refutation a lemma over the constraints of
// its core. check_assignment instead hands nlsat the current values, and when they violate a
// constraint, nlsat's linear cell around them becomes a lemma.
// Deviations from Z3:
// - nlsat input it does not implement (NlsatUnsupported) answers unknown. That is a linear cell
//   around an irrational section, where Z3 exits the process (levelwise.cpp,
//   add_linear_approximations).
// - nlsat's check(rvalues) never answers satisfied, because its solver starts with the clause
//   [true], whose literal is unassigned outside search. So the satisfied branch of
//   check_assignment, which switches nla to nlsat's model, is left out.
// - A lemma literal of check_assignment is always linear, because the cell bounds are, so
//   add_mul_def, which defines a fresh monomial column, is left out. A nonlinear literal would
//   answer unknown.
// - nlsat's polynomial and algebraic number managers count their steps in the calls that the port
//   shares with Z3, but where the port computes the same result along other calls, such as
//   eval_sign_at's first evaluation, it can take other steps, so a long search stops at a
//   different point than Z3's. Like Z3's, it then throws, which ends the whole check as unknown.
// - Transcendental functions are not supported, so none are registered with nlsat.
//
// Like the other helpers of nla (see the top of nla_core.rs), the solver's state is a field of
// `NlaCore` and the functions that TS runs on the core take the view: `this.core.nra.check(…)`
// reads `NraSolver::check(nla, …)`. The ones that read only the monomials and the lar_solver take
// them as arguments, so a caller can hold the constraint they check.
use std::collections::{HashMap, HashSet};

use prove_num::{Int, Rational, get_lcm};

use crate::lp::constraints::{KIND_EQ, KIND_GE, KIND_GT, KIND_LE, KIND_LT, KIND_NE, LarConstraint};
use crate::lp::explanation::Explanation;
use crate::lp::lar_solver::LarSolver;
use crate::lp::lar_term::LarTerm;
use crate::lp::nla_core::{Nla, get_val};
use crate::lp::nla_emonics::Emonics;
use crate::lp::nla_types::{LemmaBuilder, mk_term_ineq};
use crate::nlsat::algebraic::{AlgebraicManager, Anum};
use crate::nlsat::polynomial::{Polynomial, Var};
use crate::nlsat::solver::NlsatSolver;
use crate::nlsat::types::{Atom, IneqKind};
use crate::util::error::SmtError;
use crate::util::lbool::LBool;
use crate::util::ordered_map::OrderedSet;

#[derive(Default)]
struct Occurrences {
    constraints: Vec<usize>,
    monics: Vec<usize>,
    terms: Vec<usize>,
}

struct Cone {
    vars: HashSet<usize>,
    constraints: OrderedSet<usize>,
    monics: HashSet<usize>,
}

// lar_base_constraint::coeffs: the term of a term column, else the column itself.
fn get_constraint_coeffs(
    lra: &LarSolver<'_>,
    constraint: &LarConstraint,
) -> Vec<(usize, Rational)> {
    match lra.columns[constraint.column].term {
        Some(term) => lra.terms[term]
            .iter()
            .map(|entry| (entry.0, entry.1.clone()))
            .collect(),
        None => vec![(constraint.column, Rational::one())],
    }
}

// coi::init: the constraints reachable from the monomials to refine through shared variables,
// monomials and terms, in the order the search reaches them.
fn get_cone_of_influence(nla: &Nla<'_, '_>) -> Result<Cone, SmtError> {
    let lra = &*nla.lra;
    let mut occurrences: Vec<Occurrences> = Vec::new();
    occurrences.resize_with(lra.get_column_count(), Occurrences::default);
    for (index, constraint) in lra.constraints.constraints.iter().enumerate() {
        if !constraint.is_active {
            continue;
        }
        for entry in get_constraint_coeffs(lra, constraint) {
            occurrences[entry.0].constraints.push(index);
        }
    }
    for monic in &nla.emons.monics {
        for lp_var in &monic.vars {
            occurrences[*lp_var].monics.push(monic.variable);
        }
    }
    for term in &lra.terms {
        for entry in term.iter() {
            occurrences[entry.0].terms.push(term.column);
        }
    }
    let mut todo = nla.to_refine.elems.clone();
    let mut cone = Cone {
        vars: HashSet::new(),
        constraints: OrderedSet::new(),
        monics: HashSet::new(),
    };
    let mut index = 0;
    while index < todo.len() {
        let lp_var = todo[index];
        index += 1;
        if !cone.vars.insert(lp_var) {
            continue;
        }
        let occurring = &occurrences[lp_var];
        for constraint_index in &occurring.constraints {
            cone.constraints.insert(*constraint_index);
            let constraint = &lra.constraints.constraints[*constraint_index];
            for entry in get_constraint_coeffs(lra, constraint) {
                todo.push(entry.0);
            }
        }
        todo.extend_from_slice(&occurring.monics);
        for term_column in &occurring.terms {
            for entry in lra.get_term(*term_column)?.iter() {
                todo.push(entry.0);
            }
            todo.push(*term_column);
        }
        if lra.has_term(lp_var) {
            for entry in lra.get_term(lp_var)?.iter() {
                todo.push(entry.0);
            }
        }
        if nla.emons.is_monic_var(lp_var) {
            cone.monics.insert(lp_var);
            todo.extend_from_slice(&nla.emons.get(lp_var).vars);
        }
    }
    Ok(cone)
}

// has_large_dyadic_denominator: a denominator 2^k with k >= 24.
fn has_large_dyadic_denominator(value: &Rational) -> bool {
    let den = value.den();
    *den >= (Int::one() << 24) && (den & &(den - &Int::one())) == 0
}

// is_dyadic_artifact: a constraint of an nla lemma's atom with a constant whose denominator is a
// large power of two, the value of a column at an LP vertex. nlsat leaves it out, since clearing
// such denominators blows up its resultants.
fn is_dyadic_artifact(lra: &LarSolver<'_>, constraint: &LarConstraint) -> bool {
    constraint.is_auxiliary
        && (has_large_dyadic_denominator(&constraint.rhs.x)
            || get_constraint_coeffs(lra, constraint)
                .iter()
                .any(|entry| has_large_dyadic_denominator(&entry.1)))
}

// mk_definition's result: each column's polynomial, None for an excluded column, and the integer
// denominator it is scaled by (0 for an excluded column).
struct Definitions {
    definitions: Vec<Option<Polynomial>>,
    denominators: Vec<Int>,
}

// The lemma clause of check_assignment, with the constraint each literal came from.
struct AssignmentClause {
    clause: Vec<u32>,
    literal_constraints: HashMap<u32, usize>,
}

pub struct NraSolver {
    // m_nlsat and m_values: the solver of the last check, and the values of its model.
    solver: NlsatSolver,
    values: Vec<Anum>,
    // m_lp2nl: the nlsat variable of each column the solver has.
    lp2nl: HashMap<usize, Var>,
}

impl Default for NraSolver {
    fn default() -> NraSolver {
        NraSolver {
            solver: NlsatSolver::new(None, None),
            values: Vec::new(),
            lp2nl: HashMap::new(),
        }
    }
}

impl NraSolver {
    pub fn am(&mut self) -> &mut AlgebraicManager {
        &mut self.solver.am
    }

    // The steps of the last check.
    pub fn steps(&self) -> u64 {
        self.solver.steps()
    }

    // mk_definition: each included column as a polynomial in the included columns that are neither
    // monomials nor terms, scaled by an integer denominator to keep the coefficients integral.
    // Excluded columns have no definition.
    fn mk_definitions(
        &mut self,
        emons: &Emonics,
        lra: &LarSolver<'_>,
        is_included: impl Fn(usize) -> bool,
    ) -> Result<Definitions, SmtError> {
        let solver = &mut self.solver;
        let mut definitions: Vec<Option<Polynomial>> = Vec::new();
        let mut denominators: Vec<Int> = Vec::new();
        for lp_var in 0..lra.columns.len() {
            if !is_included(lp_var) {
                definitions.push(None);
                denominators.push(Int::zero());
                continue;
            }
            let variable = solver.mk_var(lra.is_int(lp_var));
            self.lp2nl.insert(lp_var, variable);
            if emons.is_monic_var(lp_var) {
                let mut definition: Option<Polynomial> = None;
                let mut denominator = Int::one();
                for factor in &emons.get(lp_var).vars {
                    denominator = &denominators[*factor] * &denominator;
                    let factor_definition = definitions[*factor]
                        .clone()
                        .expect("a monomial's factor is included with it");
                    definition = Some(match definition {
                        None => factor_definition,
                        Some(definition) => solver.pm.mul(&definition, &factor_definition)?,
                    });
                }
                definitions.push(Some(
                    definition.unwrap_or_else(|| solver.pm.mk_var(variable, 1)),
                ));
                denominators.push(denominator);
                continue;
            }
            if lra.has_term(lp_var) {
                let term: Vec<(usize, Rational)> = lra
                    .get_term(lp_var)?
                    .iter()
                    .map(|entry| (entry.0, entry.1.clone()))
                    .collect();
                let denominator = term.iter().fold(Int::one(), |result, entry| {
                    get_lcm(
                        entry
                            .1
                            .div(&Rational::from_int(denominators[entry.0].clone()))
                            .den(),
                        &result,
                    )
                });
                let mut definition: Option<Polynomial> = None;
                for entry in &term {
                    let coeff = entry.1.mul(&Rational::of(
                        denominator.clone(),
                        denominators[entry.0].clone(),
                    ));
                    let constant = solver.pm.mk_const(coeff.num());
                    let scaled = solver.pm.mul(
                        &constant,
                        definitions[entry.0]
                            .as_ref()
                            .expect("a term's column is included with it"),
                    )?;
                    definition = Some(match definition {
                        None => scaled,
                        Some(definition) => solver.pm.add(&definition, &scaled),
                    });
                }
                definitions.push(Some(definition.unwrap_or_else(|| solver.pm.zero())));
                denominators.push(denominator);
                continue;
            }
            definitions.push(Some(solver.pm.mk_var(variable, 1)));
            denominators.push(Int::one());
        }
        Ok(Definitions {
            definitions,
            denominators,
        })
    }

    // add_constraint: the constraint sum(coeff * v) kind rhs as den * (sum(coeff / den[v] * def[v]) -
    // rhs) kind 0, where den clears every denominator, in a unit clause that assumes the constraint.
    fn add_constraint(
        &mut self,
        lra: &LarSolver<'_>,
        constraint_index: usize,
        definitions: &Definitions,
    ) -> Result<u32, SmtError> {
        let solver = &mut self.solver;
        let constraint = &lra.constraints.constraints[constraint_index];
        let rhs = &constraint.rhs.x;
        let coeffs = get_constraint_coeffs(lra, constraint);
        let denominator = coeffs.iter().fold(rhs.den().clone(), |result, entry| {
            get_lcm(
                &result,
                entry
                    .1
                    .div(&Rational::from_int(
                        definitions.denominators[entry.0].clone(),
                    ))
                    .den(),
            )
        });
        let mut polynomial = solver
            .pm
            .mk_const(&(-(rhs.num() * &denominator) / rhs.den()));
        for entry in &coeffs {
            let coeff = entry.1.mul(&Rational::of(
                denominator.clone(),
                definitions.denominators[entry.0].clone(),
            ));
            let constant = solver.pm.mk_const(coeff.num());
            let product = solver.pm.mul(
                definitions.definitions[entry.0]
                    .as_ref()
                    .expect("a constraint's column is included with it"),
                &constant,
            )?;
            polynomial = solver.pm.add(&polynomial, &product);
        }
        let kind = constraint.kind;
        let literal = if kind == KIND_LE {
            solver.mk_ineq_literal(IneqKind::Gt, &[polynomial], &[false]) ^ 1
        } else if kind == KIND_GE {
            solver.mk_ineq_literal(IneqKind::Lt, &[polynomial], &[false]) ^ 1
        } else {
            let ineq_kind = if kind == KIND_LT {
                IneqKind::Lt
            } else if kind == KIND_GT {
                IneqKind::Gt
            } else {
                IneqKind::Eq
            };
            solver.mk_ineq_literal(ineq_kind, &[polynomial], &[false])
        };
        solver.mk_external_clause(&[literal], Some(constraint_index as u32));
        Ok(literal)
    }

    // check: nlsat's search on the constraints in the cone of influence, with every included column
    // replaced by its polynomial, giving up after max_conflicts conflicts or budget steps (None for
    // TS's Infinity). A model becomes nla's, when it satisfies every constraint and monomial, and a
    // refutation becomes the lemma that the constraints of its core are inconsistent.
    pub fn check(
        nla: &mut Nla<'_, '_>,
        max_conflicts: Option<u64>,
        budget: Option<u64>,
    ) -> Result<LBool, SmtError> {
        let result = NraSolver::check_in_scope(nla, max_conflicts, budget)?;
        // nla's check runs m_nra.check() inside scoped_limits, which pushes m_nra_lim as a child
        // of its limit, and scoped_rlimit, which sets the budget (z3-5.3.3,
        // src/math/lp/nla_core.cpp:1098-1103 and 1139-1145, src/util/rlimit.h:94-129). Both end
        // with the check, so the model's arithmetic later counts against neither.
        nla.core.nra.solver.limit.detach();
        Ok(result)
    }

    fn check_in_scope(
        nla: &mut Nla<'_, '_>,
        max_conflicts: Option<u64>,
        budget: Option<u64>,
    ) -> Result<LBool, SmtError> {
        let cone = {
            let nra = &mut nla.core.nra;
            nra.solver = NlsatSolver::new(Some(nla.limit), budget);
            nra.solver.max_conflicts = max_conflicts;
            nra.values.clear();
            nra.lp2nl.clear();
            get_cone_of_influence(nla)?
        };
        let core = &mut *nla.core;
        let lra = &*nla.lra;
        let definitions = core
            .nra
            .mk_definitions(&core.emons, lra, |lp_var| cone.vars.contains(&lp_var))?;
        let mut skipped = HashSet::new();
        for constraint_index in cone.constraints.iter() {
            if is_dyadic_artifact(lra, &lra.constraints.constraints[*constraint_index]) {
                skipped.insert(*constraint_index);
                continue;
            }
            core.nra
                .add_constraint(lra, *constraint_index, &definitions)?;
        }
        let result = match core.nra.solver.check() {
            Err(SmtError::NlsatUnsupported(_)) => LBool::Undef,
            result => result?,
        };
        if result == LBool::True {
            nla.core.nra.solver.restore_order();
            nla.set_use_nra_model(true);
            nla.lra.init_model();
            let core = &mut *nla.core;
            let lra = &*nla.lra;
            // A violated constraint or monomial that nlsat saw would be a bug.
            for (constraint_index, constraint) in lra.constraints.constraints.iter().enumerate() {
                if !constraint.is_active
                    || core
                        .nra
                        .is_constraint_satisfied(&core.emons, lra, constraint)?
                {
                    continue;
                }
                if cone.constraints.contains(&constraint_index)
                    && !skipped.contains(&constraint_index)
                {
                    return Err(SmtError::Invariant(format!(
                        "nlsat's model violates constraint {constraint_index}"
                    )));
                }
                return Ok(LBool::Undef);
            }
            for monic in &core.emons.monics {
                if core
                    .nra
                    .is_monic_satisfied(&core.emons, lra, monic.variable, &monic.vars)?
                {
                    continue;
                }
                if cone.monics.contains(&monic.variable) {
                    return Err(SmtError::Invariant(format!(
                        "nlsat's model violates monomial {}",
                        monic.variable
                    )));
                }
                return Ok(LBool::Undef);
            }
        }
        if result == LBool::False {
            let mut explanation = Explanation::new();
            for constraint_index in nla.nra.solver.get_core() {
                explanation.push(constraint_index as usize);
            }
            LemmaBuilder::new(nla).add_explanation(nla, &explanation);
            nla.set_use_nra_model(true);
        }
        Ok(result)
    }

    // value: the model's value of a column. A monomial or term gets the value of its definition, a
    // column outside the cone of influence its value in lar_solver.
    pub fn value(nla: &mut Nla<'_, '_>, lp_var: usize) -> Result<Anum, SmtError> {
        let core = &mut *nla.core;
        core.nra.get_value(&core.emons, nla.lra, lp_var)
    }

    fn get_value(
        &mut self,
        emons: &Emonics,
        lra: &LarSolver<'_>,
        lp_var: usize,
    ) -> Result<Anum, SmtError> {
        for column in self.values.len()..=lp_var {
            let am = &mut self.solver.am;
            if emons.is_monic_var(column) {
                let mut product = Anum::new(Rational::one());
                for factor in &emons.get(column).vars {
                    product = am.mul(&product, &self.values[*factor])?;
                }
                self.values.push(product);
                continue;
            }
            if lra.has_term(column) {
                let mut sum = Anum::new(Rational::zero());
                for entry in lra.get_term(column)?.iter() {
                    let product = am.mul(&Anum::new(entry.1.clone()), &self.values[entry.0])?;
                    sum = am.add(&sum, &product)?;
                }
                self.values.push(sum);
                continue;
            }
            let value = match self.lp2nl.get(&column) {
                None => Anum::new(get_val(lra, column).clone()),
                Some(variable) => self.solver.get_value(*variable),
            };
            self.values.push(value);
        }
        Ok(self.values[lp_var].clone())
    }

    // check_monic
    fn is_monic_satisfied(
        &mut self,
        emons: &Emonics,
        lra: &LarSolver<'_>,
        lp_var: usize,
        vars: &[usize],
    ) -> Result<bool, SmtError> {
        let mut product = Anum::new(Rational::one());
        for factor in vars {
            let value = self.get_value(emons, lra, *factor)?;
            product = self.solver.am.mul(&product, &value)?;
        }
        let value = self.get_value(emons, lra, lp_var)?;
        Ok(self.solver.am.compare(&value, &product)? == 0)
    }

    // check_constraint: the value of the left side against the right side, without δ.
    fn is_constraint_satisfied(
        &mut self,
        emons: &Emonics,
        lra: &LarSolver<'_>,
        constraint: &LarConstraint,
    ) -> Result<bool, SmtError> {
        let coeffs = get_constraint_coeffs(lra, constraint);
        let mut sum = Anum::new(constraint.rhs.x.neg());
        for entry in coeffs {
            let value = self.get_value(emons, lra, entry.0)?;
            let product = self.solver.am.mul(&Anum::new(entry.1), &value)?;
            sum = self.solver.am.add(&sum, &product)?;
        }
        let sign = self.solver.am.compare(&sum, &Anum::new(Rational::zero()))?;
        let kind = constraint.kind;
        Ok(if kind == KIND_LE {
            sign <= 0
        } else if kind == KIND_GE {
            sign >= 0
        } else if kind == KIND_LT {
            sign < 0
        } else if kind == KIND_GT {
            sign > 0
        } else {
            sign == 0
        })
    }

    // setup_assignment_solver and nlsat's check(rvalues, clause): the lemma clause, with the
    // constraint each literal came from, or None when nlsat finds no violated constraint.
    fn get_clause(nla: &mut Nla<'_, '_>) -> Result<Option<AssignmentClause>, SmtError> {
        let cone = {
            let nra = &mut nla.core.nra;
            nra.solver = NlsatSolver::new(Some(nla.limit), None);
            nra.lp2nl.clear();
            get_cone_of_influence(nla)?
        };
        let core = &mut *nla.core;
        let lra = &*nla.lra;
        let definitions = core.nra.mk_definitions(&core.emons, lra, |_| true)?;
        let values: Vec<Anum> = (0..lra.columns.len())
            .map(|lp_var| Anum::new(get_val(lra, lp_var).clone()))
            .collect();
        core.nra.values = values.clone();
        let mut literal_constraints = HashMap::new();
        for constraint_index in cone.constraints.iter() {
            let literal = core
                .nra
                .add_constraint(lra, *constraint_index, &definitions)?;
            literal_constraints.insert(literal, *constraint_index);
        }
        let assignment: Vec<Option<Anum>> = values.into_iter().map(Some).collect();
        let result = core.nra.solver.check_assignment(&assignment)?;
        if result.0 != LBool::False {
            return Ok(None);
        }
        Ok(Some(AssignmentClause {
            clause: result.1,
            literal_constraints,
        }))
    }

    // check_assignment, which nla runs inside scoped_limits (z3-5.3.3,
    // src/math/lp/nla_core.cpp:1052-1054, src/util/rlimit.h:122-129).
    pub fn check_assignment(nla: &mut Nla<'_, '_>) -> Result<LBool, SmtError> {
        let result = NraSolver::check_assignment_in_scope(nla)?;
        nla.core.nra.solver.limit.detach();
        Ok(result)
    }

    fn check_assignment_in_scope(nla: &mut Nla<'_, '_>) -> Result<LBool, SmtError> {
        let clause = match NraSolver::get_clause(nla) {
            Err(SmtError::NlsatUnsupported(_)) => None,
            clause => clause?,
        };
        let Some(clause) = clause else {
            return Ok(LBool::Undef);
        };
        NraSolver::add_lemma(nla, &clause.clause, &clause.literal_constraints)
    }

    // add_lemma: a literal whose negation is a constraint's literal becomes that constraint in the
    // explanation, and any other literal an inequality over the columns. Unknown, without the lemma,
    // when such an inequality already holds.
    fn add_lemma(
        nla: &mut Nla<'_, '_>,
        clause: &[u32],
        literal_constraints: &HashMap<u32, usize>,
    ) -> Result<LBool, SmtError> {
        let lemma = LemmaBuilder::new(nla);
        for literal in clause {
            if let Some(constraint_index) = literal_constraints.get(&(literal ^ 1)) {
                let mut explanation = Explanation::new();
                explanation.push(*constraint_index);
                lemma.add_explanation(nla, &explanation);
                continue;
            }
            let Some(atom) = nla.nra.solver.get_atom(*literal) else {
                return Err(SmtError::Invariant(format!(
                    "nlsat literal {literal} has no atom"
                )));
            };
            // A root atom or a product of factors is unknown, and so is a nonlinear polynomial.
            let Atom::Ineq(atom) = &*atom else {
                nla.lemmas.pop();
                return Ok(LBool::Undef);
            };
            if atom.polynomials.len() != 1
                || nla.nra.solver.pm.total_degree(&atom.polynomials[0]) > 1
            {
                nla.lemmas.pop();
                return Ok(LBool::Undef);
            }
            // process_polynomial_check_assignment, for a linear polynomial.
            let polynomial = &atom.polynomials[0];
            let mut term = LarTerm::new();
            let mut bound = Rational::zero();
            for index in 0..polynomial.size() {
                let monomial = polynomial.monomial_at(index);
                let coeff = Rational::from_int(polynomial.coeff_at(index));
                match nla.nra.solver.pm.monomial_vars(monomial).first() {
                    None => bound = bound.sub(&coeff),
                    Some(variable) => term.add_monomial(&coeff, *variable as usize),
                }
            }
            let is_negated = literal & 1 == 1;
            let kind = match (atom.kind, is_negated) {
                (IneqKind::Eq, true) => KIND_NE,
                (IneqKind::Eq, false) => KIND_EQ,
                (IneqKind::Lt, true) => KIND_GE,
                (IneqKind::Lt, false) => KIND_LT,
                (IneqKind::Gt, true) => KIND_LE,
                (IneqKind::Gt, false) => KIND_GT,
            };
            let ineq = mk_term_ineq(term, kind, bound);
            if nla.ineq_holds(&ineq) {
                nla.lemmas.pop();
                return Ok(LBool::Undef);
            }
            lemma.add_ineq(nla, ineq);
        }
        nla.is_check_feasible = true;
        Ok(LBool::False)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lp::constraints::ConstraintKind;
    use crate::lp::nla_core::tests::{NlaFixture, show_lemmas};
    use crate::nlsat::algebraic::AnumValue;

    // Activates the bounds once all are made, as the TS tests do, then finds a feasible solution and
    // the monomials to refine.
    fn activate_bounds(
        fixture: &mut NlaFixture<'_>,
        bounds: &[(usize, ConstraintKind, i64)],
    ) -> Vec<usize> {
        let constraints: Vec<usize> = bounds
            .iter()
            .map(|bound| {
                fixture
                    .lra
                    .mk_var_bound(bound.0, bound.1, &Rational::from(bound.2))
            })
            .collect();
        for constraint in &constraints {
            fixture.lra.activate(*constraint);
        }
        fixture.lra.find_feasible_solution();
        fixture.with_nla(|nla| nla.init_to_refine());
        constraints
    }

    // The cases of smt-nlsat.test.ts's nra groups, with the same expectations. The exact lemmas and
    // step counts are what the TS printed on the same setups.

    // nra check_assignment: the monic m = x*y with x and y fixed by their bounds, and one more
    // bound on m.
    fn get_core(
        is_square: bool,
        kind: ConstraintKind,
        bound: i64,
    ) -> (NlaFixture<'static>, Vec<usize>) {
        let mut fixture = NlaFixture::new();
        let x = fixture.lra.add_var(0, false);
        let y = fixture.lra.add_var(1, false);
        let m = fixture.lra.add_var(2, false);
        let factors = if is_square { [x, x] } else { [x, y] };
        fixture.with_nla(|nla| nla.add_monic(m, &factors));
        let constraints = activate_bounds(
            &mut fixture,
            &[
                (x, KIND_GE, 2),
                (x, KIND_LE, 2),
                (y, KIND_GE, 1),
                (y, KIND_LE, 1),
                (m, kind, bound),
            ],
        );
        (fixture, constraints)
    }

    #[test]
    fn refutes_x_y_le_1_at_x_2_and_y_1_with_a_lemma() {
        let (mut fixture, constraints) = get_core(false, KIND_LE, 1);
        assert_eq!(
            fixture.with_nla(NraSolver::check_assignment),
            Ok(LBool::False)
        );
        assert_eq!(fixture.core.lemmas.len(), 1);
        assert_eq!(show_lemmas(&fixture.core), ["[] {0,2,4}"]);
        assert!(
            fixture.core.lemmas[0]
                .expl
                .iter()
                .any(|index| index == constraints[4])
        );
        assert!(fixture.core.is_check_feasible);
    }

    #[test]
    fn refutes_x_x_le_1_at_x_2_with_a_lemma_factoring_x2_minus_1() {
        let (mut fixture, constraints) = get_core(true, KIND_LE, 1);
        assert_eq!(
            fixture.with_nla(NraSolver::check_assignment),
            Ok(LBool::False)
        );
        assert_eq!(fixture.core.lemmas.len(), 1);
        assert_eq!(show_lemmas(&fixture.core), ["[] {0,4}"]);
        assert!(
            fixture.core.lemmas[0]
                .expl
                .iter()
                .any(|index| index == constraints[4])
        );
    }

    #[test]
    fn refutes_x_x_eq_2_at_x_2_with_a_lemma_bounding_the_irrational_root_linearly() {
        let (mut fixture, constraints) = get_core(true, KIND_EQ, 2);
        assert_eq!(
            fixture.with_nla(NraSolver::check_assignment),
            Ok(LBool::False)
        );
        assert_eq!(fixture.core.lemmas.len(), 1);
        assert_eq!(show_lemmas(&fixture.core), ["[] {0,4}"]);
        assert!(
            fixture.core.lemmas[0]
                .expl
                .iter()
                .any(|index| index == constraints[4])
        );
    }

    // nra check: the monic m = x*x with the bounds x >= 1 and m kind bound.
    fn get_square(
        kind: ConstraintKind,
        bound: i64,
    ) -> (NlaFixture<'static>, usize, usize, Vec<usize>) {
        let mut fixture = NlaFixture::new();
        let x = fixture.lra.add_var(0, false);
        let m = fixture.lra.add_var(1, false);
        fixture.with_nla(|nla| nla.add_monic(m, &[x, x]));
        let constraints = activate_bounds(&mut fixture, &[(x, KIND_GE, 1), (m, kind, bound)]);
        (fixture, x, m, constraints)
    }

    #[test]
    fn refutes_x_x_lt_1_with_a_lemma_over_the_constraints_of_nlsats_core() {
        let (mut fixture, _, _, constraints) = get_square(KIND_LT, 1);
        assert_eq!(
            fixture.with_nla(|nla| NraSolver::check(nla, None, None)),
            Ok(LBool::False)
        );
        assert_eq!(fixture.core.lemmas.len(), 1);
        assert_eq!(show_lemmas(&fixture.core), ["[] {0,1}"]);
        assert_eq!(fixture.core.nra.steps(), 32);
        assert!(fixture.core.lemmas[0].ineqs.is_empty());
        // TS sorts the indices as strings.
        let mut expl: Vec<usize> = fixture.core.lemmas[0].expl.iter().collect();
        expl.sort_by_key(usize::to_string);
        assert_eq!(expl, constraints);
        assert!(fixture.core.is_using_nra_model);
    }

    #[test]
    fn finds_the_model_x_sqrt_2_of_x_x_eq_2_and_makes_it_nlas() {
        let (mut fixture, x, m, _) = get_square(KIND_EQ, 2);
        fixture.with_nla(|nla| {
            assert_eq!(NraSolver::check(nla, None, None), Ok(LBool::True));
            assert!(nla.is_using_nra_model);
            assert_eq!(nla.nra.steps(), 121);
            let value = NraSolver::value(nla, x).unwrap();
            let am = nla.nra.am();
            assert_eq!(am.is_rational(&value), Ok(false));
            let square = am.mul(&value, &value).unwrap();
            assert_eq!(am.compare(&square, &Anum::new(Rational::from(2))), Ok(0));
            let value = NraSolver::value(nla, m).unwrap();
            assert!(
                matches!(&*value.value(), AnumValue::Rational(value) if *value == Rational::from(2))
            );
        });
    }

    #[test]
    fn throws_a_named_error_once_the_search_takes_more_steps_than_its_budget() {
        let (mut fixture, _, _, _) = get_square(KIND_EQ, 2);
        assert_eq!(
            fixture.with_nla(|nla| NraSolver::check(nla, None, Some(1))),
            Err(SmtError::Canceled)
        );
    }
}
