//! Ported from Z3 (src/smt/theory_lra.cpp, src/math/lp/lp_api.h), MIT license, see
//! z3-license.txt, through `theory-lra-bounds.ts`. The atoms of theory_lra: each is a bound on a
//! column, with axioms between the bounds of the same column.

use std::collections::HashSet;

use prove_num::Rational;

use crate::core::ast::{Expr, OP_GE, OP_IS_INT, OP_LE};
use crate::core::context::{Context, TrailClosure};
use crate::core::literal::{BoolVar, Literal, mk_literal, negate};
use crate::core::theory_lra_state::{ApiBound, AssertedAtom, TheoryClosure, set_at};
use crate::lp::constraints::{ConstraintKind, KIND_GE, KIND_GT, KIND_LE, KIND_LT};
use crate::util::error::SmtError;

pub(crate) fn get_atom_literal(bound: &ApiBound) -> Literal {
    mk_literal(bound.bool_var, false)
}

/// bound2constraint_kind: the kind of the bound when its atom is true or false.
pub(crate) fn get_bound_kind(bound: &ApiBound, is_true: bool) -> ConstraintKind {
    if bound.is_lower {
        return if is_true {
            KIND_GE
        } else if bound.is_int {
            KIND_LE
        } else {
            KIND_LT
        };
    }
    if is_true {
        KIND_LE
    } else if bound.is_int {
        KIND_GE
    } else {
        KIND_GT
    }
}

/// next_inf and next_sup's result: the position, and whether a bound of the side was met.
struct Neighbor {
    result: usize,
    is_found: bool,
}

impl Context {
    /// Whether the theory took the atom.
    pub fn theory_internalize_atom(&mut self, expr: Expr) -> Result<bool, SmtError> {
        if self.theory.is_none() {
            return Err(SmtError::Invariant("the theory is not set up".into()));
        }
        let op = self.m.get_op(expr);
        let bool_var = self.mk_bool_var(expr);
        set_at(
            &mut self.lra_mut().bool_var_to_bound,
            bool_var as usize,
            None,
            None,
        );
        self.set_var_theory(bool_var);
        if op == OP_IS_INT {
            self.lra_mk_enode(expr)?;
            if !self.relevancy.is_enabled {
                self.lra_mk_is_int_axiom(expr)?;
            }
            return Ok(true);
        }
        if op != OP_LE && op != OP_GE {
            self.lra_found_unsupported(expr);
            return Ok(true);
        }
        let is_right_numeral = self.m.is_numeral(self.m.get_arg(expr, 1));
        if !is_right_numeral && !self.m.is_numeral(self.m.get_arg(expr, 0)) {
            self.lra_mut().delay_ineqs.push(expr);
            self.push_trail(TrailClosure::Theory(TheoryClosure::PopDelayIneq));
            return Ok(true);
        }
        let (term, numeral) = if is_right_numeral {
            (self.m.get_arg(expr, 0), self.m.get_arg(expr, 1))
        } else {
            (self.m.get_arg(expr, 1), self.m.get_arg(expr, 0))
        };
        let bound = self.m.get_rational_value(numeral).clone();
        let is_lower = (op == OP_GE) == is_right_numeral;
        let th_var = self.lra_internalize_def(term)?;
        let value = if self.lra_is_int_var(th_var) && !bound.is_int() {
            if is_lower {
                bound.ceil()
            } else {
                bound.floor()
            }
        } else {
            bound
        };
        let api_bound = self.lra_mk_var_bound(bool_var, th_var, is_lower, value)?;
        let theory = self.lra_mut();
        theory.bounds[th_var as usize].push(api_bound);
        self.lra_update_unassigned_bounds(th_var as usize, 1);
        let theory = self.lra_mut();
        theory.bounds_trail.push(th_var as usize);
        theory.bool_var_to_bound[bool_var as usize] = Some(api_bound);
        self.lra_mk_bound_axioms(api_bound)?;
        Ok(true)
    }

    fn lra_update_unassigned_bounds(&mut self, th_var: usize, increment: i32) {
        let saved = self.lra().unassigned_bounds[th_var];
        self.push_trail(TrailClosure::Theory(TheoryClosure::UnassignedBounds {
            th_var,
            saved,
        }));
        self.lra_mut().unassigned_bounds[th_var] = saved + increment;
    }

    /// The handle of a new bound in the arena.
    fn lra_mk_var_bound(
        &mut self,
        bool_var: BoolVar,
        th_var: i32,
        is_lower: bool,
        value: Rational,
    ) -> Result<usize, SmtError> {
        self.lra_push_internalize_state()?;
        self.lra_mut().internalize_head -= 1;
        let column = self.lra_register_var(th_var);
        let is_int = self.lra_is_int_var(th_var);
        let kind_true = if is_lower { KIND_GE } else { KIND_LE };
        let kind_false = match (is_lower, is_int) {
            (true, true) => KIND_LE,
            (true, false) => KIND_LT,
            (false, true) => KIND_GE,
            (false, false) => KIND_GT,
        };
        let theory = self.lra_mut();
        let constraint_true = theory.solver.mk_var_bound(column, kind_true, &value);
        let false_value = if !is_int {
            value.clone()
        } else if is_lower {
            value.sub(&Rational::one())
        } else {
            value.add(&Rational::one())
        };
        let constraint_false = theory.solver.mk_var_bound(column, kind_false, &false_value);
        set_at(
            &mut theory.constraint_sources,
            constraint_true,
            Some(mk_literal(bool_var, false)),
            None,
        );
        set_at(
            &mut theory.constraint_sources,
            constraint_false,
            Some(mk_literal(bool_var, true)),
            None,
        );
        theory.api_bounds.push(ApiBound {
            bool_var,
            th_var,
            column,
            is_int,
            value,
            is_lower,
            constraint_true,
            constraint_false,
        });
        Ok(theory.api_bounds.len() - 1)
    }

    /// mk_bound_axioms: implications between a new bound and its closest neighbors on the
    /// variable.
    fn lra_mk_bound_axioms(&mut self, bound: usize) -> Result<(), SmtError> {
        if !self.is_searching {
            self.lra_mut().new_bounds.push(bound);
            return Ok(());
        }
        let theory = self.lra();
        let this = &theory.api_bounds[bound];
        let mut lo_inf: Option<usize> = None;
        let mut lo_sup: Option<usize> = None;
        let mut hi_inf: Option<usize> = None;
        let mut hi_sup: Option<usize> = None;
        let value_of =
            |handle: Option<usize>| handle.map(|handle| &theory.api_bounds[handle].value);
        for &other_handle in &theory.bounds[this.th_var as usize] {
            let other = &theory.api_bounds[other_handle];
            if other_handle == bound || other.bool_var == this.bool_var {
                continue;
            }
            let comparison = other.value.compare(&this.value);
            if comparison.is_eq() && other.is_lower == this.is_lower {
                continue;
            }
            if other.is_lower {
                if comparison.is_lt() {
                    if value_of(lo_inf).is_none_or(|value| other.value.compare(value).is_gt()) {
                        lo_inf = Some(other_handle);
                    }
                } else if value_of(lo_sup).is_none_or(|value| other.value.compare(value).is_lt()) {
                    lo_sup = Some(other_handle);
                }
            } else if comparison.is_lt() {
                if value_of(hi_inf).is_none_or(|value| other.value.compare(value).is_gt()) {
                    hi_inf = Some(other_handle);
                }
            } else if value_of(hi_sup).is_none_or(|value| other.value.compare(value).is_lt()) {
                hi_sup = Some(other_handle);
            }
        }
        for other in [lo_inf, lo_sup, hi_inf, hi_sup].into_iter().flatten() {
            self.lra_mk_bound_axiom(bound, other)?;
        }
        Ok(())
    }

    fn lra_mk_bound_axiom(&mut self, first: usize, second: usize) -> Result<(), SmtError> {
        let theory = self.lra();
        let first = &theory.api_bounds[first];
        let second = &theory.api_bounds[second];
        let l1 = get_atom_literal(first);
        let l2 = get_atom_literal(second);
        let k1 = &first.value;
        let k2 = &second.value;
        if k1 == k2 && first.is_lower == second.is_lower {
            return Ok(());
        }
        let mut clauses: Vec<Vec<Literal>> = Vec::new();
        if first.is_lower {
            if second.is_lower {
                if k2.compare(k1).is_le() {
                    clauses.push(vec![negate(l1), l2]);
                } else {
                    clauses.push(vec![l1, negate(l2)]);
                }
            } else if k1.compare(k2).is_le() {
                clauses.push(vec![l1, l2]);
            } else {
                clauses.push(vec![negate(l1), negate(l2)]);
                if first.is_int && *k1 == k2.add(&Rational::one()) {
                    clauses.push(vec![l1, l2]);
                }
            }
        } else if second.is_lower {
            if k1.compare(k2).is_ge() {
                clauses.push(vec![l1, l2]);
            } else {
                clauses.push(vec![negate(l1), negate(l2)]);
                if first.is_int && *k1 == k2.sub(&Rational::one()) {
                    clauses.push(vec![l1, l2]);
                }
            }
        } else if k1.compare(k2).is_ge() {
            clauses.push(vec![l1, negate(l2)]);
        } else {
            clauses.push(vec![negate(l1), l2]);
        }
        for mut clause in clauses {
            self.mk_th_axiom(&mut clause)?;
        }
        Ok(())
    }

    /// flush_bound_axioms: the axioms of the bounds created before the search, per variable.
    pub(crate) fn lra_flush_bound_axioms(&mut self) -> Result<(), SmtError> {
        while !self.lra().new_bounds.is_empty() {
            let theory = self.lra_mut();
            let mut pending = std::mem::take(&mut theory.new_bounds);
            pending.sort_by_key(|bound| theory.api_bounds[*bound].th_var);
            let mut index = 0;
            while index < pending.len() {
                let theory = self.lra();
                let th_var = theory.api_bounds[pending[index]].th_var;
                let mut atoms: Vec<usize> = Vec::new();
                while index < pending.len() && theory.api_bounds[pending[index]].th_var == th_var {
                    atoms.push(pending[index]);
                    index += 1;
                }
                let by_value = |first: &usize, second: &usize| {
                    theory.api_bounds[*first]
                        .value
                        .compare(&theory.api_bounds[*second].value)
                };
                atoms.sort_by(by_value);
                let mut occs = theory.bounds[th_var as usize].clone();
                occs.sort_by(by_value);
                let end = occs.len();
                let get_first = |is_lower: bool| {
                    occs.iter()
                        .position(|bound| theory.api_bounds[*bound].is_lower == is_lower)
                        .unwrap_or(end)
                };
                let next_inf = |atom: usize, is_lower: bool, start: usize| {
                    let mut result = end;
                    let mut is_found = false;
                    for (position, other) in occs.iter().enumerate().take(end).skip(start) {
                        let other_bound = &theory.api_bounds[*other];
                        if *other == atom || other_bound.is_lower != is_lower {
                            continue;
                        }
                        is_found = true;
                        if other_bound
                            .value
                            .compare(&theory.api_bounds[atom].value)
                            .is_le()
                        {
                            result = position;
                        } else {
                            break;
                        }
                    }
                    Neighbor { result, is_found }
                };
                let next_sup = |atom: usize, is_lower: bool, start: usize| {
                    let mut is_found = false;
                    for (position, other) in occs.iter().enumerate().take(end).skip(start) {
                        let other_bound = &theory.api_bounds[*other];
                        if *other == atom || other_bound.is_lower != is_lower {
                            continue;
                        }
                        is_found = true;
                        if theory.api_bounds[atom]
                            .value
                            .compare(&other_bound.value)
                            .is_lt()
                        {
                            return Neighbor {
                                result: position,
                                is_found,
                            };
                        }
                    }
                    Neighbor {
                        result: end,
                        is_found,
                    }
                };
                let mut lo_inf = get_first(true);
                let mut lo_sup = lo_inf;
                let mut hi_inf = get_first(false);
                let mut hi_sup = hi_inf;
                let mut visited: HashSet<usize> = HashSet::new();
                let mut axioms: Vec<(usize, usize)> = Vec::new();
                for &atom in &atoms {
                    let lo_inf1 = next_inf(atom, true, lo_inf);
                    let hi_inf1 = next_inf(atom, false, hi_inf);
                    let lo_sup1 = next_sup(atom, true, lo_sup);
                    let hi_sup1 = next_sup(atom, false, hi_sup);
                    if lo_inf1.result != end {
                        lo_inf = lo_inf1.result;
                    }
                    if lo_sup1.result != end {
                        lo_sup = lo_sup1.result;
                    }
                    if hi_inf1.result != end {
                        hi_inf = hi_inf1.result;
                    }
                    if hi_sup1.result != end {
                        hi_sup = hi_sup1.result;
                    }
                    if !lo_inf1.is_found {
                        lo_inf = end;
                    }
                    if !hi_inf1.is_found {
                        hi_inf = end;
                    }
                    if !lo_sup1.is_found {
                        lo_sup = end;
                    }
                    if !hi_sup1.is_found {
                        hi_sup = end;
                    }
                    visited.insert(atom);
                    for (found, position) in [
                        (lo_inf1.result, lo_inf),
                        (lo_sup1.result, lo_sup),
                        (hi_inf1.result, hi_inf),
                        (hi_sup1.result, hi_sup),
                    ] {
                        if found != end && position != end && !visited.contains(&occs[position]) {
                            axioms.push((atom, occs[position]));
                        }
                    }
                }
                // The axioms only add clauses, which change neither the bounds nor the order, so
                // they are made after the walk that the TypeScript interleaves them with.
                for (atom, other) in axioms {
                    self.lra_mk_bound_axiom(atom, other)?;
                }
            }
        }
        Ok(())
    }

    pub fn theory_assign_eh(&mut self, bool_var: BoolVar, is_true: bool) -> Result<(), SmtError> {
        if self.theory.is_none() {
            return Err(SmtError::Invariant("the theory is not set up".into()));
        }
        let theory = self.lra_mut();
        theory
            .asserted_atoms
            .push(AssertedAtom { bool_var, is_true });
        if let Some(Some(bound)) = theory.bool_var_to_bound.get(bool_var as usize) {
            let th_var = theory.api_bounds[*bound].th_var as usize;
            self.lra_update_unassigned_bounds(th_var, -1);
        }
        Ok(())
    }
}
