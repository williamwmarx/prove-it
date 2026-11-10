// Ported from Z3 (src/math/lp/horner.h, src/math/lp/horner.cpp, and nexvar, create_sum_from_row,
// and add_deps_of_fixed from src/math/lp/nla_common.cpp), MIT license, see z3-license.txt. Horner
// lemmas: a tableau row is a sum that equals zero. Each cross-nested form of the row that
// intervals proves nonzero yields a conflict.
//
// CrossNested holds the creator mutably while its callbacks hold the view, and the creator is a
// field of nla's state: so the creator is moved out of the state for the run (`std::mem::take`)
// and back after it.
use prove_num::Rational;

use crate::lp::cross_nested::{CrossNested, CrossNestedCallbacks};
use crate::lp::dependency::{Dependency, mk_join};
use crate::lp::nex::{Nex, NexId, get_degree};
use crate::lp::nex_creator::{NexCreator, NexFactor};
use crate::lp::nla_core::{NLA_PARAMS, Nla, NlaCore};
use crate::lp::nla_intervals::Intervals;
use crate::lp::static_matrix::RowCell;

// The callbacks that horner and grobner give CrossNested: check_nex of each form with the
// dependency, var_is_fixed, and the limit's inc, which is !is_canceled.
pub struct CheckNexCallbacks<'n, 'a, 'l> {
    pub nla: &'n mut Nla<'a, 'l>,
    pub dep: Dependency,
}

impl CrossNestedCallbacks for CheckNexCallbacks<'_, '_, '_> {
    fn call_on_result(&mut self, nex_creator: &NexCreator, expr: NexId) -> bool {
        Intervals::check_nex(self.nla, &nex_creator.nexes, expr, &self.dep)
    }

    fn var_is_fixed(&self, variable: usize) -> bool {
        self.nla.var_is_fixed(variable)
    }

    fn inc(&mut self) -> bool {
        !self.nla.is_canceled()
    }
}

#[derive(Default)]
pub struct Horner {
    nex_creator: NexCreator,
    // The joined bounds of the fixed variables that the row's sum replaced by their values.
    fixed_dep: Dependency,
}

impl Horner {
    pub fn horner_lemmas(nla: &mut Nla<'_, '_>) -> bool {
        if !NLA_PARAMS.horner {
            return false;
        }
        if nla.to_refine.size() == 0 {
            nla.is_nla_satisfied = true;
            return false;
        }
        // The TypeScript's set of rows, sorted: the rows sorted without duplicates.
        let mut rows: Vec<usize> = Vec::new();
        for &lp_var in &nla.core.to_refine.elems {
            for cell in &nla.lra.core.matrix.columns[lp_var] {
                rows.push(cell.row);
            }
        }
        nla.active_var_set.clear();
        rows.sort();
        rows.dedup();
        let matrix = &nla.lra.core.matrix;
        let core = &mut *nla.core;
        rows.retain(|row_index| Horner::row_is_interesting(core, &matrix.rows[*row_index]));
        let offset = nla.random() as usize;
        for index in 0..rows.len() {
            if Horner::lemmas_on_row(nla, rows[(index + offset) % rows.len()]) {
                return true;
            }
        }
        false
    }

    // row_is_interesting: whether two monomials of the row share a variable.
    fn row_is_interesting(core: &mut NlaCore, row: &[RowCell]) -> bool {
        if row.len() > NLA_PARAMS.horner_row_length_limit {
            return false;
        }
        core.active_var_set.clear();
        for cell in row {
            if !core.is_monic_var(cell.column) {
                if core.active_var_set.has(cell.column) {
                    return true;
                }
                core.active_var_set.add(cell.column);
                continue;
            }
            let vars = &core.emons.get(cell.column).vars;
            if vars.iter().any(|lp_var| core.active_var_set.has(*lp_var)) {
                return true;
            }
            for &lp_var in vars {
                core.active_var_set.add(lp_var);
            }
        }
        false
    }

    fn lemmas_on_row(nla: &mut Nla<'_, '_>, row_index: usize) -> bool {
        nla.active_var_set.clear();
        nla.horner.fixed_dep = None;
        let mut creator = std::mem::take(&mut nla.horner.nex_creator);
        // No expression outlives the run, so dropping the earlier ones (which TS's garbage
        // collector frees) changes nothing.
        creator.clear();
        let cells: Vec<(Rational, usize)> = nla.lra.core.matrix.rows[row_index]
            .iter()
            .map(|cell| (cell.coeff.clone(), cell.column))
            .collect();
        let summands: Vec<NexId> = cells
            .iter()
            .map(|cell| Horner::nexvar(nla, &mut creator, &cell.0, cell.1))
            .collect();
        let fixed_dep = nla.horner.fixed_dep.clone();
        Horner::set_active_vars_weights(nla, &mut creator);
        let sum = creator.mk_sum(&summands);
        let expr = creator.simplify(sum);
        let is_done = if get_degree(&creator.nexes, expr) < 2
            || !matches!(creator.nexes[expr], Nex::Sum(_))
        {
            false
        } else {
            let random_seed = nla.random();
            let callbacks = CheckNexCallbacks {
                nla: &mut *nla,
                dep: fixed_dep,
            };
            let mut cross_nested = CrossNested::new(callbacks, random_seed, &mut creator);
            cross_nested.run(expr);
            cross_nested.done()
        };
        nla.horner.nex_creator = creator;
        is_done
    }

    // set_active_vars_weights: without the weights the comparisons of nex_creator are wrong.
    fn set_active_vars_weights(nla: &Nla<'_, '_>, creator: &mut NexCreator) {
        creator.set_number_of_vars(nla.lra.get_column_count());
        for &lp_var in &nla.active_var_set.elems {
            creator.set_var_weight(lp_var, nla.get_var_weight(lp_var));
        }
    }

    // add_deps_of_fixed.
    fn add_deps_of_fixed(nla: &mut Nla<'_, '_>, lp_var: usize) {
        nla.core.horner.fixed_dep = mk_join(
            &nla.core.horner.fixed_dep,
            &nla.lra.get_bound_witnesses(lp_var),
        );
    }

    // nexvar: coeff times the column, a product for a monic, where horner_subs_fixed replaces
    // fixed variables by their values (1) or only those fixed to zero (2).
    fn nexvar(
        nla: &mut Nla<'_, '_>,
        creator: &mut NexCreator,
        coeff: &Rational,
        lp_var: usize,
    ) -> NexId {
        let subs_fixed = NLA_PARAMS.horner_subs_fixed;
        if subs_fixed == 1 && nla.var_is_fixed(lp_var) {
            Horner::add_deps_of_fixed(nla, lp_var);
            return creator.mk_scalar(coeff.mul(&nla.lra.core.lower_bounds[lp_var].x));
        }
        if subs_fixed == 2 && nla.var_is_fixed_to_zero(lp_var) {
            Horner::add_deps_of_fixed(nla, lp_var);
            return creator.mk_scalar(Rational::zero());
        }
        if !nla.is_monic_var(lp_var) {
            nla.active_var_set.add(lp_var);
            let scalar = creator.mk_scalar(coeff.clone());
            let variable = creator.mk_var(lp_var);
            return creator.mk_mul(&[NexFactor::Expr(scalar), NexFactor::Expr(variable)]);
        }
        let mut factors = vec![NexFactor::Scalar(coeff.clone())];
        let initial_dep = nla.horner.fixed_dep.clone();
        for factor_var in nla.emon(lp_var).vars.clone() {
            if subs_fixed == 1 && nla.var_is_fixed(factor_var) {
                Horner::add_deps_of_fixed(nla, factor_var);
                factors.push(NexFactor::Scalar(
                    nla.lra.core.lower_bounds[factor_var].x.clone(),
                ));
            } else if subs_fixed == 2 && nla.var_is_fixed_to_zero(factor_var) {
                nla.horner.fixed_dep = initial_dep;
                Horner::add_deps_of_fixed(nla, factor_var);
                return creator.mk_scalar(Rational::zero());
            } else {
                nla.active_var_set.add(factor_var);
                factors.push(NexFactor::Expr(creator.mk_var(factor_var)));
            }
        }
        creator.mk_mul(&factors)
    }
}

#[cfg(test)]
mod tests {
    use prove_num::Rational;

    use super::Horner;
    use crate::lp::constraints::{KIND_GE, KIND_LE};
    use crate::lp::nla_core::tests::{NlaFixture, show_lemmas};

    // Expected lemmas from the TS oracle on the same setup: the row of t = x*y + x*z is
    // x*(y + z) - t = 0 in cross-nested form, whose interval [-oo, -3] excludes 0.
    #[test]
    fn finds_a_cross_nested_form_whose_interval_excludes_zero() {
        let mut fixture = NlaFixture::new();
        for external in 0..5 {
            fixture.lra.add_var(external, true);
        }
        fixture.with_nla(|nla| {
            nla.add_monic(3, &[0, 1]);
            nla.add_monic(4, &[0, 2]);
        });
        let term = fixture
            .lra
            .add_term(&[(3, Rational::one()), (4, Rational::one())], 5);
        let constraints = [
            fixture.add_bound(0, KIND_GE, 1),
            fixture.add_bound(0, KIND_LE, 2),
            fixture.add_bound(1, KIND_GE, 1),
            fixture.add_bound(1, KIND_LE, 2),
            fixture.add_bound(2, KIND_GE, 1),
            fixture.add_bound(2, KIND_LE, 2),
            fixture.add_bound(term, KIND_LE, -1),
        ];
        fixture.prepare();
        assert!(fixture.with_nla(Horner::horner_lemmas));
        assert_eq!(constraints, [0, 1, 2, 3, 4, 5, 6]);
        assert_eq!(fixture.show_state(), "values 1,1,1,0,-1,-1 toRefine 4,3");
        assert_eq!(show_lemmas(&fixture.core), ["[] {0,2,4,6}"]);
    }
}
