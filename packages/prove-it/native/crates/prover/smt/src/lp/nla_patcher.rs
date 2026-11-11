// Ported from Z3 (src/math/lp/nla_patcher.{h,cpp}, src/util/mpz.cpp is_perfect_square), MIT
// license, see z3-license.txt. Moves the values of monic variables, or of one of their factors, to
// agree with the products, without breaking monics that are already correct.
//
// TS hands lar_solver's tryToPatch two closures over the core. LarSolver::try_to_patch holds the
// solver mutably and passes it to its callbacks, so the functions those callbacks run take nla's
// state and the solver apart (`core: &mut NlaCore, lra: &LarSolver`), and the two callbacks share
// the core through a RefCell, one at a time as try_to_patch calls them.
use std::cell::RefCell;

use prove_num::Rational;

use crate::lp::lar_solver::LarSolver;
use crate::lp::nla_core::{Nla, NlaCore, get_mul_val, get_val};
use crate::lp::numeric_pair::Impq;

// in_power: whether the variable at an index occurs next to an equal one.
fn is_in_power(vars: &[usize], index: usize) -> bool {
    let lp_var = vars[index];
    (index != 0 && vars[index - 1] == lp_var)
        || (index + 1 < vars.len() && lp_var == vars[index + 1])
}

#[derive(Default)]
pub struct Patcher {
    patched_var: usize,
    // The monic index of the monic being patched.
    patched_monic: Option<usize>,
}

impl Patcher {
    fn var_breaks_correct_monic_as_factor(
        core: &NlaCore,
        lra: &LarSolver<'_>,
        lp_var: usize,
        monic: usize,
    ) -> bool {
        let monic = &core.emons.monics[monic];
        if !get_val(lra, monic.variable).is_zero() {
            return true;
        }
        if !get_val(lra, lp_var).is_zero() {
            return false;
        }
        !monic
            .vars
            .iter()
            .any(|other| *other != lp_var && get_val(lra, *other).is_zero())
    }

    fn var_breaks_correct_monic(core: &mut NlaCore, lra: &LarSolver<'_>, lp_var: usize) -> bool {
        if core.is_monic_var(lp_var) && !core.to_refine.has(lp_var) {
            return true;
        }
        let mut use_list = core.emons.get_use_list(lp_var, &core.var_eqs);
        while let Some(monic) = use_list.next(&core.emons) {
            if core.to_refine.has(core.emons.monics[monic].variable) {
                continue;
            }
            if Patcher::var_breaks_correct_monic_as_factor(core, lra, lp_var, monic) {
                return true;
            }
        }
        false
    }

    fn update_to_refine_of_monic(core: &mut NlaCore, lra: &LarSolver<'_>, monic: usize) {
        let monic = &core.emons.monics[monic];
        let variable = monic.variable;
        if *get_val(lra, variable) == get_mul_val(lra, monic) {
            core.erase_from_to_refine(variable);
        } else {
            core.insert_to_refine(variable);
        }
    }

    fn update_to_refine_of_var(core: &mut NlaCore, lra: &LarSolver<'_>, lp_var: usize) {
        let mut use_list = core.emons.get_use_list(lp_var, &core.var_eqs);
        while let Some(monic) = use_list.next(&core.emons) {
            Patcher::update_to_refine_of_monic(core, lra, monic);
        }
        if core.is_monic_var(lp_var) {
            Patcher::update_to_refine_of_monic(core, lra, core.emons.get_index(lp_var));
        }
    }

    fn is_patch_blocked(
        core: &mut NlaCore,
        lra: &LarSolver<'_>,
        lp_var: usize,
        value: &Impq,
    ) -> bool {
        if !lra.inside_bounds(lp_var, value) || (lra.is_int(lp_var) && !value.is_int()) {
            return true;
        }
        if lp_var == core.patcher.patched_var {
            return false;
        }
        if let Some(monic) = core.patcher.patched_monic {
            let monic = &core.emons.monics[monic];
            if monic.contains_var(lp_var) || lp_var == monic.variable {
                return true;
            }
        }
        Patcher::var_breaks_correct_monic(core, lra, lp_var)
    }

    fn try_to_patch(nla: &mut Nla<'_, '_>, value: &Rational) -> bool {
        let patched_var = nla.patcher.patched_var;
        let core = RefCell::new(&mut *nla.core);
        nla.lra.try_to_patch(
            patched_var,
            value,
            |lra, lp_var, target| {
                Patcher::is_patch_blocked(&mut core.borrow_mut(), lra, lp_var, target)
            },
            |lra, lp_var| Patcher::update_to_refine_of_var(&mut core.borrow_mut(), lra, lp_var),
        )
    }

    fn patch_monomial(nla: &mut Nla<'_, '_>, lp_var: usize) {
        let monic = nla.emons.get_index(lp_var);
        nla.patcher.patched_monic = Some(monic);
        nla.patcher.patched_var = lp_var;
        let product = nla.mul_val(monic);
        if nla.val(lp_var) == product {
            nla.erase_from_to_refine(lp_var);
            return;
        }
        if !Patcher::var_breaks_correct_monic(nla.core, nla.lra, lp_var)
            && Patcher::try_to_patch(nla, &product)
        {
            return;
        }
        let vars = nla.emons.monics[monic].vars.clone();
        if vars.len() == 2 && vars[0] == vars[1] {
            let Some(root) = product.root(2) else {
                return;
            };
            nla.patcher.patched_var = vars[0];
            if !Patcher::var_breaks_correct_monic(nla.core, nla.lra, vars[0])
                && (Patcher::try_to_patch(nla, &root) || Patcher::try_to_patch(nla, &root.neg()))
            {
                return;
            }
            return;
        }
        if product.is_zero() {
            return;
        }
        let ratio = nla.val(lp_var).div(&product);
        for index in 0..nla.emons.monics[monic].size() {
            let patched_var = vars[index];
            nla.patcher.patched_var = patched_var;
            if !is_in_power(&vars, index)
                && !Patcher::var_breaks_correct_monic(nla.core, nla.lra, patched_var)
                && Patcher::try_to_patch(nla, &ratio.mul(&nla.val(patched_var)))
            {
                nla.erase_from_to_refine(lp_var);
                break;
            }
        }
    }

    pub fn patch_monomials(nla: &mut Nla<'_, '_>) {
        let to_refine = nla.to_refine.elems.clone();
        let size = to_refine.len();
        let start = nla.random() as usize;
        let mut index = 0;
        while index < size && nla.to_refine.size() > 0 {
            Patcher::patch_monomial(nla, to_refine[(start + index) % size]);
            index += 1;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lp::constraints::{KIND_GE, KIND_LE};
    use crate::lp::nla_core::tests::NlaFixture;

    // Expected states from the TS oracle on the same setups.
    #[test]
    fn patches_the_monic_to_the_product() {
        let (mut fixture, _) = NlaFixture::mk_scenario(
            3,
            &[(2, &[0, 1])],
            &[
                (0, KIND_GE, 2),
                (0, KIND_LE, 2),
                (1, KIND_GE, 3),
                (1, KIND_LE, 3),
            ],
        );
        fixture.with_nla(Patcher::patch_monomials);
        assert_eq!(fixture.show_state(), "values 2,3,6 toRefine ");
        assert!(fixture.core.lemmas.is_empty());
    }

    // The square's root and the factor's ratio are of the product 0, so neither patches.
    #[test]
    fn leaves_a_blocked_square_and_a_zero_product() {
        let (mut fixture, _) =
            NlaFixture::mk_scenario(2, &[(1, &[0, 0])], &[(1, KIND_GE, 9), (1, KIND_LE, 9)]);
        fixture.with_nla(Patcher::patch_monomials);
        assert_eq!(fixture.show_state(), "values 0,9 toRefine 1");
        let (mut fixture, _) = NlaFixture::mk_scenario(
            3,
            &[(2, &[0, 1])],
            &[
                (2, KIND_GE, 12),
                (2, KIND_LE, 12),
                (0, KIND_GE, 2),
                (0, KIND_LE, 2),
            ],
        );
        fixture.with_nla(Patcher::patch_monomials);
        assert_eq!(fixture.show_state(), "values 2,0,12 toRefine 2");
    }
}
