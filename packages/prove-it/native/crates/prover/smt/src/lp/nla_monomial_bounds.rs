// Ported from Z3 (src/math/lp/monomial_bounds.{h,cpp}, src/util/mpq.h root), MIT license, see
// z3-license.txt. Bounds of monomials from the intervals of their factors and back, the
// linearization of monomials with at most one non-fixed factor, and the optimization of the bounds
// of nonlinear variables over the tableau. The shared-factor and binomial-sign lemmas, off by
// default (arith.nl.monomial_sandwich, arith.nl.monomial_binomial_sign), are not ported.
//
// STUB(P3b-lp): ported next. Only the API nla_core calls exists: no lemma, no bound, no change.
// Its port must call `nla.drain_changed_bounds()` right after each of its own
// `nla.lra.find_feasible_solution()` calls (optimize_nl_bounds makes two), see nla_core.rs.
use crate::lp::nla_core::Nla;

#[derive(Default)]
pub struct MonomialBounds {}

impl MonomialBounds {
    // STUB(P3b-lp): ported next. Generates no lemma.
    pub fn generate_lemmas(_nla: &mut Nla<'_, '_>) {}

    // STUB(P3b-lp): ported next. Propagates nothing.
    pub fn propagate_changed_bounds(_nla: &mut Nla<'_, '_>) -> bool {
        false
    }

    // STUB(P3b-lp): ported next. Propagates nothing.
    pub fn propagate_violated_linear_monomials(_nla: &mut Nla<'_, '_>) -> bool {
        false
    }

    // STUB(P3b-lp): ported next. Tightens nothing.
    pub fn tighten_lp_bounds(_nla: &mut Nla<'_, '_>) -> bool {
        false
    }

    // STUB(P3b-lp): ported next. Improves no bound.
    pub fn optimize_nl_bounds(_nla: &mut Nla<'_, '_>) -> bool {
        false
    }
}
