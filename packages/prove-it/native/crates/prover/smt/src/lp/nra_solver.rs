// Ported from Z3 (src/math/lp/nra_solver.cpp, src/math/lp/nla_coi.cpp), MIT license, see
// z3-license.txt. nla's bridge to nlsat. The constraints in the cone of influence of the monomials
// to refine go to nlsat, with every monomial and term column replaced by its polynomial. check runs
// nlsat's search on them: a model becomes nla's, and a refutation a lemma over the constraints of
// its core. check_assignment instead hands nlsat the current values, and when they violate a
// constraint, nlsat's linear cell around them becomes a lemma.
//
// STUB(P3b-lp): ported once nlsat is. Until then both checks decline with
// `SmtError::Unsupported`, which nla's check propagates, never a made-up answer.
use crate::lp::nla_core::Nla;
use crate::util::error::SmtError;
use crate::util::lbool::LBool;

#[derive(Default)]
pub struct NraSolver {}

impl NraSolver {
    // The steps of the last check.
    // STUB(P3b-lp): ported next.
    pub fn steps(&self) -> u64 {
        0
    }

    // check: nlsat's search, giving up after max_conflicts conflicts or budget steps; u64::MAX
    // stands for TS's Infinity.
    // STUB(P3b-lp): ported next. Declines.
    pub fn check(
        _nla: &mut Nla<'_, '_>,
        _max_conflicts: u64,
        _budget: u64,
    ) -> Result<LBool, SmtError> {
        Err(SmtError::Unsupported("nra-solver is not ported yet".into()))
    }

    // check_assignment
    // STUB(P3b-lp): ported next. Declines.
    pub fn check_assignment(_nla: &mut Nla<'_, '_>) -> Result<LBool, SmtError> {
        Err(SmtError::Unsupported("nra-solver is not ported yet".into()))
    }
}
