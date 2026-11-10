// Ported from Z3 (src/math/lp/nla_monotone_lemmas.h, src/math/lp/nla_monotone_lemmas.cpp), MIT
// license, see z3-license.txt. The monotonicity lemmas of nla: the absolute value of a monomial is
// at most, or at least, the product of its factors' absolute values when they are.
//
// STUB(P3b-lp): ported next. Only the API nla_core calls exists, generating no lemma.
use crate::lp::nla_core::Nla;

#[derive(Default)]
pub struct Monotone {}

impl Monotone {
    // STUB(P3b-lp): ported next. Generates no lemma.
    pub fn monotonicity_lemma(_nla: &mut Nla<'_, '_>) {}
}
