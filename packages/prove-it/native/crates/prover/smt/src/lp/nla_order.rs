// Ported from Z3 (src/math/lp/nla_order_lemmas.h, src/math/lp/nla_order_lemmas.cpp), MIT
// license, see z3-license.txt. The order lemmas of nla: a > b and c > 0 imply ac > bc, over the
// binary factorizations of the monomials to refine, and the sign lemmas of binomials.
//
// STUB(P3b-lp): ported next. Only the API nla_core calls exists, generating no lemma.
use crate::lp::nla_core::Nla;

#[derive(Default)]
pub struct Order {}

impl Order {
    // STUB(P3b-lp): ported next. Generates no lemma.
    pub fn order_lemma(_nla: &mut Nla<'_, '_>) {}
}
