// Ported from Z3 (src/math/lp/nla_tangent_lemmas.h, src/math/lp/nla_tangent_lemmas.cpp), MIT
// license, see z3-license.txt. The tangent lemmas of nla: for a binary product whose value is
// wrong, the lines through the point of its factors' values and two planes tangent to z = xy that
// cut the point off.
//
// STUB(P3b-lp): ported next. Only the API nla_core calls exists, generating no lemma.
use crate::lp::nla_core::Nla;

#[derive(Default)]
pub struct Tangents {}

impl Tangents {
    // STUB(P3b-lp): ported next. Generates no lemma.
    pub fn tangent_lemma(_nla: &mut Nla<'_, '_>) {}
}
