// Ported from Z3 (src/math/lp/horner.h, src/math/lp/horner.cpp, and nexvar, create_sum_from_row,
// and add_deps_of_fixed from src/math/lp/nla_common.cpp), MIT license, see z3-license.txt. Horner
// lemmas: a tableau row is a sum that equals zero. Each cross-nested form of the row that
// intervals proves nonzero yields a conflict.
//
// STUB(P3b-lp): ported next. Only the API nla_core calls exists, generating no lemma.
use crate::lp::nla_core::Nla;

#[derive(Default)]
pub struct Horner {}

impl Horner {
    // STUB(P3b-lp): ported next. Generates no lemma, and does not set is_nla_satisfied (the TS sets
    // it when nothing is to refine, which check never calls it with).
    pub fn horner_lemmas(_nla: &mut Nla<'_, '_>) -> bool {
        false
    }
}
