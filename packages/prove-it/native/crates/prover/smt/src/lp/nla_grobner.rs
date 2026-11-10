// Ported from Z3 (src/math/lp/nla_grobner.h, src/math/lp/nla_grobner.cpp), MIT license, see
// z3-license.txt. nla's Grobner pass: the rows around the monomials to refine become polynomial
// equations, which dd::solver saturates, and the equations then yield lemmas: interval conflicts,
// quotient and residue bounds, failed gcd tests, fixed variables, factorizations, and new linear
// rows. Z3's nlsat conflict check (is_nla_conflict) is not ported, nor are the statistics.
//
// STUB(P3b-lp): ported next. Only the API nla_core calls exists, generating no lemma.
use crate::lp::nla_core::Nla;
use crate::util::error::SmtError;

#[derive(Default)]
pub struct Grobner {}

impl Grobner {
    // TS makes its PddManager over the lar_solver's column count when nla is made.
    // STUB(P3b-lp): ported next.
    pub fn new(_column_count: usize) -> Grobner {
        Grobner {}
    }

    // operator(): runs the pass, unless the quota of misses delays it.
    // STUB(P3b-lp): ported next. Generates no lemma.
    pub fn run(_nla: &mut Nla<'_, '_>) -> Result<(), SmtError> {
        Ok(())
    }
}
