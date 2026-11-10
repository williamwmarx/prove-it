// STUB: replaced at integration
use crate::ZenonError;
use crate::expr::Expressions;
use crate::llproof::Lemma;

pub fn postprocess_tla(_exprs: &Expressions, lemmas: Vec<Lemma>) -> Result<Vec<Lemma>, ZenonError> {
    Ok(lemmas)
}
