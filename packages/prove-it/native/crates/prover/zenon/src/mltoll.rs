// STUB: replaced at integration
use std::collections::HashSet;
use std::rc::Rc;

use crate::ZenonError;
use crate::eqrel::Relations;
use crate::expr::{Expr, Expressions};
use crate::llproof::Lemma;
use crate::parse::Phrase;
use crate::proof::{Proof, ProofKey};

const META_PREFIX: &str = "zenon_X";

pub struct TranslateContext<'a> {
    pub exprs: &'a Expressions,
    pub get_number: &'a dyn Fn(&Expr) -> usize,
    pub shared_proofs: &'a HashSet<ProofKey>,
    pub relations: &'a Relations,
}

pub fn is_meta_name(name: &str) -> bool {
    name.starts_with(META_PREFIX)
}

pub fn translate_proof(
    _context: &TranslateContext,
    _phrases: &[Phrase],
    _proof: &Rc<Proof>,
) -> Result<Vec<Lemma>, ZenonError> {
    Err(ZenonError::new("Zenon: mltoll isn't ported yet"))
}
