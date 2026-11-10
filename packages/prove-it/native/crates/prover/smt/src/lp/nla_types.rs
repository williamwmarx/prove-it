// Ported from Z3 (src/math/lp/nla_types.h, src/math/lp/nla_defs.h, src/math/lp/nla_common.h, and
// lemma_builder of src/math/lp/nla_core.cpp), MIT license, see z3-license.txt. The inequalities and
// lemmas that the nla passes make, and the builder that adds a lemma to the core.
//
// TS's LemmaBuilder holds the core and pushes its lemma onto `core.lemmas` when it is made, so the
// lemma is visible, empty, from that moment and is filled in place. Here the builder holds the
// index of that lemma in `lemmas`, pushed by `LemmaBuilder::new` as TS does, and each method takes
// the core or the `Nla` view. A builder must not be used after `clear` empties `lemmas` (TS would
// write into a lemma no longer in the list; no TS caller does either).
use prove_num::Rational;

use crate::lp::constraints::{
    ConstraintKind, KIND_EQ, KIND_GE, KIND_GT, KIND_LE, KIND_LT, KIND_NE,
};
use crate::lp::explanation::Explanation;
use crate::lp::lar_term::LarTerm;
use crate::lp::nla_core::{Nla, NlaCore};
use crate::lp::nla_factorization::{Factor, Factorization};

pub fn negate_kind(kind: ConstraintKind) -> ConstraintKind {
    match kind {
        KIND_LE => KIND_GT,
        KIND_LT => KIND_GE,
        KIND_GE => KIND_LT,
        KIND_GT => KIND_LE,
        KIND_EQ => KIND_NE,
        _ => KIND_EQ,
    }
}

pub fn get_rat_sign(value: &Rational) -> i32 {
    if value.is_positive() {
        1
    } else if value.is_negative() {
        -1
    } else {
        0
    }
}

pub fn sign_to_rat(is_negated: bool) -> Rational {
    if is_negated {
        Rational::minus_one()
    } else {
        Rational::one()
    }
}

// An ineq: term cmp rs.
#[derive(Clone)]
pub struct Ineq {
    pub cmp: ConstraintKind,
    pub term: LarTerm,
    pub rs: Rational,
}

// mkIneq with a column for the term: the term 1 * column.
pub fn mk_ineq(lp_var: usize, cmp: ConstraintKind, rs: Rational) -> Ineq {
    mk_term_ineq(LarTerm::from_entries([(lp_var, &Rational::one())]), cmp, rs)
}

// mkIneq with a term.
pub fn mk_term_ineq(term: LarTerm, cmp: ConstraintKind, rs: Rational) -> Ineq {
    Ineq { cmp, term, rs }
}

// A lemma: its explanation implies one of its inequalities, or false when it has none.
#[derive(Clone, Default)]
pub struct Lemma {
    pub ineqs: Vec<Ineq>,
    pub expl: Explanation,
}

pub fn is_conflict_lemma(lemma: &Lemma) -> bool {
    lemma.ineqs.is_empty() && !lemma.expl.is_empty()
}

// lemma_builder: adds a lemma to the core and builds it in place.
pub struct LemmaBuilder {
    index: usize,
}

impl LemmaBuilder {
    pub fn new(core: &mut NlaCore) -> LemmaBuilder {
        core.lemmas.push(Lemma::default());
        LemmaBuilder {
            index: core.lemmas.len() - 1,
        }
    }

    // The index of the lemma in `lemmas`.
    pub fn index(&self) -> usize {
        self.index
    }

    pub fn expl<'c>(&self, core: &'c NlaCore) -> &'c Explanation {
        &core.lemmas[self.index].expl
    }

    // |=: an inequality, unless the bounds already explain its negation away.
    pub fn add_ineq(&self, nla: &mut Nla<'_, '_>, ineq: Ineq) -> &Self {
        if !nla.explain_ineq(self, &ineq.term, ineq.cmp, &ineq.rs) {
            nla.lemmas[self.index].ineqs.push(ineq);
        }
        self
    }

    pub fn add_explanation(&self, core: &mut NlaCore, explanation: &Explanation) -> &Self {
        core.lemmas[self.index].expl.add_explanation(explanation);
        self
    }

    // &= on a monic (a monic index): the equivalences of its variables.
    pub fn explain_monic(&self, core: &mut NlaCore, monic: usize) -> &Self {
        for index in 0..core.emons.monics[monic].vars.len() {
            self.explain_var(core, core.emons.monics[monic].vars[index]);
        }
        self
    }

    pub fn explain_factor(&self, core: &mut NlaCore, factor: &Factor) -> &Self {
        if factor.is_mon {
            self.explain_monic(core, core.emons.get_index(factor.variable));
        } else {
            self.explain_var(core, factor.variable);
        }
        self
    }

    pub fn explain_factorization(
        &self,
        core: &mut NlaCore,
        factorization: &Factorization,
    ) -> &Self {
        if factorization.mon.is_some() {
            return self;
        }
        for factor in &factorization.factors {
            self.explain_factor(core, factor);
        }
        self
    }

    pub fn explain_var(&self, core: &mut NlaCore, lp_var: usize) -> &Self {
        core.var_eqs
            .explain_var(lp_var, &mut core.lemmas[self.index].expl);
        self
    }

    pub fn explain_fixed(&self, nla: &mut Nla<'_, '_>, lp_var: usize) -> &Self {
        self.explain_existing_lower_bound(nla, lp_var);
        self.explain_existing_upper_bound(nla, lp_var);
        self
    }

    pub fn explain_var_separated_from_zero(&self, nla: &mut Nla<'_, '_>, lp_var: usize) -> &Self {
        if nla.var_has_negative_upper_bound(lp_var) {
            self.explain_existing_upper_bound(nla, lp_var);
        } else {
            self.explain_existing_lower_bound(nla, lp_var);
        }
        self
    }

    pub fn explain_existing_lower_bound(&self, nla: &mut Nla<'_, '_>, lp_var: usize) -> &Self {
        let mut explanation = Explanation::new();
        explanation.push_dependency(nla.lra.get_lower_witness(lp_var));
        self.add_explanation(nla, &explanation)
    }

    pub fn explain_existing_upper_bound(&self, nla: &mut Nla<'_, '_>, lp_var: usize) -> &Self {
        let mut explanation = Explanation::new();
        explanation.push_dependency(nla.lra.get_upper_witness(lp_var));
        self.add_explanation(nla, &explanation)
    }
}
