//! The proof context of a theory tlapm writes, as the Isabelle/TLA+ heap sets it up: its simpset,
//! claset, context rules and atomize rules, and Blast instantiated as PredicateLogic.thy does.
//!
//! (`tla/context.ts`.)

use std::rc::Rc;

use crate::error::{Res, error_exn};
use crate::isar::method::ProofContext;
use crate::provers::blast::blast::{blast_depth_tac, blast_tac};
use crate::provers::blast::state::{BlastContext, BlastData};
use crate::provers::classical::ClassicalContext;
use crate::provers::hypsubst::blast_hyp_subst_tac;
use crate::tools::intuitionistic::IntuitionisticContext;

use super::classical_setup::{
    get_claset, get_classical_data, get_fact, get_hypsubst_data, to_net_pair,
};
use super::logic::TlaLogic;
use super::simpdata::get_simpset;

/// The atomize rules, newest first as Object_Logic keeps them.
pub(crate) const ATOMIZE_RULES: [&str; 7] = [
    "Zenon.atomize_object_bAll",
    "Zenon.atomize_meta_bAll",
    "PredicateLogic.atomize_conj",
    "PredicateLogic.atomize_eq",
    "PredicateLogic.atomize_not",
    "PredicateLogic.atomize_imp",
    "PredicateLogic.atomize_all",
];

/// The TypeScript's toBlastContext reads the logic's facts for blast's data each time it is
/// called; they are the same theorems each time, so this reads them once. Each call still makes a
/// blast context of its own, with no rule converted yet.
pub fn get_proof_context(logic: &Rc<TlaLogic>) -> Res<ProofContext> {
    let atomize_rules = ATOMIZE_RULES
        .iter()
        .map(|name| get_fact(logic, name))
        .collect::<Res<Vec<_>>>()?;
    let classical = ClassicalContext {
        claset: Rc::new(get_claset(logic)?),
        data: Rc::new(get_classical_data(logic)?),
    };
    let hypsubst = get_hypsubst_data(logic)?;
    let blast_data = Rc::new(BlastData {
        trueprop: "PredicateLogic.Trueprop".into(),
        equality_name: "PredicateLogic.eq".into(),
        not_name: "PredicateLogic.not".into(),
        not_e: get_fact(logic, "PredicateLogic.notE")?,
        ccontr: get_fact(logic, "PredicateLogic.contradiction")?,
        hyp_subst_tac: blast_hyp_subst_tac(&hypsubst),
        classical: get_fact(logic, "PredicateLogic.classical")?,
        atomize: atomize_rules.clone(),
    });
    let to_blast_context = {
        let logic = logic.clone();
        move |context: &ClassicalContext| {
            Rc::new(BlastContext::new(
                context.claset.clone(),
                blast_data.clone(),
                logic.clone(),
            ))
        }
    };
    let to_depth_context = to_blast_context.clone();
    let facts = logic.clone();
    Ok(ProofContext {
        simpset: get_simpset(logic)?,
        classical,
        intuitionistic: IntuitionisticContext {
            safe_rules: to_net_pair(&logic.context_rules.bang)?,
            rules: to_net_pair(&logic.context_rules.plain)?,
        },
        atomize_rules,
        blast_depth_tac: Rc::new(move |context, limit| {
            blast_depth_tac(to_depth_context(context), limit)
        }),
        blast_tac: Rc::new(move |context| blast_tac(to_blast_context(context))),
        get_fact: Rc::new(move |name| {
            let fact = facts.fact_names.get(name).map_or(name, |fact| &**fact);
            facts
                .facts
                .get(fact)
                .cloned()
                .ok_or_else(|| error_exn(format!("Undefined fact: {name}")))
        }),
    })
}
