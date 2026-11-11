//! The classical reasoner and hypsubst as PredicateLogic.thy and SetTheory.thy of Isabelle/TLA+
//! instantiate them (BSD licensed, see LICENSE-tlapm): the Hypsubst and Classical functor
//! arguments, the claset with its nets as the reference heap orders them, and SetTheory's bspec
//! wrapper.
//!
//! (`tla/classical-setup.ts`.)

use std::rc::Rc;

use crate::error::{Res, error_exn, term_exn};
use crate::provers::classical::{Claset, ClassicalData, addbefore};
use crate::provers::hypsubst::{HypsubstData, hyp_subst_tac};
use crate::pure::net::empty_net;
use crate::pure::tactic::{Brl, NetPair, assume_tac, dresolve_tac, insert_tagged_brl};
use crate::pure::tactical::then_goal;
use crate::pure::term::Term;
use crate::pure::thm::Thm;

use super::logic::{LogicNetPair, TlaLogic};

pub fn get_fact(logic: &TlaLogic, name: &str) -> Res<Thm> {
    match logic.facts.get(name).map(Vec::as_slice) {
        Some([thm]) => Ok(thm.clone()),
        _ => Err(error_exn(format!("Undefined fact: {name}"))),
    }
}

fn dest_binary(name: &'static str) -> Box<dyn Fn(&Term) -> Res<(Term, Term)>> {
    Box::new(move |term| {
        term.dest_app()
            .and_then(|(fun, right)| {
                fun.dest_app()
                    .filter(|(head, _)| head.is_const_named(name))
                    .map(|(_, left)| (left.clone(), right.clone()))
            })
            .ok_or_else(|| term_exn(format!("dest {name}")))
    })
}

fn dest_trueprop(term: &Term) -> Res<Term> {
    term.dest_app()
        .filter(|(fun, _)| fun.is_const_named("PredicateLogic.Trueprop"))
        .map(|(_, arg)| arg.clone())
        .ok_or_else(|| term_exn("dest_Trueprop"))
}

pub fn get_hypsubst_data(logic: &TlaLogic) -> Res<Rc<HypsubstData>> {
    Ok(Rc::new(HypsubstData {
        dest_trueprop: Box::new(dest_trueprop),
        dest_eq: dest_binary("PredicateLogic.eq"),
        dest_imp: dest_binary("PredicateLogic.imp"),
        eq_reflection: get_fact(logic, "PredicateLogic.eq_reflection")?,
        rev_eq_reflection: get_fact(logic, "PredicateLogic.meta_to_obj_eq")?,
        imp_intr: get_fact(logic, "PredicateLogic.impI")?,
        rev_mp: get_fact(logic, "PredicateLogic.rev_mp")?,
        subst: get_fact(logic, "PredicateLogic.subst")?,
        sym: get_fact(logic, "PredicateLogic.sym")?,
        thin_refl: get_fact(logic, "PredicateLogic.thin_refl")?,
    }))
}

pub fn get_classical_data(logic: &TlaLogic) -> Res<ClassicalData> {
    let hypsubst = get_hypsubst_data(logic)?;
    Ok(ClassicalData {
        imp_elim: get_fact(logic, "PredicateLogic.impCE'")?,
        not_elim: get_fact(logic, "PredicateLogic.notE")?,
        swap: get_fact(logic, "PredicateLogic.swap")?,
        classical: get_fact(logic, "PredicateLogic.classical")?,
        judgment: "PredicateLogic.Trueprop".into(),
        hyp_subst_tacs: vec![hyp_subst_tac(&hypsubst)],
    })
}

/// Net.content lists a leaf's items newest first, so inserting them in reverse rebuilds the leaf.
/// (context.ts's toNetPair is the same for the context rules.)
pub(crate) fn to_net_pair<Item: Brl + Clone>(pair: &LogicNetPair<Item>) -> Res<NetPair<Item>> {
    let insert_all = |items: &[Item], netpair: NetPair<Item>| {
        items.iter().rev().try_fold(netpair, |result, item| {
            insert_tagged_brl(item.clone(), &result)
        })
    };
    insert_all(
        &pair.elim,
        insert_all(
            &pair.intro,
            NetPair {
                intro: empty_net(),
                elim: empty_net(),
            },
        )?,
    )
}

pub fn get_claset(logic: &TlaLogic) -> Res<Claset> {
    let claset = Claset {
        safe_is: logic.claset.safe_is.clone(),
        safe_es: logic.claset.safe_es.clone(),
        unsafe_is: logic.claset.unsafe_is.clone(),
        unsafe_es: logic.claset.unsafe_es.clone(),
        swrappers: Vec::new(),
        uwrappers: Vec::new(),
        safe0: to_net_pair(&logic.claset.safe0)?,
        safep: to_net_pair(&logic.claset.safep)?,
        r#unsafe: to_net_pair(&logic.claset.r#unsafe)?,
        dup: to_net_pair(&logic.claset.dup)?,
    };
    // SetTheory.thy: ctxt addbefore ("bspec", fn ctxt' => dresolve_tac ctxt' @{thms bspec} THEN' assume_tac ctxt')
    let bspec = then_goal(
        dresolve_tac(&[get_fact(logic, "SetTheory.bspec")?])?,
        assume_tac(),
    );
    Ok(addbefore(&claset, "bspec", bspec))
}
