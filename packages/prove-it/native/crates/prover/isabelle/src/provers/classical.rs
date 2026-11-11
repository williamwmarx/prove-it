//! Ported from Isabelle2025's Provers/classical.ML. Copyright (c) 1986-2025 University of
//! Cambridge, Technische Universitaet Muenchen, and contributors, see LICENSE.
//!
//! The classical reasoner: rule sets of safe and unsafe introduction and elimination rules, and
//! the tactics that search with them. The rules Isabelle/TLA+ declares come with the logic; a
//! method adds more with intro: and dest:.
//!
//! (`provers/classical.ts`.) The TypeScript's hypsubst tactic factories, which take the limits,
//! are goal tactics here, since the limits are installed for the thread.

use std::rc::Rc;

use crate::error::{Res, error_exn, thm_exn};
use crate::pure::drule::{make_elim, revcut_rl, thin_rl, zero_var_indexes};
use crate::pure::goal::select_goal;
use crate::pure::interrupt::without_limits;
use crate::pure::logic::{strip_assums_concl, strip_assums_hyp};
use crate::pure::object_logic::atomize_prems_tac;
use crate::pure::search::best_first;
use crate::pure::seq::{list_of_seq, seq_head};
use crate::pure::tactic::{
    NetPair, TaggedRule, assume_tac, bimatch_from_nets_tac, biresolution_from_nets_tac,
    biresolve_from_nets_tac, ematch_tac, eq_assume_tac, eresolve_tac, insert_tagged_brl,
    order_tagged, subgoals_of_brl,
};
use crate::pure::tactical::{
    GoalTactic, Tactic, all_goals, all_tac, append_goal, cond_tac, first_goal, first_goal_tac,
    has_fewer_prems, no_tac, or_else, or_else_goal, repeat_determ, repeat_determ1, subgoal,
    then_goal, then_tac,
};
use crate::pure::term::{Name, Term, TermNode, aconv, size_of_term};
use crate::pure::thm::{BiresRule, Thm, assumption, biresolution, nprems, prems_of, rs, rsn};
use crate::pure::variable::trade;

/// A rule as the user gave it, as the nets use it, and as the complete search duplicates it, each
/// with its swapped forms for negated assumptions.
#[derive(Clone)]
pub struct ClassicalRule {
    pub rule: Thm,
    pub internal: Thm,
    pub swapped: Vec<Thm>,
    pub dup: Thm,
    pub dup_swapped: Vec<Thm>,
}

#[derive(Clone)]
pub struct Wrapper {
    pub name: Name,
    pub wrap: Rc<dyn Fn(GoalTactic) -> GoalTactic>,
}

#[derive(Clone)]
pub struct Claset {
    /// Newest first, as Item_Net.content lists them.
    pub safe_is: Vec<ClassicalRule>,
    pub safe_es: Vec<ClassicalRule>,
    pub unsafe_is: Vec<ClassicalRule>,
    pub unsafe_es: Vec<ClassicalRule>,
    pub swrappers: Vec<Wrapper>,
    pub uwrappers: Vec<Wrapper>,
    pub safe0: NetPair<TaggedRule>,
    pub safep: NetPair<TaggedRule>,
    pub r#unsafe: NetPair<TaggedRule>,
    pub dup: NetPair<TaggedRule>,
}

/// CLASSICAL_DATA: the object logic's rules for the classical reasoner.
pub struct ClassicalData {
    /// P --> Q ==> (~ R ==> P) ==> (Q ==> R) ==> R
    pub imp_elim: Thm,
    /// ~P ==> P ==> R
    pub not_elim: Thm,
    /// ~ P ==> (~ R ==> P) ==> R
    pub swap: Thm,
    /// (~ P ==> P) ==> P
    pub classical: Thm,
    /// The object logic's Trueprop, which Object_Logic.elim_concl looks through.
    pub judgment: Name,
    pub hyp_subst_tacs: Vec<GoalTactic>,
}

#[derive(Clone)]
pub struct ClassicalContext {
    pub claset: Rc<Claset>,
    pub data: Rc<ClassicalData>,
}

pub fn with_claset(context: &ClassicalContext, claset: Claset) -> ClassicalContext {
    ClassicalContext {
        claset: Rc::new(claset),
        data: context.data.clone(),
    }
}

/// classical_rule: strengthens an elimination rule whose conclusion is a variable, so that the
/// negated conclusion becomes available to every case.
fn classical_rule(data: &ClassicalData, rule: &Thm) -> Res<Thm> {
    let concl = if prems_of(rule).is_empty() {
        &rule.prop
    } else {
        strip_assums_concl(&rule.prop)
    };
    let body = match &**concl {
        TermNode::App { fun, arg, .. } if fun.is_const_named(&data.judgment) => arg,
        _ => concl,
    };
    let is_elim = body.is_var()
        && prems_of(rule)
            .iter()
            .any(|premise| aconv(concl, strip_assums_concl(premise)));
    if !is_elim {
        return Ok(rule.clone());
    }
    let strengthened = rs(rule, &data.classical)?;
    let strengthened_concl = strip_assums_concl(&strengthened.prop).clone();
    let is_redundant = move |goal: &Term| {
        if aconv(&strengthened_concl, strip_assums_concl(goal)) {
            return true;
        }
        let hyps = strip_assums_hyp(goal);
        !hyps.is_empty() && hyps[1..].iter().any(|hyp| aconv(hyp, &hyps[0]))
    };
    let Some(thinned) = seq_head(&all_goals(subgoal(move |goal, index| {
        Ok(if index == 1 || is_redundant(goal) {
            eresolve_tac(&[thin_rl()])(index)
        } else {
            all_tac()
        })
    }))(strengthened)?)?
    else {
        return Err(thm_exn("classical_rule"));
    };
    let result = zero_var_indexes(&thinned)?;
    Ok(if aconv(&result.prop, &rule.prop) {
        rule.clone()
    } else {
        result
    })
}

/// swapify: the rules that eliminate ~A from the rules that introduce A.
fn swapify(data: &ClassicalData, rules: &[Thm]) -> Res<Vec<Thm>> {
    let mut result = Vec::new();
    for rule in rules {
        result.extend(without_limits(|| {
            list_of_seq(&biresolution(
                false,
                &[BiresRule {
                    is_elim: false,
                    rule: rule.clone(),
                }],
                2,
                &data.swap,
            )?)
        })?);
    }
    Ok(result)
}

fn dup_intr(data: &ClassicalData, rule: &Thm) -> Res<Thm> {
    zero_var_indexes(&rs(rule, &data.classical)?)
}

/// Drule.rule_by_tactic: runs the tactic on the rule with its variables fixed.
/// Tactic.rule_by_tactic
fn rule_by_tactic(tactic: Tactic, rule: &Thm) -> Res<Thm> {
    let results = trade(
        |fixed| {
            let Some(result) = seq_head(&tactic(fixed)?)? else {
                return Err(thm_exn("rule_by_tactic"));
            };
            Ok(vec![result])
        },
        rule,
    )?;
    zero_var_indexes(&results[0])
}

fn dup_elim(rule: &Thm) -> Res<Thm> {
    let Some(duplicated) =
        without_limits(|| seq_head(&assumption(2, &rsn(rule, 2, &revcut_rl())?)?))?
    else {
        return Err(thm_exn("dup_elim"));
    };
    rule_by_tactic(
        all_goals(Rc::new(|index| {
            or_else(eresolve_tac(&[revcut_rl()])(index), all_tac())
        })),
        &duplicated,
    )
}

/// tag_brls: rules with fewer subgoals first, then the rules added last.
fn tag_rules(start: i64, rules: Vec<BiresRule>) -> Vec<TaggedRule> {
    rules
        .into_iter()
        .enumerate()
        .map(|(index, brule)| TaggedRule {
            tag: 1_000_000 * i64::from(subgoals_of_brl(&brule)) + start + index as i64,
            is_elim: brule.is_elim,
            rule: brule.rule,
        })
        .collect()
}

fn insert_rules(
    counts: (usize, usize),
    intros: &[Thm],
    elims: &[Thm],
    netpair: &NetPair<TaggedRule>,
) -> Res<NetPair<TaggedRule>> {
    let brules = elims
        .iter()
        .map(|rule| BiresRule {
            is_elim: true,
            rule: rule.clone(),
        })
        .chain(intros.iter().map(|rule| BiresRule {
            is_elim: false,
            rule: rule.clone(),
        }))
        .collect();
    tag_rules(-(2 * counts.0 as i64 + counts.1 as i64), brules)
        .into_iter()
        .rev()
        .try_fold(netpair.clone(), |result, tagged| {
            insert_tagged_brl(tagged, &result)
        })
}

fn is_member(rules: &[ClassicalRule], rule: &ClassicalRule) -> bool {
    rules
        .iter()
        .any(|other| aconv(&other.rule.prop, &rule.rule.prop))
}

/// addI: an unsafe introduction rule, which intro: declares.
pub fn add_unsafe_intro(context: &ClassicalContext, rule: &Thm) -> Res<Claset> {
    let claset: &Claset = &context.claset;
    if prems_of(rule).iter().any(|premise| match &**premise {
        TermNode::App { fun, .. } => match &**fun {
            TermNode::Const { name, .. } => name.starts_with("Pure."),
            _ => false,
        },
        _ => false,
    }) {
        return Err(error_exn(
            "Rules with meta-level premises are not supported",
        ));
    }
    let dup = dup_intr(&context.data, rule)?;
    let entry = ClassicalRule {
        rule: rule.clone(),
        internal: rule.clone(),
        swapped: swapify(&context.data, std::slice::from_ref(rule))?,
        dup_swapped: swapify(&context.data, std::slice::from_ref(&dup))?,
        dup,
    };
    if is_member(&claset.unsafe_is, &entry) {
        return Ok(claset.clone());
    }
    let counts = (claset.unsafe_is.len() + 1, claset.unsafe_es.len());
    let r#unsafe = insert_rules(
        counts,
        std::slice::from_ref(&entry.internal),
        &entry.swapped,
        &claset.r#unsafe,
    )?;
    let dup = insert_rules(
        counts,
        std::slice::from_ref(&entry.dup),
        &entry.dup_swapped,
        &claset.dup,
    )?;
    let mut unsafe_is = vec![entry];
    unsafe_is.extend(claset.unsafe_is.iter().cloned());
    Ok(Claset {
        unsafe_is,
        r#unsafe,
        dup,
        ..claset.clone()
    })
}

/// addE: an unsafe elimination rule.
fn add_unsafe_elim(context: &ClassicalContext, rule: &Thm) -> Res<Claset> {
    let claset: &Claset = &context.claset;
    if nprems(rule) < 1 {
        return Err(error_exn("Ill-formed elimination rule"));
    }
    let internal = classical_rule(&context.data, rule)?;
    let entry = ClassicalRule {
        rule: rule.clone(),
        dup: dup_elim(&internal)?,
        internal,
        swapped: Vec::new(),
        dup_swapped: Vec::new(),
    };
    if is_member(&claset.unsafe_es, &entry) {
        return Ok(claset.clone());
    }
    let counts = (claset.unsafe_is.len(), claset.unsafe_es.len() + 1);
    let r#unsafe = insert_rules(
        counts,
        &[],
        std::slice::from_ref(&entry.internal),
        &claset.r#unsafe,
    )?;
    let dup = insert_rules(counts, &[], std::slice::from_ref(&entry.dup), &claset.dup)?;
    let mut unsafe_es = vec![entry];
    unsafe_es.extend(claset.unsafe_es.iter().cloned());
    Ok(Claset {
        unsafe_es,
        r#unsafe,
        dup,
        ..claset.clone()
    })
}

/// addD: an unsafe destruction rule, which dest: declares.
pub fn add_unsafe_dest(context: &ClassicalContext, rule: &Thm) -> Res<Claset> {
    if nprems(rule) < 1 {
        return Err(error_exn("Ill-formed destruction rule"));
    }
    add_unsafe_elim(context, &make_elim(rule)?)
}

/// AList.update: replaces a wrapper of the same name in place, or adds it in front.
fn update_wrappers(wrappers: &[Wrapper], wrapper: Wrapper) -> Vec<Wrapper> {
    if wrappers.iter().any(|other| other.name == wrapper.name) {
        return wrappers
            .iter()
            .map(|other| {
                if other.name == wrapper.name {
                    wrapper.clone()
                } else {
                    other.clone()
                }
            })
            .collect();
    }
    let mut result = vec![wrapper];
    result.extend(wrappers.iter().cloned());
    result
}

/// addSafter: a safe tactic to try after safe_step_tac fails.
pub fn add_safter(claset: &Claset, name: &str, tactic: GoalTactic) -> Claset {
    Claset {
        swrappers: update_wrappers(
            &claset.swrappers,
            Wrapper {
                name: name.into(),
                wrap: Rc::new(move |inner| or_else_goal(inner, tactic.clone())),
            },
        ),
        ..claset.clone()
    }
}

/// addbefore: a tactic to try before the unsafe step tactic, with backtracking.
pub fn addbefore(claset: &Claset, name: &str, tactic: GoalTactic) -> Claset {
    Claset {
        uwrappers: update_wrappers(
            &claset.uwrappers,
            Wrapper {
                name: name.into(),
                wrap: Rc::new(move |inner| append_goal(tactic.clone(), inner)),
            },
        ),
        ..claset.clone()
    }
}

fn app_swrappers(context: &ClassicalContext, tactic: GoalTactic) -> GoalTactic {
    context
        .claset
        .swrappers
        .iter()
        .fold(tactic, |result, wrapper| (wrapper.wrap)(result))
}

pub fn app_wrappers(context: &ClassicalContext, tactic: GoalTactic) -> GoalTactic {
    context
        .claset
        .uwrappers
        .iter()
        .fold(tactic, |result, wrapper| (wrapper.wrap)(result))
}

/// contr_tac: solves a goal that assumes both P and ~P.
fn contr_tac(context: &ClassicalContext) -> GoalTactic {
    then_goal(
        eresolve_tac(std::slice::from_ref(&context.data.not_elim)),
        or_else_goal(eq_assume_tac(), assume_tac()),
    )
}

/// eq_mp_tac: from P --> Q and P, keeps Q, without instantiating variables.
fn eq_mp_tac(context: &ClassicalContext) -> GoalTactic {
    let ematch = ematch_tac(&[context.data.not_elim.clone(), context.data.imp_elim.clone()]);
    Rc::new(move |index| then_tac(ematch(index), eq_assume_tac()(index)))
}

/// safe_step_tac: one safe inference, by matching rather than unification.
fn safe_step_tac(context: &ClassicalContext) -> GoalTactic {
    app_swrappers(
        context,
        first_goal(vec![
            eq_assume_tac(),
            eq_mp_tac(context),
            bimatch_from_nets_tac(context.claset.safe0.clone()),
            first_goal(context.data.hyp_subst_tacs.clone()),
            bimatch_from_nets_tac(context.claset.safep.clone()),
        ]),
    )
}

/// safe_steps_tac: safe inferences on goal index for as long as they apply.
pub fn safe_steps_tac(context: &ClassicalContext) -> GoalTactic {
    let context = context.clone();
    Rc::new(move |index| {
        let context = context.clone();
        repeat_determ1(cond_tac(
            has_fewer_prems(index),
            no_tac(),
            Rc::new(move |state| safe_step_tac(&context)(index)(state)),
        ))
    })
}

/// safe_tac: safe inferences on all goals for as long as they apply.
pub fn safe_tac(context: &ClassicalContext) -> Tactic {
    repeat_determ1(first_goal_tac(safe_steps_tac(context)))
}

fn n_bimatch_from_nets_tac(count: i32, netpair: &NetPair<TaggedRule>) -> GoalTactic {
    biresolution_from_nets_tac(
        move |rules: Vec<TaggedRule>| {
            order_tagged(
                rules
                    .into_iter()
                    .filter(|rule| subgoals_of_brl(rule) == count)
                    .collect(),
            )
        },
        true,
        netpair.clone(),
    )
}

fn eq_contr_tac(context: &ClassicalContext) -> GoalTactic {
    let ematch = ematch_tac(std::slice::from_ref(&context.data.not_elim));
    Rc::new(move |index| then_tac(ematch(index), eq_assume_tac()(index)))
}

fn eq_assume_contr_tac(context: &ClassicalContext) -> GoalTactic {
    or_else_goal(eq_assume_tac(), eq_contr_tac(context))
}

/// bimatch2_tac: two-way branching only where one branch closes at once.
fn bimatch2_tac(context: &ClassicalContext, netpair: &NetPair<TaggedRule>) -> GoalTactic {
    let bimatch = n_bimatch_from_nets_tac(2, netpair);
    let close = eq_assume_contr_tac(context);
    Rc::new(move |index| then_tac(bimatch(index), or_else(close(index), close(index + 1))))
}

fn clarify_step_tac(context: &ClassicalContext) -> GoalTactic {
    app_swrappers(
        context,
        first_goal(vec![
            eq_assume_contr_tac(context),
            bimatch_from_nets_tac(context.claset.safe0.clone()),
            first_goal(context.data.hyp_subst_tacs.clone()),
            n_bimatch_from_nets_tac(1, &context.claset.safep),
            bimatch2_tac(context, &context.claset.safep),
        ]),
    )
}

/// clarify_tac: safe steps that do not split the goal.
pub fn clarify_tac(context: &ClassicalContext) -> GoalTactic {
    select_goal(repeat_determ(clarify_step_tac(context)(1)))
}

pub fn inst0_step_tac(context: &ClassicalContext) -> GoalTactic {
    append_goal(
        assume_tac(),
        append_goal(
            contr_tac(context),
            biresolve_from_nets_tac(context.claset.safe0.clone()),
        ),
    )
}

pub fn instp_step_tac(context: &ClassicalContext) -> GoalTactic {
    biresolve_from_nets_tac(context.claset.safep.clone())
}

fn inst_step_tac(context: &ClassicalContext) -> GoalTactic {
    append_goal(inst0_step_tac(context), instp_step_tac(context))
}

pub fn unsafe_step_tac(context: &ClassicalContext) -> GoalTactic {
    biresolve_from_nets_tac(context.claset.r#unsafe.clone())
}

/// step_tac: a safe step, or else an unsafe one.
fn step_tac(context: &ClassicalContext) -> GoalTactic {
    let context = context.clone();
    Rc::new(move |index| {
        or_else(
            safe_tac(&context),
            app_wrappers(
                &context,
                or_else_goal(inst_step_tac(&context), unsafe_step_tac(&context)),
            )(index),
        )
    })
}

/// Drule.size_of_thm, the sizef of Isabelle/TLA+'s Classical: the size of the proposition with its
/// flex-flex pairs.
fn size_of_thm(thm: &Thm) -> usize {
    thm.tpairs
        .iter()
        .fold(size_of_term(&thm.prop), |size, pair| {
            size + 2 + size_of_term(&pair.0) + size_of_term(&pair.1)
        })
}

/// first_best_tac: best-first search with step_tac on the first goal.
pub fn first_best_tac(context: &ClassicalContext, atomize_rules: &[Thm]) -> Res<GoalTactic> {
    Ok(then_goal(
        atomize_prems_tac(atomize_rules)?,
        select_goal(best_first(
            has_fewer_prems(1),
            size_of_thm,
            first_goal_tac(step_tac(context)),
        )),
    ))
}

#[cfg(test)]
mod tests {
    use crate::provers::testing::check_provers;

    // The expectations are recorded from the TypeScript on the fixture theories' statements and on
    // facts and rules of the logic, under a step limit.
    #[test]
    fn classical_tactics_match_the_typescript() {
        check_provers(include_str!("../../testdata/provers/classical.txt"));
    }
}
