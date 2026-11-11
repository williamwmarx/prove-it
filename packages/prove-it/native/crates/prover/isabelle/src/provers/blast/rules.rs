//! Ported from Isabelle2025's Provers/blast.ML. Copyright (c) 1986-2025 University of Cambridge,
//! Technische Universitaet Muenchen, and contributors, see LICENSE.
//!
//! Conversion of the classical rules to tableau operations, each with the Isabelle tactic that
//! replays it during proof reconstruction.
//!
//! (`provers/blast/rules.ts`.) The TypeScript's goal tactics for replay may raise when given their
//! goal index (rev_dup_elim and dup_intr run then), so a replay tactic returns a `Res`.

use std::cell::{OnceCell, RefCell};
use std::rc::Rc;

use crate::error::{Res, error_exn};
use crate::pure::drule::{revcut_rl, zero_var_indexes};
use crate::pure::interrupt::without_limits;
use crate::pure::net::unify_term_net;
use crate::pure::seq::{seq_head, single_seq};
use crate::pure::tactic::{
    NetPair, TaggedRule, ematch_tac, eresolve_tac, match_tac, order_list, resolve_tac, rotate_tac,
};
use crate::pure::tactical::{GoalTactic, Tactic, then_goal, then_tac};
use crate::pure::term::{dummy_t, mk_app, mk_const};
use crate::pure::thm::{Thm, assumption, rotate_rule, rs, rsn};

use super::state::{BlastState, gensym, thm_address};
use super::term::{
    BlastTerm, BlastTermNode, FALSE_NAME, GOAL_NAME, Template, VarRef, blast_subst_bound,
    dest_const_app, from_term, instantiate_template, mk_blast_const, mk_blast_skolem, mk_blast_var,
    mk_goal, strip_blast_imp_concl, strip_blast_imp_prems, to_template, to_term,
};

/// A goal tactic of the replay, which may raise when given its goal index.
pub type ReplayTactic = Rc<dyn Fn(i32) -> Res<Tactic>>;

/// A goal tactic that can't raise, as a replay tactic.
pub fn replay_tactic(tactic: GoalTactic) -> ReplayTactic {
    Rc::new(move |index| Ok(tactic(index)))
}

/// Blast converts each rule it looks up afresh, with fresh variables and Skolem terms. This
/// converts each rule once, numbering them: concl is the conclusion's variable, which conversion
/// sets to *False*, and skolems counts the Skolem terms, which take fresh names in this order. An
/// ill-formed rule has no major premise, but still takes the names its conversion took.
pub struct RuleTemplate {
    pub count: usize,
    pub concl: Option<usize>,
    pub skolems: usize,
    pub major: Option<Template>,
    pub prems: Vec<Vec<Template>>,
}

/// The conclusion becomes the goal or the negated assumption *False*: delete it. A premise without
/// it is ill-formed and could make reconstruction fail.
fn delete_concl(state: &BlastState, prems: Vec<BlastTerm>) -> Option<Vec<BlastTerm>> {
    let position = prems.iter().position(|prem| {
        let BlastTermNode::App { fun, arg } = &**prem else {
            return false;
        };
        let BlastTermNode::Const { name, .. } = &**fun else {
            return false;
        };
        let BlastTermNode::Var { var_ref } = &**arg else {
            return false;
        };
        var_ref.value().is_some_and(
            |value| matches!(&*value, BlastTermNode::Const { name, .. } if &**name == FALSE_NAME),
        ) && (&**name == GOAL_NAME || *name == state.context.data.not_name)
    })?;
    let mut prems = prems;
    prems.remove(position);
    Some(prems)
}

/// Skolemizes a premise with placeholder Skolem terms, adding them to skolems in the order that
/// blast names them.
fn sko_prem(skolems: &mut Vec<BlastTerm>, prem: &BlastTerm) -> BlastTerm {
    let Some(body) = dest_const_app(prem, "Pure.all") else {
        return prem.clone();
    };
    let BlastTermNode::Abs { body, .. } = &**body else {
        return prem.clone();
    };
    let skolem = mk_blast_skolem("", Rc::from([]));
    skolems.push(skolem.clone());
    sko_prem(skolems, &blast_subst_bound(&skolem, body))
}

fn ill_formed(skolems: usize) -> RuleTemplate {
    RuleTemplate {
        count: 0,
        concl: None,
        skolems,
        major: None,
        prems: Vec::new(),
    }
}

/// The goal and the assumptions of a skolemized premise.
fn goal_and_prems(trueprop: &str, skolemized: &BlastTerm) -> Vec<BlastTerm> {
    let mut items = vec![mk_goal(strip_blast_imp_concl(trueprop, skolemized))];
    items.extend(strip_blast_imp_prems(trueprop, skolemized));
    items
}

/// fromRule's convertRule, which expects an elimination rule to have a formula variable as its
/// conclusion.
fn make_elim_template(state: &BlastState, rule: &Thm) -> Res<RuleTemplate> {
    let trueprop = &*state.context.data.trueprop;
    let term = from_term(&state.context.logic.consts, &rule.prop)?;
    let mut refs: Vec<VarRef> = Vec::new();
    to_template(&mut refs, &[], &term);
    let prems = strip_blast_imp_prems(trueprop, &term);
    let concl = strip_blast_imp_concl(trueprop, &term);
    let BlastTermNode::Var { var_ref: concl_ref } = &*concl else {
        return Ok(ill_formed(0));
    };
    if prems.is_empty() {
        return Ok(ill_formed(0));
    }
    concl_ref.set_value(Some(mk_blast_const(FALSE_NAME, Vec::new())));
    let mut skolems: Vec<BlastTerm> = Vec::new();
    let mut converted: Vec<Vec<BlastTerm>> = Vec::new();
    for prem in &prems[1..] {
        let skolemized = sko_prem(&mut skolems, prem);
        let Some(deleted) = delete_concl(state, goal_and_prems(trueprop, &skolemized)) else {
            return Ok(ill_formed(skolems.len()));
        };
        converted.push(deleted);
    }
    let count = refs.len();
    let concl = refs
        .iter()
        .position(|other| VarRef::ptr_eq(other, concl_ref));
    let major = to_template(&mut refs, &skolems, &prems[0]);
    let prems = converted
        .iter()
        .map(|prem| {
            prem.iter()
                .map(|item| to_template(&mut refs, &skolems, item))
                .collect()
        })
        .collect();
    Ok(RuleTemplate {
        count,
        concl,
        skolems: skolems.len(),
        major: Some(major),
        prems,
    })
}

/// fromIntrRule's conversion.
fn make_intro_template(state: &BlastState, rule: &Thm) -> Res<RuleTemplate> {
    let trueprop = &*state.context.data.trueprop;
    let term = from_term(&state.context.logic.consts, &rule.prop)?;
    let mut refs: Vec<VarRef> = Vec::new();
    to_template(&mut refs, &[], &term);
    let mut skolems: Vec<BlastTerm> = Vec::new();
    let converted: Vec<Vec<BlastTerm>> = strip_blast_imp_prems(trueprop, &term)
        .iter()
        .map(|prem| {
            let skolemized = sko_prem(&mut skolems, prem);
            goal_and_prems(trueprop, &skolemized)
        })
        .collect();
    let count = refs.len();
    let major = to_template(
        &mut refs,
        &skolems,
        &mk_goal(strip_blast_imp_concl(trueprop, &term)),
    );
    let prems = converted
        .iter()
        .map(|prem| {
            prem.iter()
                .map(|item| to_template(&mut refs, &skolems, item))
                .collect()
        })
        .collect();
    Ok(RuleTemplate {
        count,
        concl: None,
        skolems: skolems.len(),
        major: Some(major),
        prems,
    })
}

/// Like dup_elim, but puts the duplicated major premise first.
fn rev_dup_elim(rule: &Thm) -> Res<Thm> {
    let result = without_limits(|| seq_head(&assumption(2, &rsn(rule, 2, &revcut_rl())?)?))?;
    result.ok_or_else(|| error_exn("rev_dup_elim: Seq.hd"))
}

fn count_new_hyps(prem: &[BlastTerm]) -> usize {
    prem.iter()
        .filter(|term| dest_const_app(term, GOAL_NAME).is_none())
        .count()
}

/// Rotates the assumptions in all new subgoals for the LIFO discipline.
fn rot_subgoals_tac(is_rotated: bool, prems: Rc<Vec<Vec<BlastTerm>>>, index: i32) -> Tactic {
    Rc::new(move |state| {
        let counts: Vec<usize> = if is_rotated {
            prems.iter().map(|prem| count_new_hyps(prem)).collect()
        } else {
            Vec::new()
        };
        let mut current = state;
        for (offset, count) in counts.into_iter().enumerate() {
            if count != 0 {
                current = rotate_rule(-(count as i32), index + offset as i32, &current)?;
            }
        }
        Ok(single_seq(current))
    })
}

/// Resolution or matching: if the inference updated the branch, the proof state may be updated.
/// Matching keeps the tactics more deterministic in the presence of variables.
fn emtac(is_updated: bool, rule: Thm) -> GoalTactic {
    if is_updated {
        eresolve_tac(&[rule])
    } else {
        ematch_tac(&[rule])
    }
}

fn rmtac(is_updated: bool, rule: Thm) -> GoalTactic {
    if is_updated {
        resolve_tac(&[rule])
    } else {
        match_tac(&[rule])
    }
}

fn elim_rule_tactic(
    rule: Thm,
    prems: Rc<Vec<Vec<BlastTerm>>>,
    is_updated: bool,
    is_dup: bool,
    is_rotated: bool,
) -> ReplayTactic {
    Rc::new(move |index| {
        let rule = if is_dup {
            rev_dup_elim(&rule)?
        } else {
            rule.clone()
        };
        Ok(then_tac(
            emtac(is_updated, rule)(index),
            rot_subgoals_tac(is_rotated, prems.clone(), index),
        ))
    })
}

fn intr_rule_tactic(
    classical: Thm,
    rule: Thm,
    prems: Rc<Vec<Vec<BlastTerm>>>,
    is_updated: bool,
    is_dup: bool,
    is_rotated: bool,
) -> ReplayTactic {
    Rc::new(move |index| {
        let rule = if is_dup {
            zero_var_indexes(&rs(&rule, &classical)?)?
        } else {
            rule.clone()
        };
        Ok(then_tac(
            rmtac(is_updated, rule)(index),
            rot_subgoals_tac(is_rotated, prems.clone(), index),
        ))
    })
}

/// A tableau rule: the formula it applies to, the formulae of each new branch, and the tactic
/// for the flags upd (the inference updated the branch), dup (duplicate the formula) and rot
/// (rotate the new hypotheses).
///
/// The TypeScript's InstantiatedRule, its only kind: a tableau rule from a rule's template. Blast
/// tries the rules in order until one's major premise unifies, and often only checks that a rule
/// exists, so this instantiates the template with fresh variables only when the major premise is
/// used, and the premises only when they are.
pub struct TableauRule {
    classical: Thm,
    rule: Thm,
    is_intro: bool,
    template: Rc<RuleTemplate>,
    skolems: Vec<BlastTerm>,
    vars: OnceCell<Vec<BlastTerm>>,
    instantiated_major: OnceCell<BlastTerm>,
    instantiated_prems: RefCell<Option<Rc<Vec<Vec<BlastTerm>>>>>,
}

impl TableauRule {
    /// Fresh variables for the template's, with the conclusion's set to *False*.
    fn get_vars(&self) -> &[BlastTerm] {
        self.vars.get_or_init(|| {
            (0..self.template.count)
                .map(|index| {
                    mk_blast_var(VarRef::new(if Some(index) == self.template.concl {
                        Some(mk_blast_const(FALSE_NAME, Vec::new()))
                    } else {
                        None
                    }))
                })
                .collect()
        })
    }

    pub fn major(&self) -> BlastTerm {
        self.instantiated_major
            .get_or_init(|| {
                let template = self
                    .template
                    .major
                    .as_ref()
                    .unwrap_or_else(|| unreachable!("a tableau rule has a major premise"));
                instantiate_template(self.get_vars(), &self.skolems, template)
            })
            .clone()
    }

    pub fn prems(&self) -> Rc<Vec<Vec<BlastTerm>>> {
        if let Some(prems) = &*self.instantiated_prems.borrow() {
            return prems.clone();
        }
        let prems: Rc<Vec<Vec<BlastTerm>>> = Rc::new(
            self.template
                .prems
                .iter()
                .map(|prem| {
                    prem.iter()
                        .map(|template| {
                            instantiate_template(self.get_vars(), &self.skolems, template)
                        })
                        .collect()
                })
                .collect(),
        );
        *self.instantiated_prems.borrow_mut() = Some(prems.clone());
        prems
    }

    /// Since unsafe rules are delayed, dup is always false for introduction rules.
    pub fn tactic(&self, is_updated: bool, is_dup: bool, is_rotated: bool) -> ReplayTactic {
        if self.is_intro {
            intr_rule_tactic(
                self.classical.clone(),
                self.rule.clone(),
                self.prems(),
                is_updated,
                is_dup,
                is_rotated,
            )
        } else {
            elim_rule_tactic(
                self.rule.clone(),
                self.prems(),
                is_updated,
                is_dup,
                is_rotated,
            )
        }
    }
}

/// fromRule or fromIntrRule: None for an ill-formed rule. Its Skolem terms take their names now,
/// as blast converts all the rules it looks up at once.
fn instantiate_rule(
    state: &BlastState,
    vars: &[VarRef],
    rule: &Thm,
    is_intro: bool,
) -> Res<Option<TableauRule>> {
    let context = &state.context;
    let templates = if is_intro {
        &context.intro_templates
    } else {
        &context.elim_templates
    };
    let known = templates
        .borrow()
        .get(&thm_address(rule))
        .map(|entry| entry.1.clone());
    let template = match known {
        Some(template) => template,
        None => {
            let template = Rc::new(if is_intro {
                make_intro_template(state, rule)?
            } else {
                make_elim_template(state, rule)?
            });
            templates
                .borrow_mut()
                .insert(thm_address(rule), (rule.clone(), template.clone()));
            template
        }
    };
    let args: Rc<[VarRef]> = vars.into();
    let skolems: Vec<BlastTerm> = (0..template.skolems)
        .map(|_| mk_blast_skolem(gensym(state, "S"), args.clone()))
        .collect();
    if template.major.is_none() {
        return Ok(None);
    }
    Ok(Some(TableauRule {
        classical: context.data.classical.clone(),
        rule: rule.clone(),
        is_intro,
        template,
        skolems,
        vars: OnceCell::new(),
        instantiated_major: OnceCell::new(),
        instantiated_prems: RefCell::new(None),
    }))
}

/// Too flexible assertions or goals, such as those of (!!P. ~P) ==> 0 == 1.
fn is_var_form(state: &BlastState, term: &BlastTerm) -> bool {
    matches!(&**term, BlastTermNode::Var { .. })
        || dest_const_app(term, &state.context.data.not_name)
            .is_some_and(|arg| matches!(&**arg, BlastTermNode::Var { .. }))
}

fn order_rules(rules: &[TaggedRule]) -> Vec<Thm> {
    order_list(
        &rules
            .iter()
            .map(|rule| (rule.tag, rule.rule.clone()))
            .collect::<Vec<_>>(),
    )
}

pub fn net_mk_rules(
    state: &BlastState,
    formula: &BlastTerm,
    vars: &[VarRef],
    netpairs: &[&NetPair<TaggedRule>],
) -> Res<Vec<TableauRule>> {
    let goal = dest_const_app(formula, GOAL_NAME);
    if goal.is_none() && is_var_form(state, formula) {
        return Ok(Vec::new());
    }
    let trueprop = mk_const(state.context.data.trueprop.clone(), dummy_t());
    let pattern = match goal {
        None => mk_app(trueprop, to_term(3, formula)),
        Some(goal) => mk_app(trueprop, to_term(2, goal)),
    };
    let mut matched: Vec<TaggedRule> = Vec::new();
    for netpair in netpairs {
        matched.extend(unify_term_net(
            if goal.is_none() {
                &netpair.elim
            } else {
                &netpair.intro
            },
            &pattern,
        ));
    }
    let mut rules = Vec::new();
    for rule in order_rules(&matched) {
        if let Some(instantiated) = instantiate_rule(state, vars, &rule, goal.is_some())? {
            rules.push(instantiated);
        }
    }
    Ok(rules)
}

/// Converts *Goal* to a negated assumption in first position.
pub fn neg_of_goal_tac(state: &BlastState) -> GoalTactic {
    then_goal(
        resolve_tac(std::slice::from_ref(&state.context.data.ccontr)),
        rotate_tac(-1),
    )
}
