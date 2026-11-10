//! Ported from Isabelle2025's Pure/raw_simplifier.ML, the bottom-up rewriting of terms, and the
//! goal conversions of Pure/conv.ML. Copyright (c) 1986-2025 University of Cambridge, Technische
//! Universitaet Muenchen, and contributors, see LICENSE.
//!
//! (`pure/rewriter.ts`.) The traversal recurses as deep as the term and its premises, so its
//! recursive functions enter a level of `check_stack`.

use std::rc::Rc;

use crate::error::{Error, Exception, Res, error_exn, thm_exn};

use super::conv::{Conversion, gconv_rule, imp_cong_rule};
use super::drule::{imp_cong, swap_prems_eq};
use super::envir::empty_tenv;
use super::interrupt::{check_interrupt, check_stack};
use super::logic::{
    dest_equals, dest_implies, incr_indexes, is_implies, list_implies, mk_implies, strip_imp_concl,
    strip_imp_prems,
};
use super::name::bound_name;
use super::net::match_term_net;
use super::pattern::{MatchEnv, first_order_match_pattern, match_pattern, matches};
use super::raw_simplifier::{
    RawRrule, Rrule, SIMP_DEPTH_LIMIT, SimpContext, Simpset, add_prems, cong_key, cong_name,
    extract_safe_rrules, has_var, insert_rrule, mk_procrule, vars_of,
};
use super::seq::{empty_seq, list_of_seq, seq_head, single_seq};
use super::table::{lookup_table, table_entries};
use super::tactic::resolve_tac;
use super::tactical::{Tactic, all_goals, eq_thm};
use super::term::{
    Term, TermNode, aconv, dummy_t, exists_subterm, list_comb, maxidx_of_term, mk_bound, mk_free,
    mk_var, prop_t, rename_abs, strip_comb, subst_bound,
};
use super::term_ord::term_ord;
use super::thm::{
    Instantiation, Thm, abstract_rule, assume, beta_conversion, combination, eta_conversion,
    flexflex_rule, implies_elim, implies_intr, incr_indexes_thm, instantiate, instantiate_types,
    nprems, reflexive, renamed_prop, symmetric, transitive,
};
use super::types::{empty_ty_env, subst_type};

/// Proves the instance of a conditional rewrite rule, or gives up with `None`.
pub type Prover = Rc<dyn Fn(&SimpContext, &Thm) -> Res<Option<Thm>>>;

/// simple_prover: proves the premises of a rewrite rule with the premises of the simpset.
pub fn simple_prover(context: &SimpContext, thm: &Thm) -> Res<Option<Thm>> {
    seq_head(&all_goals(resolve_tac(&context.simpset.prems))(
        thm.clone(),
    )?)
}

fn is_thm_error(error: &Error) -> bool {
    error.is(Exception::Thm)
}

fn lhs_of(thm: &Thm) -> Res<Term> {
    Ok(dest_equals(&thm.prop)?.0)
}

fn rhs_of(thm: &Thm) -> Res<Term> {
    Ok(dest_equals(&thm.prop)?.1)
}

fn beta_eta_conversion(term: &Term) -> Res<Thm> {
    let beta = beta_conversion(true, term)?;
    transitive(&beta, &eta_conversion(&rhs_of(&beta)?)?)
}

/// Thm.match and Thm.instantiate: instantiates rule so that pattern becomes object.
fn instantiate_match(env: &MatchEnv, rule: &Thm) -> Res<Thm> {
    let typed = instantiate_types(&env.tyenv, rule);
    let insts: Vec<Instantiation> = table_entries(&env.tenv)
        .into_iter()
        .map(|(key, binding)| Instantiation {
            variable: mk_var(key.name, key.index, subst_type(&env.tyenv, &binding.ty)),
            term: binding.term,
        })
        .collect();
    instantiate(&insts, &typed)
}

fn rename_boundvars(pattern: &Term, object: &Term, thm: &Thm) -> Res<Thm> {
    match rename_abs(pattern, object, &thm.prop) {
        None => Ok(thm.clone()),
        Some(renamed) => renamed_prop(renamed, thm),
    }
}

/// check_conv: joins thm and next, allowing for beta and eta differences in the middle term.
fn check_conv(thm: &Thm, next: &Thm) -> Res<Option<Thm>> {
    match transitive(thm, next) {
        Ok(joined) => return Ok(Some(joined)),
        Err(error) if !is_thm_error(&error) => return Err(error),
        Err(_) => {}
    }
    let joined = (|| {
        let normalized = transitive(&symmetric(&beta_eta_conversion(&lhs_of(next)?)?)?, next)?;
        match transitive(thm, &normalized) {
            Err(error) if is_thm_error(&error) => transitive(
                &transitive(thm, &beta_eta_conversion(&rhs_of(thm)?)?)?,
                &normalized,
            ),
            result => result,
        }
    })();
    match joined {
        Ok(joined) => Ok(Some(joined)),
        Err(error) if is_thm_error(&error) => Ok(None),
        Err(error) => Err(error),
    }
}

fn skel0() -> Term {
    thread_local!(static SKEL0: Term = mk_bound(0));
    SKEL0.with(Clone::clone)
}

fn skel_fun(skel: &Term) -> Term {
    match &**skel {
        TermNode::App { fun, .. } => fun.clone(),
        _ => skel0(),
    }
}

fn skel_arg(skel: &Term) -> Term {
    match &**skel {
        TermNode::App { arg, .. } => arg.clone(),
        _ => skel0(),
    }
}

fn skel_body(skel: &Term) -> Term {
    match &**skel {
        TermNode::Abs { body, .. } => body.clone(),
        _ => skel0(),
    }
}

fn is_weak_cong(context: &SimpContext, lhs: &Term) -> bool {
    let weak = &context.simpset.weak_congs;
    if weak.is_empty() {
        return false;
    }
    exists_subterm(
        &mut |sub| match &**sub {
            TermNode::Const { name, .. } => {
                weak.iter().any(|cong| cong.is_const && cong.name == *name)
            }
            TermNode::Free { name, .. } => {
                weak.iter().any(|cong| !cong.is_const && cong.name == *name)
            }
            _ => false,
        },
        lhs,
    )
}

fn uncond_skel(context: &SimpContext, lhs: &Term, rhs: &Term) -> Term {
    if is_weak_cong(context, lhs) {
        skel0()
    } else {
        rhs.clone()
    }
}

fn cond_skel(context: &SimpContext, lhs: &Term, rhs: &Term) -> Term {
    let lhs_vars = vars_of(lhs);
    if vars_of(rhs)
        .iter()
        .all(|variable| has_var(&lhs_vars, variable))
    {
        uncond_skel(context, lhs, rhs)
    } else {
        skel0()
    }
}

struct Rewritten {
    thm: Thm,
    skel: Term,
}

fn is_simple(rrule: &Rrule) -> bool {
    rrule
        .thm
        .prop
        .dest_app()
        .and_then(|(fun, _)| fun.dest_app())
        .is_some_and(|(head, _)| head.is_const_named("Pure.eq"))
}

/// The unconditional rules first, each kind in the reverse of the net's order.
fn sort_rrules(rrules: Vec<Rrule>) -> Vec<Rrule> {
    let (simple, conditional): (Vec<Rrule>, Vec<Rrule>) =
        rrules.into_iter().rev().partition(is_simple);
    simple.into_iter().chain(conditional).collect()
}

/// rewritec's rew: rewrites the eta-contracted term with one rule.
fn rew(
    prover: &Prover,
    maxt: i32,
    context: &SimpContext,
    eta_thm: &Thm,
    rrule: &Rrule,
) -> Res<Option<Rewritten>> {
    let eta_term = rhs_of(eta_thm)?;
    let (rthm, elhs) = if maxt == -1 || !rrule.extra {
        (rrule.thm.clone(), rrule.elhs.clone())
    } else {
        (
            incr_indexes_thm(maxt + 1, &rrule.thm)?,
            incr_indexes(&[], maxt + 1, &rrule.elhs),
        )
    };
    let empty = MatchEnv {
        tyenv: empty_ty_env(),
        tenv: empty_tenv(),
    };
    let env = if rrule.fo {
        first_order_match_pattern(&elhs, &eta_term, &empty)?
    } else {
        match_pattern(&elhs, &eta_term, &empty)?
    };
    let Some(env) = env else {
        return Ok(None);
    };
    let instantiated = instantiate_match(&env, &rename_boundvars(&rrule.lhs, &eta_term, &rthm)?)?;
    let prop = &instantiated.prop;
    let is_unconditional = !is_implies(prop);
    let (lhs, rhs) = dest_equals(strip_imp_concl(prop))?;
    if rrule.perm && term_ord(&rhs, &lhs).is_ge() {
        return Ok(None);
    }
    if is_unconditional {
        let Some(joined) = check_conv(eta_thm, &instantiated)? else {
            return Err(error_exn("check_conv"));
        };
        let (rule_lhs, rule_rhs) = dest_equals(&rrule.thm.prop)?;
        return Ok(Some(Rewritten {
            thm: joined,
            skel: uncond_skel(context, &rule_lhs, &rule_rhs),
        }));
    }
    if context.simpset.depth > SIMP_DEPTH_LIMIT {
        return Ok(None);
    }
    let Some(proved) = prover(context, &instantiated)? else {
        return Ok(None);
    };
    let Some(joined) = check_conv(eta_thm, &proved)? else {
        return Ok(None);
    };
    let (rule_lhs, rule_rhs) = dest_equals(strip_imp_concl(&rrule.thm.prop))?;
    Ok(Some(Rewritten {
        thm: joined,
        skel: cond_skel(context, &rule_lhs, &rule_rhs),
    }))
}

/// rewritec's rews: the first rule that rewrites the term.
fn rews(
    prover: &Prover,
    maxt: i32,
    context: &SimpContext,
    eta_thm: &Thm,
    rrules: &[Rrule],
) -> Res<Option<Rewritten>> {
    for rrule in rrules {
        if let Some(result) = rew(prover, maxt, context, eta_thm, rrule)? {
            return Ok(Some(result));
        }
    }
    Ok(None)
}

/// rewritec: one rewrite step at the root of a term.
fn rewritec(
    prover: &Prover,
    maxt: i32,
    context: &SimpContext,
    term: &Term,
) -> Res<Option<Rewritten>> {
    check_interrupt()?;
    let eta_thm = eta_conversion(term)?;
    let eta_term = rhs_of(&eta_thm)?;
    if let TermNode::App { fun, .. } = &*eta_term
        && fun.is_abs()
    {
        return Ok(Some(Rewritten {
            thm: transitive(&eta_thm, &beta_conversion(false, &eta_term)?)?,
            skel: skel0(),
        }));
    }
    let rewritten = rews(
        prover,
        maxt,
        context,
        &eta_thm,
        &sort_rrules(match_term_net(&context.simpset.rules, &eta_term)),
    )?;
    if rewritten.is_some() {
        return Ok(rewritten);
    }
    for proc in match_term_net(&context.simpset.simprocs, &eta_term) {
        if !matches(&proc.lhs, term, &empty_ty_env(), &empty_tenv())? {
            continue;
        }
        let Some(raw) = (proc.proc)(context, &eta_term)? else {
            continue;
        };
        if let Some(result) = rews(prover, maxt, context, &eta_thm, &mk_procrule(&raw)?)? {
            return Ok(Some(result));
        }
    }
    Ok(None)
}

/// congc: applies a congruence rule to a term. Raises MatchFailure where the rule doesn't match.
fn congc(
    prover: &dyn Fn(&Thm) -> Res<Option<Thm>>,
    maxt: i32,
    cong: &Thm,
    term: &Term,
) -> Res<Option<Thm>> {
    let rthm = incr_indexes_thm(maxt + 1, cong)?;
    let rlhs = dest_equals(strip_imp_concl(&rthm.prop))?.0;
    let env = match_pattern(
        &rlhs,
        term,
        &MatchEnv {
            tyenv: empty_ty_env(),
            tenv: empty_tenv(),
        },
    )?;
    let Some(env) = env else {
        return Err(Error::MatchFailure);
    };
    let instantiated = instantiate_match(&env, &rename_boundvars(&rlhs, term, &rthm)?)?;
    let Some(proved) = prover(&instantiated)? else {
        return Ok(None);
    };
    let Some(joined) = check_conv(&beta_eta_conversion(term)?, &proved)? else {
        return Ok(None);
    };
    let (lhs, rhs) = dest_equals(&joined.prop)?;
    Ok(if aconv(&lhs, &rhs) {
        None
    } else {
        Some(joined)
    })
}

fn transitive1(first: Option<Thm>, second: Option<Thm>) -> Res<Option<Thm>> {
    Ok(match (first, second) {
        (None, second) => second,
        (first, None) => first,
        (Some(first), Some(second)) => Some(transitive(&first, &second)?),
    })
}

fn instantiate_abc(rule: &Thm, term_a: &Term, term_b: &Term, term_c: &Term) -> Res<Thm> {
    instantiate(
        &[
            Instantiation {
                variable: mk_var("A", 0, prop_t()),
                term: term_a.clone(),
            },
            Instantiation {
                variable: mk_var("B", 0, prop_t()),
                term: term_b.clone(),
            },
            Instantiation {
                variable: mk_var("C", 0, prop_t()),
                term: term_c.clone(),
            },
        ],
        rule,
    )
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RewriteMode {
    pub simprem: bool,
    pub useprem: bool,
    pub mutsimp: bool,
}

#[derive(Clone)]
struct PremRules {
    rules: Vec<RawRrule>,
    asm: Option<Thm>,
}

fn reversed<Item: Clone>(items: &[Item]) -> Vec<Item> {
    items.iter().rev().cloned().collect()
}

/// bottomc: bottom-up rewriting with the simpset of the context.
struct Bottom {
    mode: RewriteMode,
    prover: Prover,
    maxidx: i32,
}

impl Bottom {
    /// Isabelle's botc recurses after each rewrite at the top and chains the steps on the way back,
    /// so a simpset that rewrites forever keeps every step until Isabelle runs out of memory. This
    /// loops and chains each step as it goes, which gives the same theorem, so such a simpset runs
    /// into the time limit holding only the latest one.
    fn botc(&self, skel: &Term, context: &SimpContext, term: &Term) -> Res<Option<Thm>> {
        let _depth = check_stack()?;
        let mut chained: Option<Thm> = None;
        let mut current_skel = skel.clone();
        let mut current = term.clone();
        loop {
            if current_skel.is_var() {
                return Ok(chained);
            }
            let sub = self.subc(&current_skel, context, &current)?;
            let subject = match &sub {
                None => current.clone(),
                Some(sub) => rhs_of(sub)?,
            };
            let Some(step) = rewritec(&self.prover, self.maxidx, context, &subject)? else {
                return transitive1(chained, sub);
            };
            chained = transitive1(transitive1(chained, sub)?, Some(step.thm.clone()))?;
            current_skel = step.skel;
            current = rhs_of(&step.thm)?;
        }
    }

    fn try_botc(&self, context: &SimpContext, term: &Term) -> Res<Thm> {
        match self.botc(&skel0(), context, term)? {
            Some(thm) => Ok(thm),
            None => reflexive(term),
        }
    }

    fn appc(&self, skel: &Term, context: &SimpContext, term: &Term) -> Res<Option<Thm>> {
        let Some((fun, arg)) = term.dest_app() else {
            unreachable!("appc on an application")
        };
        let fun_thm = self.botc(&skel_fun(skel), context, fun)?;
        let arg_thm = self.botc(&skel_arg(skel), context, arg)?;
        if let Some(fun_thm) = fun_thm {
            let arg_thm = match arg_thm {
                Some(arg_thm) => arg_thm,
                None => reflexive(arg)?,
            };
            return Ok(Some(combination(&fun_thm, &arg_thm)?));
        }
        match arg_thm {
            None => Ok(None),
            Some(arg_thm) => Ok(Some(combination(&reflexive(fun)?, &arg_thm)?)),
        }
    }

    fn subc(&self, skel: &Term, context: &SimpContext, term: &Term) -> Res<Option<Thm>> {
        let _depth = check_stack()?;
        if let TermNode::Abs { name, ty, body, .. } = &**term {
            let variable = mk_free(bound_name(context.bounds), ty.clone());
            let body = subst_bound(&variable, body);
            let inner_context = SimpContext {
                bounds: context.bounds + 1,
                ..context.clone()
            };
            let inner = self.botc(&skel_body(skel), &inner_context, &body)?;
            return match inner {
                None => Ok(None),
                Some(inner) => Ok(Some(abstract_rule(name, &variable, &inner)?)),
            };
        }
        let Some((head, _)) = term.dest_app() else {
            return Ok(None);
        };
        if let Some((imp, _)) = head.dest_app()
            && imp.is_const_named("Pure.imp")
        {
            return self.impc(term, context);
        }
        if head.is_abs() {
            let beta = beta_conversion(false, term)?;
            let rest = self.subc(&skel0(), context, &rhs_of(&beta)?)?;
            return match rest {
                None => Ok(Some(beta)),
                Some(rest) => Ok(Some(transitive(&beta, &rest)?)),
            };
        }
        let (head_term, args) = strip_comb(head);
        let cong = cong_name(&head_term)
            .and_then(|name| lookup_table(&context.simpset.congs, &cong_key(&name)).cloned());
        let Some(cong) = cong else {
            return self.appc(skel, context, term);
        };
        let congruence = || -> Res<Option<Thm>> {
            let thm = congc(
                &|rule| (self.prover)(context, rule),
                self.maxidx,
                &cong,
                term,
            )?;
            let result = match &thm {
                None => term.clone(),
                Some(thm) => rhs_of(thm)?,
            };
            let (left, right) = match result.dest_app() {
                Some((fun, arg)) => (fun.clone(), arg.clone()),
                None => {
                    let (fun, arg) = term.dest_app().expect("an application");
                    (fun.clone(), arg.clone())
                }
            };
            let cong_skel = list_comb(
                head_term.clone(),
                &args
                    .iter()
                    .map(|_| mk_var("", 0, dummy_t()))
                    .collect::<Vec<_>>(),
            );
            let inner = self.botc(&cong_skel, context, &left)?;
            match inner {
                None => Ok(thm),
                Some(inner) => transitive1(thm, Some(combination(&inner, &reflexive(&right)?)?)),
            }
        };
        match congruence() {
            Err(Error::MatchFailure) => self.appc(skel, context, term),
            result => result,
        }
    }

    fn impc(&self, term: &Term, context: &SimpContext) -> Res<Option<Thm>> {
        if self.mode.mutsimp {
            self.mut_impc0(&[], term, &[], context)
        } else {
            self.nonmut_impc(term, context)
        }
    }

    fn rules_of_prem(&self, prem: &Term, context: &SimpContext) -> Res<(PremRules, SimpContext)> {
        if maxidx_of_term(prem, -1) != -1 {
            return Ok((
                PremRules {
                    rules: Vec::new(),
                    asm: None,
                },
                context.clone(),
            ));
        }
        let asm = assume(prem.clone())?;
        Ok((
            PremRules {
                rules: extract_safe_rrules(context, &asm)?,
                asm: Some(asm),
            },
            context.clone(),
        ))
    }

    fn add_rrules(&self, rules: &[PremRules], context: &SimpContext) -> SimpContext {
        let simpset: Simpset = rules.iter().fold(context.simpset.clone(), |current, prem| {
            prem.rules
                .iter()
                .fold(current, |inner, raw| insert_rrule(raw, &inner))
        });
        let asms: Vec<Thm> = rules.iter().filter_map(|prem| prem.asm.clone()).collect();
        SimpContext {
            simpset: add_prems(&asms, &simpset),
            ..context.clone()
        }
    }

    fn disch(&self, is_reordered: bool, prem: &Term, eq: &Thm) -> Res<Thm> {
        let (lhs, rhs) = dest_equals(&eq.prop)?;
        let discharged = implies_elim(
            &instantiate_abc(&imp_cong(), prem, &lhs, &rhs)?,
            &implies_intr(prem, eq)?,
        )?;
        if !is_reordered {
            return Ok(discharged);
        }
        let (prem_a, concl) = dest_implies(&lhs)?;
        let (prem_b, _) = dest_implies(&rhs)?;
        transitive(
            &transitive(
                &instantiate_abc(&swap_prems_eq(), &prem_a, prem, &concl)?,
                &discharged,
            )?,
            &instantiate_abc(&swap_prems_eq(), prem, &prem_b, &concl)?,
        )
    }

    fn rebuild(
        &self,
        prems: &[Term],
        concl: &Term,
        rules: &[PremRules],
        context: &SimpContext,
        eq: Option<Thm>,
    ) -> Res<Option<Thm>> {
        let _depth = check_stack()?;
        let Some((prem, rest)) = prems.split_first() else {
            return Ok(eq);
        };
        let later_rules = rules.get(1..).unwrap_or(&[]);
        let inner = self.add_rrules(&reversed(later_rules), context);
        let next_concl = mk_implies(
            prem.clone(),
            match &eq {
                None => concl.clone(),
                Some(eq) => rhs_of(eq)?,
            },
        );
        let dprem = match &eq {
            None => None,
            Some(eq) => Some(self.disch(false, prem, eq)?),
        };
        let Some(step) = rewritec(&self.prover, self.maxidx, &inner, &next_concl)? else {
            return self.rebuild(rest, &next_concl, later_rules, context, dprem);
        };
        let Some(joined) = transitive1(dprem, Some(step.thm.clone()))? else {
            return Err(error_exn("rebuild"));
        };
        let folded = rest
            .iter()
            .try_fold(joined, |current, item| self.disch(false, item, &current))?;
        let simplified = self.mut_impc0(
            &reversed(rest),
            &rhs_of(&step.thm)?,
            &reversed(later_rules),
            context,
        )?;
        transitive1(Some(folded), simplified)
    }

    fn mut_impc0(
        &self,
        prems: &[Term],
        concl: &Term,
        rules: &[PremRules],
        context: &SimpContext,
    ) -> Res<Option<Thm>> {
        let new_prems = strip_imp_prems(concl);
        let mut current = context.clone();
        let mut new_rules = Vec::new();
        for prem in &new_prems {
            let (rule, next) = self.rules_of_prem(prem, &current)?;
            new_rules.push(rule);
            current = next;
        }
        self.mut_impc(
            [prems, &new_prems].concat(),
            strip_imp_concl(concl),
            [rules, &new_rules].concat(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
            &current,
            -1,
            -1,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn mut_impc(
        &self,
        prems: Vec<Term>,
        concl: &Term,
        rules: Vec<PremRules>,
        done_prems: Vec<Term>,
        done_rules: Vec<PremRules>,
        eqns: Vec<Option<Thm>>,
        context: &SimpContext,
        changed: i32,
        count: i32,
    ) -> Res<Option<Thm>> {
        let _depth = check_stack()?;
        if prems.is_empty() {
            let mut folded: Option<Thm> = None;
            for (index, eq1) in eqns.iter().enumerate() {
                let discharged = match &folded {
                    None => None,
                    Some(eq2) => Some(self.disch(false, &done_prems[index], eq2)?),
                };
                folded = transitive1(eq1.clone(), discharged)?;
            }
            let rest = if changed > 0 {
                self.mut_impc(
                    reversed(&done_prems),
                    concl,
                    reversed(&done_rules),
                    Vec::new(),
                    Vec::new(),
                    Vec::new(),
                    context,
                    -1,
                    changed,
                )?
            } else {
                let simplified = self.botc(
                    &skel0(),
                    &self.add_rrules(&reversed(&done_rules), context),
                    concl,
                )?;
                self.rebuild(&done_prems, concl, &done_rules, context, simplified)?
            };
            return transitive1(folded, rest);
        }
        let mut other_prems = prems;
        let prem = other_prems.remove(0);
        let mut other_rules = rules;
        let rule = other_rules.remove(0);
        let simplified = if count == 0 {
            None
        } else {
            let known = [reversed(&done_rules), other_rules.clone()].concat();
            self.botc(&skel0(), &self.add_rrules(&known, context), &prem)?
        };
        let Some(simplified) = simplified else {
            return self.mut_impc(
                other_prems,
                concl,
                other_rules,
                [vec![prem], done_prems].concat(),
                [vec![rule], done_rules].concat(),
                [vec![None], eqns].concat(),
                context,
                changed,
                if count == 0 { 0 } else { count - 1 },
            );
        };
        let new_prem = rhs_of(&simplified)?;
        let index = 1 + simplified.hyps.iter().fold(-1, |result, hyp| {
            let position = other_prems
                .iter()
                .position(|other| aconv(other, hyp))
                .map_or(-1, |position| position as i32);
            result.max(position)
        });
        let index = index as usize;
        let (new_rule, next) = self.rules_of_prem(&new_prem, context)?;
        let eqn = other_prems[..index].iter().rev().try_fold(
            imp_cong_rule(
                &simplified,
                &reflexive(&list_implies(&other_prems[index..], concl.clone()))?,
            )?,
            |current, item| self.disch(true, item, &current),
        )?;
        let done_count = done_prems.len() as i32;
        self.mut_impc(
            other_prems,
            concl,
            other_rules,
            [vec![new_prem], done_prems].concat(),
            [vec![new_rule], done_rules].concat(),
            [vec![Some(eqn)], eqns].concat(),
            &next,
            done_count,
            -1,
        )
    }

    fn nonmut_impc(&self, term: &Term, context: &SimpContext) -> Res<Option<Thm>> {
        let (prem, conc) = dest_implies(term)?;
        let first = if self.mode.simprem {
            self.botc(&skel0(), context, &prem)?
        } else {
            None
        };
        let simplified_prem = match &first {
            None => prem.clone(),
            Some(first) => rhs_of(first)?,
        };
        let inner = if self.mode.useprem {
            self.add_rrules(&[self.rules_of_prem(&simplified_prem, context)?.0], context)
        } else {
            context.clone()
        };
        let second = self.botc(&skel0(), &inner, &conc)?;
        let Some(second) = second else {
            return match first {
                None => Ok(None),
                Some(first) => Ok(Some(imp_cong_rule(&first, &reflexive(&conc)?)?)),
            };
        };
        let discharged = self.disch(false, &simplified_prem, &second)?;
        match first {
            None => Ok(Some(discharged)),
            Some(first) => Ok(Some(transitive(
                &imp_cong_rule(&first, &reflexive(&conc)?)?,
                &discharged,
            )?)),
        }
    }
}

/// Drule.flexflex_unique
fn flexflex_unique(thm: &Thm) -> Res<Thm> {
    if thm.tpairs.is_empty() {
        return Ok(thm.clone());
    }
    let results = list_of_seq(&flexflex_rule(thm)?)?;
    let distinct: Vec<&Thm> = results
        .iter()
        .enumerate()
        .filter(|(index, result)| {
            results.iter().position(|other| eq_thm(other, result)) == Some(*index)
        })
        .map(|(_, result)| result)
        .collect();
    match distinct.as_slice() {
        [unique] => Ok((*unique).clone()),
        [] => Err(thm_exn("flexflex_unique: impossible constraints")),
        _ => Err(thm_exn("flexflex_unique: multiple unifiers")),
    }
}

/// rewrite_cterm: proves term == term' by rewriting.
pub fn rewrite_cterm(
    mode: RewriteMode,
    prover: Prover,
    context: &SimpContext,
    term: &Term,
) -> Res<Thm> {
    let inner = SimpContext {
        simpset: Simpset {
            depth: context.simpset.depth + 1,
            ..context.simpset.clone()
        },
        ..context.clone()
    };
    let wrapped: Prover = Rc::new(move |current, thm| match prover(current, thm)? {
        None => Ok(None),
        Some(result) => Ok(Some(flexflex_unique(&result)?)),
    });
    Bottom {
        mode,
        prover: wrapped,
        maxidx: maxidx_of_term(term, -1),
    }
    .try_botc(&inner, term)
}

/// rewrite_cterm as a conversion.
pub(crate) fn rewrite_conv(mode: RewriteMode, prover: Prover, context: SimpContext) -> Conversion {
    Rc::new(move |term| rewrite_cterm(mode, prover.clone(), &context, term))
}

pub fn generic_rewrite_goal_tac(
    mode: RewriteMode,
    prover: Prover,
    context: &SimpContext,
    index: i32,
) -> Tactic {
    let convert = rewrite_conv(mode, prover, context.clone());
    Rc::new(move |state: Thm| {
        if index > 0 && index as usize <= nprems(&state) {
            Ok(single_seq(gconv_rule(&convert, index, &state)?))
        } else {
            Ok(empty_seq())
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pure::interrupt::with_limits;
    use crate::pure::raw_simplifier::empty_simpset;
    use crate::pure::term::{fun_t, mk_app, mk_type};
    use prove_decide::Limits;

    /// Rewrites f (f (... a)) nested depth times with the empty simpset: the steps it took, or
    /// the error.
    fn rewrite_nested(depth: usize) -> Result<u64, Error> {
        let c = mk_type("PredicateLogic.c", Vec::new());
        let f = mk_free("f", fun_t(c.clone(), c.clone()));
        let term = (0..depth).fold(mk_free("a", c), |term, _| mk_app(f.clone(), term));
        let context = SimpContext {
            simpset: empty_simpset(),
            bounds: 0,
        };
        let mode = RewriteMode {
            simprem: true,
            useprem: true,
            mutsimp: true,
        };
        let limits = Limits::new(f64::INFINITY, None, None);
        with_limits(&limits, || {
            rewrite_cterm(mode, Rc::new(simple_prover), &context, &term)
        })?;
        Ok(limits.steps())
    }

    // The TypeScript (under Node 22) takes 12001 steps at depth 6000, and overflows JavaScript's
    // stack at depth 12000, where this gives up with Error::Stack. The thread has the stack that
    // prove-it-host gives a decision.
    #[test]
    fn gives_up_on_a_term_too_deep_to_rewrite() {
        let results = std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(|| (rewrite_nested(6000), rewrite_nested(12000)))
            .unwrap()
            .join()
            .unwrap();
        assert_eq!(results, (Ok(12001), Err(Error::Stack)));
    }
}
