//! Ported from Isabelle2025's Provers/hypsubst.ML. Copyright (c) 1986-2025 University of
//! Cambridge, Technische Universitaet Muenchen, and contributors, see LICENSE.
//!
//! Substitution using an equality assumption x = t: eliminates x from the subgoal.
//!
//! (`provers/hypsubst.ts`.) The TypeScript's context, the limits and the data, is the data alone,
//! since the limits are installed for the thread.

use std::rc::Rc;

use crate::error::{Error, Exception, Res, term_exn, thm_exn, type_exn};
use crate::pure::drule::{asm_rl, comp_incr, revcut_rl, thin_rl, zero_var_indexes};
use crate::pure::envir::{aeconv, eta_contract};
use crate::pure::interrupt::without_limits;
use crate::pure::logic::{occs, strip_assums_concl, strip_assums_hyp, strip_params};
use crate::pure::name::is_bound_name;
use crate::pure::raw_simplifier::{MkRews, SimpContext, Simpset, empty_simpset};
use crate::pure::seq::list_of_seq;
use crate::pure::simplifier::asm_lr_simp_tac;
use crate::pure::tactic::{compose_tac, ematch_tac, eresolve_tac, resolve_tac, rotate_tac};
use crate::pure::tactical::{
    GoalTactic, Tactic, all_tac, determ, every, first_goal, no_tac, repeat_determ_n,
    repeat_determ1, subgoal, then_tac,
};
use crate::pure::term::{
    HAS_VAR, Term, TermNode, Typ, abstract_over, binder_types, body_type, exists_type, fastype_of1,
    flags_of, fun_ts, head_of, incr_boundvars, loose_bvar1, maxidx_of_typ, mk_abs, mk_bound,
    mk_var, subst_bounds,
};
use crate::pure::thm::{
    Instantiation, Thm, assumption, instantiate, instantiate_types, lift_rule, prem_of, prems_of,
    rs, rsn, symmetric,
};
use crate::pure::types::{empty_ty_env, match_types, subst_type};

/// What hypsubst needs of the object logic. The destructors raise TERM on a term of another form.
pub struct HypsubstData {
    pub dest_trueprop: Box<dyn Fn(&Term) -> Res<Term>>,
    pub dest_eq: Box<dyn Fn(&Term) -> Res<(Term, Term)>>,
    pub dest_imp: Box<dyn Fn(&Term) -> Res<(Term, Term)>>,
    pub eq_reflection: Thm,
    pub rev_eq_reflection: Thm,
    pub imp_intr: Thm,
    pub rev_mp: Thm,
    pub subst: Thm,
    pub sym: Thm,
    pub thin_refl: Thm,
}

/// The simplifier turns bound variables into special free variables; any bound variable will do.
fn inspect_contract(term: &Term) -> Term {
    let contracted = eta_contract(term);
    if matches!(&*contracted, TermNode::Free { name, .. } if is_bound_name(name)) {
        return mk_bound(0);
    }
    contracted
}

fn has_vars(term: &Term) -> bool {
    flags_of(term) & HAS_VAR != 0
}

fn has_tvars(term: &Term) -> bool {
    exists_type(&mut |ty| maxidx_of_typ(ty, -1) >= 0, term)
}

/// inspect_pair: true to use the equality as it is, false to reorient it first, with the variable
/// to substitute.
fn inspect_pair(is_bound: bool, is_no_vars: bool, left: &Term, right: &Term) -> Res<(bool, Term)> {
    if is_no_vars && (has_tvars(left) || has_tvars(right)) {
        return Err(Error::NoMatch);
    }
    let left_contracted = inspect_contract(left);
    let right_contracted = inspect_contract(right);
    if let TermNode::Bound { index } = &*left_contracted {
        if loose_bvar1(right, *index) || (is_no_vars && has_vars(right)) {
            return Err(Error::NoMatch);
        }
        return Ok((true, left_contracted));
    }
    if let TermNode::Bound { index } = &*right_contracted {
        if loose_bvar1(left, *index) || (is_no_vars && has_vars(left)) {
            return Err(Error::NoMatch);
        }
        return Ok((false, right_contracted));
    }
    if left_contracted.is_free() {
        if is_bound || occs(&left_contracted, right) || (is_no_vars && has_vars(right)) {
            return Err(Error::NoMatch);
        }
        return Ok((true, left_contracted));
    }
    if right_contracted.is_free() {
        if is_bound || occs(&right_contracted, left) || (is_no_vars && has_vars(left)) {
            return Err(Error::NoMatch);
        }
        return Ok((false, right_contracted));
    }
    Err(Error::NoMatch)
}

fn is_term_or_no_match(error: &Error) -> bool {
    error.is(Exception::Term) || matches!(error, Error::NoMatch)
}

/// eq_var: the number of assumptions before a substitutable equality, its orientation, and whether
/// it eliminates a free variable. (The TypeScript's recursion over the premises is a loop.)
fn eq_var(
    data: &HypsubstData,
    is_bound: bool,
    is_no_vars: bool,
    is_checking_frees: bool,
    goal: &Term,
) -> Res<(usize, (bool, bool))> {
    let check_free = |terms: &[Term], orientation: bool, variable: &Term| {
        if !variable.is_free() {
            return Ok((orientation, false));
        }
        if !is_checking_frees || !orientation || terms.iter().any(|term| occs(variable, term)) {
            return Ok((orientation, true));
        }
        Err(Error::NoMatch)
    };
    let mut count = 0;
    let mut current = goal.clone();
    let mut hyps: Vec<Term> = Vec::new();
    loop {
        if let Some((fun, arg)) = current.dest_app()
            && fun.is_const_named("Pure.all")
            && let Some(body) = arg.abs_body()
        {
            current = body.clone();
            continue;
        }
        let Some((premise, conclusion)) = current.dest_app().and_then(|(fun, conclusion)| {
            fun.dest_app()
                .filter(|(imp, _)| imp.is_const_named("Pure.imp"))
                .map(|(_, premise)| (premise.clone(), conclusion.clone()))
        }) else {
            return Err(Error::EqVar);
        };
        let found = (|| {
            let (left, right) = (data.dest_eq)(&(data.dest_trueprop)(&premise)?)?;
            let (orientation, variable) = inspect_pair(is_bound, is_no_vars, &left, &right)?;
            let terms: Vec<Term> = std::iter::once(conclusion.clone())
                .chain(hyps.iter().cloned())
                .collect();
            check_free(&terms, orientation, &variable)
        })();
        match found {
            Ok(result) => return Ok((count, result)),
            Err(error) if is_term_or_no_match(&error) => {}
            Err(error) => return Err(error),
        }
        count += 1;
        current = conclusion;
        hyps.insert(0, premise);
    }
}

fn with_eq_var(build: impl Fn(&Term, i32) -> Res<Tactic> + 'static) -> GoalTactic {
    subgoal(move |goal, index| match build(goal, index) {
        Err(error) if matches!(error, Error::EqVar) || error.is(Exception::Thm) => Ok(no_tac()),
        result => result,
    })
}

/// mk_eqs: the equality as a rewrite rule that eliminates its variable.
fn mk_eqs(data: &HypsubstData, is_bound: bool, thm: &Thm) -> Res<Vec<Thm>> {
    let result = (|| {
        let (left, right) = (data.dest_eq)(&(data.dest_trueprop)(&thm.prop)?)?;
        Ok(if inspect_pair(is_bound, false, &left, &right)?.0 {
            vec![rs(thm, &data.eq_reflection)?]
        } else {
            vec![symmetric(&rs(thm, &data.eq_reflection)?)?]
        })
    })();
    match result {
        Err(error) if is_term_or_no_match(&error) => Ok(Vec::new()),
        result => result,
    }
}

fn gen_hyp_subst_tac(data: &Rc<HypsubstData>, is_bound: bool) -> GoalTactic {
    let data = data.clone();
    with_eq_var(move |goal, index| {
        let (count, (orientation, is_free)) = eq_var(&data, is_bound, true, true, goal)?;
        let rews_data = data.clone();
        let simp_context = SimpContext {
            simpset: Simpset {
                mk_rews: MkRews {
                    mk: Rc::new(move |thm, _| mk_eqs(&rews_data, is_bound, thm)),
                    mk_eq_true: Rc::new(|_| Ok(None)),
                },
                ..empty_simpset()
            },
            bounds: 0,
        };
        let count = count as i32;
        Ok(every(vec![
            rotate_tac(count)(index),
            asm_lr_simp_tac(&simp_context)(index),
            if !is_free {
                eresolve_tac(&[thin_rl()])(index)
            } else if orientation {
                eresolve_tac(std::slice::from_ref(&data.rev_mp))(index)
            } else {
                eresolve_tac(&[rs(&data.sym, &data.rev_mp)?])(index)
            },
            rotate_tac(-count)(index),
            if is_free {
                resolve_tac(std::slice::from_ref(&data.imp_intr))(index)
            } else {
                all_tac()
            },
        ]))
    })
}

fn get_ssubst(data: &HypsubstData) -> Res<Thm> {
    zero_var_indexes(&rs(&data.sym, &data.subst)?)
}

fn inst_subst_tac(data: &Rc<HypsubstData>, is_left: bool, rule: Thm) -> GoalTactic {
    let data = data.clone();
    subgoal(move |goal, index| {
        let data = data.clone();
        let rule = rule.clone();
        let goal = goal.clone();
        Ok(Rc::new(move |state: Thm| {
            let sides = (|| -> Res<Option<(Term, Term)>> {
                let Some(hyp) = strip_assums_hyp(&goal).into_iter().next() else {
                    return Ok(None);
                };
                let (left, right) = (data.dest_eq)(&(data.dest_trueprop)(&hyp)?)?;
                Ok(Some((eta_contract(&left), eta_contract(&right))))
            })();
            let sides = match sides {
                Err(error) if error.is(Exception::Term) => None,
                sides => sides?,
            };
            let Some((left, right)) = sides else {
                return no_tac()(state);
            };
            let params = strip_params(&goal);
            let param_type = fastype_of1(
                &params
                    .iter()
                    .rev()
                    .map(|param| param.ty.clone())
                    .collect::<Vec<Typ>>(),
                &left,
            )?;
            let conclusion = (data.dest_trueprop)(strip_assums_concl(&goal))?;
            let lifted = lift_rule(&goal, state.maxidx, &rule);
            let head = head_of(&(data.dest_trueprop)(strip_assums_concl(&lifted.prop))?).clone();
            let (v1, v2) = (data.dest_eq)(&(data.dest_trueprop)(strip_assums_concl(
                &prems_of(&lifted)[0],
            ))?)?;
            let TermNode::Var {
                name: head_name,
                index: head_index,
                ty: head_type,
            } = &*head
            else {
                return Err(term_exn("dest_Var"));
            };
            let binders = binder_types(head_type);
            let (last_type, param_types) = binders
                .split_last()
                .expect("the substitution rule's motive is a function");
            let abs_params = |body: Term| {
                params.iter().rev().fold(body, |result, param| {
                    mk_abs(param.name.clone(), param.ty.clone(), result)
                })
            };
            let chosen = if is_left { &left } else { &right };
            let body = match &**chosen {
                TermNode::Bound {
                    index: chosen_index,
                } => {
                    let rest = (params.len() as i32 - chosen_index - 1).max(0);
                    let args: Vec<Term> = (0..*chosen_index)
                        .map(|position| mk_bound(position + 1))
                        .chain(std::iter::once(mk_bound(0)))
                        .chain((0..rest).map(|position| mk_bound(chosen_index + 2 + position)))
                        .collect();
                    subst_bounds(&args, &conclusion)
                }
                _ => abstract_over(chosen, &incr_boundvars(1, &conclusion)),
            };
            let motive = abs_params(mk_abs("x", param_type.clone(), body));
            let tyenv = match_types(last_type, &param_type, &empty_ty_env())?
                .ok_or_else(|| type_exn("Thm.match"))?;
            let (
                TermNode::Var {
                    name: v1_name,
                    index: v1_index,
                    ..
                },
                TermNode::Var {
                    name: v2_name,
                    index: v2_index,
                    ..
                },
            ) = (&**head_of(&v1), &**head_of(&v2))
            else {
                return Err(term_exn("dest_Var"));
            };
            let substituted: Vec<Typ> = param_types
                .iter()
                .map(|ty| subst_type(&tyenv, ty))
                .collect();
            let instantiated = instantiate(
                &[
                    Instantiation {
                        variable: mk_var(
                            head_name.clone(),
                            *head_index,
                            fun_ts(
                                &[substituted.clone(), vec![param_type.clone()]].concat(),
                                subst_type(&tyenv, &body_type(head_type)),
                            ),
                        ),
                        term: motive,
                    },
                    Instantiation {
                        variable: mk_var(
                            v1_name.clone(),
                            *v1_index,
                            fun_ts(&substituted, param_type.clone()),
                        ),
                        term: abs_params(left.clone()),
                    },
                    Instantiation {
                        variable: mk_var(
                            v2_name.clone(),
                            *v2_index,
                            fun_ts(&substituted, param_type.clone()),
                        ),
                        term: abs_params(right.clone()),
                    },
                ],
                &instantiate_types(&tyenv, &lifted),
            )?;
            compose_tac(
                true,
                comp_incr(&instantiated, &asm_rl())?,
                prems_of(&rule).len(),
            )(index)(state)
        }) as Tactic)
    })
}

fn vars_gen_hyp_subst_tac(data: &Rc<HypsubstData>, is_bound: bool) -> GoalTactic {
    let data = data.clone();
    with_eq_var(move |goal, index| {
        let count = strip_assums_hyp(goal).len() as i32 - 1;
        let (position, (orientation, is_free)) = eq_var(&data, is_bound, false, true, goal)?;
        let ssubst = get_ssubst(&data)?;
        let base = if is_free {
            rev_dup_elim(&ssubst)?
        } else {
            ssubst
        };
        let rule = if orientation {
            base
        } else {
            rs(&data.sym, &base)?
        };
        let position = position as i32;
        Ok(determ(every(vec![
            repeat_determ_n(
                position,
                eresolve_tac(std::slice::from_ref(&data.rev_mp))(index),
            ),
            rotate_tac(1)(index),
            repeat_determ_n(
                count - position,
                eresolve_tac(std::slice::from_ref(&data.rev_mp))(index),
            ),
            inst_subst_tac(&data, orientation, rule)(index),
            repeat_determ_n(
                count,
                then_tac(
                    resolve_tac(std::slice::from_ref(&data.imp_intr))(index),
                    rotate_tac(-1)(index),
                ),
            ),
        ])))
    })
}

fn rev_dup_elim(thm: &Thm) -> Res<Thm> {
    let resolved = rsn(thm, 2, &revcut_rl())?;
    let results = without_limits(|| list_of_seq(&assumption(2, &resolved)?))?;
    results
        .into_iter()
        .next()
        .ok_or_else(|| thm_exn("rev_dup_elim"))
}

/// hyp_subst_tac with hypsubst_thin off, its default: substitutes for free or bound variables and
/// drops equalities on bound variables.
pub fn hyp_subst_tac(data: &Rc<HypsubstData>) -> GoalTactic {
    let data = data.clone();
    Rc::new(move |index| {
        repeat_determ1(first_goal(vec![
            ematch_tac(std::slice::from_ref(&data.thin_refl)),
            gen_hyp_subst_tac(&data, false),
            vars_gen_hyp_subst_tac(&data, false),
        ])(index))
    })
}

fn reverse_n_tac(data: &HypsubstData, count: usize, index: i32) -> Tactic {
    match count {
        0 => all_tac(),
        1 => rotate_tac(-1)(index),
        _ => then_tac(
            repeat_determ_n(
                count as i32,
                then_tac(
                    rotate_tac(-1)(index),
                    eresolve_tac(std::slice::from_ref(&data.rev_mp))(index),
                ),
            ),
            repeat_determ_n(
                count as i32,
                then_tac(
                    resolve_tac(std::slice::from_ref(&data.imp_intr))(index),
                    rotate_tac(-1)(index),
                ),
            ),
        ),
    }
}

/// all_imp_intr_tac: reintroduces the hypotheses, leaving the changed ones at the end. (The
/// TypeScript's recursion over the hypotheses, which pulls each step at once, is a loop.)
fn all_imp_intr_tac(data: &Rc<HypsubstData>, hyps: Vec<Term>, index: i32) -> Tactic {
    let data = data.clone();
    Rc::new(move |state| {
        let mut current = state;
        let mut count = 0;
        for expected in hyps.iter().rev() {
            let (hyp, _) = (data.dest_imp)(&(data.dest_trueprop)(strip_assums_concl(&prem_of(
                &current, index,
            )?))?)?;
            let is_same = aeconv(expected, &hyp);
            let tactic = if is_same {
                then_tac(
                    resolve_tac(std::slice::from_ref(&data.imp_intr))(index),
                    rotate_tac(-1)(index),
                )
            } else {
                resolve_tac(std::slice::from_ref(&data.imp_intr))(index)
            };
            let Some((result, _)) = tactic(current.clone())?.pull()? else {
                return all_tac()(current);
            };
            current = result;
            if !is_same {
                count += 1;
            }
        }
        reverse_n_tac(&data, count, index)(current)
    })
}

/// blast_hyp_subst_tac: the version for blast, which moves the hypotheses the substitution changes
/// to the front.
pub fn blast_hyp_subst_tac(data: &Rc<HypsubstData>) -> GoalTactic {
    let data = data.clone();
    with_eq_var(move |goal, index| {
        let (count, (orientation, _)) = eq_var(&data, false, false, false, goal)?;
        let all_hyps = strip_assums_hyp(goal)
            .iter()
            .map(|hyp| (data.dest_trueprop)(hyp))
            .collect::<Res<Vec<Term>>>()?;
        let hyps: Vec<Term> = all_hyps
            .into_iter()
            .enumerate()
            .filter(|(position, _)| *position != count)
            .map(|(_, hyp)| hyp)
            .collect();
        let remaining = hyps.len() as i32 - count as i32;
        Ok(determ(every(vec![
            repeat_determ_n(
                count as i32,
                eresolve_tac(std::slice::from_ref(&data.rev_mp))(index),
            ),
            rotate_tac(1)(index),
            repeat_determ_n(
                remaining,
                eresolve_tac(std::slice::from_ref(&data.rev_mp))(index),
            ),
            inst_subst_tac(
                &data,
                orientation,
                if orientation {
                    get_ssubst(&data)?
                } else {
                    data.subst.clone()
                },
            )(index),
            all_imp_intr_tac(&data, hyps, index),
        ])))
    })
}

#[cfg(test)]
mod tests {
    use prove_decide::Limits;

    use super::*;
    use crate::pure::interrupt::with_limits;
    use crate::pure::simp_testing::fixture_goal;
    use crate::pure::testing::{check_problems, parse_term};
    use crate::pure::thm::tests::many;
    use crate::pure::thm::trivial;
    use crate::tla::classical_setup::get_hypsubst_data;
    use crate::tla::logic::load_logic;

    /// A term's text, or `@name`: the statement of a fixture.
    fn read_goal(field: &str) -> Term {
        match field.strip_prefix('@') {
            Some(name) => fixture_goal(name),
            None => parse_term(field),
        }
    }

    /// `tactic<TAB>name<TAB>step limit<TAB>goal`: the first two results of the tactic on the goal.
    fn solve(data: &Rc<HypsubstData>, kind: &str, fields: &[&str]) -> Vec<String> {
        assert_eq!(kind, "tactic");
        let tactic = match fields[0] {
            "hyp_subst" => hyp_subst_tac(data),
            "blast_hyp_subst" => blast_hyp_subst_tac(data),
            name => panic!("unknown tactic {name}"),
        };
        let limit = (fields[1] != "Infinity").then(|| fields[1].parse().unwrap());
        let limits = Limits::new(f64::INFINITY, limit, None);
        let mut lines = Vec::new();
        with_limits(&limits, || {
            many(&mut lines, "results", 2, || {
                tactic(1)(trivial(&read_goal(fields[2]))?)
            });
        });
        lines.push(format!("steps {}", limits.steps()));
        lines
    }

    // The expectations are recorded from hypsubst.ts, with classical-setup.ts's data, on synthetic
    // goals, the fixtures' statements, the subgoals safe_tac leaves, and the logic's facts.
    #[test]
    fn hypsubst_matches_the_typescript() {
        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(|| {
                let data = get_hypsubst_data(&load_logic()).unwrap();
                check_problems(
                    include_str!("../../testdata/provers/hypsubst.txt"),
                    |kind, fields| solve(&data, kind, fields),
                );
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
