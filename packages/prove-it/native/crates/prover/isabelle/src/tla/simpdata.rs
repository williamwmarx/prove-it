//! The simplifier as Isabelle/TLA+ sets it up in simplifier_setup.ML and PredicateLogic.thy (BSD
//! licensed, see LICENSE-tlapm): how theorems become rewrite rules, the solvers, the neq simproc,
//! and the simpset of the reference heap.
//!
//! The heap's only looper, "split PredicateLogic.cond", is left out: its rule splitCond has the
//! premise isBool(Q(x)), so Splitter.split_tac never composes it with a goal and the looper always
//! fails.
//!
//! (`tla/simpdata.ts`.)

use std::rc::Rc;

use crate::error::{Exception, Res, error_exn};
use crate::pure::drule::{gen_all, reflexive_thm};
use crate::pure::net::{Net, empty_net, insert_term_net};
use crate::pure::raw_simplifier::{
    MkRews, Procedure, SimpContext, Simpset, Solver, cong_key, empty_congs, rules_from_entries,
};
use crate::pure::simplifier::{asm_simp_tac, simplify};
use crate::pure::table::update_table;
use crate::pure::tactic::{
    assume_tac, ematch_tac, eq_assume_tac, eresolve_tac, match_tac, resolve_tac,
};
use crate::pure::tactical::{
    GoalTactic, first, first_goal, or_else, repeat_determ, then_all_new, then_goal,
};
use crate::pure::term::{Term, TermNode, aconv, eq_term, head_of};
use crate::pure::thm::{Thm, concl_of, rs};
use crate::pure::variable::trade;

use super::classical_setup::get_fact;
use super::logic::TlaLogic;

fn is_const_app(name: &str, arity: usize, term: &Term) -> bool {
    if arity == 0 {
        return term.is_const_named(name);
    }
    term.dest_app()
        .is_some_and(|(fun, _)| is_const_app(name, arity - 1, fun))
}

fn catch_thm<Result>(derive: impl FnOnce() -> Res<Result>) -> Res<Option<Result>> {
    match derive() {
        Ok(result) => Ok(Some(result)),
        Err(error) if error.is(Exception::Thm) => Ok(None),
        Err(error) => Err(error),
    }
}

struct Rewriting {
    eq_reflection: Thm,
    eq_true_i: Thm,
    neq_to_eq_false: Thm,
    /// The rules that split a premise by its outermost operator, and whether to simplify what they
    /// give.
    pairs: Vec<(&'static str, Vec<Thm>, bool)>,
}

impl Rewriting {
    /// Simpdata.mk_eq
    fn mk_eq(&self, thm: &Thm) -> Res<Thm> {
        let conclusion = concl_of(thm);
        if is_const_app("Pure.eq", 2, conclusion) {
            return Ok(thm.clone());
        }
        if let Some((_, arg)) = conclusion.dest_app() {
            if is_const_app("PredicateLogic.eq", 2, arg) {
                return rs(thm, &self.eq_reflection);
            }
            if let Some((fun, inner)) = arg.dest_app()
                && is_const_app("PredicateLogic.not", 0, fun)
                && is_const_app("PredicateLogic.eq", 2, inner)
            {
                return rs(thm, &self.neq_to_eq_false);
            }
        }
        rs(&rs(thm, &self.eq_true_i)?, &self.eq_reflection)
    }

    /// Simpdata.mk_atomize
    fn atoms(&self, context: &SimpContext, thm: &Thm) -> Res<Vec<Thm>> {
        let concl = concl_of(thm);
        let Some((_, arg)) = concl
            .dest_app()
            .filter(|_| is_const_app("PredicateLogic.Trueprop", 1, concl))
        else {
            return Ok(vec![thm.clone()]);
        };
        let pair = match &**head_of(arg) {
            TermNode::Const { name, .. } => {
                self.pairs.iter().find(|(known, _, _)| *known == &**name)
            }
            _ => None,
        };
        let Some((_, rules, is_simplified)) = pair else {
            return Ok(vec![thm.clone()]);
        };
        let derive = |fixed: Thm| {
            rules
                .iter()
                .map(|rule| rs(&fixed, rule))
                .collect::<Res<Vec<_>>>()
        };
        let split = catch_thm(|| {
            let derived = if thm.maxidx == -1 {
                derive(thm.clone())?
            } else {
                trade(derive, thm)?
            };
            let mut split = Vec::new();
            for result in &derived {
                split.extend(self.atoms(context, result)?);
            }
            Ok(split)
        })?;
        let Some(split) = split else {
            return Ok(vec![thm.clone()]);
        };
        if *is_simplified {
            split
                .iter()
                .map(|result| simplify(context, result))
                .collect()
        } else {
            Ok(split)
        }
    }
}

fn get_rewriting(logic: &TlaLogic) -> Res<MkRews> {
    let fact = |name: &str| get_fact(logic, &format!("PredicateLogic.{name}"));
    let eq_reflection = fact("eq_reflection")?;
    let rewriting = Rc::new(Rewriting {
        neq_to_eq_false: rs(&fact("neq_conv_eq_False")?, &eq_reflection)?,
        eq_true_i: fact("eqTrueI")?,
        pairs: vec![
            ("PredicateLogic.not", vec![fact("boolifyFalseI")?], true),
            (
                "PredicateLogic.iff",
                vec![fact("iffThenBoolifyEqual")?],
                true,
            ),
            ("PredicateLogic.imp", vec![fact("mp")?], false),
            (
                "PredicateLogic.conj",
                vec![fact("conjD1")?, fact("conjD2")?],
                false,
            ),
            ("PredicateLogic.All", vec![fact("spec")?], false),
            ("PredicateLogic.TRUE", Vec::new(), false),
            ("PredicateLogic.FALSE", Vec::new(), false),
            (
                "PredicateLogic.cond",
                vec![rs(&fact("if_bool_equiv_conj")?, &fact("iffD1")?)?],
                false,
            ),
        ],
        eq_reflection,
    });
    let eq_true = rewriting.clone();
    Ok(MkRews {
        mk: Rc::new(move |thm, context| {
            let mut eqs = Vec::new();
            for atom in rewriting.atoms(context, &gen_all(thm)?)? {
                eqs.extend(catch_thm(|| rewriting.mk_eq(&atom))?);
            }
            Ok(eqs)
        }),
        mk_eq_true: Rc::new(move |thm| {
            catch_thm(|| rs(&rs(thm, &eq_true.eq_true_i)?, &eq_true.eq_reflection))
        }),
    })
}

struct Solutions {
    solutions: Vec<Thm>,
    contradictions: Vec<Thm>,
    conj_i: Thm,
    simp_implies_i: Thm,
}

fn intro_simp_implies(solutions: &Solutions) -> GoalTactic {
    let rule = solutions.simp_implies_i.clone();
    Rc::new(move |index| repeat_determ(match_tac(std::slice::from_ref(&rule))(index)))
}

fn unsafe_solve_tac(solutions: Rc<Solutions>, rules: Rc<[Thm]>) -> GoalTactic {
    Rc::new(move |index| {
        or_else(
            first(vec![
                resolve_tac(&rules)(index),
                assume_tac()(index),
                eresolve_tac(&solutions.contradictions)(index),
            ]),
            then_all_new(
                match_tac(std::slice::from_ref(&solutions.conj_i)),
                unsafe_solve_tac(solutions.clone(), rules.clone()),
            )(index),
        )
    })
}

fn get_solvers(logic: &TlaLogic) -> Res<(Solver, Solver)> {
    let fact = |name: &str| get_fact(logic, &format!("PredicateLogic.{name}"));
    let solutions = Rc::new(Solutions {
        solutions: vec![
            reflexive_thm(),
            fact("trueI")?,
            fact("refl")?,
            fact("iff_refl")?,
            fact("notFalseI")?,
        ],
        contradictions: vec![fact("falseE")?, fact("not_refl_False")?],
        conj_i: fact("conjI")?,
        simp_implies_i: fact("simp_impliesI")?,
    });
    let with_prems = |solutions: &Solutions, context: &SimpContext| -> Rc<[Thm]> {
        solutions
            .solutions
            .iter()
            .chain(context.simpset.prems.iter())
            .cloned()
            .collect()
    };
    let unsafe_solutions = solutions.clone();
    let unsafe_solver = Solver {
        name: "PredicateLogic unsafe".into(),
        tactic: Rc::new(move |context| {
            let solve_tac = unsafe_solve_tac(
                unsafe_solutions.clone(),
                with_prems(&unsafe_solutions, context),
            );
            then_goal(intro_simp_implies(&unsafe_solutions), solve_tac)
        }),
    };
    let safe_solver = Solver {
        name: "PredicateLogic safe".into(),
        tactic: Rc::new(move |context| {
            then_goal(
                intro_simp_implies(&solutions),
                first_goal(vec![
                    match_tac(&with_prems(&solutions, context)),
                    eq_assume_tac(),
                    ematch_tac(&solutions.contradictions),
                ]),
            )
        }),
    };
    Ok((unsafe_solver, safe_solver))
}

/// PredicateLogic.thy's neq simproc: rewrites x = y to FALSE given y ~= x or (y = x) = FALSE.
fn get_neq_proc(logic: &TlaLogic) -> Res<Rc<dyn Fn(&SimpContext, &Term) -> Res<Option<Thm>>>> {
    let fact = |name: &str| get_fact(logic, &format!("PredicateLogic.{name}"));
    let eq_reflection = fact("eq_reflection")?;
    let neq_to_eq_false = rs(
        &rs(&fact("not_sym")?, &fact("neq_conv_eq_False")?)?,
        &eq_reflection,
    )?;
    let sym_eq_left = rs(&fact("symEqLeft")?, &eq_reflection)?;
    let is_neq = |eq: &Term, lhs: &Term, rhs: &Term, thm: &Thm| {
        let Some((_, body)) = thm.prop.dest_app() else {
            return false;
        };
        let Some((body_fun, body_arg)) = body.dest_app() else {
            return false;
        };
        if let Some((negated_fun, negated_arg)) = body_arg.dest_app()
            && negated_fun.is_app()
        {
            return is_const_app("PredicateLogic.not", 0, body_fun)
                && negated_fun.dest_app().is_some_and(|(eq_head, eq_arg)| {
                    eq_term(eq_head, eq) && aconv(negated_arg, lhs) && aconv(eq_arg, rhs)
                });
        }
        let Some((body_head, equation)) = body_fun.dest_app() else {
            return false;
        };
        is_const_app("PredicateLogic.eq", 0, body_head)
            && equation
                .dest_app()
                .is_some_and(|(equation_fun, equation_arg)| {
                    equation_fun
                        .dest_app()
                        .is_some_and(|(equation_head, equation_left)| {
                            is_const_app("PredicateLogic.eq", 0, equation_head)
                                && is_const_app("PredicateLogic.FALSE", 0, body_arg)
                                && aconv(equation_arg, lhs)
                                && aconv(equation_left, rhs)
                        })
                })
    };
    Ok(Rc::new(move |context, term| {
        let Some((fun, rhs)) = term.dest_app() else {
            return Ok(None);
        };
        let Some((eq, lhs)) = fun.dest_app() else {
            return Ok(None);
        };
        let Some(prem) = context
            .simpset
            .prems
            .iter()
            .find(|thm| is_neq(eq, lhs, rhs, thm))
        else {
            return Ok(None);
        };
        match catch_thm(|| rs(prem, &sym_eq_left))? {
            Some(result) => Ok(Some(result)),
            None => Ok(Some(rs(prem, &neq_to_eq_false)?)),
        }
    }))
}

pub fn get_simpset(logic: &TlaLogic) -> Res<Simpset> {
    let neq = get_neq_proc(logic)?;
    let (unsafe_solver, safe_solver) = get_solvers(logic)?;
    let mut simprocs: Net<Procedure> = empty_net();
    for simproc in &logic.simprocs {
        if &*simproc.name != "PredicateLogic.neq" {
            return Err(error_exn(format!("Undefined simproc: {}", simproc.name)));
        }
        for lhs in &simproc.lhss {
            simprocs = insert_term_net(
                lhs,
                Procedure {
                    name: simproc.name.clone(),
                    lhs: lhs.clone(),
                    proc: neq.clone(),
                },
                &simprocs,
            );
        }
    }
    Ok(Simpset {
        rules: rules_from_entries(&logic.simps)?,
        prems: Rc::from([]),
        depth: 0,
        congs: logic.congs.iter().fold(empty_congs(), |table, cong| {
            update_table(&table, cong_key(&cong.name), cong.rule.clone())
        }),
        weak_congs: logic.weak_congs.iter().cloned().collect(),
        simprocs,
        mk_rews: get_rewriting(logic)?,
        subgoal_tac: Rc::new(asm_simp_tac),
        loop_tacs: Rc::from([]),
        unsafe_solvers: Rc::from([unsafe_solver]),
        safe_solvers: Rc::from([safe_solver]),
    })
}
