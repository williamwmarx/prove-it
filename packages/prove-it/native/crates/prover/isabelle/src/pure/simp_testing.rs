//! Helpers for the simplifier's tests: the simpset of the Isabelle/TLA+ heap, decoded from
//! `tla::logic_data` as `tla/logic.ts` decodes it and set up as `tla/simpdata.ts` sets it up (its
//! mk_rews, solvers and neq simproc), and the statements of the fixtures as goals.

use std::collections::HashMap;
use std::rc::Rc;

use crate::error::{Exception, Res, error_exn};
use crate::isar::statement::read_statement;
use crate::isar::theory::parse_theory;
use crate::tla::logic::load_logic;
use crate::tla::logic_data::{LogicData, TermNode as DataTerm, TypeNode, logic_data};

use super::drule::{gen_all, reflexive_thm};
use super::logic::list_implies;
use super::net::{Net, empty_net, insert_term_net};
use super::raw_simplifier::{
    CongName, MkRews, Procedure, SimpContext, Simpset, Solver, cong_key, empty_congs,
    rules_from_entries,
};
use super::simplifier::{asm_simp_tac, simplify};
use super::table::update_table;
use super::tactic::{assume_tac, ematch_tac, eq_assume_tac, eresolve_tac, match_tac, resolve_tac};
use super::tactical::{
    GoalTactic, first, first_goal, or_else, repeat_determ, then_all_new, then_goal,
};
use super::term::{
    Term, TermNode, Typ, aconv, empty_sort, eq_term, head_of, mk_abs, mk_app, mk_bound, mk_const,
    mk_free, mk_tfree, mk_tvar, mk_type, mk_var,
};
use super::thm::{Thm, axiom_thm, concl_of, rs};
use super::variable::trade;

/// The parts of `tla/logic.ts`'s TlaLogic that the simpset reads.
pub(crate) struct SimpLogic {
    facts: HashMap<String, Vec<Thm>>,
    simps: Vec<Thm>,
    congs: Vec<(CongName, Thm)>,
    weak_congs: Vec<CongName>,
    simprocs: Vec<(String, Vec<Term>)>,
}

struct Decoder<'data> {
    data: &'data LogicData,
    types: Vec<Option<Typ>>,
    terms: Vec<Option<Term>>,
}

impl<'data> Decoder<'data> {
    fn string(&self, id: u32) -> &'data str {
        &self.data.strings[id as usize]
    }

    fn get_type(&mut self, id: u32) -> Typ {
        if let Some(known) = &self.types[id as usize] {
            return known.clone();
        }
        let ty = match &self.data.types[id as usize] {
            TypeNode::Type { name, args } => {
                let args = args.iter().map(|arg| self.get_type(*arg)).collect();
                mk_type(self.string(*name), args)
            }
            TypeNode::TFree { name } => mk_tfree(self.string(*name), empty_sort()),
            TypeNode::TVar { name, index } => mk_tvar(self.string(*name), *index, empty_sort()),
        };
        self.types[id as usize] = Some(ty.clone());
        ty
    }

    fn get_term(&mut self, id: u32) -> Term {
        if let Some(known) = &self.terms[id as usize] {
            return known.clone();
        }
        let term = match &self.data.terms[id as usize] {
            DataTerm::Const { name, typ } => mk_const(self.string(*name), self.get_type(*typ)),
            DataTerm::Free { name, typ } => mk_free(self.string(*name), self.get_type(*typ)),
            DataTerm::Var { name, index, typ } => {
                mk_var(self.string(*name), *index, self.get_type(*typ))
            }
            DataTerm::Bound { index } => mk_bound(*index),
            DataTerm::Abs { name, typ, body } => {
                let ty = self.get_type(*typ);
                mk_abs(self.string(*name), ty, self.get_term(*body))
            }
            DataTerm::App { function, argument } => {
                let function = self.get_term(*function);
                mk_app(function, self.get_term(*argument))
            }
        };
        self.terms[id as usize] = Some(term.clone());
        term
    }
}

pub(crate) fn simp_logic() -> SimpLogic {
    let data = logic_data();
    let mut decoder = Decoder {
        data,
        types: vec![None; data.types.len()],
        terms: vec![None; data.terms.len()],
    };
    let thms: Vec<Thm> = data
        .thms
        .iter()
        .map(|id| axiom_thm(decoder.get_term(*id)))
        .collect();
    let thm = |id: &u32| thms[*id as usize].clone();
    SimpLogic {
        facts: data
            .facts
            .iter()
            .map(|fact| (fact.name.clone(), fact.thms.iter().map(thm).collect()))
            .collect(),
        simps: data.simps.iter().map(thm).collect(),
        congs: data
            .congs
            .iter()
            .map(|cong| {
                (
                    CongName {
                        is_const: cong.is_const,
                        name: cong.name.as_str().into(),
                    },
                    thm(&cong.rule),
                )
            })
            .collect(),
        weak_congs: data
            .weak_congs
            .iter()
            .map(|cong| CongName {
                is_const: cong.is_const,
                name: cong.name.as_str().into(),
            })
            .collect(),
        simprocs: data
            .simprocs
            .iter()
            .map(|simproc| {
                (
                    simproc.name.clone(),
                    simproc
                        .lhss
                        .iter()
                        .map(|id| decoder.get_term(*id))
                        .collect(),
                )
            })
            .collect(),
    }
}

/// classical-setup.ts's getFact.
pub(crate) fn get_fact(logic: &SimpLogic, name: &str) -> Thm {
    match logic.facts.get(name).map(Vec::as_slice) {
        Some([thm]) => thm.clone(),
        _ => panic!("Undefined fact: {name}"),
    }
}

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

fn get_rewriting(logic: &SimpLogic) -> MkRews {
    let fact = |name: &str| get_fact(logic, &format!("PredicateLogic.{name}"));
    let eq_reflection = fact("eq_reflection");
    let rewriting = Rc::new(Rewriting {
        neq_to_eq_false: rs(&fact("neq_conv_eq_False"), &eq_reflection).unwrap(),
        eq_true_i: fact("eqTrueI"),
        pairs: vec![
            ("PredicateLogic.not", vec![fact("boolifyFalseI")], true),
            (
                "PredicateLogic.iff",
                vec![fact("iffThenBoolifyEqual")],
                true,
            ),
            ("PredicateLogic.imp", vec![fact("mp")], false),
            (
                "PredicateLogic.conj",
                vec![fact("conjD1"), fact("conjD2")],
                false,
            ),
            ("PredicateLogic.All", vec![fact("spec")], false),
            ("PredicateLogic.TRUE", Vec::new(), false),
            ("PredicateLogic.FALSE", Vec::new(), false),
            (
                "PredicateLogic.cond",
                vec![rs(&fact("if_bool_equiv_conj"), &fact("iffD1")).unwrap()],
                false,
            ),
        ],
        eq_reflection,
    });
    let eq_true = rewriting.clone();
    MkRews {
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
    }
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

fn get_solvers(logic: &SimpLogic) -> (Solver, Solver) {
    let fact = |name: &str| get_fact(logic, &format!("PredicateLogic.{name}"));
    let solutions = Rc::new(Solutions {
        solutions: vec![
            reflexive_thm(),
            fact("trueI"),
            fact("refl"),
            fact("iff_refl"),
            fact("notFalseI"),
        ],
        contradictions: vec![fact("falseE"), fact("not_refl_False")],
        conj_i: fact("conjI"),
        simp_implies_i: fact("simp_impliesI"),
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
    (unsafe_solver, safe_solver)
}

/// PredicateLogic.thy's neq simproc: rewrites x = y to FALSE given y ~= x or (y = x) = FALSE.
fn get_neq_proc(logic: &SimpLogic) -> Rc<dyn Fn(&SimpContext, &Term) -> Res<Option<Thm>>> {
    let fact = |name: &str| get_fact(logic, &format!("PredicateLogic.{name}"));
    let eq_reflection = fact("eq_reflection");
    let neq_to_eq_false = rs(
        &rs(&fact("not_sym"), &fact("neq_conv_eq_False")).unwrap(),
        &eq_reflection,
    )
    .unwrap();
    let sym_eq_left = rs(&fact("symEqLeft"), &eq_reflection).unwrap();
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
    Rc::new(move |context, term| {
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
    })
}

/// simpdata.ts's getSimpset: the simpset of the reference heap.
pub(crate) fn get_simpset(logic: &SimpLogic) -> Res<Simpset> {
    let neq = get_neq_proc(logic);
    let (unsafe_solver, safe_solver) = get_solvers(logic);
    let mut simprocs: Net<Procedure> = empty_net();
    for (name, lhss) in &logic.simprocs {
        if name != "PredicateLogic.neq" {
            return Err(error_exn(format!("Undefined simproc: {name}")));
        }
        for lhs in lhss {
            simprocs = insert_term_net(
                lhs,
                Procedure {
                    name: name.as_str().into(),
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
        congs: logic
            .congs
            .iter()
            .fold(empty_congs(), |table, (name, rule)| {
                update_table(&table, cong_key(name), rule.clone())
            }),
        weak_congs: logic.weak_congs.iter().cloned().collect(),
        simprocs,
        mk_rews: get_rewriting(logic),
        subgoal_tac: Rc::new(asm_simp_tac),
        loop_tacs: Rc::from([]),
        unsafe_solvers: Rc::from([unsafe_solver]),
        safe_solvers: Rc::from([safe_solver]),
    })
}

macro_rules! fixtures {
    ($($name:literal),* $(,)?) => {
        [$((
            $name,
            include_str!(concat!("../../../../../../tests/fixtures/isabelle/", $name, ".thy")),
        )),*]
    };
}

/// The statement of a fixture as a goal: its assumptions imply its conclusion.
pub(crate) fn fixture_goal(name: &str) -> Term {
    let (_, text) = fixtures!(
        "AllocatorImplementation_proof-127",
        "AllocatorImplementation_proof-33",
        "AtomicBakeryWithoutSMT-465",
        "AtomicBakeryWithoutSMT-6",
        "FiniteSetTheorems_proofs-453",
        "NaturalsInduction_proofs-1",
        "Paxos-109",
        "Sets-183",
        "TLAPS-2",
        "constantfcn_test-1",
        "function_except_tuple_soundness_gh201_test-1",
    )
    .into_iter()
    .find(|(known, _)| *known == name)
    .unwrap_or_else(|| panic!("no fixture {name}"));
    let statement = read_statement(&load_logic(), &parse_theory(text).unwrap()).unwrap();
    list_implies(&statement.assumptions, statement.conclusion)
}
