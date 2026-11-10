//! Helpers for the provers' tests, whose expectations in `testdata/provers` are recorded from the
//! TypeScript (classical.ts, intuitionistic.ts and blast) by a script that runs the same tactics on
//! the same goals under the same step limit.
//!
//! The rules come from the logic's theorems, decoded here as tla/logic.ts's parseLogic decodes them
//! (each term and theorem once, so that they are shared), and set up as tla/classical-setup.ts and
//! tla/context.ts set them up.

use std::rc::Rc;

use prove_decide::Limits;

use crate::error::{Error, Res, term_exn};
use crate::pure::interrupt::with_limits;
use crate::pure::net::empty_net;
use crate::pure::seq::Seq;
use crate::pure::simp_testing::fixture_goal;
use crate::pure::tactic::{NetPair, TaggedRule, assume_tac, dresolve_tac, insert_tagged_brl};
use crate::pure::tactical::{GoalTactic, append_tac, then_goal};
use crate::pure::term::{
    Term, Typ, empty_sort, mk_abs, mk_app, mk_bound, mk_const, mk_free, mk_tfree, mk_tvar, mk_type,
    mk_var,
};
use crate::pure::testing::{check_problems, show_error};
use crate::pure::thm::tests::{digest, show_thm};
use crate::pure::thm::{Thm, axiom_thm, trivial};
use crate::tla::logic::load_logic;
use crate::tla::logic_data::{self, ExtraNetItem, LogicData, LogicRule, NetItem, logic_data};
use crate::tools::intuitionistic::{ContextRule, IntuitionisticContext, prover_tac};

use super::blast::blast::{blast_depth_tac, blast_tac};
use super::blast::state::{BlastContext, BlastData};
use super::classical::{
    Claset, ClassicalContext, ClassicalData, ClassicalRule, add_unsafe_dest, add_unsafe_intro,
    addbefore, app_wrappers, clarify_tac, first_best_tac, inst0_step_tac, instp_step_tac, safe_tac,
    unsafe_step_tac, with_claset,
};
use super::hypsubst::{HypsubstData, blast_hyp_subst_tac, hyp_subst_tac};

/// parseLogic's getType, getTerm and thms.
struct Decoder {
    data: &'static LogicData,
    types: Vec<Option<Typ>>,
    terms: Vec<Option<Term>>,
}

impl Decoder {
    fn string(&self, id: u32) -> &'static str {
        &self.data.strings[id as usize]
    }

    fn get_type(&mut self, id: u32) -> Typ {
        if let Some(known) = &self.types[id as usize] {
            return known.clone();
        }
        let ty = match &self.data.types[id as usize] {
            logic_data::TypeNode::Type { name, args } => {
                let args = args.iter().map(|arg| self.get_type(*arg)).collect();
                mk_type(self.string(*name), args)
            }
            logic_data::TypeNode::TFree { name } => mk_tfree(self.string(*name), empty_sort()),
            logic_data::TypeNode::TVar { name, index } => {
                mk_tvar(self.string(*name), *index, empty_sort())
            }
        };
        self.types[id as usize] = Some(ty.clone());
        ty
    }

    fn get_term(&mut self, id: u32) -> Term {
        if let Some(known) = &self.terms[id as usize] {
            return known.clone();
        }
        let term = match &self.data.terms[id as usize] {
            logic_data::TermNode::Const { name, typ } => {
                mk_const(self.string(*name), self.get_type(*typ))
            }
            logic_data::TermNode::Free { name, typ } => {
                mk_free(self.string(*name), self.get_type(*typ))
            }
            logic_data::TermNode::Var { name, index, typ } => {
                mk_var(self.string(*name), *index, self.get_type(*typ))
            }
            logic_data::TermNode::Bound { index } => mk_bound(*index),
            logic_data::TermNode::Abs { name, typ, body } => {
                let ty = self.get_type(*typ);
                mk_abs(self.string(*name), ty, self.get_term(*body))
            }
            logic_data::TermNode::App { function, argument } => {
                let function = self.get_term(*function);
                mk_app(function, self.get_term(*argument))
            }
        };
        self.terms[id as usize] = Some(term.clone());
        term
    }
}

/// The logic's theorems, by id, and what the tests build from them.
pub(crate) struct Rules {
    pub thms: Vec<Thm>,
    pub claset: Rc<Claset>,
    pub classical_data: Rc<ClassicalData>,
    pub blast_data: Rc<BlastData>,
    pub intuitionistic: IntuitionisticContext,
    pub atomize_rules: Vec<Thm>,
}

pub(crate) fn get_fact(thms: &[Thm], name: &str) -> Thm {
    let fact = logic_data()
        .facts
        .iter()
        .find(|fact| fact.name == name)
        .unwrap_or_else(|| panic!("no fact {name}"));
    assert_eq!(fact.thms.len(), 1, "{name}");
    thms[fact.thms[0] as usize].clone()
}

fn to_rule(thms: &[Thm], raw: &LogicRule) -> ClassicalRule {
    ClassicalRule {
        rule: thms[raw.rule as usize].clone(),
        internal: thms[raw.internal as usize].clone(),
        swapped: raw
            .swapped
            .iter()
            .map(|id| thms[*id as usize].clone())
            .collect(),
        dup: thms[raw.dup as usize].clone(),
        dup_swapped: raw
            .dup_swapped
            .iter()
            .map(|id| thms[*id as usize].clone())
            .collect(),
    }
}

/// classical-setup.ts's toNetPair: Net.content lists a leaf's items newest first, so inserting
/// them in reverse rebuilds the leaf.
fn to_net_pair(thms: &[Thm], pair: &logic_data::NetPair<NetItem>) -> NetPair<TaggedRule> {
    let insert_all = |items: &[NetItem], netpair: NetPair<TaggedRule>| {
        items.iter().rev().fold(netpair, |result, item| {
            insert_tagged_brl(
                TaggedRule {
                    tag: i64::from(item.tag),
                    is_elim: item.is_elim,
                    rule: thms[item.rule as usize].clone(),
                },
                &result,
            )
            .unwrap()
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
        ),
    )
}

/// context.ts's toNetPair.
fn to_context_net_pair(
    thms: &[Thm],
    pair: &logic_data::NetPair<ExtraNetItem>,
) -> NetPair<ContextRule> {
    let insert_all = |items: &[ExtraNetItem], netpair: NetPair<ContextRule>| {
        items.iter().rev().fold(netpair, |result, item| {
            insert_tagged_brl(
                ContextRule {
                    weight: i64::from(item.weight),
                    tag: i64::from(item.tag),
                    is_elim: item.is_elim,
                    rule: thms[item.rule as usize].clone(),
                },
                &result,
            )
            .unwrap()
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
        ),
    )
}

/// classical-setup.ts's destBinary.
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

/// classical-setup.ts's getHypsubstData.
fn hypsubst_data(thms: &[Thm]) -> Rc<HypsubstData> {
    Rc::new(HypsubstData {
        dest_trueprop: Box::new(|term| {
            term.dest_app()
                .filter(|(fun, _)| fun.is_const_named("PredicateLogic.Trueprop"))
                .map(|(_, arg)| arg.clone())
                .ok_or_else(|| term_exn("dest_Trueprop"))
        }),
        dest_eq: dest_binary("PredicateLogic.eq"),
        dest_imp: dest_binary("PredicateLogic.imp"),
        eq_reflection: get_fact(thms, "PredicateLogic.eq_reflection"),
        rev_eq_reflection: get_fact(thms, "PredicateLogic.meta_to_obj_eq"),
        imp_intr: get_fact(thms, "PredicateLogic.impI"),
        rev_mp: get_fact(thms, "PredicateLogic.rev_mp"),
        subst: get_fact(thms, "PredicateLogic.subst"),
        sym: get_fact(thms, "PredicateLogic.sym"),
        thin_refl: get_fact(thms, "PredicateLogic.thin_refl"),
    })
}

const ATOMIZE_RULES: [&str; 7] = [
    "Zenon.atomize_object_bAll",
    "Zenon.atomize_meta_bAll",
    "PredicateLogic.atomize_conj",
    "PredicateLogic.atomize_eq",
    "PredicateLogic.atomize_not",
    "PredicateLogic.atomize_imp",
    "PredicateLogic.atomize_all",
];

fn build_rules() -> Rules {
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
    let raw = &data.claset;
    let claset = Claset {
        safe_is: raw
            .safe_is
            .iter()
            .map(|rule| to_rule(&thms, rule))
            .collect(),
        safe_es: raw
            .safe_es
            .iter()
            .map(|rule| to_rule(&thms, rule))
            .collect(),
        unsafe_is: raw
            .unsafe_is
            .iter()
            .map(|rule| to_rule(&thms, rule))
            .collect(),
        unsafe_es: raw
            .unsafe_es
            .iter()
            .map(|rule| to_rule(&thms, rule))
            .collect(),
        swrappers: Vec::new(),
        uwrappers: Vec::new(),
        safe0: to_net_pair(&thms, &raw.safe0),
        safep: to_net_pair(&thms, &raw.safep),
        r#unsafe: to_net_pair(&thms, &raw.r#unsafe),
        dup: to_net_pair(&thms, &raw.dup),
    };
    // SetTheory.thy: ctxt addbefore ("bspec", fn ctxt' => dresolve_tac ctxt' @{thms bspec} THEN' assume_tac ctxt')
    let bspec: GoalTactic = then_goal(
        dresolve_tac(&[get_fact(&thms, "SetTheory.bspec")]).unwrap(),
        assume_tac(),
    );
    let claset = addbefore(&claset, "bspec", bspec);
    let hypsubst = hypsubst_data(&thms);
    let classical_data = Rc::new(ClassicalData {
        imp_elim: get_fact(&thms, "PredicateLogic.impCE'"),
        not_elim: get_fact(&thms, "PredicateLogic.notE"),
        swap: get_fact(&thms, "PredicateLogic.swap"),
        classical: get_fact(&thms, "PredicateLogic.classical"),
        judgment: "PredicateLogic.Trueprop".into(),
        hyp_subst_tacs: vec![hyp_subst_tac(&hypsubst)],
    });
    let atomize_rules: Vec<Thm> = ATOMIZE_RULES
        .iter()
        .map(|name| get_fact(&thms, name))
        .collect();
    let blast_data = Rc::new(BlastData {
        trueprop: "PredicateLogic.Trueprop".into(),
        equality_name: "PredicateLogic.eq".into(),
        not_name: "PredicateLogic.not".into(),
        not_e: get_fact(&thms, "PredicateLogic.notE"),
        ccontr: get_fact(&thms, "PredicateLogic.contradiction"),
        hyp_subst_tac: blast_hyp_subst_tac(&hypsubst),
        classical: get_fact(&thms, "PredicateLogic.classical"),
        atomize: atomize_rules.clone(),
    });
    let intuitionistic = IntuitionisticContext {
        safe_rules: to_context_net_pair(&thms, &data.context_rules.bang),
        rules: to_context_net_pair(&thms, &data.context_rules.plain),
    };
    Rules {
        thms,
        claset: Rc::new(claset),
        classical_data,
        blast_data,
        intuitionistic,
        atomize_rules,
    }
}

pub(crate) fn rules() -> Rc<Rules> {
    thread_local!(static RULES: Rc<Rules> = Rc::new(build_rules()));
    RULES.with(Rc::clone)
}

/// A goal by the name the script gives it: `thy:` a fixture theory's statement, `fact:` a fact of
/// the logic, `rule:` a rule of the claset's lists.
pub(crate) fn goal_of(name: &str) -> Term {
    let rules = rules();
    if let Some(file) = name.strip_prefix("thy:") {
        return fixture_goal(file);
    }
    if let Some(fact) = name.strip_prefix("fact:") {
        return get_fact(&rules.thms, fact).prop.clone();
    }
    let parts: Vec<&str> = name.split(':').collect();
    assert_eq!(parts[0], "rule");
    let index: usize = parts[2].parse().unwrap();
    let list = match parts[1] {
        "safeIs" => &rules.claset.safe_is,
        "safeEs" => &rules.claset.safe_es,
        "unsafeIs" => &rules.claset.unsafe_is,
        "unsafeEs" => &rules.claset.unsafe_es,
        other => panic!("no rule list {other}"),
    };
    list[index].rule.prop.clone()
}

pub(crate) fn classical_context() -> ClassicalContext {
    let rules = rules();
    ClassicalContext {
        claset: rules.claset.clone(),
        data: rules.classical_data.clone(),
    }
}

pub(crate) fn blast_context() -> Rc<BlastContext> {
    let rules = rules();
    Rc::new(BlastContext::new(
        rules.claset.clone(),
        rules.blast_data.clone(),
        load_logic(),
    ))
}

/// An exception as the script prints it, with a stack overflow as `error Stack`.
fn show_outcome(error: &Error) -> String {
    match error {
        Error::Stack => "error Stack".into(),
        other => show_error(other),
    }
}

/// The first count results of a sequence, as the script prints them.
fn many(lines: &mut Vec<String>, label: &str, count: usize, run: impl FnOnce() -> Res<Seq<Thm>>) {
    lines.push(label.into());
    let result = (|| {
        let mut seq = run()?;
        for index in 0.. {
            if index == count {
                lines.push("stop".into());
                return Ok(());
            }
            let Some((result, rest)) = seq.pull()? else {
                lines.push("end".into());
                return Ok(());
            };
            lines.push(format!("result {index}"));
            lines.extend(show_thm(&result));
            seq = rest;
        }
        Ok(())
    })();
    if let Err(error) = result {
        lines.push(show_outcome(&error));
    }
}

fn run(kind: &str, goal: &Term) -> Res<Seq<Thm>> {
    let rules = rules();
    let context = classical_context();
    let state = trivial(goal)?;
    match kind {
        "safe" => safe_tac(&context)(state),
        "clarify" => clarify_tac(&context)(1)(state),
        "best" => first_best_tac(&context, &rules.atomize_rules)?(1)(state),
        "steps" => {
            let inner = context.clone();
            append_tac(
                inst0_step_tac(&context)(1),
                app_wrappers(
                    &context,
                    Rc::new(move |index| {
                        append_tac(
                            instp_step_tac(&inner)(index),
                            unsafe_step_tac(&inner)(index),
                        )
                    }),
                )(1),
            )(state)
        }
        "blast" => blast_tac(blast_context())?(1)(state),
        "depth" => blast_depth_tac(blast_context(), 2)?(1)(state),
        "iprover" => prover_tac(&rules.intuitionistic)(1)(state),
        other => panic!("unknown kind {other}"),
    }
}

/// add_unsafe_intro or add_unsafe_dest of a fact, then an unsafe step with the new claset.
fn add_problem(kind: &str, name: &str, lines: &mut Vec<String>) -> Res<()> {
    let rules = rules();
    let context = classical_context();
    let fact = get_fact(&rules.thms, name.strip_prefix("fact:").unwrap());
    let claset = if kind == "intro" {
        add_unsafe_intro(&context, &fact)?
    } else {
        add_unsafe_dest(&context, &fact)?
    };
    let entries = if kind == "intro" {
        &claset.unsafe_is
    } else {
        &claset.unsafe_es
    };
    lines.push(format!("count {}", entries.len()));
    let entry = &entries[0];
    lines.push(format!("internal {}", digest(&entry.internal.prop)));
    lines.push(format!("dup {}", digest(&entry.dup.prop)));
    for swapped in &entry.swapped {
        lines.push(format!("swapped {}", digest(&swapped.prop)));
    }
    for swapped in &entry.dup_swapped {
        lines.push(format!("dupSwapped {}", digest(&swapped.prop)));
    }
    let new_context = with_claset(&context, claset);
    let goal = fact.prop.clone();
    many(lines, "results", 2, || {
        unsafe_step_tac(&new_context)(1)(trivial(&goal)?)
    });
    Ok(())
}

/// Solves a problem of the script: `kind<TAB>goal<TAB>step limit`.
fn solve(kind: &str, fields: &[&str]) -> Vec<String> {
    let limits = Limits::new(f64::INFINITY, Some(fields[1].parse().unwrap()), None);
    let mut lines = Vec::new();
    with_limits(&limits, || {
        if kind == "intro" || kind == "dest" {
            if let Err(error) = add_problem(kind, fields[0], &mut lines) {
                lines.push(show_outcome(&error));
            }
        } else {
            let goal = goal_of(fields[0]);
            many(&mut lines, "results", 2, || run(kind, &goal));
        }
    });
    lines.push(format!("steps {}", limits.steps()));
    lines
}

/// Checks the problems of a test file on a thread with the stack a decision runs on
/// (prove-it-host's DECIDE_STACK_BYTES), since blast's search recurses at each choice point.
pub(crate) fn check_provers(text: &'static str) {
    std::thread::Builder::new()
        .stack_size(256 * 1024 * 1024)
        .spawn(move || check_problems(text, solve))
        .unwrap()
        .join()
        .unwrap();
}
