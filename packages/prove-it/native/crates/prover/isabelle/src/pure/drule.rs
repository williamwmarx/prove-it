//! Ported from Isabelle2025's Pure/drule.ML, Pure/term_subst.ML and the basic rules of Pure.thy.
//! Copyright (c) 1986-2025 University of Cambridge, Technische Universitaet Muenchen, and
//! contributors, see LICENSE.
//!
//! (`pure/drule.ts`.) The basic rules are built once per thread, so that each is the same theorem
//! every time, as the TypeScript's constants.

use crate::error::{Res, thm_exn};

use super::interrupt::without_limits;
use super::logic::{all_const, is_protected, mk_equals, mk_implies, mk_term, protect};
use super::name::{NameContext, clean_name, empty_name_context, variant_list, variant_name};
use super::seq::list_of_seq;
use super::table::{
    IndexKey, Table, empty_table, fast_indexname_ord, lookup_table, table_entries, update_table,
};
use super::tactical::eq_thm;
use super::term::{
    Name, Term, TermNode, Typ, TypNode, Var, empty_sort, fold_atyps, fold_types, fold_vars, fun_t,
    mk_abs, mk_app, mk_bound, mk_tvar, mk_var, prop_t, strip_all_vars,
};
use super::thm::{
    ComposeFlags, ComposeRule, Instantiation, Thm, axiom_thm, bicompose, forall_elim, forall_intr,
    incr_indexes_thm, instantiate, instantiate_types, rs,
};
use super::types::{TyEnv, norm_type};

fn prop_var(name: &str) -> Term {
    mk_var(name, 0, prop_t())
}

fn type_a() -> Typ {
    mk_tvar("'a", 0, empty_sort())
}

/// `mk_equals` on terms whose type is known.
fn equals(left: Term, right: Term) -> Term {
    mk_equals(left, right).unwrap_or_else(|_| unreachable!("a variable has a type"))
}

macro_rules! basic_rule {
    ($(#[$doc:meta])* $name:ident, $prop:expr) => {
        $(#[$doc])*
        pub fn $name() -> Thm {
            thread_local!(static RULE: Thm = axiom_thm($prop));
            RULE.with(Clone::clone)
        }
    };
}

// The basic rules of Pure.thy, with the variable names Isabelle gives them.
basic_rule!(
    cut_rl,
    mk_implies(
        mk_implies(prop_var("psi"), prop_var("theta")),
        mk_implies(prop_var("psi"), prop_var("theta")),
    )
);
basic_rule!(
    revcut_rl,
    mk_implies(
        prop_var("V"),
        mk_implies(mk_implies(prop_var("V"), prop_var("W")), prop_var("W")),
    )
);
basic_rule!(
    thin_rl,
    mk_implies(prop_var("V"), mk_implies(prop_var("W"), prop_var("W")))
);
basic_rule!(asm_rl, mk_implies(prop_var("psi"), prop_var("psi")));
basic_rule!(
    remdups_rl,
    mk_implies(
        prop_var("phi"),
        mk_implies(
            prop_var("phi"),
            mk_implies(prop_var("psi"), prop_var("psi")),
        ),
    )
);
basic_rule!(protect_i, mk_implies(prop_var("A"), protect(prop_var("A"))));
basic_rule!(protect_d, mk_implies(protect(prop_var("A")), prop_var("A")));
basic_rule!(
    reflexive_thm,
    equals(mk_var("x", 0, type_a()), mk_var("x", 0, type_a()))
);
basic_rule!(
    term_i,
    mk_term(mk_var("x", 0, type_a())).unwrap_or_else(|_| unreachable!("a variable has a type"))
);
basic_rule!(
    imp_cong,
    mk_implies(
        mk_implies(prop_var("A"), equals(prop_var("B"), prop_var("C"))),
        equals(
            mk_implies(prop_var("A"), prop_var("B")),
            mk_implies(prop_var("A"), prop_var("C")),
        ),
    )
);
basic_rule!(
    swap_prems_eq,
    equals(
        mk_implies(prop_var("A"), mk_implies(prop_var("B"), prop_var("C"))),
        mk_implies(prop_var("B"), mk_implies(prop_var("A"), prop_var("C"))),
    )
);
basic_rule!(
    symmetric_thm,
    mk_implies(
        equals(mk_var("x", 0, type_a()), mk_var("y", 0, type_a())),
        equals(mk_var("y", 0, type_a()), mk_var("x", 0, type_a())),
    )
);
basic_rule!(
    triv_forall_equality,
    equals(
        mk_app(all_const(type_a()), mk_abs("x", type_a(), prop_var("V"))),
        prop_var("V"),
    )
);
basic_rule!(
    /// Drule.norm_hhf_eq: (PROP ?phi ==> (!!x. PROP ?psi x)) == (!!x. PROP ?phi ==> PROP ?psi x).
    norm_hhf_eq,
    equals(
        mk_implies(
            prop_var("phi"),
            mk_app(
                all_const(type_a()),
                mk_abs(
                    "x",
                    type_a(),
                    mk_app(mk_var("psi", 0, fun_t(type_a(), prop_t())), mk_bound(0)),
                ),
            ),
        ),
        mk_app(
            all_const(type_a()),
            mk_abs(
                "x",
                type_a(),
                mk_implies(
                    prop_var("phi"),
                    mk_app(mk_var("psi", 0, fun_t(type_a(), prop_t())), mk_bound(0)),
                ),
            ),
        ),
    )
);

/// Drule.is_norm_hhf: no quantifier right of an implication and no beta redex.
pub fn is_norm_hhf(is_protecting: bool, term: &Term) -> bool {
    match &**term {
        TermNode::Const { name, .. } => &**name != "Pure.sort_constraint",
        TermNode::Abs { body, .. } => is_norm_hhf(is_protecting, body),
        TermNode::App { fun, arg, .. } => {
            if fun.is_abs() {
                return false;
            }
            if fun
                .dest_app()
                .is_some_and(|(head, _)| head.is_const_named("Pure.imp"))
                && arg
                    .dest_app()
                    .is_some_and(|(head, _)| head.is_const_named("Pure.all"))
            {
                return false;
            }
            if is_protected(term) {
                return is_protecting || is_norm_hhf(is_protecting, arg);
            }
            is_norm_hhf(is_protecting, fun) && is_norm_hhf(is_protecting, arg)
        }
        _ => true,
    }
}

/// Drule.outer_params: the outermost parameters, named apart.
fn outer_params(term: &Term) -> Vec<(Name, Typ)> {
    let vars = strip_all_vars(term);
    let names = variant_list(
        &[],
        &vars
            .iter()
            .map(|(name, _)| Name::from(clean_name(name)))
            .collect::<Vec<_>>(),
    );
    vars.into_iter()
        .zip(names)
        .map(|((_, ty), name)| (name, ty))
        .collect()
}

/// Variable.gen_all: the outermost parameters become schematic variables.
pub fn gen_all(thm: &Thm) -> Res<Thm> {
    let index = thm.maxidx.max(-1) + 1;
    outer_params(&thm.prop)
        .into_iter()
        .try_fold(thm.clone(), |result, (name, ty)| {
            forall_elim(&mk_var(name, index, ty), &result)
        })
}

fn full_props(thm: &Thm) -> Vec<Term> {
    thm.tpairs
        .iter()
        .flat_map(|pair| [pair.0.clone(), pair.1.clone()])
        .chain([thm.prop.clone()])
        .collect()
}

/// Thm.forall_intr_vars: quantifies the schematic variables in order of appearance.
pub fn forall_intr_vars(thm: &Thm) -> Res<Thm> {
    let vars = full_props(thm).iter().fold(Vec::new(), |result, term| {
        fold_vars(
            &mut |atom: &Var, mut current: Vec<Var>| {
                if !current
                    .iter()
                    .any(|other| other.name() == atom.name() && other.index() == atom.index())
                {
                    current.push(atom.clone());
                }
                current
            },
            term,
            result,
        )
    });
    vars.iter().rev().try_fold(thm.clone(), |result, variable| {
        forall_intr(variable, &result)
    })
}

fn variant_bound(name: &str, used: &NameContext) -> (Name, NameContext) {
    variant_name(if name.starts_with(':') { "u" } else { name }, used)
}

/// Drule.zero_var_indexes: renames the schematic variables apart with index 0.
pub fn zero_var_indexes(thm: &Thm) -> Res<Thm> {
    let terms = full_props(thm);
    let tvars = terms.iter().fold(
        empty_table::<IndexKey, Typ>(fast_indexname_ord),
        |table, term| {
            fold_types(
                &mut |ty: &Typ, inner| {
                    fold_atyps(
                        &mut |atom: &Typ, current: Table<IndexKey, Typ>| match &**atom {
                            TypNode::TVar { name, index, .. } => update_table(
                                &current,
                                IndexKey {
                                    name: name.clone(),
                                    index: *index,
                                },
                                atom.clone(),
                            ),
                            _ => current,
                        },
                        ty,
                        inner,
                    )
                },
                term,
                table,
            )
        },
    );
    let mut used = empty_name_context();
    let mut tyenv: TyEnv = empty_table(fast_indexname_ord);
    for (key, ty) in table_entries(&tvars) {
        let (name, next) = variant_bound(&key.name, &used);
        used = next;
        if name != key.name || key.index != 0 {
            let sort = match &*ty {
                TypNode::TVar { sort, .. } => sort.clone(),
                _ => empty_sort(),
            };
            tyenv = update_table(&tyenv, key, mk_tvar(name, 0, sort));
        }
    }
    let vars = terms.iter().fold(
        empty_table::<IndexKey, Var>(fast_indexname_ord),
        |table, term| {
            fold_vars(
                &mut |atom: &Var, current: Table<IndexKey, Var>| {
                    let TermNode::Var { name, index, ty } = &**atom else {
                        unreachable!("a Var that isn't one")
                    };
                    let key = IndexKey {
                        name: name.clone(),
                        index: *index,
                    };
                    if lookup_table(&current, &key).is_some() {
                        return current;
                    }
                    update_table(
                        &current,
                        key,
                        mk_var(name.clone(), *index, norm_type(&tyenv, ty)),
                    )
                },
                term,
                table,
            )
        },
    );
    used = empty_name_context();
    let mut insts = Vec::new();
    for (key, variable) in table_entries(&vars) {
        let (name, next) = variant_bound(&key.name, &used);
        used = next;
        if name != key.name || key.index != 0 {
            let ty = variable.ty().expect("a Var").clone();
            insts.push(Instantiation {
                variable,
                term: mk_var(name, 0, ty),
            });
        }
    }
    instantiate(&insts, &instantiate_types(&tyenv, thm))
}

/// Tactic.make_elim: turns a destruction rule into an elimination rule.
pub fn make_elim(rule: &Thm) -> Res<Thm> {
    zero_var_indexes(&rs(rule, &revcut_rl())?)
}

/// The results that differ under eq_thm, in order.
fn distinct_results(results: Vec<Thm>) -> Vec<Thm> {
    results
        .iter()
        .enumerate()
        .filter(|(position, result)| {
            results.iter().position(|other| eq_thm(other, result)) == Some(*position)
        })
        .map(|(_, result)| result.clone())
        .collect()
}

/// Drule.compose: resolves tha into premise index of thb without lifting, with a unique result.
fn compose(tha: &Thm, index: i32, thb: &Thm) -> Res<Thm> {
    let results = distinct_results(without_limits(|| {
        list_of_seq(&bicompose(
            ComposeFlags {
                flatten: true,
                is_match: false,
                incremented: true,
            },
            ComposeRule {
                is_elim: false,
                rule: tha.clone(),
                subgoals: 0,
            },
            index,
            thb,
        )?)
    })?);
    if results.len() != 1 {
        return Err(thm_exn(format!("compose: unique result expected {index}")));
    }
    Ok(results[0].clone())
}

/// COMP_INCR
pub fn comp_incr(tha: &Thm, thb: &Thm) -> Res<Thm> {
    compose(tha, 1, &incr_indexes_thm(tha.maxidx + 1, thb)?)
}

/// Drule.comp_no_flatten: composes th, keeping its first count premises, into premise index of
/// rule.
pub fn comp_no_flatten(thm: &Thm, count: usize, index: i32, rule: &Thm) -> Res<Thm> {
    let results = distinct_results(without_limits(|| {
        list_of_seq(&bicompose(
            ComposeFlags {
                flatten: false,
                is_match: false,
                incremented: true,
            },
            ComposeRule {
                is_elim: false,
                rule: thm.clone(),
                subgoals: count,
            },
            index,
            &incr_indexes_thm(thm.maxidx + 1, rule)?,
        )?)
    })?);
    if results.len() != 1 {
        return Err(thm_exn(format!("comp_no_flatten {index}")));
    }
    Ok(results[0].clone())
}
