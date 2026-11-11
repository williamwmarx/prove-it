//! The Isabelle/TLA+ object logic that tlapm ships, decoded from logic_data.rs: its constants, the
//! theorems its theories prove, and the order of the simpset and the classical rule nets.
//!
//! (`tla/logic.ts`.) Each theorem is one `axiom_thm`, shared by id wherever the logic names it, as
//! parseLogic shares it.

use std::collections::HashMap;
use std::rc::Rc;

use crate::provers::classical::ClassicalRule;
use crate::pure::consts::{TypargPosition, typargs_of};
use crate::pure::raw_simplifier::CongName;
use crate::pure::tactic::TaggedRule;
use crate::pure::term::{
    Name, Term, Typ, empty_sort, mk_abs, mk_app, mk_bound, mk_const, mk_free, mk_tfree, mk_tvar,
    mk_type, mk_var,
};

use crate::pure::thm::{Thm, axiom_thm};
use crate::tools::intuitionistic::ContextRule;

use super::logic_data::{self, LogicData, LogicRule, TermNode, TypeNode, logic_data};

#[derive(Clone)]
pub struct ConstInfo {
    pub ty: Typ,
    pub typargs: Rc<[TypargPosition]>,
    /// The right-hand side of an abbreviation, which parsing unfolds.
    pub abbreviation: Option<Term>,
}

/// A rule of a claset net, with its insertion tag: the TypeScript's LogicNetItem, which is the
/// tagged rule the net holds.
pub type LogicNetItem = TaggedRule;

/// A rule of the context rules, with its weight: the TypeScript's LogicExtraNetItem.
pub type LogicExtraNetItem = ContextRule;

pub struct LogicNetPair<Item> {
    pub intro: Vec<Item>,
    pub elim: Vec<Item>,
}

pub struct LogicCong {
    pub name: CongName,
    pub rule: Thm,
}

pub struct LogicSimproc {
    pub name: Name,
    pub lhss: Vec<Term>,
}

pub struct LogicClaset {
    pub safe_is: Vec<ClassicalRule>,
    pub safe_es: Vec<ClassicalRule>,
    pub unsafe_is: Vec<ClassicalRule>,
    pub unsafe_es: Vec<ClassicalRule>,
    pub safe0: LogicNetPair<LogicNetItem>,
    pub safep: LogicNetPair<LogicNetItem>,
    pub r#unsafe: LogicNetPair<LogicNetItem>,
    pub dup: LogicNetPair<LogicNetItem>,
}

pub struct LogicContextRules {
    pub bang: LogicNetPair<LogicExtraNetItem>,
    pub plain: LogicNetPair<LogicExtraNetItem>,
}

pub struct TlaLogic {
    pub consts: HashMap<Name, ConstInfo>,
    /// The constant each unqualified name stands for.
    pub const_names: HashMap<Name, Name>,
    pub facts: HashMap<Name, Vec<Thm>>,
    pub fact_names: HashMap<Name, Name>,
    /// The simpset's rewrite rules, in the order of Net.entries.
    pub simps: Vec<Thm>,
    pub congs: Vec<LogicCong>,
    pub weak_congs: Vec<CongName>,
    pub simprocs: Vec<LogicSimproc>,
    pub claset: LogicClaset,
    pub context_rules: LogicContextRules,
}

/// parseLogic's getType and getTerm: decodes types and terms by id, each once, so that the logic
/// shares them as the TypeScript does.
struct Decoder<'data> {
    data: &'data LogicData,
    strings: Vec<Name>,
    types: Vec<Option<Typ>>,
    terms: Vec<Option<Term>>,
}

impl<'data> Decoder<'data> {
    fn new(data: &'data LogicData) -> Self {
        Decoder {
            data,
            strings: data
                .strings
                .iter()
                .map(|string| Name::from(&**string))
                .collect(),
            types: vec![None; data.types.len()],
            terms: vec![None; data.terms.len()],
        }
    }

    fn string(&self, id: u32) -> Name {
        self.strings[id as usize].clone()
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
            TermNode::Const { name, typ } => mk_const(self.string(*name), self.get_type(*typ)),
            TermNode::Free { name, typ } => mk_free(self.string(*name), self.get_type(*typ)),
            TermNode::Var { name, index, typ } => {
                mk_var(self.string(*name), *index, self.get_type(*typ))
            }
            TermNode::Bound { index } => mk_bound(*index),
            TermNode::Abs { name, typ, body } => {
                let ty = self.get_type(*typ);
                mk_abs(self.string(*name), ty, self.get_term(*body))
            }
            TermNode::App { function, argument } => {
                let function = self.get_term(*function);
                mk_app(function, self.get_term(*argument))
            }
        };
        self.terms[id as usize] = Some(term.clone());
        term
    }
}

fn parse_logic() -> TlaLogic {
    let data = logic_data();
    let mut decoder = Decoder::new(data);
    let thms: Vec<Thm> = data
        .thms
        .iter()
        .map(|id| axiom_thm(decoder.get_term(*id)))
        .collect();
    let thm = |id: &u32| thms[*id as usize].clone();
    let to_rule = |raw: &LogicRule| ClassicalRule {
        rule: thm(&raw.rule),
        internal: thm(&raw.internal),
        swapped: raw.swapped.iter().map(thm).collect(),
        dup: thm(&raw.dup),
        dup_swapped: raw.dup_swapped.iter().map(thm).collect(),
    };
    let to_items = |pair: &logic_data::NetPair<logic_data::NetItem>| {
        let side = |items: &[logic_data::NetItem]| {
            items
                .iter()
                .map(|item| TaggedRule {
                    tag: i64::from(item.tag),
                    is_elim: item.is_elim,
                    rule: thm(&item.rule),
                })
                .collect()
        };
        LogicNetPair {
            intro: side(&pair.intro),
            elim: side(&pair.elim),
        }
    };
    let to_extra_items = |pair: &logic_data::NetPair<logic_data::ExtraNetItem>| {
        let side = |items: &[logic_data::ExtraNetItem]| {
            items
                .iter()
                .map(|item| ContextRule {
                    weight: i64::from(item.weight),
                    tag: i64::from(item.tag),
                    is_elim: item.is_elim,
                    rule: thm(&item.rule),
                })
                .collect()
        };
        LogicNetPair {
            intro: side(&pair.intro),
            elim: side(&pair.elim),
        }
    };
    let claset = &data.claset;
    TlaLogic {
        consts: data
            .consts
            .iter()
            .map(|entry| {
                let ty = decoder.get_type(entry.typ);
                let info = ConstInfo {
                    typargs: typargs_of(&ty).into(),
                    ty,
                    abbreviation: entry.abbreviation.map(|id| decoder.get_term(id)),
                };
                (Name::from(&*entry.name), info)
            })
            .collect(),
        const_names: data
            .names
            .iter()
            .map(|(name, constant)| (Name::from(&**name), Name::from(&**constant)))
            .collect(),
        facts: data
            .facts
            .iter()
            .map(|fact| (Name::from(&*fact.name), fact.thms.iter().map(thm).collect()))
            .collect(),
        fact_names: data
            .fact_names
            .iter()
            .map(|(name, fact)| (Name::from(&**name), Name::from(&**fact)))
            .collect(),
        simps: data.simps.iter().map(thm).collect(),
        congs: data
            .congs
            .iter()
            .map(|cong| LogicCong {
                name: CongName {
                    is_const: cong.is_const,
                    name: Name::from(&*cong.name),
                },
                rule: thm(&cong.rule),
            })
            .collect(),
        weak_congs: data
            .weak_congs
            .iter()
            .map(|cong| CongName {
                is_const: cong.is_const,
                name: Name::from(&*cong.name),
            })
            .collect(),
        simprocs: data
            .simprocs
            .iter()
            .map(|simproc| LogicSimproc {
                name: Name::from(&*simproc.name),
                lhss: simproc
                    .lhss
                    .iter()
                    .map(|id| decoder.get_term(*id))
                    .collect(),
            })
            .collect(),
        claset: LogicClaset {
            safe_is: claset.safe_is.iter().map(to_rule).collect(),
            safe_es: claset.safe_es.iter().map(to_rule).collect(),
            unsafe_is: claset.unsafe_is.iter().map(to_rule).collect(),
            unsafe_es: claset.unsafe_es.iter().map(to_rule).collect(),
            safe0: to_items(&claset.safe0),
            safep: to_items(&claset.safep),
            r#unsafe: to_items(&claset.r#unsafe),
            dup: to_items(&claset.dup),
        },
        context_rules: LogicContextRules {
            bang: to_extra_items(&data.context_rules.bang),
            plain: to_extra_items(&data.context_rules.plain),
        },
    }
}

/// Nothing changes the logic, so it parses once per thread (its terms are `Rc`).
pub fn load_logic() -> Rc<TlaLogic> {
    thread_local!(static LOGIC: Rc<TlaLogic> = Rc::new(parse_logic()));
    LOGIC.with(Rc::clone)
}
