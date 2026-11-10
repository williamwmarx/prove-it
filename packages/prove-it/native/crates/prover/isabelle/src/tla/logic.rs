//! The Isabelle/TLA+ object logic that tlapm ships, decoded from logic_data.rs: its constants, the
//! theorems its theories prove, and the order of the simpset and the classical rule nets.

use std::collections::HashMap;
use std::rc::Rc;

use crate::pure::consts::{TypargPosition, typargs_of};
use crate::pure::term::{
    Name, Term, Typ, empty_sort, mk_abs, mk_app, mk_bound, mk_const, mk_free, mk_tfree, mk_tvar,
    mk_type, mk_var,
};

use super::logic_data::{LogicData, TermNode, TypeNode, logic_data};

#[derive(Clone)]
pub struct ConstInfo {
    pub ty: Typ,
    pub typargs: Rc<[TypargPosition]>,
    /// The right-hand side of an abbreviation, which parsing unfolds.
    pub abbreviation: Option<Term>,
}

pub struct TlaLogic {
    pub consts: HashMap<Name, ConstInfo>,
    /// The constant each unqualified name stands for.
    pub const_names: HashMap<Name, Name>,
    // The theorems, simpset and claset are added with thm.rs.
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
    }
}

/// Nothing changes the logic, so it parses once per thread (its terms are `Rc`).
pub fn load_logic() -> Rc<TlaLogic> {
    thread_local!(static LOGIC: Rc<TlaLogic> = Rc::new(parse_logic()));
    LOGIC.with(Rc::clone)
}
