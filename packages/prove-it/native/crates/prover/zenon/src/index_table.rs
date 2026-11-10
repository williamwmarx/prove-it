// Ported from Zenon's index.ml, as shipped in tlapm. Copyright 2004 INRIA, see LICENSE.
//! The formulas on the current branch, indexed by head symbol, by the sides of equalities and
//! transitive relations, and the cache of proved lemmas. Formulas are added and removed in LIFO
//! order as the search descends and backtracks. Lists keep Zenon's order, latest first. No table
//! here is iterated, so std hash maps keep the TypeScript's behaviour.

use std::cell::RefCell;
use std::collections::{HashMap, VecDeque};
use std::hash::Hash;
use std::rc::Rc;

use crate::expr::{Expr, Expressions, Kind};
use crate::parse::Definition;
use crate::proof::Proof;

struct LemmaRecord {
    is_present: bool,
    proofs: VecDeque<Rc<RefCell<Suspect>>>,
}

struct Suspect {
    proof: Rc<Proof>,
    cursor: usize,
    records: Vec<Rc<RefCell<LemmaRecord>>>,
}

/// A stack of values per key, as a Hashtbl with Hashtbl.add and Hashtbl.remove.
fn push_value<K: Eq + Hash, V>(table: &mut HashMap<K, Vec<V>>, key: K, value: V) {
    table.entry(key).or_default().push(value);
}

fn pop_value<K: Eq + Hash, V>(table: &mut HashMap<K, Vec<V>>, key: &K) {
    let Some(values) = table.get_mut(key) else {
        return;
    };
    values.pop();
    if values.is_empty() {
        table.remove(key);
    }
}

fn get_latest_first<K: Eq + Hash, V: Clone>(table: &HashMap<K, Vec<V>>, key: &K) -> Vec<V> {
    table
        .get(key)
        .map(|values| values.iter().rev().cloned().collect())
        .unwrap_or_default()
}

/// Zenon's head of a term. Taus and metavariables are heads by identity.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Head {
    Symbol(Rc<str>),
    Expr(Expr),
}

/// `getHead`: the head of a term, or `None` for Zenon's No_head.
pub fn get_head(expression: &Expr) -> Option<Head> {
    match expression.kind {
        Kind::App | Kind::Var => Some(Head::Symbol(expression.symbol.clone())),
        Kind::Meta | Kind::Tau => Some(Head::Expr(expression.clone())),
        Kind::True => Some(Head::Symbol("$true".into())),
        Kind::False => Some(Head::Symbol("$false".into())),
        Kind::All => Some(Head::Symbol("A.".into())),
        Kind::Ex => Some(Head::Symbol("E.".into())),
        _ => None,
    }
}

/// Zenon indexes formulas by head under a string; every tau shares "t." and every metavariable "".
fn get_head_key(head: &Head) -> Rc<str> {
    match head {
        Head::Symbol(symbol) => symbol.clone(),
        Head::Expr(expression) if expression.kind == Kind::Tau => "t.".into(),
        Head::Expr(_) => "".into(),
    }
}

/// Zenon's add_element: `pushValue`.
fn add_element<K: Eq + Hash, V>(table: &mut HashMap<K, Vec<V>>, key: K, value: V) {
    push_value(table, key, value);
}

/// Zenon's remove_element. Removing from a one-element list drops the key whatever the element,
/// as Zenon does. False stands for Zenon's Not_found.
fn remove_element<K: Eq + Hash, V: PartialEq>(
    table: &mut HashMap<K, Vec<V>>,
    key: &K,
    value: &V,
) -> bool {
    let Some(values) = table.get_mut(key) else {
        return false;
    };
    if values.len() == 1 {
        table.remove(key);
    } else if values.last() == Some(value) {
        values.pop();
    }
    true
}

/// Formulas by the key of their head.
type HeadTable = HashMap<Rc<str>, Vec<Expr>>;

/// Keys pair a relation with a head. Heads that are expressions are told apart by identity.
type RelationKey = (Rc<str>, Head);

struct StringEquality {
    is_reversed: bool,
    term: Expr,
    value: Rc<str>,
}

fn get_string_literal(expression: &Expr) -> Option<Rc<str>> {
    (expression.is_app_with_arity("$string", 1) && expression.args[0].kind == Kind::Var)
        .then(|| expression.args[0].symbol.clone())
}

fn get_string_equality(formula: &Expr) -> Option<StringEquality> {
    if !formula.is_app_with_arity("=", 2) {
        return None;
    }
    if let Some(value) = get_string_literal(&formula.args[1]) {
        return Some(StringEquality {
            is_reversed: false,
            term: formula.args[0].clone(),
            value,
        });
    }
    get_string_literal(&formula.args[0]).map(|value| StringEquality {
        is_reversed: true,
        term: formula.args[1].clone(),
        value,
    })
}

fn is_equality(formula: &Expr) -> bool {
    formula.is_app_with_arity("=", 2)
}

#[derive(Default)]
pub struct Index {
    formulas: HashMap<Expr, Vec<i64>>,
    positive: HeadTable,
    negative: HeadTable,
    trans_left: HashMap<RelationKey, Vec<Expr>>,
    trans_right: HashMap<RelationKey, Vec<Expr>>,
    neg_trans_left: HashMap<RelationKey, Vec<Expr>>,
    neg_trans_right: HashMap<RelationKey, Vec<Expr>>,
    all_neg_trans_left: HashMap<Head, Vec<Expr>>,
    all_neg_trans_right: HashMap<Head, Vec<Expr>>,
    equal_left_right: HashMap<Expr, Vec<Expr>>,
    equal_right_left: HashMap<Expr, Vec<Expr>>,
    unequal_left_right: HashMap<Expr, Vec<Expr>>,
    unequal_right_left: HashMap<Expr, Vec<Expr>>,
    /// Latest first.
    string_equalities: VecDeque<(Expr, Rc<str>)>,
    reversed_string_equalities: VecDeque<(Expr, Rc<str>)>,
    definitions: HashMap<String, Rc<Definition>>,
    lemmas: HashMap<Expr, Rc<RefCell<LemmaRecord>>>,
    new_formulas: Vec<Expr>,
    suspects: VecDeque<VecDeque<Rc<RefCell<Suspect>>>>,
    formula_count: u64,
    top_formula_count: u64,
}

impl Index {
    pub fn new() -> Index {
        Index::default()
    }

    pub fn is_member(&self, formula: &Expr) -> bool {
        self.formulas.contains_key(formula)
    }

    pub fn get_goalness(&self, formula: &Expr) -> i64 {
        self.formulas
            .get(formula)
            .and_then(|goalnesses| goalnesses.last().copied())
            .unwrap_or(0)
    }

    fn with_goalness(&self, list: Vec<Expr>) -> Vec<(Expr, i64)> {
        list.into_iter()
            .map(|formula| {
                let goalness = self.get_goalness(&formula);
                (formula, goalness)
            })
            .collect()
    }

    /// Zenon's negpos: a negation under the head of its operand, anything else under its own head.
    fn get_head_table(&mut self, formula: &Expr) -> Option<(&mut HeadTable, Rc<str>)> {
        if formula.kind == Kind::Not {
            let head = get_head(&formula.args[0])?;
            return Some((&mut self.negative, get_head_key(&head)));
        }
        let head = get_head(formula)?;
        Some((&mut self.positive, get_head_key(&head)))
    }

    pub fn add(&mut self, formula: &Expr, goalness: i64) {
        push_value(&mut self.formulas, formula.clone(), goalness);
        if is_equality(formula) {
            push_value(
                &mut self.equal_left_right,
                formula.args[0].clone(),
                formula.args[1].clone(),
            );
            push_value(
                &mut self.equal_right_left,
                formula.args[1].clone(),
                formula.args[0].clone(),
            );
        } else if formula.kind == Kind::Not && is_equality(&formula.args[0]) {
            let equality = &formula.args[0];
            push_value(
                &mut self.unequal_left_right,
                equality.args[0].clone(),
                equality.args[1].clone(),
            );
            push_value(
                &mut self.unequal_right_left,
                equality.args[1].clone(),
                equality.args[0].clone(),
            );
        }
        if let Some(equality) = get_string_equality(formula) {
            let list = if equality.is_reversed {
                &mut self.reversed_string_equalities
            } else {
                &mut self.string_equalities
            };
            list.push_front((equality.term, equality.value));
        }
        self.formula_count += 1;
        self.top_formula_count = self.top_formula_count.max(self.formula_count);
        if let Some((table, key)) = self.get_head_table(formula) {
            add_element(table, key, formula.clone());
        }
        if let Some(lemma) = self.lemmas.get(formula) {
            lemma.borrow_mut().is_present = true;
        }
        self.new_formulas.insert(0, formula.clone());
    }

    fn remove_trans(&mut self, formula: &Expr) {
        if !formula.is_relation() {
            return;
        }
        if let Some(head) = get_head(&formula.args[0]) {
            remove_element(
                &mut self.trans_left,
                &(formula.symbol.clone(), head),
                formula,
            );
        }
        if let Some(head) = get_head(&formula.args[1]) {
            remove_element(
                &mut self.trans_right,
                &(formula.symbol.clone(), head),
                formula,
            );
        }
    }

    fn remove_neg_trans(&mut self, formula: &Expr) {
        if !formula.is_negated_relation() {
            return;
        }
        let relation = &formula.args[0];
        if let Some(head) = get_head(&relation.args[0])
            && remove_element(
                &mut self.neg_trans_left,
                &(relation.symbol.clone(), head.clone()),
                formula,
            )
        {
            remove_element(&mut self.all_neg_trans_left, &head, formula);
        }
        if let Some(head) = get_head(&relation.args[1])
            && remove_element(
                &mut self.neg_trans_right,
                &(relation.symbol.clone(), head.clone()),
                formula,
            )
        {
            remove_element(&mut self.all_neg_trans_right, &head, formula);
        }
    }

    pub fn remove(&mut self, formula: &Expr) {
        self.formula_count -= 1;
        self.remove_trans(formula);
        self.remove_neg_trans(formula);
        if let Some((table, key)) = self.get_head_table(formula) {
            remove_element(table, &key, formula);
        }
        if let Some(equality) = get_string_equality(formula) {
            let list = if equality.is_reversed {
                &mut self.reversed_string_equalities
            } else {
                &mut self.string_equalities
            };
            list.pop_front();
        }
        if is_equality(formula) {
            pop_value(&mut self.equal_left_right, &formula.args[0]);
            pop_value(&mut self.equal_right_left, &formula.args[1]);
        } else if formula.kind == Kind::Not && is_equality(&formula.args[0]) {
            pop_value(&mut self.unequal_left_right, &formula.args[0].args[0]);
            pop_value(&mut self.unequal_right_left, &formula.args[0].args[1]);
        }
        pop_value(&mut self.formulas, formula);
        if let Some(lemma) = self.lemmas.get(formula) {
            lemma.borrow_mut().is_present = false;
        }
    }

    /// Zenon's add_trans, which stops at the first side without a head. False means No_head.
    pub fn add_trans(&mut self, formula: &Expr) -> bool {
        let Some(left_head) = get_head(&formula.args[0]) else {
            return false;
        };
        add_element(
            &mut self.trans_left,
            (formula.symbol.clone(), left_head),
            formula.clone(),
        );
        let Some(right_head) = get_head(&formula.args[1]) else {
            return false;
        };
        add_element(
            &mut self.trans_right,
            (formula.symbol.clone(), right_head),
            formula.clone(),
        );
        true
    }

    pub fn add_neg_trans(&mut self, formula: &Expr) {
        let relation = &formula.args[0];
        if let Some(head) = get_head(&relation.args[0]) {
            add_element(
                &mut self.neg_trans_left,
                (relation.symbol.clone(), head.clone()),
                formula.clone(),
            );
            add_element(&mut self.all_neg_trans_left, head, formula.clone());
        }
        if let Some(head) = get_head(&relation.args[1]) {
            add_element(
                &mut self.neg_trans_right,
                (relation.symbol.clone(), head.clone()),
                formula.clone(),
            );
            add_element(&mut self.all_neg_trans_right, head, formula.clone());
        }
    }

    pub fn add_lemma(&mut self, proof: Rc<Proof>) {
        let records = proof
            .conclusions
            .iter()
            .map(|formula| {
                if let Some(existing) = self.lemmas.get(formula) {
                    return existing.clone();
                }
                let record = Rc::new(RefCell::new(LemmaRecord {
                    is_present: self.formulas.contains_key(formula),
                    proofs: VecDeque::new(),
                }));
                self.lemmas.insert(formula.clone(), record.clone());
                record
            })
            .collect();
        let suspect = Suspect {
            proof,
            cursor: 0,
            records,
        };
        self.suspects
            .push_front(VecDeque::from([Rc::new(RefCell::new(suspect))]));
    }

    /// A cached lemma whose conclusions are all on the branch. A lemma waits on the first
    /// conclusion that is missing, and is checked again when that formula comes back.
    pub fn search_lemma(&mut self) -> Option<Rc<Proof>> {
        for formula in std::mem::take(&mut self.new_formulas) {
            if let Some(record) = self.lemmas.get(&formula) {
                let mut record = record.borrow_mut();
                if record.is_present {
                    let proofs = std::mem::take(&mut record.proofs);
                    self.suspects.push_front(proofs);
                }
            }
        }
        while let Some(group) = self.suspects.front_mut() {
            let Some(suspect) = group.front().cloned() else {
                self.suspects.pop_front();
                continue;
            };
            let mut borrowed = suspect.borrow_mut();
            let count = borrowed.records.len();
            let cursor = borrowed.cursor;
            let missing = (cursor..count)
                .chain(0..cursor)
                .find(|index| !borrowed.records[*index].borrow().is_present);
            let Some(missing) = missing else {
                return Some(borrowed.proof.clone());
            };
            group.pop_front();
            borrowed.records[missing]
                .borrow_mut()
                .proofs
                .push_front(suspect.clone());
            borrowed.cursor = missing + 1;
        }
        None
    }

    pub fn find_positive(&self, symbol: &str) -> Vec<(Expr, i64)> {
        self.with_goalness(get_latest_first(&self.positive, &Rc::from(symbol)))
    }

    pub fn find_negative(&self, symbol: &str) -> Vec<(Expr, i64)> {
        self.with_goalness(get_latest_first(&self.negative, &Rc::from(symbol)))
    }

    pub fn find_equal_right(&self, term: &Expr) -> Vec<Expr> {
        get_latest_first(&self.equal_left_right, term)
    }

    pub fn find_equal_left(&self, term: &Expr) -> Vec<Expr> {
        get_latest_first(&self.equal_right_left, term)
    }

    pub fn find_disequalities(&self, exprs: &Expressions, term: &Expr) -> Vec<Expr> {
        let left_right = get_latest_first(&self.unequal_left_right, term)
            .into_iter()
            .map(|other| exprs.enot(&exprs.eapp("=", &[term.clone(), other])));
        let right_left = get_latest_first(&self.unequal_right_left, term)
            .into_iter()
            .map(|other| exprs.enot(&exprs.eapp("=", &[other, term.clone()])));
        left_right.chain(right_left).collect()
    }

    /// The string equalities on the branch, latest first.
    pub fn get_string_equalities(&self) -> &VecDeque<(Expr, Rc<str>)> {
        &self.string_equalities
    }

    pub fn get_reversed_string_equalities(&self) -> &VecDeque<(Expr, Rc<str>)> {
        &self.reversed_string_equalities
    }

    pub fn find_trans_left(&self, relation: &str, head: &Head) -> Vec<(Expr, i64)> {
        self.with_goalness(get_latest_first(
            &self.trans_left,
            &(relation.into(), head.clone()),
        ))
    }

    pub fn find_trans_right(&self, relation: &str, head: &Head) -> Vec<(Expr, i64)> {
        self.with_goalness(get_latest_first(
            &self.trans_right,
            &(relation.into(), head.clone()),
        ))
    }

    pub fn find_neg_trans_left(&self, relation: &str, head: &Head) -> Vec<(Expr, i64)> {
        self.with_goalness(get_latest_first(
            &self.neg_trans_left,
            &(relation.into(), head.clone()),
        ))
    }

    pub fn find_neg_trans_right(&self, relation: &str, head: &Head) -> Vec<(Expr, i64)> {
        self.with_goalness(get_latest_first(
            &self.neg_trans_right,
            &(relation.into(), head.clone()),
        ))
    }

    pub fn find_all_neg_trans_left(&self, head: &Head) -> Vec<(Expr, i64)> {
        self.with_goalness(get_latest_first(&self.all_neg_trans_left, head))
    }

    pub fn find_all_neg_trans_right(&self, head: &Head) -> Vec<(Expr, i64)> {
        self.with_goalness(get_latest_first(&self.all_neg_trans_right, head))
    }

    pub fn add_definition(&mut self, definition: Rc<Definition>) {
        self.definitions
            .insert(definition.symbol().to_owned(), definition);
    }

    pub fn get_definition(&self, symbol: &str) -> Option<Rc<Definition>> {
        self.definitions.get(symbol).cloned()
    }

    pub fn get_top_formula_count(&self) -> u64 {
        self.top_formula_count
    }
}
