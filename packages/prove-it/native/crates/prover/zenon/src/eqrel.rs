// Ported from Zenon's eqrel.ml, as shipped in tlapm. Copyright 2004 INRIA, see LICENSE.
//! Finds the hypotheses that make a relation reflexive, symmetric or transitive. The prover then
//! reasons with those properties directly, and drops the hypotheses that only state them. The
//! translation to Isar proves the properties again from the hypotheses that stated them.

use std::collections::HashMap;

use crate::expr::{Expr, Expressions, Kind, etrue};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Direction {
    Left,
    Right,
}

/// Where a hypothesis states a property: the conjunct at `directions`, with the relation's
/// arguments bound by the quantifiers at `variables`, counted from the outermost.
#[derive(Clone, Debug)]
pub struct Origin {
    pub formula: Expr,
    pub directions: Vec<Direction>,
    pub variables: Vec<usize>,
}

#[derive(Clone, Debug, Default)]
pub struct RelationInfo {
    pub reflexive: Option<Origin>,
    pub symmetric: Option<Origin>,
    pub transitive: Option<Origin>,
    pub transitive_symmetric: Option<Origin>,
    /// The type of the relation's arguments.
    pub type_name: String,
}

#[derive(Clone)]
struct Bound {
    name: String,
    type_name: String,
}

/// A conjunct of a hypothesis: the variables quantified around it and the literals of its
/// disjunction, when they all relate two of those variables by the same symbol.
struct Leaves {
    directions: Vec<Direction>,
    env: Vec<Bound>,
    leaves: Vec<Expr>,
    type_name: String,
}

fn get_atom(leaf: &Expr) -> &Expr {
    if leaf.kind == Kind::Not {
        &leaf.args[0]
    } else {
        leaf
    }
}

fn get_leaves(
    exprs: &Expressions,
    directions: Vec<Direction>,
    env: Vec<Bound>,
    formula: &Expr,
) -> Leaves {
    struct Visitor<'a> {
        exprs: &'a Expressions,
        env: &'a [Bound],
        leaves: Vec<Expr>,
        symbol: Option<String>,
        type_name: String,
    }
    impl Visitor<'_> {
        fn get_bound(&self, term: &Expr) -> Option<&Bound> {
            if term.kind != Kind::Var {
                return None;
            }
            self.env.iter().find(|bound| *bound.name == *term.symbol)
        }

        fn visit_leaf(&mut self, leaf: &Expr) -> bool {
            let atom = get_atom(leaf);
            if atom.kind != Kind::App {
                return false;
            }
            let first = atom
                .args
                .first()
                .and_then(|arg| self.get_bound(arg))
                .cloned();
            let is_relation = atom.args.len() == 2
                && self
                    .symbol
                    .as_ref()
                    .is_none_or(|symbol| **symbol == *atom.symbol)
                && first.is_some()
                && self.get_bound(&atom.args[1]).is_some();
            let Some(first) = first.filter(|_| is_relation) else {
                return false;
            };
            if self.symbol.is_none() {
                self.type_name = first.type_name;
            }
            self.symbol = Some(atom.symbol.to_string());
            self.leaves.insert(0, leaf.clone());
            true
        }

        fn visit(&mut self, disjunct: &Expr) -> bool {
            let exprs = self.exprs;
            match disjunct.kind {
                Kind::Or => return self.visit(&disjunct.args[0]) && self.visit(&disjunct.args[1]),
                Kind::Imply => {
                    return self.visit(&exprs.enot(&disjunct.args[0]))
                        && self.visit(&disjunct.args[1]);
                }
                Kind::Not => {
                    let operand = &disjunct.args[0];
                    match operand.kind {
                        Kind::And => {
                            return self.visit(&exprs.enot(&operand.args[0]))
                                && self.visit(&exprs.enot(&operand.args[1]));
                        }
                        Kind::Not => return self.visit(&operand.args[0]),
                        Kind::True => return true,
                        _ => {}
                    }
                }
                Kind::False => return true,
                _ => {}
            }
            self.visit_leaf(disjunct)
        }
    }
    let mut visitor = Visitor {
        exprs,
        env: &env,
        leaves: Vec::new(),
        symbol: None,
        type_name: String::new(),
    };
    if visitor.visit(formula) {
        let leaves = visitor.leaves;
        let type_name = visitor.type_name;
        Leaves {
            directions,
            env,
            leaves,
            type_name,
        }
    } else {
        Leaves {
            directions,
            env,
            leaves: Vec::new(),
            type_name: String::new(),
        }
    }
}

fn get_conjuncts(exprs: &Expressions, formula: &Expr) -> Vec<Leaves> {
    fn visit(
        exprs: &Expressions,
        conjuncts: &mut Vec<Leaves>,
        directions: &[Direction],
        env: &[Bound],
        conjunct: &Expr,
    ) {
        let left = [directions, &[Direction::Left]].concat();
        let right = [directions, &[Direction::Right]].concat();
        let operand = (conjunct.kind == Kind::Not).then(|| &conjunct.args[0]);
        let operand_kind = operand.map(|operand| operand.kind);
        let with_bound = |binder: &Expr| {
            let bound = Bound {
                name: binder.args[0].symbol.to_string(),
                type_name: binder.symbol.to_string(),
            };
            [&[bound], env].concat()
        };
        if conjunct.kind == Kind::And {
            visit(exprs, conjuncts, &left, env, &conjunct.args[0]);
            visit(exprs, conjuncts, &right, env, &conjunct.args[1]);
        } else if conjunct.kind == Kind::All {
            visit(
                exprs,
                conjuncts,
                directions,
                &with_bound(conjunct),
                &conjunct.args[1],
            );
        } else if let (Some(operand), Some(Kind::Or)) = (operand, operand_kind) {
            visit(exprs, conjuncts, &left, env, &exprs.enot(&operand.args[0]));
            visit(exprs, conjuncts, &right, env, &exprs.enot(&operand.args[1]));
        } else if let (Some(operand), Some(Kind::Imply)) = (operand, operand_kind) {
            visit(exprs, conjuncts, &left, env, &operand.args[0]);
            visit(exprs, conjuncts, &right, env, &exprs.enot(&operand.args[1]));
        } else if let (Some(operand), Some(Kind::Ex)) = (operand, operand_kind) {
            visit(
                exprs,
                conjuncts,
                directions,
                &with_bound(operand),
                &exprs.enot(&operand.args[1]),
            );
        } else if let (Some(operand), Some(Kind::Not)) = (operand, operand_kind) {
            visit(exprs, conjuncts, directions, env, &operand.args[0]);
        } else if conjunct.kind == Kind::Equiv {
            visit(
                exprs,
                conjuncts,
                &left,
                env,
                &exprs.eimply(&conjunct.args[0], &conjunct.args[1]),
            );
            visit(
                exprs,
                conjuncts,
                &right,
                env,
                &exprs.eimply(&conjunct.args[1], &conjunct.args[0]),
            );
        } else if let (Some(operand), Some(Kind::Equiv)) = (operand, operand_kind) {
            visit(
                exprs,
                conjuncts,
                &left,
                env,
                &exprs.eor(&operand.args[0], &operand.args[1]),
            );
            let negated = exprs.eor(&exprs.enot(&operand.args[0]), &exprs.enot(&operand.args[1]));
            visit(exprs, conjuncts, &right, env, &negated);
        } else {
            conjuncts.insert(
                0,
                get_leaves(exprs, directions.to_vec(), env.to_vec(), conjunct),
            );
        }
    }
    let mut conjuncts = Vec::new();
    visit(exprs, &mut conjuncts, &[], &[], formula);
    conjuncts
}

type Pair = [String; 2];

fn get_pair(leaf: &Expr) -> Pair {
    let atom = get_atom(leaf);
    [
        atom.args[0].symbol.to_string(),
        atom.args[1].symbol.to_string(),
    ]
}

/// The leaves as Zenon's partition returns them: positive and negative, each reversed.
fn partition(leaves: &[Expr]) -> (Vec<Pair>, Vec<Pair>) {
    let get = |is_negative: bool| {
        leaves
            .iter()
            .rev()
            .filter(|leaf| (leaf.kind == Kind::Not) == is_negative)
            .map(get_pair)
            .collect()
    };
    (get(false), get(true))
}

/// Each check returns the variables that the translation instantiates to prove the property, or
/// `None` when the conjunct doesn't state it.
fn get_reflexive(leaves: &[Expr]) -> Option<Vec<String>> {
    if leaves.len() != 1 || leaves[0].kind == Kind::Not {
        return None;
    }
    let pair = get_pair(&leaves[0]);
    (pair[0] == pair[1]).then(|| vec![pair[0].clone()])
}

fn get_symmetric(leaves: &[Expr]) -> Option<Vec<String>> {
    let (positive, negative) = partition(leaves);
    if positive.len() != 1 || negative.len() != 1 {
        return None;
    }
    let positive = &positive[0];
    let negative = &negative[0];
    (positive[0] == negative[1] && positive[1] == negative[0]).then(|| negative.to_vec())
}

fn get_triple(leaves: &[Expr]) -> Option<(Pair, Pair, Pair)> {
    let (positive, negative) = partition(leaves);
    (positive.len() == 1 && negative.len() == 2).then(|| {
        (
            positive[0].clone(),
            negative[0].clone(),
            negative[1].clone(),
        )
    })
}

fn get_transitive(leaves: &[Expr]) -> Option<Vec<String>> {
    let (result, first, second) = get_triple(leaves)?;
    if first[1] == second[0] && result[0] == first[0] && result[1] == second[1] {
        return Some(vec![result[0].clone(), first[1].clone(), result[1].clone()]);
    }
    if second[1] == first[0] && result[0] == second[0] && result[1] == first[1] {
        return Some(vec![result[0].clone(), first[0].clone(), result[1].clone()]);
    }
    None
}

fn get_transitive_symmetric(leaves: &[Expr]) -> Option<Vec<String>> {
    let (result, first, second) = get_triple(leaves)?;
    if first[1] == second[0] && result[1] == first[0] && result[0] == second[1] {
        return Some(vec![result[1].clone(), first[1].clone(), result[0].clone()]);
    }
    if second[1] == first[0] && result[1] == second[0] && result[0] == first[1] {
        return Some(vec![result[1].clone(), first[0].clone(), result[0].clone()]);
    }
    None
}

fn get_symbol(leaves: &[Expr]) -> String {
    get_atom(&leaves[0]).symbol.to_string()
}

/// The relations the hypotheses describe: `createRelations`.
pub struct Relations {
    relations: HashMap<String, RelationInfo>,
}

impl Default for Relations {
    fn default() -> Self {
        Self::new()
    }
}

impl Relations {
    pub fn new() -> Relations {
        let equality_origin = Origin {
            formula: etrue(),
            directions: Vec::new(),
            variables: Vec::new(),
        };
        let equality = RelationInfo {
            reflexive: Some(equality_origin.clone()),
            symmetric: Some(equality_origin.clone()),
            transitive: Some(equality_origin.clone()),
            transitive_symmetric: Some(equality_origin),
            type_name: String::new(),
        };
        Relations {
            relations: HashMap::from([("=".to_owned(), equality)]),
        }
    }

    fn get_record(&mut self, symbol: String) -> &mut RelationInfo {
        self.relations.entry(symbol).or_default()
    }

    pub fn analyse(&mut self, exprs: &Expressions, formula: &Expr) {
        for conjunct in get_conjuncts(exprs, formula) {
            let leaves = &conjunct.leaves;
            let env = &conjunct.env;
            let get_origin = |names: Option<Vec<String>>| {
                names.map(|names| Origin {
                    formula: formula.clone(),
                    directions: conjunct.directions.clone(),
                    variables: names
                        .iter()
                        .map(|name| {
                            env.iter()
                                .position(|bound| bound.name == *name)
                                .map_or(env.len(), |index| env.len() - 1 - index)
                        })
                        .collect(),
                })
            };
            let reflexive = get_origin(get_reflexive(leaves));
            let symmetric = get_origin(get_symmetric(leaves));
            let transitive = get_origin(get_transitive(leaves));
            let transitive_symmetric = get_origin(get_transitive_symmetric(leaves));
            if reflexive.is_none()
                && symmetric.is_none()
                && transitive.is_none()
                && transitive_symmetric.is_none()
            {
                continue;
            }
            let record = self.get_record(get_symbol(leaves));
            if reflexive.is_some() {
                record.reflexive = reflexive;
            }
            if symmetric.is_some() {
                record.symmetric = symmetric;
            }
            if transitive.is_some() {
                record.transitive = transitive;
            }
            if transitive_symmetric.is_some() {
                record.transitive_symmetric = transitive_symmetric;
            }
            record.type_name = conjunct.type_name.clone();
        }
    }

    pub fn is_subsumed(&mut self, exprs: &Expressions, formula: &Expr) -> bool {
        get_conjuncts(exprs, formula).iter().all(|conjunct| {
            let leaves = &conjunct.leaves;
            if get_reflexive(leaves).is_some() {
                return self.get_record(get_symbol(leaves)).reflexive.is_some();
            }
            if get_symmetric(leaves).is_some() {
                return self.get_record(get_symbol(leaves)).symmetric.is_some();
            }
            if get_transitive(leaves).is_some() {
                return self.get_record(get_symbol(leaves)).transitive.is_some();
            }
            if get_transitive_symmetric(leaves).is_some() {
                let record = self.get_record(get_symbol(leaves));
                return record.symmetric.is_some() && record.transitive.is_some();
            }
            false
        })
    }

    pub fn is_reflexive(&self, symbol: &str) -> bool {
        self.get(symbol)
            .is_some_and(|record| record.reflexive.is_some())
    }

    pub fn is_symmetric(&self, symbol: &str) -> bool {
        self.get(symbol).is_some_and(|record| {
            record.symmetric.is_some()
                || (record.reflexive.is_some() && record.transitive_symmetric.is_some())
        })
    }

    pub fn is_transitive(&self, symbol: &str) -> bool {
        self.get(symbol).is_some_and(|record| {
            record.transitive.is_some()
                || (record.reflexive.is_some() && record.transitive_symmetric.is_some())
        })
    }

    pub fn is_any(&self, symbol: &str) -> bool {
        self.get(symbol).is_some_and(|record| {
            record.reflexive.is_some() || record.symmetric.is_some() || record.transitive.is_some()
        })
    }

    /// Where the hypotheses state a relation's properties, for the translation to Isar.
    pub fn get(&self, symbol: &str) -> Option<&RelationInfo> {
        self.relations.get(symbol)
    }
}
