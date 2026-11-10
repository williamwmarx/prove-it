// Ported from Zenon's llproof.ml, as shipped in tlapm. Copyright 2004 INRIA, see LICENSE.
//! The low-level proofs that Zenon prints: each node's conclusions are the formulas its subproofs
//! leave open, and the proof is a list of lemmas, the theorem last.

use std::collections::HashMap;
use std::rc::Rc;

use crate::ZenonError;
use crate::expr::{Expr, Expressions, Kind, efalse, etrue};

/// A binary connective: and, or, imply or equiv.
pub type Connective = Kind;

#[derive(Clone, Debug)]
pub enum LlRule {
    False,
    NotTrue,
    Axiom(Expr),
    Cut(Expr),
    NotEq(Expr),
    EqSym {
        left: Expr,
        right: Expr,
    },
    NotNot(Expr),
    Connect {
        connective: Connective,
        left: Expr,
        right: Expr,
    },
    NotConnect {
        connective: Connective,
        left: Expr,
        right: Expr,
    },
    /// The quantified formula, and the witness or the term that instantiates it.
    Ex {
        quantified: Expr,
        term: Expr,
    },
    All {
        quantified: Expr,
        term: Expr,
    },
    NotEx {
        quantified: Expr,
        term: Expr,
    },
    NotAll {
        quantified: Expr,
        term: Expr,
    },
    PNotP {
        positive: Expr,
        negative: Expr,
    },
    NotEqual {
        left: Expr,
        right: Expr,
    },
    CongruenceLr {
        context: Expr,
        left: Expr,
        right: Expr,
    },
    CongruenceRl {
        context: Expr,
        left: Expr,
        right: Expr,
    },
    Definition {
        name: String,
        folded: Expr,
        unfolded: Expr,
    },
    Extension {
        name: String,
        args: Vec<Expr>,
        conclusions: Vec<Expr>,
        branches: Vec<Vec<Expr>>,
    },
    Lemma {
        name: String,
        args: Vec<Expr>,
    },
}

impl LlRule {
    /// The TypeScript's `kind` of the rule.
    pub fn kind(&self) -> &'static str {
        match self {
            LlRule::False => "false",
            LlRule::NotTrue => "nottrue",
            LlRule::Axiom(_) => "axiom",
            LlRule::Cut(_) => "cut",
            LlRule::NotEq(_) => "noteq",
            LlRule::EqSym { .. } => "eqsym",
            LlRule::NotNot(_) => "notnot",
            LlRule::Connect { .. } => "connect",
            LlRule::NotConnect { .. } => "notconnect",
            LlRule::Ex { .. } => "ex",
            LlRule::All { .. } => "all",
            LlRule::NotEx { .. } => "notex",
            LlRule::NotAll { .. } => "notall",
            LlRule::PNotP { .. } => "pnotp",
            LlRule::NotEqual { .. } => "notequal",
            LlRule::CongruenceLr { .. } => "congruencelr",
            LlRule::CongruenceRl { .. } => "congruencerl",
            LlRule::Definition { .. } => "definition",
            LlRule::Extension { .. } => "extension",
            LlRule::Lemma { .. } => "lemma",
        }
    }
}

#[derive(Debug)]
pub struct LlProof {
    pub conclusions: Vec<Expr>,
    pub rule: LlRule,
    pub subproofs: Vec<Rc<LlProof>>,
}

/// A lemma's parameters pair each free tau or metavariable with its type.
#[derive(Clone, Debug)]
pub struct Lemma {
    pub name: String,
    pub params: Vec<(String, Expr)>,
    pub proof: Rc<LlProof>,
}

/// The formula of `connective` on two operands.
pub fn connect(exprs: &Expressions, connective: Connective, left: &Expr, right: &Expr) -> Expr {
    exprs.binary(connective, left, right)
}

fn get_lemma<'a>(lemmas: &'a HashMap<String, Lemma>, name: &str) -> Result<&'a Lemma, ZenonError> {
    lemmas
        .get(name)
        .ok_or_else(|| ZenonError::new(format!("Zenon: no lemma {name}")))
}

fn make_leaf(conclusions: Vec<Expr>, rule: LlRule) -> Rc<LlProof> {
    Rc::new(LlProof {
        conclusions,
        rule,
        subproofs: Vec::new(),
    })
}

/// Zenon's direct_close: a node that closes the conclusions at once, if one does.
fn get_direct_close(exprs: &Expressions, conclusions: &[Expr]) -> Option<Rc<LlProof>> {
    for (position, formula) in conclusions.iter().enumerate() {
        let rest = &conclusions[position + 1..];
        if formula.kind == Kind::False {
            return Some(make_leaf(vec![formula.clone()], LlRule::False));
        }
        if formula.kind == Kind::Not {
            let operand = &formula.args[0];
            if operand.kind == Kind::True {
                return Some(make_leaf(vec![formula.clone()], LlRule::NotTrue));
            }
            if operand.is_app_with_arity("=", 2) && operand.args[0] == operand.args[1] {
                return Some(make_leaf(
                    vec![formula.clone()],
                    LlRule::NotEq(operand.args[0].clone()),
                ));
            }
            if rest.contains(operand) {
                return Some(make_leaf(
                    vec![formula.clone(), operand.clone()],
                    LlRule::Axiom(operand.clone()),
                ));
            }
            continue;
        }
        let negation = exprs.enot(formula);
        if rest.contains(&negation) {
            return Some(make_leaf(
                vec![formula.clone(), negation],
                LlRule::Axiom(formula.clone()),
            ));
        }
    }
    None
}

/// The formulas that a rule takes from its conclusions.
fn get_eliminated(
    exprs: &Expressions,
    lemmas: &HashMap<String, Lemma>,
    rule: &LlRule,
) -> Result<Vec<Expr>, ZenonError> {
    let equal = |left: &Expr, right: &Expr| exprs.eapp("=", &[left.clone(), right.clone()]);
    Ok(match rule {
        LlRule::False => vec![efalse()],
        LlRule::NotTrue => vec![exprs.enot(&etrue())],
        LlRule::Axiom(formula) => vec![formula.clone(), exprs.enot(formula)],
        LlRule::Cut(_) => Vec::new(),
        LlRule::NotEq(term) => vec![exprs.enot(&equal(term, term))],
        LlRule::EqSym { left, right } => vec![equal(left, right), exprs.enot(&equal(right, left))],
        LlRule::NotNot(formula) => vec![exprs.enot(&exprs.enot(formula))],
        LlRule::Connect {
            connective,
            left,
            right,
        } => vec![connect(exprs, *connective, left, right)],
        LlRule::NotConnect {
            connective,
            left,
            right,
        } => vec![exprs.enot(&connect(exprs, *connective, left, right))],
        LlRule::Ex { quantified, .. } | LlRule::All { quantified, .. } => vec![quantified.clone()],
        LlRule::NotEx { quantified, .. } | LlRule::NotAll { quantified, .. } => {
            vec![exprs.enot(quantified)]
        }
        LlRule::PNotP { positive, negative } => vec![positive.clone(), negative.clone()],
        LlRule::NotEqual { left, right } => vec![exprs.enot(&equal(left, right))],
        LlRule::CongruenceLr {
            context,
            left,
            right,
        } => vec![exprs.apply(context, left)?, equal(left, right)],
        LlRule::CongruenceRl {
            context,
            left,
            right,
        } => vec![exprs.apply(context, left)?, equal(right, left)],
        LlRule::Definition { folded, .. } => vec![folded.clone()],
        LlRule::Extension { conclusions, .. } => conclusions.clone(),
        LlRule::Lemma { name, .. } => get_lemma(lemmas, name)?.proof.conclusions.clone(),
    })
}

/// Zenon's Llproof.optimise: drops the conclusions that no rule uses and the nodes whose subproof
/// already proves their conclusions.
pub fn optimise(exprs: &Expressions, proof: &[Lemma]) -> Result<Vec<Lemma>, ZenonError> {
    fn optimise_tree(
        exprs: &Expressions,
        lemmas: &HashMap<String, Lemma>,
        tree: &LlProof,
    ) -> Result<Rc<LlProof>, ZenonError> {
        let subproofs = tree
            .subproofs
            .iter()
            .map(|subproof| optimise_tree(exprs, lemmas, subproof))
            .collect::<Result<Vec<_>, _>>()?;
        if let Some(closed) = get_direct_close(exprs, &tree.conclusions) {
            return Ok(closed);
        }
        let mut useful = get_eliminated(exprs, lemmas, &tree.rule)?;
        useful.extend(
            subproofs
                .iter()
                .flat_map(|subproof| subproof.conclusions.iter().cloned()),
        );
        let conclusions: Vec<Expr> = tree
            .conclusions
            .iter()
            .filter(|formula| useful.contains(formula))
            .cloned()
            .collect();
        if let Some(subsuming) = subproofs.iter().find(|subproof| {
            subproof
                .conclusions
                .iter()
                .all(|formula| conclusions.contains(formula))
        }) {
            return Ok(subsuming.clone());
        }
        let rule = match &tree.rule {
            LlRule::Lemma { name, .. } => LlRule::Lemma {
                name: name.clone(),
                args: get_lemma(lemmas, name)?
                    .params
                    .iter()
                    .map(|param| param.1.clone())
                    .collect(),
            },
            rule => rule.clone(),
        };
        Ok(Rc::new(LlProof {
            conclusions,
            rule,
            subproofs,
        }))
    }
    let mut lemmas = HashMap::new();
    proof
        .iter()
        .map(|lemma| {
            let optimised = Lemma {
                name: lemma.name.clone(),
                params: lemma.params.clone(),
                proof: optimise_tree(exprs, &lemmas, &lemma.proof)?,
            };
            lemmas.insert(optimised.name.clone(), optimised.clone());
            Ok(optimised)
        })
        .collect()
}
