// Ported from Zenon's mltoll.ml, as shipped in tlapm. Copyright 2004 INRIA, see LICENSE.
//! Translates the proof that the search finds into a low-level proof: the derived rules expand into
//! core rules, and each proof that the search reused becomes a lemma.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::ZenonError;
use crate::eqrel::{Direction, Origin, Relations};
use crate::expr::{Expr, Expressions, Kind, difference, union};
use crate::llproof::{Connective, Lemma, LlProof, LlRule, connect};
use crate::parse::{Definition, Phrase};
use crate::proof::{Proof, ProofKey, Rule, RuleName};
use crate::tla::llproof::get_tla_ll_proof;

/// A translated proof, with the hypotheses it uses that aren't conclusions of the node.
pub type Translated = (Rc<LlProof>, Vec<Expr>);

pub struct TranslateContext<'a> {
    pub exprs: &'a Expressions,
    /// Zenon's Index.get_number, which also names the formulas in the Isar output.
    pub get_number: &'a dyn Fn(&Expr) -> usize,
    /// The proofs that the search reused, which Zenon counts in mlrefc.
    pub shared_proofs: &'a HashSet<ProofKey>,
    pub relations: &'a Relations,
}

#[derive(Clone, Copy)]
enum RelationProperty {
    Reflexive,
    Symmetric,
    Transitive,
}

impl RelationProperty {
    fn as_str(self) -> &'static str {
        match self {
            RelationProperty::Reflexive => "reflexive",
            RelationProperty::Symmetric => "symmetric",
            RelationProperty::Transitive => "transitive",
        }
    }
}

/// Zenon's Eqrel.hyp_kind: how to prove a hypothesis about a relation. A relation is also
/// symmetric or transitive when it's reflexive and transitive in the symmetric sense.
#[derive(Clone)]
enum HypothesisKind {
    Reflexive(Origin),
    Symmetric(Origin),
    Transitive(Origin),
    Symmetric2(DerivedOrigins),
    Transitive2(DerivedOrigins),
}

#[derive(Clone)]
struct DerivedOrigins {
    relation: String,
    reflexive: Origin,
    transitive_symmetric: Origin,
}

/// A recomposed disjunction tree, with the translated subproofs it didn't consume.
type Disjunction<'s> = (Rc<LlProof>, Vec<Expr>, &'s [Translated]);

const LEMMA_PREFIX: &str = "zenon_L";
const META_PREFIX: &str = "zenon_X";

pub fn is_meta_name(name: &str) -> bool {
    name.starts_with(META_PREFIX)
}

/// Zenon's type_to_ident.
fn to_identifier(type_name: &str) -> String {
    type_name
        .chars()
        .map(|char| {
            if char.is_ascii_alphanumeric() {
                char.to_string()
            } else {
                let mut units = [0; 2];
                format!("_{:02x}", char.encode_utf16(&mut units)[0])
            }
        })
        .collect()
}

fn get_binder(expression: &Expr, kind: Kind) -> Result<&Expr, ZenonError> {
    if expression.kind != kind {
        return Err(ZenonError::new(format!(
            "Zenon: expected a {} binder",
            kind.name()
        )));
    }
    Ok(expression)
}

fn get_single(proof: &Proof) -> Result<Rc<Proof>, ZenonError> {
    match proof.subproofs.as_slice() {
        [subproof] => Ok(subproof.clone()),
        _ => Err(ZenonError::new("Zenon: expected one subproof")),
    }
}

fn get_subproof(proof: &Proof, position: usize) -> Result<Rc<Proof>, ZenonError> {
    proof
        .subproofs
        .get(position)
        .cloned()
        .ok_or_else(|| ZenonError::new("Zenon: a subproof that is missing"))
}

fn get_definition(rule: &Rule) -> Result<&Definition, ZenonError> {
    rule.definition
        .as_deref()
        .ok_or_else(|| ZenonError::new("Zenon: a definition rule without its definition"))
}

/// Zenon's Mlproof.make_node: the node's conclusions and those its subproofs leave open.
fn make_node(
    conclusions: Vec<Expr>,
    rule: Rule,
    branches: &[Vec<Expr>],
    subproofs: Vec<Rc<Proof>>,
) -> Rc<Proof> {
    let open = subproofs
        .iter()
        .enumerate()
        .map(|(position, subproof)| {
            difference(
                &subproof.conclusions,
                branches.get(position).map_or(&[], Vec::as_slice),
            )
        })
        .fold(Vec::new(), |accumulated, extra| union(&accumulated, &extra));
    Rc::new(Proof {
        conclusions: union(&conclusions, &open),
        rule,
        uses: Vec::new(),
        subproofs,
    })
}

fn is_derived(rule: &Rule) -> bool {
    match rule.name {
        RuleName::CloseRefl | RuleName::CloseSym => rule.relation.as_deref() != Some("="),
        RuleName::Definition => {
            !matches!(rule.definition.as_deref(), Some(Definition::Real { .. }))
        }
        RuleName::ConjTree
        | RuleName::DisjTree
        | RuleName::NotAllEx
        | RuleName::Refl
        | RuleName::PNotPSym
        | RuleName::Trans
        | RuleName::TransSym
        | RuleName::TransEq
        | RuleName::TransEq2
        | RuleName::TransEqSym => true,
        name => !CORE_RULES.contains(&name),
    }
}

/// The rules that tr_rule translates directly: the core rules and the extension rules named "".
const CORE_RULES: [RuleName; 27] = [
    RuleName::Close,
    RuleName::False,
    RuleName::NotTrue,
    RuleName::NotNot,
    RuleName::And,
    RuleName::NotOr,
    RuleName::NotImpl,
    RuleName::Ex,
    RuleName::All,
    RuleName::NotEx,
    RuleName::Or,
    RuleName::Impl,
    RuleName::NotAnd,
    RuleName::Equiv,
    RuleName::NotEquiv,
    RuleName::PNotP,
    RuleName::NotEqual,
    RuleName::Cut,
    RuleName::CongruenceLr,
    RuleName::CongruenceRl,
    RuleName::Notall,
    RuleName::Notallex,
    RuleName::Stringequal,
    RuleName::Stringdiffll,
    RuleName::Stringdifflr,
    RuleName::Stringdiffrl,
    RuleName::Stringdiffrr,
];

fn get_rule_connective(name: RuleName) -> Option<Connective> {
    match name {
        RuleName::And | RuleName::NotAnd => Some(Kind::And),
        RuleName::Or | RuleName::NotOr => Some(Kind::Or),
        RuleName::Impl | RuleName::NotImpl => Some(Kind::Imply),
        RuleName::Equiv | RuleName::NotEquiv => Some(Kind::Equiv),
        _ => None,
    }
}

fn get_lemma_name(number: usize) -> String {
    format!("{LEMMA_PREFIX}{number}_")
}

/// Zenon's get_params: the free taus of a lemma's conclusions, each with its type.
fn get_params(
    accumulated: Vec<(String, Expr)>,
    expression: &Expr,
) -> Result<Vec<(String, Expr)>, ZenonError> {
    match expression.kind {
        Kind::Tau => Ok(if accumulated.iter().any(|param| param.1 == *expression) {
            accumulated
        } else {
            std::iter::once((expression.symbol.to_string(), expression.clone()))
                .chain(accumulated)
                .collect()
        }),
        Kind::All | Kind::Ex | Kind::Lam => get_params(accumulated, &expression.args[1]),
        Kind::Meta => Err(ZenonError::new(
            "Zenon: a metavariable in a translated formula",
        )),
        _ => expression.args.iter().try_fold(accumulated, get_params),
    }
}

/// A node of recomp_conj, with the formulas it removes from its subproof's conclusions.
fn recompose(
    conclusion: Expr,
    rule: LlRule,
    removed: &[Expr],
    next: Translated,
    extra: &Expr,
) -> Translated {
    (
        Rc::new(LlProof {
            conclusions: union(&[conclusion], &difference(&next.0.conclusions, removed)),
            rule,
            subproofs: vec![next.0],
        }),
        difference(&next.1, std::slice::from_ref(extra)),
    )
}

/// A node of recomp_disj on two recomposed subtrees.
#[expect(
    clippy::too_many_arguments,
    reason = "a literal port of recomp_disj's node"
)]
fn make_disjunction_node<'s>(
    conclusion: Expr,
    connective: Connective,
    is_negated: bool,
    left: Expr,
    right: Expr,
    first: Disjunction<'s>,
    first_removed: Expr,
    second: Disjunction<'s>,
    second_removed: Expr,
    extra: &Expr,
) -> Disjunction<'s> {
    let conclusions = union(
        &[conclusion],
        &union(
            &difference(&first.0.conclusions, &[first_removed]),
            &difference(&second.0.conclusions, &[second_removed]),
        ),
    );
    (
        Rc::new(LlProof {
            conclusions,
            rule: if is_negated {
                LlRule::NotConnect {
                    connective,
                    left,
                    right,
                }
            } else {
                LlRule::Connect {
                    connective,
                    left,
                    right,
                }
            },
            subproofs: vec![first.0, second.0],
        }),
        difference(&union(&first.1, &second.1), std::slice::from_ref(extra)),
        second.2,
    )
}

fn take_sub(subs: &[Translated]) -> Result<Disjunction<'_>, ZenonError> {
    let Some((first, rest)) = subs.split_first() else {
        return Err(ZenonError::new(
            "Zenon: a disjunction tree without subproofs",
        ));
    };
    Ok((first.0.clone(), first.1.clone(), rest))
}

// The constructors of Zenon's Mlproof, for the proofs that the translation builds.

fn equal(exprs: &Expressions, left: &Expr, right: &Expr) -> Expr {
    exprs.eapp("=", &[left.clone(), right.clone()])
}

fn relate(exprs: &Expressions, relation: &str, left: &Expr, right: &Expr) -> Expr {
    exprs.eapp(relation, &[left.clone(), right.clone()])
}

fn make_close(exprs: &Expressions, formula: &Expr) -> Rc<Proof> {
    make_node(
        vec![formula.clone(), exprs.enot(formula)],
        Rule::new(RuleName::Close, vec![formula.clone()]),
        &[],
        Vec::new(),
    )
}

fn make_close_refl(exprs: &Expressions, relation: &str, term: &Expr) -> Rc<Proof> {
    make_node(
        vec![exprs.enot(&relate(exprs, relation, term, term))],
        Rule::relation(RuleName::CloseRefl, relation, vec![term.clone()]),
        &[],
        Vec::new(),
    )
}

fn make_close_sym(exprs: &Expressions, relation: &str, left: &Expr, right: &Expr) -> Rc<Proof> {
    make_node(
        vec![
            relate(exprs, relation, left, right),
            exprs.enot(&relate(exprs, relation, right, left)),
        ],
        Rule::relation(
            RuleName::CloseSym,
            relation,
            vec![left.clone(), right.clone()],
        ),
        &[],
        Vec::new(),
    )
}

fn make_not_not(exprs: &Expressions, formula: &Expr, subproof: Rc<Proof>) -> Rc<Proof> {
    make_node(
        vec![exprs.enot(&exprs.enot(formula))],
        Rule::new(RuleName::NotNot, vec![formula.clone()]),
        &[vec![formula.clone()]],
        vec![subproof],
    )
}

fn make_and(exprs: &Expressions, left: &Expr, right: &Expr, subproof: Rc<Proof>) -> Rc<Proof> {
    make_node(
        vec![exprs.eand(left, right)],
        Rule::new(RuleName::And, vec![left.clone(), right.clone()]),
        &[vec![left.clone(), right.clone()]],
        vec![subproof],
    )
}

fn make_imply(
    exprs: &Expressions,
    left: &Expr,
    right: &Expr,
    first: Rc<Proof>,
    second: Rc<Proof>,
) -> Rc<Proof> {
    make_node(
        vec![exprs.eimply(left, right)],
        Rule::new(RuleName::Impl, vec![left.clone(), right.clone()]),
        &[vec![exprs.enot(left)], vec![right.clone()]],
        vec![first, second],
    )
}

fn make_not_and(
    exprs: &Expressions,
    left: &Expr,
    right: &Expr,
    first: Rc<Proof>,
    second: Rc<Proof>,
) -> Rc<Proof> {
    make_node(
        vec![exprs.enot(&exprs.eand(left, right))],
        Rule::new(RuleName::NotAnd, vec![left.clone(), right.clone()]),
        &[vec![exprs.enot(left)], vec![exprs.enot(right)]],
        vec![first, second],
    )
}

fn make_all(
    exprs: &Expressions,
    quantified: &Expr,
    term: &Expr,
    subproof: Rc<Proof>,
) -> Result<Rc<Proof>, ZenonError> {
    let binder = get_binder(quantified, Kind::All)?;
    let instance = exprs.substitute(&[(binder.args[0].clone(), term.clone())], &binder.args[1]);
    Ok(make_node(
        vec![quantified.clone()],
        Rule::new(RuleName::All, vec![quantified.clone(), term.clone()]),
        &[vec![instance]],
        vec![subproof],
    ))
}

fn make_alls(
    exprs: &Expressions,
    quantified: &Expr,
    terms: &[Expr],
    subproof: Rc<Proof>,
) -> Result<Rc<Proof>, ZenonError> {
    let Some((term, rest)) = terms.split_first() else {
        return Ok(subproof);
    };
    let binder = get_binder(quantified, Kind::All)?;
    let instance = exprs.substitute(&[(binder.args[0].clone(), term.clone())], &binder.args[1]);
    let inner = make_alls(exprs, &instance, rest, subproof)?;
    make_all(exprs, quantified, term, inner)
}

/// Zenon's make_impls: the implications from `hypotheses` to `conclusion`, and their proof.
fn make_implies(
    exprs: &Expressions,
    hypotheses: &[Expr],
    conclusion: &Expr,
    proofs: &[Rc<Proof>],
    conclusion_proof: Rc<Proof>,
) -> Result<(Expr, Rc<Proof>), ZenonError> {
    let Some((hypothesis, other_hypotheses)) = hypotheses.split_first() else {
        return Ok((conclusion.clone(), conclusion_proof));
    };
    let Some((proof, other_proofs)) = proofs.split_first() else {
        return Err(ZenonError::new("Zenon: make_impls without a proof"));
    };
    let rest = make_implies(
        exprs,
        other_hypotheses,
        conclusion,
        other_proofs,
        conclusion_proof,
    )?;
    Ok((
        exprs.eimply(hypothesis, &rest.0),
        make_imply(exprs, hypothesis, &rest.0, proof.clone(), rest.1),
    ))
}

fn make_p_not_p(
    exprs: &Expressions,
    positive: &Expr,
    negative: &Expr,
    subproofs: Vec<Rc<Proof>>,
) -> Result<Rc<Proof>, ZenonError> {
    if positive.kind != Kind::App
        || negative.kind != Kind::Not
        || negative.args[0].kind != Kind::App
    {
        return Err(ZenonError::new(
            "Zenon: make_pnp on a formula that isn't an application",
        ));
    }
    let negative_args = &negative.args[0].args;
    let branches = positive
        .args
        .iter()
        .enumerate()
        .map(|(position, arg)| {
            let negative_arg = negative_args.get(position).ok_or_else(|| {
                ZenonError::new("Zenon: make_pnp on applications of different arities")
            })?;
            Ok(vec![exprs.enot(&equal(exprs, arg, negative_arg))])
        })
        .collect::<Result<Vec<_>, ZenonError>>()?;
    Ok(make_node(
        vec![positive.clone(), negative.clone()],
        Rule::new(RuleName::PNotP, vec![positive.clone(), negative.clone()]),
        &branches,
        subproofs,
    ))
}

fn make_cut(exprs: &Expressions, formula: &Expr, first: Rc<Proof>, second: Rc<Proof>) -> Rc<Proof> {
    make_node(
        Vec::new(),
        Rule::new(RuleName::Cut, vec![formula.clone()]),
        &[vec![formula.clone()], vec![exprs.enot(formula)]],
        vec![first, second],
    )
}

/// Zenon's inst_nall: the instance of a negated universal at its counterexample.
fn instantiate_negation(exprs: &Expressions, negation: &Expr) -> Result<(Expr, Expr), ZenonError> {
    if negation.kind != Kind::Not {
        return Err(ZenonError::new("Zenon: inst_nall without a negation"));
    }
    let binder = get_binder(&negation.args[0], Kind::All)?;
    let body = exprs.enot(&binder.args[1]);
    let witness = exprs.etau(&binder.args[0], &binder.symbol, &body);
    Ok((
        exprs.substitute(&[(binder.args[0].clone(), witness.clone())], &body),
        witness,
    ))
}

/// Zenon's decompose_disj: closes each literal of a disjunction with one of `forms`.
fn decompose_disjunction(
    exprs: &Expressions,
    formula: &Expr,
    forms: &[Expr],
) -> Result<Rc<Proof>, ZenonError> {
    let visit = |disjunct: &Expr| decompose_disjunction(exprs, disjunct, forms);
    let get_form = |form: Expr| {
        if !forms.contains(&form) {
            return Err(ZenonError::new("Zenon: decompose_disj lacks a literal"));
        }
        Ok(form)
    };
    let unexpected = || ZenonError::new("Zenon: decompose_disj on an unexpected formula");
    match formula.kind {
        Kind::Or => Ok(make_node(
            vec![formula.clone()],
            Rule::new(
                RuleName::Or,
                vec![formula.args[0].clone(), formula.args[1].clone()],
            ),
            &[vec![formula.args[0].clone()], vec![formula.args[1].clone()]],
            vec![visit(&formula.args[0])?, visit(&formula.args[1])?],
        )),
        Kind::Imply => {
            let negated = exprs.enot(&formula.args[0]);
            Ok(make_node(
                vec![formula.clone()],
                Rule::new(
                    RuleName::Impl,
                    vec![formula.args[0].clone(), formula.args[1].clone()],
                ),
                &[vec![negated.clone()], vec![formula.args[1].clone()]],
                vec![visit(&negated)?, visit(&formula.args[1])?],
            ))
        }
        Kind::False => Ok(make_node(
            vec![formula.clone()],
            Rule::new(RuleName::False, Vec::new()),
            &[],
            Vec::new(),
        )),
        Kind::App => Ok(make_node(
            vec![formula.clone(), get_form(exprs.enot(formula))?],
            Rule::new(RuleName::Close, vec![formula.clone()]),
            &[],
            Vec::new(),
        )),
        Kind::Not => {
            let operand = &formula.args[0];
            match operand.kind {
                Kind::And => {
                    let left = exprs.enot(&operand.args[0]);
                    let right = exprs.enot(&operand.args[1]);
                    Ok(make_node(
                        vec![formula.clone()],
                        Rule::new(
                            RuleName::NotAnd,
                            vec![operand.args[0].clone(), operand.args[1].clone()],
                        ),
                        &[vec![left.clone()], vec![right.clone()]],
                        vec![visit(&left)?, visit(&right)?],
                    ))
                }
                Kind::Not => Ok(make_node(
                    vec![formula.clone()],
                    Rule::new(RuleName::NotNot, vec![operand.args[0].clone()]),
                    &[vec![operand.args[0].clone()]],
                    vec![visit(&operand.args[0])?],
                )),
                Kind::True => Ok(make_node(
                    vec![formula.clone()],
                    Rule::new(RuleName::NotTrue, Vec::new()),
                    &[],
                    Vec::new(),
                )),
                Kind::App => Ok(make_node(
                    vec![get_form(operand.clone())?, formula.clone()],
                    Rule::new(RuleName::Close, vec![operand.clone()]),
                    &[],
                    Vec::new(),
                )),
                _ => Err(unexpected()),
            }
        }
        _ => Err(unexpected()),
    }
}

/// Zenon's decompose_conj: follows `directions` to the conjunct that states a property, and
/// instantiates the quantifiers at `variables` with `witnesses`, the others with metavariables.
fn decompose_conjunction(
    exprs: &Expressions,
    position: usize,
    formula: &Expr,
    directions: &[Direction],
    variables: &[usize],
    forms: &[Expr],
    witnesses: &[Expr],
) -> Result<Rc<Proof>, ZenonError> {
    let next = |subformula: &Expr, rest: &[Direction]| {
        decompose_conjunction(
            exprs, position, subformula, rest, variables, forms, witnesses,
        )
    };
    let direction = directions.first().copied();
    let rest = directions.get(1..).unwrap_or_default();
    let instantiate = |quantified: &Expr, binder: &Expr, is_negated: bool, name: RuleName| {
        let is_witness = variables.first() == Some(&position);
        let term = if is_witness {
            witnesses
                .first()
                .cloned()
                .ok_or_else(|| ZenonError::new("Zenon: decompose_conj ran out of witnesses"))?
        } else {
            exprs.emeta(binder)
        };
        let substituted =
            exprs.substitute(&[(binder.args[0].clone(), term.clone())], &binder.args[1]);
        let instance = if is_negated {
            exprs.enot(&substituted)
        } else {
            substituted
        };
        let subproof = decompose_conjunction(
            exprs,
            position + 1,
            &instance,
            directions,
            if is_witness {
                &variables[1..]
            } else {
                variables
            },
            forms,
            if is_witness {
                &witnesses[1..]
            } else {
                witnesses
            },
        )?;
        Ok(make_node(
            vec![quantified.clone()],
            Rule::new(name, vec![quantified.clone(), term]),
            &[vec![instance]],
            vec![subproof],
        ))
    };
    if let (Kind::And, Some(direction)) = (formula.kind, direction) {
        let branch = if direction == Direction::Left {
            &formula.args[0]
        } else {
            &formula.args[1]
        };
        return Ok(make_node(
            vec![formula.clone()],
            Rule::new(
                RuleName::And,
                vec![formula.args[0].clone(), formula.args[1].clone()],
            ),
            &[vec![branch.clone()]],
            vec![next(branch, rest)?],
        ));
    }
    if formula.kind == Kind::All {
        return instantiate(formula, formula, false, RuleName::All);
    }
    if let (Kind::Equiv, Some(direction)) = (formula.kind, direction) {
        let left = &formula.args[0];
        let right = &formula.args[1];
        let rule = Rule::new(RuleName::Equiv, vec![left.clone(), right.clone()]);
        return Ok(if direction == Direction::Left {
            let negated = exprs.enot(left);
            make_node(
                vec![formula.clone()],
                rule,
                &[vec![negated.clone()], vec![right.clone()]],
                vec![
                    decompose_disjunction(exprs, &negated, forms)?,
                    decompose_disjunction(exprs, right, forms)?,
                ],
            )
        } else {
            let negated = exprs.enot(right);
            make_node(
                vec![formula.clone()],
                rule,
                &[vec![negated.clone()], vec![left.clone()]],
                vec![
                    decompose_disjunction(exprs, &negated, forms)?,
                    decompose_disjunction(exprs, left, forms)?,
                ],
            )
        });
    }
    let operand = (formula.kind == Kind::Not).then(|| &formula.args[0]);
    let operand_kind = operand.map(|inner| inner.kind);
    if let (Some(operand), Some(Kind::Or), Some(direction)) = (operand, operand_kind, direction) {
        let branch = exprs.enot(if direction == Direction::Left {
            &operand.args[0]
        } else {
            &operand.args[1]
        });
        return Ok(make_node(
            vec![formula.clone()],
            Rule::new(
                RuleName::NotOr,
                vec![operand.args[0].clone(), operand.args[1].clone()],
            ),
            &[vec![branch.clone()]],
            vec![next(&branch, rest)?],
        ));
    }
    if let (Some(operand), Some(Kind::Imply), Some(direction)) = (operand, operand_kind, direction)
    {
        let branch = if direction == Direction::Left {
            operand.args[0].clone()
        } else {
            exprs.enot(&operand.args[1])
        };
        // HACK: Zenon names the right branch of a negated implication not_or.
        let name = if direction == Direction::Left {
            RuleName::NotImpl
        } else {
            RuleName::NotOr
        };
        return Ok(make_node(
            vec![formula.clone()],
            Rule::new(name, vec![operand.args[0].clone(), operand.args[1].clone()]),
            &[vec![branch.clone()]],
            vec![next(&branch, rest)?],
        ));
    }
    if let (Some(operand), Some(Kind::Ex)) = (operand, operand_kind) {
        return instantiate(formula, operand, true, RuleName::NotEx);
    }
    if let (Some(operand), Some(Kind::Not)) = (operand, operand_kind) {
        return Ok(make_node(
            vec![formula.clone()],
            Rule::new(RuleName::NotNot, vec![operand.args[0].clone()]),
            &[vec![operand.args[0].clone()]],
            vec![next(&operand.args[0], directions)?],
        ));
    }
    if let (Some(operand), Some(Kind::Equiv), Some(direction)) = (operand, operand_kind, direction)
    {
        let left = &operand.args[0];
        let right = &operand.args[1];
        let rule = Rule::new(RuleName::NotEquiv, vec![left.clone(), right.clone()]);
        // HACK: Zenon's right branch proves its second case from the negation of `right`.
        return Ok(if direction == Direction::Left {
            make_node(
                vec![formula.clone()],
                rule,
                &[vec![right.clone()], vec![left.clone()]],
                vec![
                    decompose_disjunction(exprs, right, forms)?,
                    decompose_disjunction(exprs, left, forms)?,
                ],
            )
        } else {
            let negated = exprs.enot(left);
            make_node(
                vec![formula.clone()],
                rule,
                &[vec![negated.clone()], vec![right.clone()]],
                vec![
                    decompose_disjunction(exprs, &negated, forms)?,
                    decompose_disjunction(exprs, &exprs.enot(right), forms)?,
                ],
            )
        });
    }
    if !directions.is_empty() || !variables.is_empty() || !witnesses.is_empty() {
        return Err(ZenonError::new(
            "Zenon: decompose_conj left directions or variables",
        ));
    }
    decompose_disjunction(exprs, formula, forms)
}

fn get_relation(formula: &Expr) -> Result<&Expr, ZenonError> {
    let atom = if formula.kind == Kind::Not {
        &formula.args[0]
    } else {
        formula
    };
    if atom.kind != Kind::App || atom.args.len() != 2 {
        return Err(ZenonError::new(
            "Zenon: a transitivity rule on a formula that isn't a relation",
        ));
    }
    Ok(atom)
}

fn get_three(proof: &Proof) -> Result<[Rc<Proof>; 3], ZenonError> {
    match proof.subproofs.as_slice() {
        [first, second, third] => Ok([first.clone(), second.clone(), third.clone()]),
        _ => Err(ZenonError::new("Zenon: expected three subproofs")),
    }
}

/// Zenon's make_direct_sym_neq: a != b / b != a / (proof).
fn make_symmetric_disequality(
    exprs: &Expressions,
    a: &Expr,
    b: &Expr,
    proof: Rc<Proof>,
) -> Result<Rc<Proof>, ZenonError> {
    let reflexive = equal(exprs, b, b);
    let refuted = make_close_refl(exprs, "=", b);
    let swapped = make_p_not_p(
        exprs,
        &reflexive,
        &exprs.enot(&equal(exprs, a, b)),
        vec![proof, refuted.clone()],
    )?;
    Ok(make_cut(exprs, &reflexive, swapped, refuted))
}

/// Zenon's make_direct_sym_eq: a = b / b = a / (proof).
fn make_symmetric_equality(
    exprs: &Expressions,
    a: &Expr,
    b: &Expr,
    proof: Rc<Proof>,
) -> Result<Rc<Proof>, ZenonError> {
    let ab = equal(exprs, a, b);
    let ba = equal(exprs, b, a);
    let close_ab = make_close(exprs, &ab);
    let disequality = make_symmetric_disequality(exprs, b, a, close_ab)?;
    Ok(make_cut(exprs, &ba, proof, disequality))
}

fn expand_trans_equal(
    exprs: &Expressions,
    [a, b, c, d]: [&Expr; 4],
    first: Rc<Proof>,
    second: Rc<Proof>,
) -> Result<Rc<Proof>, ZenonError> {
    let symmetric = make_symmetric_disequality(exprs, a, c, first)?;
    make_p_not_p(
        exprs,
        &equal(exprs, a, b),
        &exprs.enot(&equal(exprs, c, d)),
        vec![symmetric, second],
    )
}

/// Zenon's make_ex.
fn make_existential(
    exprs: &Expressions,
    existential: &Expr,
    subproof: Rc<Proof>,
) -> Result<Rc<Proof>, ZenonError> {
    let binder = get_binder(existential, Kind::Ex)?;
    let witness = exprs.etau(&binder.args[0], &binder.symbol, &binder.args[1]);
    let instance = exprs.substitute(&[(binder.args[0].clone(), witness)], &binder.args[1]);
    Ok(make_node(
        vec![existential.clone()],
        Rule::new(RuleName::Ex, vec![existential.clone()]),
        &[vec![instance]],
        vec![subproof],
    ))
}

/// Zenon's find_diff: the context in which two formulas differ, and the two subterms.
fn find_diff(
    exprs: &Expressions,
    variable: &Expr,
    left: &Expr,
    right: &Expr,
) -> Result<(Expr, Expr, Expr), ZenonError> {
    if left == right {
        return Err(ZenonError::new("Zenon: find_diff on equal formulas"));
    }
    if left.kind == Kind::App && right.kind == Kind::App && left.symbol == right.symbol {
        let different =
            left.args
                .iter()
                .enumerate()
                .find_map(|(index, arg)| match right.args.get(index) {
                    Some(other) if other == arg => None,
                    other => Some((index, other)),
                });
        let Some((position, Some(other))) = different else {
            return Err(ZenonError::new(
                "Zenon: find_diff on applications of different arities",
            ));
        };
        let diff = find_diff(exprs, variable, &left.args[position], other)?;
        let args: Vec<Expr> = left
            .args
            .iter()
            .enumerate()
            .map(|(index, arg)| {
                if index == position {
                    diff.0.clone()
                } else {
                    arg.clone()
                }
            })
            .collect();
        return Ok((exprs.eapp(&left.symbol, &args), diff.1, diff.2));
    }
    if left.kind == Kind::Not && right.kind == Kind::Not {
        let diff = find_diff(exprs, variable, &left.args[0], &right.args[0])?;
        return Ok((exprs.enot(&diff.0), diff.1, diff.2));
    }
    // HACK: Zenon compares every binary connective with a conjunction here.
    if left.kind.is_binary() && right.kind == Kind::And {
        if left.args[0] == right.args[0] {
            let diff = find_diff(exprs, variable, &left.args[1], &right.args[1])?;
            return Ok((
                connect(exprs, left.kind, &left.args[0], &diff.0),
                diff.1,
                diff.2,
            ));
        }
        let diff = find_diff(exprs, variable, &left.args[0], &right.args[0])?;
        return Ok((
            connect(exprs, left.kind, &diff.0, &left.args[1]),
            diff.1,
            diff.2,
        ));
    }
    if left.kind == right.kind && left.kind.is_binder() {
        return Err(ZenonError::new("Zenon: find_diff under a binder"));
    }
    Ok((variable.clone(), left.clone(), right.clone()))
}

fn defines_symbol(side: &Expr, symbol: &str) -> bool {
    matches!(side.kind, Kind::App | Kind::Var) && &*side.symbol == symbol
}

/// The state of Zenon's Mltoll.translate.
struct Translator<'a, 'c> {
    context: &'c TranslateContext<'a>,
    translated_exprs: HashMap<Expr, Expr>,
    lemma_numbers: HashMap<ProofKey, usize>,
    lemma_table: HashMap<String, (Lemma, Vec<Expr>)>,
    lemmas: Vec<Lemma>,
    // Zenon's Eqrel.get_refl_hyp, get_sym_hyp and get_trans_hyp: the hypothesis that states a
    // property of a relation, which the translation proves from the hypotheses that implied it.
    relation_hypotheses: HashMap<String, Expr>,
    hypothesis_kinds: HashMap<Expr, HypothesisKind>,
}

impl<'a> Translator<'a, '_> {
    fn exprs(&self) -> &'a Expressions {
        self.context.exprs
    }

    /// Zenon's tr_expr: metavariables become variables named after their quantifier.
    fn translate_expr(&mut self, expression: &Expr) -> Result<Expr, ZenonError> {
        if expression.metas.is_empty() {
            return Ok(expression.clone());
        }
        if let Some(cached) = self.translated_exprs.get(expression) {
            return Ok(cached.clone());
        }
        let exprs = self.exprs();
        let result = match expression.kind {
            Kind::Meta => {
                let quantified = &expression.args[0];
                if quantified.kind != Kind::All && quantified.kind != Kind::Ex {
                    return Err(ZenonError::new(
                        "Zenon: a metavariable without a quantifier",
                    ));
                }
                exprs.evar(&format!(
                    "{META_PREFIX}{}_{}",
                    (self.context.get_number)(quantified),
                    to_identifier(&quantified.symbol)
                ))
            }
            Kind::App => {
                let args = self.translate_all_exprs(&expression.args)?;
                exprs.eapp(&expression.symbol, &args)
            }
            Kind::Not => exprs.enot(&self.translate_expr(&expression.args[0])?),
            Kind::And | Kind::Or | Kind::Imply | Kind::Equiv => {
                let right = self.translate_expr(&expression.args[1])?;
                connect(
                    exprs,
                    expression.kind,
                    &self.translate_expr(&expression.args[0])?,
                    &right,
                )
            }
            Kind::All | Kind::Ex | Kind::Tau | Kind::Lam => exprs.binder(
                expression.kind,
                &expression.args[0],
                &expression.symbol,
                &self.translate_expr(&expression.args[1])?,
            ),
            _ => expression.clone(),
        };
        self.translated_exprs
            .insert(expression.clone(), result.clone());
        Ok(result)
    }

    fn translate_all_exprs(&mut self, expressions: &[Expr]) -> Result<Vec<Expr>, ZenonError> {
        expressions
            .iter()
            .map(|expression| self.translate_expr(expression))
            .collect()
    }

    fn translate_rule(&mut self, rule: &Rule) -> Result<LlRule, ZenonError> {
        let exprs = self.exprs();
        let args = &rule.args;
        Ok(match rule.name {
            RuleName::Close => LlRule::Axiom(self.translate_expr(&args[0])?),
            RuleName::CloseRefl => LlRule::NotEq(self.translate_expr(&args[0])?),
            RuleName::CloseSym => {
                let right = self.translate_expr(&args[1])?;
                LlRule::EqSym {
                    left: self.translate_expr(&args[0])?,
                    right,
                }
            }
            RuleName::False => LlRule::False,
            RuleName::NotTrue => LlRule::NotTrue,
            RuleName::NotNot => LlRule::NotNot(self.translate_expr(&args[0])?),
            RuleName::And | RuleName::Or | RuleName::Impl | RuleName::Equiv => {
                let right = self.translate_expr(&args[1])?;
                LlRule::Connect {
                    connective: get_rule_connective(rule.name).unwrap_or(Kind::And),
                    left: self.translate_expr(&args[0])?,
                    right,
                }
            }
            RuleName::NotOr | RuleName::NotImpl | RuleName::NotAnd | RuleName::NotEquiv => {
                let right = self.translate_expr(&args[1])?;
                LlRule::NotConnect {
                    connective: get_rule_connective(rule.name).unwrap_or(Kind::And),
                    left: self.translate_expr(&args[0])?,
                    right,
                }
            }
            RuleName::Ex => {
                let quantified = get_binder(&args[0], Kind::Ex)?;
                let term = self.translate_expr(&exprs.etau(
                    &quantified.args[0],
                    &quantified.symbol,
                    &quantified.args[1],
                ))?;
                LlRule::Ex {
                    quantified: self.translate_expr(quantified)?,
                    term,
                }
            }
            RuleName::All => {
                let term = self.translate_expr(&args[1])?;
                LlRule::All {
                    quantified: self.translate_expr(&args[0])?,
                    term,
                }
            }
            RuleName::NotEx => {
                let negation = &args[0];
                if negation.kind != Kind::Not {
                    return Err(ZenonError::new("Zenon: not_ex without a negation"));
                }
                let term = self.translate_expr(&args[1])?;
                LlRule::NotEx {
                    quantified: self.translate_expr(&negation.args[0])?,
                    term,
                }
            }
            RuleName::PNotP => {
                let negative = self.translate_expr(&args[1])?;
                LlRule::PNotP {
                    positive: self.translate_expr(&args[0])?,
                    negative,
                }
            }
            RuleName::NotEqual => {
                let right = self.translate_expr(&args[1])?;
                LlRule::NotEqual {
                    left: self.translate_expr(&args[0])?,
                    right,
                }
            }
            RuleName::Definition => {
                let Definition::Real { name, .. } = get_definition(rule)? else {
                    return Err(ZenonError::new("Zenon: a pseudo-definition in tr_rule"));
                };
                let unfolded = self.translate_expr(&args[1])?;
                LlRule::Definition {
                    name: name.clone(),
                    folded: self.translate_expr(&args[0])?,
                    unfolded,
                }
            }
            RuleName::Cut => LlRule::Cut(self.translate_expr(&args[0])?),
            RuleName::CongruenceLr | RuleName::CongruenceRl => {
                let right = self.translate_expr(&args[2])?;
                let left = self.translate_expr(&args[1])?;
                let context = self.translate_expr(&args[0])?;
                if rule.name == RuleName::CongruenceLr {
                    LlRule::CongruenceLr {
                        context,
                        left,
                        right,
                    }
                } else {
                    LlRule::CongruenceRl {
                        context,
                        left,
                        right,
                    }
                }
            }
            RuleName::Notall => {
                let negation = &args[0];
                let quantified = get_binder(
                    if negation.kind == Kind::Not {
                        &negation.args[0]
                    } else {
                        negation
                    },
                    Kind::All,
                )?;
                let term = self.translate_expr(&exprs.etau(
                    &quantified.args[0],
                    &quantified.symbol,
                    &exprs.enot(&quantified.args[1]),
                ))?;
                LlRule::NotAll {
                    quantified: self.translate_expr(quantified)?,
                    term,
                }
            }
            RuleName::Notallex => {
                let lambda = get_binder(&args[0], Kind::Lam)?;
                let variable = &lambda.args[0];
                let body = &lambda.args[1];
                let conclusion = exprs.enot(&exprs.eall(variable, &lambda.symbol, body));
                let hypothesis = exprs.eex(variable, &lambda.symbol, &exprs.enot(body));
                LlRule::Extension {
                    name: "zenon_notallex".to_owned(),
                    args: vec![lambda.clone()],
                    conclusions: vec![conclusion],
                    branches: vec![vec![hypothesis]],
                }
            }
            RuleName::Stringequal => {
                let first = &args[0];
                let second = &args[1];
                let conclusion = equal(
                    exprs,
                    &exprs.eapp("$string", std::slice::from_ref(first)),
                    &exprs.eapp("$string", std::slice::from_ref(second)),
                );
                LlRule::Extension {
                    name: "zenon_stringequal".to_owned(),
                    args: vec![first.clone(), second.clone()],
                    conclusions: vec![conclusion],
                    branches: Vec::new(),
                }
            }
            RuleName::Stringdiffll
            | RuleName::Stringdifflr
            | RuleName::Stringdiffrl
            | RuleName::Stringdiffrr => {
                let [first, first_value, second, second_value] = &args[..] else {
                    return Err(ZenonError::new(format!(
                        "Zenon: the rule {} has too few arguments",
                        rule.name.as_str()
                    )));
                };
                let is_first_left =
                    matches!(rule.name, RuleName::Stringdiffll | RuleName::Stringdifflr);
                let is_second_left =
                    matches!(rule.name, RuleName::Stringdiffll | RuleName::Stringdiffrl);
                let first_conclusion = if is_first_left {
                    equal(exprs, first, first_value)
                } else {
                    equal(exprs, first_value, first)
                };
                let second_conclusion = if is_second_left {
                    equal(exprs, second, second_value)
                } else {
                    equal(exprs, second_value, second)
                };
                let hypothesis = exprs.enot(&equal(exprs, first, second));
                LlRule::Extension {
                    // HACK: Zenon names the last of the four rules after the third.
                    name: if rule.name == RuleName::Stringdiffrr {
                        "zenon_stringdiffrl".to_owned()
                    } else {
                        format!("zenon_{}", rule.name.as_str())
                    },
                    args: args.clone(),
                    conclusions: vec![first_conclusion, second_conclusion],
                    branches: vec![vec![hypothesis]],
                }
            }
            name => {
                return Err(ZenonError::new(format!(
                    "Zenon: the derived rule {} in tr_rule",
                    name.as_str()
                )));
            }
        })
    }

    fn get_lemma_reference(&self, proof: &Rc<Proof>) -> Result<Translated, ZenonError> {
        let entry = self
            .lemma_numbers
            .get(&ProofKey(proof.clone()))
            .and_then(|number| self.lemma_table.get(&get_lemma_name(*number)))
            .ok_or_else(|| ZenonError::new("Zenon: a lemma that was never made"))?;
        let lemma = &entry.0;
        Ok((
            Rc::new(LlProof {
                conclusions: lemma.proof.conclusions.clone(),
                rule: LlRule::Lemma {
                    name: lemma.name.clone(),
                    args: lemma.params.iter().map(|param| param.1.clone()).collect(),
                },
                subproofs: Vec::new(),
            }),
            entry.1.clone(),
        ))
    }

    fn make_lemma(
        &mut self,
        translated: Rc<LlProof>,
        extras: Vec<Expr>,
        proof: &Rc<Proof>,
    ) -> Result<(), ZenonError> {
        let number = self.lemmas.len() + 1;
        self.lemma_numbers.insert(ProofKey(proof.clone()), number);
        let lemma = Lemma {
            name: get_lemma_name(number),
            params: translated
                .conclusions
                .iter()
                .try_fold(Vec::new(), get_params)?,
            proof: translated,
        };
        self.lemma_table
            .insert(lemma.name.clone(), (lemma.clone(), extras));
        self.lemmas.push(lemma);
        Ok(())
    }

    fn translate(&mut self, proof: &Rc<Proof>) -> Result<Translated, ZenonError> {
        if self.lemma_numbers.contains_key(&ProofKey(proof.clone())) {
            return self.get_lemma_reference(proof);
        }
        let result = if is_derived(&proof.rule) {
            self.translate_derived(proof)?
        } else {
            let subproofs = self.translate_all(&proof.subproofs)?;
            let extras = difference(&subproofs.1, &proof.conclusions);
            let conclusions = extras
                .iter()
                .rev()
                .chain(&proof.conclusions)
                .map(|formula| self.translate_expr(formula))
                .collect::<Result<Vec<_>, _>>()?;
            (
                Rc::new(LlProof {
                    conclusions,
                    rule: self.translate_rule(&proof.rule)?,
                    subproofs: subproofs.0,
                }),
                extras,
            )
        };
        if !self.is_shared_proof(proof) {
            return Ok(result);
        }
        self.make_lemma(result.0, result.1, proof)?;
        self.get_lemma_reference(proof)
    }

    fn is_shared_proof(&self, proof: &Rc<Proof>) -> bool {
        let key = ProofKey(proof.clone());
        self.context.shared_proofs.contains(&key) && !self.lemma_numbers.contains_key(&key)
    }

    /// Zenon's get_sub: the subproofs, and the union of their extras from the right.
    fn translate_all(
        &mut self,
        proofs: &[Rc<Proof>],
    ) -> Result<(Vec<Rc<LlProof>>, Vec<Expr>), ZenonError> {
        let translated = self.translate_each(proofs)?;
        let extras = translated
            .iter()
            .rev()
            .fold(Vec::new(), |accumulated, entry| {
                union(&entry.1, &accumulated)
            });
        Ok((
            translated.into_iter().map(|entry| entry.0).collect(),
            extras,
        ))
    }

    fn translate_each(&mut self, proofs: &[Rc<Proof>]) -> Result<Vec<Translated>, ZenonError> {
        proofs.iter().map(|proof| self.translate(proof)).collect()
    }

    fn recomp_conj(&mut self, sub: Translated, formula: &Expr) -> Result<Translated, ZenonError> {
        if formula.kind == Kind::Not {
            return self.recomp_conj_negated(sub, &formula.args[0]);
        }
        if formula.kind != Kind::And {
            return Ok(sub);
        }
        let left = self.translate_expr(&formula.args[0])?;
        let right = self.translate_expr(&formula.args[1])?;
        let first = self.recomp_conj(sub, &formula.args[0])?;
        let second = self.recomp_conj(first, &formula.args[1])?;
        Ok(recompose(
            self.translate_expr(formula)?,
            LlRule::Connect {
                connective: Kind::And,
                left: left.clone(),
                right: right.clone(),
            },
            &[left, right],
            second,
            formula,
        ))
    }

    fn recomp_conj_negated(
        &mut self,
        sub: Translated,
        formula: &Expr,
    ) -> Result<Translated, ZenonError> {
        let exprs = self.exprs();
        let conclusion = exprs.enot(&self.translate_expr(formula)?);
        let negation = exprs.enot(formula);
        match formula.kind {
            Kind::Or => {
                let left = self.translate_expr(&formula.args[0])?;
                let right = self.translate_expr(&formula.args[1])?;
                let first = self.recomp_conj_negated(sub, &formula.args[0])?;
                let second = self.recomp_conj_negated(first, &formula.args[1])?;
                let removed = [exprs.enot(&left), exprs.enot(&right)];
                Ok(recompose(
                    conclusion,
                    LlRule::NotConnect {
                        connective: Kind::Or,
                        left,
                        right,
                    },
                    &removed,
                    second,
                    &negation,
                ))
            }
            Kind::Imply => {
                let left = self.translate_expr(&formula.args[0])?;
                let right = self.translate_expr(&formula.args[1])?;
                let first = self.recomp_conj(sub, &formula.args[0])?;
                let second = self.recomp_conj_negated(first, &formula.args[1])?;
                let removed = [left.clone(), exprs.enot(&right)];
                Ok(recompose(
                    conclusion,
                    LlRule::NotConnect {
                        connective: Kind::Imply,
                        left,
                        right,
                    },
                    &removed,
                    second,
                    &negation,
                ))
            }
            Kind::Not => {
                let operand = self.translate_expr(&formula.args[0])?;
                let next = self.recomp_conj(sub, &formula.args[0])?;
                Ok(recompose(
                    conclusion,
                    LlRule::NotNot(operand.clone()),
                    &[operand],
                    next,
                    &negation,
                ))
            }
            _ => Ok(sub),
        }
    }

    /// Zenon's recomp_disj: consumes the translated subproofs, one for each disjunct.
    fn recomp_disj<'s>(
        &mut self,
        subs: &'s [Translated],
        formula: &Expr,
    ) -> Result<Disjunction<'s>, ZenonError> {
        let exprs = self.exprs();
        match formula.kind {
            Kind::Or => {
                let left = self.translate_expr(&formula.args[0])?;
                let right = self.translate_expr(&formula.args[1])?;
                let first = self.recomp_disj(subs, &formula.args[0])?;
                let second = self.recomp_disj(first.2, &formula.args[1])?;
                Ok(make_disjunction_node(
                    self.translate_expr(formula)?,
                    Kind::Or,
                    false,
                    left.clone(),
                    right.clone(),
                    first,
                    left,
                    second,
                    right,
                    formula,
                ))
            }
            Kind::Imply => {
                let left = self.translate_expr(&formula.args[0])?;
                let right = self.translate_expr(&formula.args[1])?;
                let first = self.recomp_disj_negated(subs, &formula.args[0])?;
                let second = self.recomp_disj(first.2, &formula.args[1])?;
                let conclusion = self.translate_expr(formula)?;
                let first_removed = exprs.enot(&left);
                Ok(make_disjunction_node(
                    conclusion,
                    Kind::Imply,
                    false,
                    left,
                    right.clone(),
                    first,
                    first_removed,
                    second,
                    right,
                    formula,
                ))
            }
            Kind::Not => self.recomp_disj_negated(subs, &formula.args[0]),
            _ => take_sub(subs),
        }
    }

    fn recomp_disj_negated<'s>(
        &mut self,
        subs: &'s [Translated],
        formula: &Expr,
    ) -> Result<Disjunction<'s>, ZenonError> {
        let exprs = self.exprs();
        match formula.kind {
            Kind::And => {
                let left = self.translate_expr(&formula.args[0])?;
                let right = self.translate_expr(&formula.args[1])?;
                let first = self.recomp_disj_negated(subs, &formula.args[0])?;
                let second = self.recomp_disj_negated(first.2, &formula.args[1])?;
                let negation = exprs.enot(formula);
                let conclusion = exprs.enot(&self.translate_expr(formula)?);
                let conclusions = union(
                    &[conclusion],
                    &union(
                        &difference(&first.0.conclusions, &[exprs.enot(&left)]),
                        &difference(&second.0.conclusions, &[exprs.enot(&right)]),
                    ),
                );
                Ok((
                    Rc::new(LlProof {
                        conclusions,
                        rule: LlRule::NotConnect {
                            connective: Kind::And,
                            left,
                            right,
                        },
                        subproofs: vec![first.0, second.0],
                    }),
                    difference(&union(&first.1, &second.1), &[negation]),
                    second.2,
                ))
            }
            Kind::Not => {
                let operand = self.translate_expr(&formula.args[0])?;
                let first = self.recomp_disj(subs, &formula.args[0])?;
                let conclusion = exprs.enot(&self.translate_expr(formula)?);
                let conclusions = union(
                    &[conclusion],
                    &difference(&first.0.conclusions, std::slice::from_ref(&operand)),
                );
                Ok((
                    Rc::new(LlProof {
                        conclusions,
                        rule: LlRule::NotNot(operand),
                        subproofs: vec![first.0],
                    }),
                    difference(&first.1, &[exprs.enot(formula)]),
                    first.2,
                ))
            }
            _ => take_sub(subs),
        }
    }

    fn get_relation_hypothesis(
        &mut self,
        property: RelationProperty,
        relation: &str,
    ) -> Result<Expr, ZenonError> {
        let key = format!("{} {relation}", property.as_str());
        if let Some(existing) = self.relation_hypotheses.get(&key) {
            return Ok(existing.clone());
        }
        let info = self.context.relations.get(relation);
        let Some(info) = info.filter(|_| relation != "=") else {
            return Err(ZenonError::new(format!(
                "Zenon: no {} hypothesis for {relation}",
                property.as_str()
            )));
        };
        let exprs = self.exprs();
        let type_name = &info.type_name;
        let x = exprs.evar("x");
        let y = exprs.evar("y");
        let z = exprs.evar("z");
        let hypothesis = match property {
            RelationProperty::Reflexive => {
                exprs.eall(&x, type_name, &relate(exprs, relation, &x, &x))
            }
            RelationProperty::Symmetric => exprs.eall(
                &x,
                type_name,
                &exprs.eall(
                    &y,
                    type_name,
                    &exprs.eimply(
                        &relate(exprs, relation, &x, &y),
                        &relate(exprs, relation, &y, &x),
                    ),
                ),
            ),
            RelationProperty::Transitive => exprs.eall(
                &x,
                type_name,
                &exprs.eall(
                    &y,
                    type_name,
                    &exprs.eall(
                        &z,
                        type_name,
                        &exprs.eimply(
                            &relate(exprs, relation, &x, &y),
                            &exprs.eimply(
                                &relate(exprs, relation, &y, &z),
                                &relate(exprs, relation, &x, &z),
                            ),
                        ),
                    ),
                ),
            ),
        };
        self.relation_hypotheses.insert(key, hypothesis.clone());
        let direct = match property {
            RelationProperty::Reflexive => &info.reflexive,
            RelationProperty::Symmetric => &info.symmetric,
            RelationProperty::Transitive => &info.transitive,
        };
        let kind = if let Some(origin) = direct {
            Some(match property {
                RelationProperty::Reflexive => HypothesisKind::Reflexive(origin.clone()),
                RelationProperty::Symmetric => HypothesisKind::Symmetric(origin.clone()),
                RelationProperty::Transitive => HypothesisKind::Transitive(origin.clone()),
            })
        } else {
            match (property, &info.reflexive, &info.transitive_symmetric) {
                (RelationProperty::Reflexive, _, _) | (_, None, _) | (_, _, None) => None,
                (_, Some(reflexive), Some(transitive_symmetric)) => {
                    let origins = DerivedOrigins {
                        relation: relation.to_owned(),
                        reflexive: reflexive.clone(),
                        transitive_symmetric: transitive_symmetric.clone(),
                    };
                    Some(if matches!(property, RelationProperty::Symmetric) {
                        HypothesisKind::Symmetric2(origins)
                    } else {
                        HypothesisKind::Transitive2(origins)
                    })
                }
            }
        };
        let Some(kind) = kind else {
            return Err(ZenonError::new(format!(
                "Zenon: {relation} isn't {}",
                property.as_str()
            )));
        };
        self.hypothesis_kinds.insert(hypothesis.clone(), kind);
        Ok(hypothesis)
    }

    /// Zenon's Eqrel.get_proof: proves a relation hypothesis from the hypotheses that implied it,
    /// and returns the proof with those hypotheses.
    fn get_relation_proof(&self, hypothesis: &Expr) -> Result<(Rc<Proof>, Vec<Expr>), ZenonError> {
        let Some(kind) = self.hypothesis_kinds.get(hypothesis) else {
            return Err(ZenonError::new(
                "Zenon: an extra hypothesis that isn't a relation's",
            ));
        };
        let exprs = self.exprs();
        let negation = exprs.enot(hypothesis);
        let not_all = |formula: &Expr, instance: &Expr, subproof: Rc<Proof>| {
            make_node(
                vec![formula.clone()],
                Rule::new(RuleName::Notall, vec![formula.clone()]),
                &[vec![instance.clone()]],
                vec![subproof],
            )
        };
        let decompose = |origin: &Origin, forms: &[Expr], witnesses: &[Expr]| {
            decompose_conjunction(
                exprs,
                0,
                &origin.formula,
                &origin.directions,
                &origin.variables,
                forms,
                witnesses,
            )
        };
        let get_implication = |formula: &Expr| {
            if formula.kind != Kind::Not || formula.args[0].kind != Kind::Imply {
                return Err(ZenonError::new(
                    "Zenon: a relation hypothesis that isn't an implication",
                ));
            }
            Ok(formula.args[0].clone())
        };
        let first = instantiate_negation(exprs, &negation)?;
        if let HypothesisKind::Reflexive(origin) = kind {
            let proof = decompose(
                origin,
                std::slice::from_ref(&first.0),
                std::slice::from_ref(&first.1),
            )?;
            return Ok((
                not_all(&negation, &first.0, proof),
                vec![origin.formula.clone()],
            ));
        }
        let second = instantiate_negation(exprs, &first.0)?;
        if let HypothesisKind::Symmetric(_) | HypothesisKind::Symmetric2(_) = kind {
            let implication = get_implication(&second.0)?;
            let premise = &implication.args[0];
            let negated_conclusion = exprs.enot(&implication.args[1]);
            let (decomposed, origins) = match kind {
                HypothesisKind::Symmetric(origin) => (
                    decompose(
                        origin,
                        &[premise.clone(), negated_conclusion.clone()],
                        &[first.1.clone(), second.1.clone()],
                    )?,
                    vec![origin.formula.clone()],
                ),
                HypothesisKind::Symmetric2(origins) => {
                    let reflexive = relate(exprs, &origins.relation, &first.1, &first.1);
                    let negated_reflexive = exprs.enot(&reflexive);
                    let from_reflexive = decompose(
                        &origins.reflexive,
                        &[negated_reflexive],
                        std::slice::from_ref(&first.1),
                    )?;
                    let from_transitive = decompose(
                        &origins.transitive_symmetric,
                        &[
                            reflexive.clone(),
                            premise.clone(),
                            negated_conclusion.clone(),
                        ],
                        &[first.1.clone(), first.1.clone(), second.1.clone()],
                    )?;
                    (
                        make_cut(exprs, &reflexive, from_transitive, from_reflexive),
                        vec![
                            origins.reflexive.formula.clone(),
                            origins.transitive_symmetric.formula.clone(),
                        ],
                    )
                }
                _ => return Err(ZenonError::new("Zenon: an unexpected relation property")),
            };
            let proof = not_all(
                &negation,
                &first.0,
                not_all(
                    &first.0,
                    &second.0,
                    make_node(
                        vec![second.0.clone()],
                        Rule::new(
                            RuleName::NotImpl,
                            vec![premise.clone(), implication.args[1].clone()],
                        ),
                        &[vec![premise.clone(), negated_conclusion]],
                        vec![decomposed],
                    ),
                ),
            );
            return Ok((proof, origins));
        }
        let third = instantiate_negation(exprs, &second.0)?;
        let outer = get_implication(&third.0)?;
        let inner = &outer.args[1];
        if inner.kind != Kind::Imply {
            return Err(ZenonError::new(
                "Zenon: a transitivity hypothesis that isn't an implication",
            ));
        }
        let premise = &outer.args[0];
        let middle = &inner.args[0];
        let negated_conclusion = exprs.enot(&inner.args[1]);
        let (decomposed, origins) = match kind {
            HypothesisKind::Transitive(origin) => (
                decompose(
                    origin,
                    &[premise.clone(), middle.clone(), negated_conclusion.clone()],
                    &[first.1.clone(), second.1.clone(), third.1.clone()],
                )?,
                vec![origin.formula.clone()],
            ),
            HypothesisKind::Transitive2(origins) => {
                let reflexive = relate(exprs, &origins.relation, &first.1, &first.1);
                let negated_reflexive = exprs.enot(&reflexive);
                let swapped = relate(exprs, &origins.relation, &third.1, &first.1);
                let negated_swapped = exprs.enot(&swapped);
                let from_swapped = decompose(
                    &origins.transitive_symmetric,
                    &[
                        swapped.clone(),
                        reflexive.clone(),
                        negated_conclusion.clone(),
                    ],
                    &[third.1.clone(), first.1.clone(), first.1.clone()],
                )?;
                let to_swapped = decompose(
                    &origins.transitive_symmetric,
                    &[premise.clone(), middle.clone(), negated_swapped],
                    &[first.1.clone(), second.1.clone(), third.1.clone()],
                )?;
                let swapped_cut = make_cut(exprs, &swapped, from_swapped, to_swapped);
                let from_reflexive = decompose(
                    &origins.reflexive,
                    &[negated_reflexive],
                    std::slice::from_ref(&first.1),
                )?;
                (
                    make_cut(exprs, &reflexive, swapped_cut, from_reflexive),
                    vec![
                        origins.reflexive.formula.clone(),
                        origins.transitive_symmetric.formula.clone(),
                    ],
                )
            }
            _ => return Err(ZenonError::new("Zenon: an unexpected relation property")),
        };
        let negated_inner = exprs.enot(inner);
        let proof = not_all(
            &negation,
            &first.0,
            not_all(
                &first.0,
                &second.0,
                not_all(
                    &second.0,
                    &third.0,
                    make_node(
                        vec![third.0.clone()],
                        Rule::new(RuleName::NotImpl, vec![premise.clone(), inner.clone()]),
                        &[vec![premise.clone(), negated_inner]],
                        // HACK: Zenon concludes the inner implication itself, not its negation.
                        vec![make_node(
                            vec![inner.clone()],
                            Rule::new(
                                RuleName::NotImpl,
                                vec![middle.clone(), inner.args[1].clone()],
                            ),
                            &[vec![middle.clone(), negated_conclusion]],
                            vec![decomposed],
                        )],
                    ),
                ),
            ),
        );
        Ok((proof, origins))
    }

    /// Zenon's make_direct_trans: r(a, b), r(b, c) / r(a, c) / (proof).
    fn make_direct_trans(
        &mut self,
        relation: &str,
        [a, b, c]: [&Expr; 3],
        proof: Rc<Proof>,
    ) -> Result<Rc<Proof>, ZenonError> {
        let exprs = self.exprs();
        let hypothesis = self.get_relation_hypothesis(RelationProperty::Transitive, relation)?;
        let ab = relate(exprs, relation, a, b);
        let bc = relate(exprs, relation, b, c);
        let ac = relate(exprs, relation, a, c);
        let closes = [make_close(exprs, &ab), make_close(exprs, &bc)];
        let implied = make_implies(exprs, &[ab, bc], &ac, &closes, proof)?;
        make_alls(
            exprs,
            &hypothesis,
            &[a.clone(), b.clone(), c.clone()],
            implied.1,
        )
    }

    /// Zenon's make_direct_nsym: -r(a, b) / -r(b, a) / (proof).
    fn make_direct_not_sym(
        &mut self,
        relation: &str,
        a: &Expr,
        b: &Expr,
        proof: Rc<Proof>,
    ) -> Result<Rc<Proof>, ZenonError> {
        let exprs = self.exprs();
        let hypothesis = self.get_relation_hypothesis(RelationProperty::Symmetric, relation)?;
        let ab = relate(exprs, relation, a, b);
        let ba = relate(exprs, relation, b, a);
        let implied = make_imply(exprs, &ba, &ab, proof, make_close(exprs, &ab));
        make_alls(exprs, &hypothesis, &[b.clone(), a.clone()], implied)
    }

    fn expand_trans(
        &mut self,
        relation: &str,
        [a, b, c, d]: [&Expr; 4],
        first: Rc<Proof>,
        second: Rc<Proof>,
    ) -> Result<Rc<Proof>, ZenonError> {
        let exprs = self.exprs();
        let ca = equal(exprs, c, a);
        let not_ca = exprs.enot(&ca);
        let related_ca = relate(exprs, relation, c, a);
        let not_related_ca = exprs.enot(&related_ca);
        let bd = equal(exprs, b, d);
        let not_related_cd = exprs.enot(&relate(exprs, relation, c, d));
        let either = exprs.eand(&not_ca, &not_related_ca);
        let close_bd = make_close(exprs, &bd);
        let via_b = {
            let close_ca = make_close(exprs, &ca);
            let symmetric = make_symmetric_disequality(exprs, a, c, close_ca)?;
            let left = make_not_not(exprs, &ca, symmetric);
            let cb = relate(exprs, relation, c, b);
            let close_refl = make_close_refl(exprs, "=", c);
            let closed = make_p_not_p(
                exprs,
                &cb,
                &not_related_cd,
                vec![close_refl, close_bd.clone()],
            )?;
            let transitive = self.make_direct_trans(relation, [c, a, b], closed)?;
            let right = make_not_not(exprs, &related_ca, transitive);
            make_not_and(exprs, &not_ca, &not_related_ca, left, right)
        };
        let via_d = {
            let left = make_not_not(exprs, &ca, make_close_sym(exprs, "=", c, a));
            let close_cd = make_close(exprs, &relate(exprs, relation, c, d));
            let transitive = self.make_direct_trans(relation, [c, a, d], close_cd)?;
            let right = make_not_not(exprs, &related_ca, transitive);
            make_not_and(exprs, &not_ca, &not_related_ca, left, right)
        };
        let from_bd = make_p_not_p(
            exprs,
            &relate(exprs, relation, a, b),
            &not_related_cd,
            vec![via_b, close_bd],
        )?;
        let from_bd_related = {
            let ad = relate(exprs, relation, a, d);
            let close_refl = make_close_refl(exprs, "=", d);
            let closed = make_p_not_p(exprs, &ad, &not_related_cd, vec![via_d, close_refl])?;
            self.make_direct_trans(relation, [a, b, d], closed)?
        };
        let cut_bd = make_cut(
            exprs,
            &bd,
            from_bd,
            make_cut(
                exprs,
                &relate(exprs, relation, b, d),
                from_bd_related,
                second,
            ),
        );
        Ok(make_cut(
            exprs,
            &either,
            make_and(exprs, &not_ca, &not_related_ca, first),
            cut_bd,
        ))
    }

    fn expand_trans_eq(
        &mut self,
        relation: &str,
        [a, b, c, d]: [&Expr; 4],
        proofs: [Rc<Proof>; 3],
    ) -> Result<Rc<Proof>, ZenonError> {
        let exprs = self.exprs();
        let [first, second, third] = proofs;
        let cd = relate(exprs, relation, c, d);
        let bd = relate(exprs, relation, b, d);
        let cb = relate(exprs, relation, c, b);
        let ca = relate(exprs, relation, c, a);
        let ad = relate(exprs, relation, a, d);
        let not_cd = exprs.enot(&cd);
        let close_refl_c = make_close_refl(exprs, "=", c);
        let close_ab = make_close(exprs, &equal(exprs, a, b));
        let close_refl_d = make_close_refl(exprs, "=", d);
        let to_cb = {
            let close_cd = make_close(exprs, &cd);
            let transitive = self.make_direct_trans(relation, [c, b, d], close_cd)?;
            let cut = make_cut(exprs, &bd, transitive, third);
            make_p_not_p(exprs, &cb, &not_cd, vec![close_refl_c.clone(), cut])?
        };
        let from_cb = make_p_not_p(
            exprs,
            &ca,
            &exprs.enot(&cb),
            vec![close_refl_c, close_ab.clone()],
        )?;
        let to_ad = {
            let symmetric = make_symmetric_disequality(exprs, a, c, first)?;
            make_p_not_p(exprs, &ad, &not_cd, vec![symmetric, close_refl_d.clone()])?
        };
        let from_ad = {
            let negated = exprs.enot(&ad);
            let symmetric = make_symmetric_disequality(exprs, b, a, close_ab)?;
            make_p_not_p(exprs, &bd, &negated, vec![symmetric, close_refl_d])?
        };
        Ok(make_cut(
            exprs,
            &ca,
            make_cut(exprs, &cb, to_cb, from_cb),
            make_cut(exprs, &bd, make_cut(exprs, &ad, to_ad, from_ad), second),
        ))
    }

    /// A derived rule's expansion, with the hypotheses it relies on that no phrase may state.
    fn translate_with(
        &mut self,
        expanded: &Rc<Proof>,
        hypotheses: &[Expr],
    ) -> Result<Translated, ZenonError> {
        let translated = self.translate(expanded)?;
        Ok((translated.0, union(hypotheses, &translated.1)))
    }

    fn translate_derived(&mut self, proof: &Rc<Proof>) -> Result<Translated, ZenonError> {
        let exprs = self.exprs();
        let rule = &proof.rule;
        let args = &rule.args;
        let relation = rule.relation.as_deref().unwrap_or_default();
        match rule.name {
            RuleName::Definition => {
                let definition = get_definition(rule)?;
                let Definition::Pseudo { origin, .. } = definition else {
                    return Err(ZenonError::new(
                        "Zenon: a real definition in translate_derived",
                    ));
                };
                let expanded =
                    self.translate_pseudo_definition(proof, definition, &args[0], &args[1])?;
                self.translate_with(&expanded, std::slice::from_ref(origin))
            }
            RuleName::ConjTree => {
                let sub = self.translate(&get_single(proof)?)?;
                self.recomp_conj(sub, &args[0])
            }
            RuleName::DisjTree => {
                let subs = self.translate_each(&proof.subproofs)?;
                let result = self.recomp_disj(&subs, &args[0])?;
                if !result.2.is_empty() {
                    return Err(ZenonError::new(
                        "Zenon: a disjunction tree with extra subproofs",
                    ));
                }
                Ok((result.0, result.1))
            }
            RuleName::CloseSym => {
                let hypothesis =
                    self.get_relation_hypothesis(RelationProperty::Symmetric, relation)?;
                let a = &args[0];
                let b = &args[1];
                let ab = relate(exprs, relation, a, b);
                let ba = relate(exprs, relation, b, a);
                let implied = make_imply(
                    exprs,
                    &ab,
                    &ba,
                    make_close(exprs, &ab),
                    make_close(exprs, &ba),
                );
                let expanded = make_alls(exprs, &hypothesis, &[a.clone(), b.clone()], implied)?;
                self.translate_with(&expanded, &[hypothesis])
            }
            RuleName::CloseRefl => {
                let hypothesis =
                    self.get_relation_hypothesis(RelationProperty::Reflexive, relation)?;
                let a = &args[0];
                let closed = make_close(exprs, &relate(exprs, relation, a, a));
                let expanded = make_all(exprs, &hypothesis, a, closed)?;
                self.translate_with(&expanded, &[hypothesis])
            }
            RuleName::Refl => {
                let hypothesis =
                    self.get_relation_hypothesis(RelationProperty::Reflexive, relation)?;
                let a = &args[0];
                let b = &args[1];
                let reflexive = relate(exprs, relation, a, a);
                let negated = exprs.enot(&relate(exprs, relation, a, b));
                let close_refl = make_close_refl(exprs, "=", a);
                let closed = make_p_not_p(
                    exprs,
                    &reflexive,
                    &negated,
                    vec![close_refl, get_single(proof)?],
                )?;
                let expanded = make_all(exprs, &hypothesis, a, closed)?;
                self.translate_with(&expanded, &[hypothesis])
            }
            RuleName::PNotPSym => {
                let positive = get_relation(&args[0])?;
                let negative = get_relation(&args[1])?;
                if relation == "=" {
                    let swapped = exprs.enot(&equal(exprs, &negative.args[1], &negative.args[0]));
                    let node = make_p_not_p(
                        exprs,
                        &args[0],
                        &swapped,
                        vec![get_subproof(proof, 1)?, get_subproof(proof, 0)?],
                    )?;
                    let expanded = make_symmetric_disequality(
                        exprs,
                        &negative.args[0],
                        &negative.args[1],
                        node,
                    )?;
                    return self.translate(&expanded);
                }
                let hypothesis =
                    self.get_relation_hypothesis(RelationProperty::Symmetric, relation)?;
                let a = &positive.args[0];
                let b = &positive.args[1];
                let ba = relate(exprs, relation, b, a);
                let node = make_p_not_p(
                    exprs,
                    &ba,
                    &args[1],
                    vec![get_subproof(proof, 0)?, get_subproof(proof, 1)?],
                )?;
                let implied = make_imply(exprs, &args[0], &ba, make_close(exprs, &args[0]), node);
                let expanded = make_alls(exprs, &hypothesis, &[a.clone(), b.clone()], implied)?;
                self.translate_with(&expanded, &[hypothesis])
            }
            RuleName::Trans | RuleName::TransSym => {
                let positive = get_relation(&args[0])?;
                let relation = &*positive.symbol;
                let a = &positive.args[0];
                let b = &positive.args[1];
                let negative = get_relation(&args[1])?;
                let c = &negative.args[0];
                let d = &negative.args[1];
                let first = get_subproof(proof, 0)?;
                let second = get_subproof(proof, 1)?;
                if relation == "=" {
                    let expanded = if rule.name == RuleName::Trans {
                        expand_trans_equal(exprs, [a, b, c, d], first, second)?
                    } else {
                        let swapped = expand_trans_equal(exprs, [a, b, d, c], first, second)?;
                        make_symmetric_disequality(exprs, c, d, swapped)?
                    };
                    return self.translate(&expanded);
                }
                if rule.name == RuleName::Trans {
                    let expanded = self.expand_trans(relation, [a, b, c, d], first, second)?;
                    let hypothesis =
                        self.get_relation_hypothesis(RelationProperty::Transitive, relation)?;
                    return self.translate_with(&expanded, &[hypothesis]);
                }
                let swapped = self.expand_trans(relation, [a, b, d, c], first, second)?;
                let expanded = self.make_direct_not_sym(relation, c, d, swapped)?;
                let hypotheses = [
                    self.get_relation_hypothesis(RelationProperty::Transitive, relation)?,
                    self.get_relation_hypothesis(RelationProperty::Symmetric, relation)?,
                ];
                self.translate_with(&expanded, &hypotheses)
            }
            RuleName::TransEq | RuleName::TransEq2 | RuleName::TransEqSym => {
                let negative = get_relation(&args[2])?;
                let relation = &*negative.symbol;
                let c = &negative.args[0];
                let d = &negative.args[1];
                let a = &args[0];
                let b = &args[1];
                let proofs = get_three(proof)?;
                if relation == "=" && rule.name == RuleName::TransEq {
                    let [first, _, third] = proofs;
                    let expanded = expand_trans_equal(exprs, [a, b, c, d], first, third)?;
                    return self.translate(&expanded);
                }
                if relation == "=" && rule.name == RuleName::TransEqSym {
                    let [first, _, third] = proofs;
                    let swapped = expand_trans_equal(exprs, [a, b, d, c], first, third)?;
                    let expanded = make_symmetric_disequality(exprs, c, d, swapped)?;
                    return self.translate(&expanded);
                }
                let hypothesis =
                    self.get_relation_hypothesis(RelationProperty::Transitive, relation)?;
                let expanded = match rule.name {
                    RuleName::TransEq => self.expand_trans_eq(relation, [a, b, c, d], proofs)?,
                    RuleName::TransEq2 => {
                        let swapped = self.expand_trans_eq(relation, [b, a, c, d], proofs)?;
                        make_symmetric_equality(exprs, a, b, swapped)?
                    }
                    _ => {
                        let swapped = self.expand_trans_eq(relation, [a, b, d, c], proofs)?;
                        self.make_direct_not_sym(relation, c, d, swapped)?
                    }
                };
                self.translate_with(&expanded, &[hypothesis])
            }
            RuleName::NotAllEx => {
                let negation = &args[0];
                let quantified = if negation.kind == Kind::Not {
                    &negation.args[0]
                } else {
                    negation
                };
                let binder = get_binder(quantified, Kind::All)?;
                let variable = &binder.args[0];
                let body = &binder.args[1];
                let existential = exprs.eex(variable, &binder.symbol, &exprs.enot(body));
                let lambda = exprs.elam(variable, &binder.symbol, body);
                let witnessed = make_existential(exprs, &existential, get_single(proof)?)?;
                let expanded = make_node(
                    vec![negation.clone()],
                    Rule::new(RuleName::Notallex, vec![lambda]),
                    &[vec![existential]],
                    vec![witnessed],
                );
                self.translate(&expanded)
            }
            _ => {
                let subproofs = self.translate_each(&proof.subproofs)?;
                get_tla_ll_proof(
                    &mut |expression| self.translate_expr(expression),
                    exprs,
                    proof,
                    &subproofs,
                )
            }
        }
    }

    /// Zenon's translate_pseudo_def: instantiates the defining hypothesis, then rewrites with it.
    fn translate_pseudo_definition(
        &mut self,
        proof: &Proof,
        definition: &Definition,
        folded: &Expr,
        unfolded: &Expr,
    ) -> Result<Rc<Proof>, ZenonError> {
        let exprs = self.exprs();
        let Definition::Pseudo {
            origin,
            symbol,
            params,
            ..
        } = definition
        else {
            return Err(ZenonError::new(
                "Zenon: a real definition in translate_derived",
            ));
        };
        let diff_args = {
            let diff = find_diff(exprs, &exprs.new_var(), folded, unfolded)?;
            match diff.1.kind {
                Kind::App => diff.1.args.clone(),
                Kind::Var => Vec::new(),
                _ => {
                    return Err(ZenonError::new(
                        "Zenon: a pseudo-definition of something other than a symbol",
                    ));
                }
            }
        };
        let mut universals: Vec<(Expr, Expr)> = Vec::new();
        let mut current = origin;
        while current.kind == Kind::All {
            universals.push((current.args[0].clone(), current.clone()));
            current = &current.args[1];
        }
        let actuals = universals
            .iter()
            .enumerate()
            .map(|(position, entry)| {
                let is_repeated = universals[position + 1..]
                    .iter()
                    .any(|later| later.0 == entry.0);
                let index = params.iter().position(|param| *param == entry.0);
                match index {
                    Some(index) if !is_repeated => diff_args.get(index).cloned().ok_or_else(|| {
                        ZenonError::new("Zenon: a pseudo-definition with too few arguments")
                    }),
                    _ => Ok(exprs.emeta(&entry.1)),
                }
            })
            .collect::<Result<Vec<_>, _>>()?;
        self.build_pseudo_definition(proof, symbol, folded, unfolded, origin, &actuals)
    }

    fn build_pseudo_definition(
        &mut self,
        proof: &Proof,
        symbol: &str,
        folded: &Expr,
        unfolded: &Expr,
        hypothesis: &Expr,
        remaining: &[Expr],
    ) -> Result<Rc<Proof>, ZenonError> {
        let exprs = self.exprs();
        if let Some((term, rest)) = remaining.split_first() {
            let binder = get_binder(hypothesis, Kind::All)?;
            let instance =
                exprs.substitute(&[(binder.args[0].clone(), term.clone())], &binder.args[1]);
            let sub =
                self.build_pseudo_definition(proof, symbol, folded, unfolded, &instance, rest)?;
            return Ok(make_node(
                vec![hypothesis.clone()],
                Rule::new(RuleName::All, vec![hypothesis.clone(), term.clone()]),
                &[vec![instance]],
                vec![sub],
            ));
        }
        let subproof = get_single(proof)?;
        if hypothesis.kind == Kind::Equiv {
            let is_crossed = folded.kind == Kind::Not && unfolded.kind == Kind::Not;
            let formula = if is_crossed { &folded.args[0] } else { folded };
            let negated = if is_crossed {
                folded.clone()
            } else {
                exprs.enot(folded)
            };
            let unfolded_formula = if is_crossed {
                &unfolded.args[0]
            } else {
                unfolded
            };
            let unfolded_negated = if is_crossed {
                unfolded.clone()
            } else {
                exprs.enot(unfolded)
            };
            let closed = make_close(exprs, formula);
            let rule = Rule::new(
                RuleName::Equiv,
                vec![hypothesis.args[0].clone(), hypothesis.args[1].clone()],
            );
            return Ok(if is_crossed {
                make_node(
                    vec![hypothesis.clone()],
                    rule,
                    &[vec![unfolded_negated], vec![formula.clone()]],
                    vec![subproof, closed],
                )
            } else {
                make_node(
                    vec![hypothesis.clone()],
                    rule,
                    &[vec![negated], vec![unfolded_formula.clone()]],
                    vec![closed, subproof],
                )
            });
        }
        if hypothesis.is_app_with_arity("=", 2) {
            if *folded == exprs.enot(hypothesis) {
                return Ok(make_node(
                    vec![folded.clone(), hypothesis.clone()],
                    Rule::new(RuleName::Close, vec![hypothesis.clone()]),
                    &[],
                    Vec::new(),
                ));
            }
            let is_defined_on_left = defines_symbol(&hypothesis.args[0], symbol);
            if !is_defined_on_left && !defines_symbol(&hypothesis.args[1], symbol) {
                return Err(ZenonError::new(
                    "Zenon: a pseudo-definition that doesn't define its symbol",
                ));
            }
            let variable = exprs.new_var();
            let diff = find_diff(exprs, &variable, folded, unfolded)?;
            let lambda = exprs.elam(&variable, "", &diff.0);
            let a = &diff.1;
            let b = &diff.2;
            let applied = exprs.apply(&lambda, a)?;
            return Ok(if is_defined_on_left {
                let conclusions = vec![applied, equal(exprs, a, b)];
                make_node(
                    conclusions,
                    Rule::new(
                        RuleName::CongruenceLr,
                        vec![lambda.clone(), a.clone(), b.clone()],
                    ),
                    &[vec![exprs.apply(&lambda, b)?]],
                    vec![subproof],
                )
            } else {
                let conclusions = vec![applied, equal(exprs, b, a)];
                make_node(
                    conclusions,
                    Rule::new(
                        RuleName::CongruenceRl,
                        vec![lambda.clone(), a.clone(), b.clone()],
                    ),
                    &[vec![exprs.apply(&lambda, b)?]],
                    vec![subproof],
                )
            });
        }
        Err(ZenonError::new(
            "Zenon: a pseudo-definition of an unexpected shape",
        ))
    }
}

/// Zenon's Mltoll.translate: the lemmas in the order they were made, then the theorem.
pub fn translate_proof(
    context: &TranslateContext,
    phrases: &[Phrase],
    proof: &Rc<Proof>,
) -> Result<Vec<Lemma>, ZenonError> {
    let mut translator = Translator {
        context,
        translated_exprs: HashMap::new(),
        lemma_numbers: HashMap::new(),
        lemma_table: HashMap::new(),
        lemmas: Vec::new(),
        relation_hypotheses: HashMap::new(),
        hypothesis_kinds: HashMap::new(),
    };
    let translated = translator.translate(proof)?;
    let is_charged = |formula: &Expr| {
        !phrases.iter().any(
            |phrase| matches!(phrase, Phrase::Hyp { formula: stated, .. } if stated == formula),
        )
    };
    // Zenon's discharge_extra: cuts each hypothesis about a relation that the phrases don't state,
    // and proves it from the hypotheses that do.
    let charged: Vec<Expr> = translated
        .1
        .iter()
        .filter(|formula| is_charged(formula))
        .cloned()
        .collect();
    let discharged = charged.iter().try_fold(translated.0, |current, extra| {
        let relation_proof = translator.get_relation_proof(extra)?;
        let proved = translator.translate(&relation_proof.0)?;
        if !proved.1.is_empty() {
            return Err(ZenonError::new("Zenon: a relation proof with extras"));
        }
        let formula = translator.translate_expr(extra)?;
        let stated = translator.translate_all_exprs(&relation_proof.1)?;
        Ok(Rc::new(LlProof {
            conclusions: union(
                &stated,
                &difference(&current.conclusions, std::slice::from_ref(&formula)),
            ),
            rule: LlRule::Cut(formula),
            subproofs: vec![current, proved.0],
        }))
    })?;
    let mut lemmas = translator.lemmas;
    lemmas.push(Lemma {
        name: "zenon_thm".to_owned(),
        params: Vec::new(),
        proof: discharged,
    });
    Ok(lemmas)
}
