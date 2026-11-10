// Ported from Zenon's ext_tla.ml, as shipped in tlapm. Copyright 2008 INRIA, see LICENSE.
//! Zenon's to_llproof for the TLA+ extension: each rule becomes an extension rule of the low-level
//! proof, named after the lemma in Zenon.thy that justifies it.

use std::collections::HashMap;
use std::rc::Rc;

use crate::ZenonError;
use crate::expr::{Expr, Expressions, Kind, difference, union};
use crate::llproof::{Lemma, LlProof, LlRule, connect};
use crate::mltoll::Translated;
use crate::proof::{Proof, RuleName};

/// The lemma's name, the terms it's instantiated with, the conclusions it uses and its branches.
type LlArgs = (String, Vec<Expr>, Vec<Expr>, Vec<Vec<Expr>>);

type Shape = fn(&str, &[Expr]) -> Result<LlArgs, ZenonError>;

fn get_shape_error(name: &str) -> ZenonError {
    ZenonError::new(format!("Zenon: the rule {name} has too few arguments"))
}

/// The first `count` arguments, or the error that the rule has too few.
fn split_args<'a>(
    name: &str,
    args: &'a [Expr],
    count: usize,
) -> Result<(&'a [Expr], &'a [Expr]), ZenonError> {
    if args.len() < count {
        return Err(get_shape_error(name));
    }
    Ok(args.split_at(count))
}

fn alpha(name: &str, args: &[Expr]) -> Result<LlArgs, ZenonError> {
    let (head, rest) = split_args(name, args, 3)?;
    Ok((
        format!("zenon_{name}"),
        rest.to_vec(),
        vec![head[0].clone()],
        vec![vec![head[1].clone(), head[2].clone()]],
    ))
}

fn beta(name: &str, args: &[Expr]) -> Result<LlArgs, ZenonError> {
    let (head, rest) = split_args(name, args, 3)?;
    Ok((
        format!("zenon_{name}"),
        rest.to_vec(),
        vec![head[0].clone()],
        vec![vec![head[1].clone()], vec![head[2].clone()]],
    ))
}

fn beta2(name: &str, args: &[Expr]) -> Result<LlArgs, ZenonError> {
    let (head, rest) = split_args(name, args, 5)?;
    Ok((
        format!("zenon_{name}"),
        rest.to_vec(),
        vec![head[0].clone()],
        vec![
            vec![head[1].clone(), head[2].clone()],
            vec![head[3].clone(), head[4].clone()],
        ],
    ))
}

fn cut12(name: &str, args: &[Expr]) -> Result<LlArgs, ZenonError> {
    let (head, rest) = split_args(name, args, 3)?;
    Ok((
        format!("zenon_{name}"),
        rest.to_vec(),
        Vec::new(),
        vec![
            vec![head[0].clone()],
            vec![head[1].clone(), head[2].clone()],
        ],
    ))
}

fn single(name: &str, args: &[Expr]) -> Result<LlArgs, ZenonError> {
    let (head, rest) = split_args(name, args, 2)?;
    Ok((
        format!("zenon_{name}"),
        rest.to_vec(),
        vec![head[0].clone()],
        vec![vec![head[1].clone()]],
    ))
}

fn close(name: &str, args: &[Expr]) -> Result<LlArgs, ZenonError> {
    let (head, rest) = split_args(name, args, 1)?;
    Ok((
        format!("zenon_{name}"),
        rest.to_vec(),
        vec![head[0].clone()],
        Vec::new(),
    ))
}

fn binsingle(name: &str, args: &[Expr]) -> Result<LlArgs, ZenonError> {
    let (head, rest) = split_args(name, args, 3)?;
    Ok((
        format!("zenon_{name}"),
        rest.to_vec(),
        vec![head[0].clone(), head[1].clone()],
        vec![vec![head[2].clone()]],
    ))
}

fn binbeta(name: &str, args: &[Expr]) -> Result<LlArgs, ZenonError> {
    let (head, rest) = split_args(name, args, 4)?;
    Ok((
        format!("zenon_{name}"),
        rest.to_vec(),
        vec![head[0].clone(), head[1].clone()],
        vec![vec![head[2].clone()], vec![head[3].clone()]],
    ))
}

/// The hypotheses in one branch, or one branch each.
fn get_hypothesis_branches(is_split: bool, hypotheses: &[Expr]) -> Vec<Vec<Expr>> {
    if is_split {
        hypotheses
            .iter()
            .map(|hypothesis| vec![hypothesis.clone()])
            .collect()
    } else {
        vec![hypotheses.to_vec()]
    }
}

/// A conclusion, two terms and then the hypotheses, in one branch or one branch each.
fn with_terms(is_split: bool, name: &str, args: &[Expr]) -> Result<LlArgs, ZenonError> {
    let (head, hypotheses) = split_args(name, args, 3)?;
    Ok((
        format!("zenon_{name}"),
        vec![head[1].clone(), head[2].clone()],
        vec![head[0].clone()],
        get_hypothesis_branches(is_split, hypotheses),
    ))
}

/// A conclusion and then the hypotheses, in one branch or one branch each.
fn without_terms(is_split: bool, name: &str, args: &[Expr]) -> Result<LlArgs, ZenonError> {
    let (head, hypotheses) = split_args(name, args, 1)?;
    Ok((
        format!("zenon_{name}"),
        Vec::new(),
        vec![head[0].clone()],
        get_hypothesis_branches(is_split, hypotheses),
    ))
}

fn get_case_branches(args: &[Expr]) -> Vec<Vec<Expr>> {
    if args.len() <= 1 {
        return if args.is_empty() {
            Vec::new()
        } else {
            vec![args.to_vec()]
        };
    }
    std::iter::once(args[..2].to_vec())
        .chain(get_case_branches(&args[2..]))
        .collect()
}

/// Zenon's to_llargs, by rule name. The rules missing here take one hypothesis.
fn get_shape(name: &str) -> Option<Shape> {
    let shape: Shape = match name {
        "in_emptyset" => |name, args| {
            Ok((
                format!("zenon_{name}"),
                args.get(1..).unwrap_or_default().to_vec(),
                args.get(..1).unwrap_or(args).to_vec(),
                Vec::new(),
            ))
        },
        "in_nat_0" | "in_nat_1" | "in_nat_2" => close,
        "in_upair" => beta,
        "notin_upair" => alpha,
        "in_cup" => beta,
        "notin_cup" => alpha,
        "in_cap" => alpha,
        "notin_cap" => beta,
        "in_setminus" => alpha,
        "notin_setminus" => beta,
        "in_subsetof" => alpha,
        "notin_subsetof" => beta,
        "in_funcset" => |name, args| {
            let (head, rest) = split_args(name, args, 4)?;
            Ok((
                format!("zenon_{name}"),
                rest.to_vec(),
                vec![head[0].clone()],
                vec![head[1..].to_vec()],
            ))
        },
        "except_notin_funcset" => |name, args| {
            let (head, rest) = split_args(name, args, 3)?;
            Ok((
                format!("zenon_{name}"),
                rest.to_vec(),
                vec![head[0].clone()],
                vec![vec![head[1].clone()], vec![head[2].clone()]],
            ))
        },
        "notin_funcset" => |name, args| {
            let (head, rest) = split_args(name, args, 4)?;
            Ok((
                format!("zenon_{name}"),
                rest.to_vec(),
                vec![head[0].clone()],
                vec![
                    vec![head[1].clone()],
                    vec![head[2].clone()],
                    vec![head[3].clone()],
                ],
            ))
        },
        "trueistrue" => binsingle,
        "fapplyfcn" => beta,
        "fapplyexcept" => |name, args| {
            let (head, rest) = split_args(name, args, 8)?;
            Ok((
                format!("zenon_{name}"),
                rest.to_vec(),
                vec![head[0].clone()],
                vec![
                    head[1..4].to_vec(),
                    head[4..7].to_vec(),
                    vec![head[7].clone()],
                ],
            ))
        },
        "boolcase_not" | "boolcase_and" | "boolcase_or" | "boolcase_imply" | "boolcase_equiv"
        | "boolcase_equal" | "boolcase_all" | "boolcase_ex" => beta2,
        "notisafcn_fcn" | "notisafcn_except" | "notisafcn_onearg" | "notisafcn_extend" => close,
        "ifthenelse" => beta2,
        "notequalchoose" => cut12,
        "case" => |name, args| {
            let (head, rest) = split_args(name, args, 2)?;
            Ok((
                format!("zenon_{name}"),
                vec![head[1].clone()],
                vec![head[0].clone()],
                get_case_branches(rest),
            ))
        },
        "p_eq_l" | "p_eq_r" | "np_eq_l" | "np_eq_r" => binbeta,
        "all_in" | "notex_in" => binsingle,
        "cup_subseteq" => alpha,
        "not_cup_subseteq" => beta,
        "subseteq_cap" => alpha,
        "not_subseteq_cap" => beta,
        "tuple_eq_match" => |name, args| without_terms(false, name, args),
        "tuple_eq_mismatch" => close,
        "in_product" => |name, args| with_terms(false, name, args),
        "notin_product" => |name, args| with_terms(true, name, args),
        "tuple_notisaseq" => close,
        "record_eq_match" => |name, args| without_terms(false, name, args),
        "record_neq_match" => |name, args| without_terms(true, name, args),
        "record_eq_mismatch" => close,
        "neq_record" | "record_neq" => |name, args| with_terms(true, name, args),
        "in_recordset" => |name, args| with_terms(false, name, args),
        "notin_recordset" => |name, args| with_terms(true, name, args),
        "record_notisafcn" => close,
        _ => return None,
    };
    Some(shape)
}

/// The pieces of an enumerated set: its first element and the set of the others.
fn get_split(exprs: &Expressions, set: &Expr, is_set_of: bool) -> Option<(Expr, Expr)> {
    let is_split = set.kind == Kind::App
        && *set.symbol == *(if is_set_of { "TLA.set" } else { "TLA.addElt" })
        && set.args.len() >= (if is_set_of { 1 } else { 2 });
    is_split.then(|| {
        (
            set.args[0].clone(),
            if is_set_of {
                exprs.eapp("TLA.set", &set.args[1..])
            } else {
                set.args[1].clone()
            },
        )
    })
}

struct TlaTranslation<'a, 'b> {
    translate_expr: &'b mut dyn FnMut(&Expr) -> Result<Expr, ZenonError>,
    exprs: &'a Expressions,
}

impl TlaTranslation<'_, '_> {
    fn tr_all(&mut self, expressions: &[Expr]) -> Result<Vec<Expr>, ZenonError> {
        expressions
            .iter()
            .map(|expression| (self.translate_expr)(expression))
            .collect()
    }

    fn member(&self, element: &Expr, set: &Expr) -> Expr {
        self.exprs.eapp("TLA.in", &[element.clone(), set.clone()])
    }

    fn equal(&self, left: &Expr, right: &Expr) -> Expr {
        self.exprs.eapp("=", &[left.clone(), right.clone()])
    }

    fn extension(
        &mut self,
        conclusions: &[Expr],
        name: &str,
        args: &[Expr],
        rule_conclusions: &[Expr],
        branches: &[Vec<Expr>],
        node_subproofs: Vec<Rc<LlProof>>,
    ) -> Result<Rc<LlProof>, ZenonError> {
        let conclusions = self.tr_all(conclusions)?;
        let args = self.tr_all(args)?;
        let rule_conclusions = self.tr_all(rule_conclusions)?;
        let branches = branches
            .iter()
            .map(|branch| self.tr_all(branch))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Rc::new(LlProof {
            conclusions,
            rule: LlRule::Extension {
                name: name.to_owned(),
                args,
                conclusions: rule_conclusions,
                branches,
            },
            subproofs: node_subproofs,
        }))
    }

    /// The membership in an enumerated set, one element at a time.
    fn get_membership(
        &mut self,
        element: &Expr,
        set: &Expr,
        remaining: &[Translated],
        conclusions: &[Expr],
        is_set_of: bool,
    ) -> Result<Translated, ZenonError> {
        let is_empty = if is_set_of {
            set.is_app_with_arity("TLA.set", 0)
        } else {
            set.kind == Kind::Var && &*set.symbol == "TLA.emptyset"
        };
        if is_empty {
            let membership = self.member(element, set);
            return Ok((
                self.extension(
                    conclusions,
                    "zenon_in_emptyset",
                    std::slice::from_ref(element),
                    &[membership],
                    &[],
                    Vec::new(),
                )?,
                Vec::new(),
            ));
        }
        let split = get_split(self.exprs, set, is_set_of);
        let (Some((value, rest)), Some(first)) = (split, remaining.first()) else {
            if !is_set_of && remaining.len() == 1 {
                return Ok(remaining[0].clone());
            }
            return Err(ZenonError::new(
                "Zenon: a membership proof that doesn't match its set",
            ));
        };
        let conclusion = self.member(element, set);
        let is_value = self.equal(element, &value);
        let is_in_rest = self.member(element, &rest);
        let next_conclusions: Vec<Expr> = std::iter::once(is_in_rest.clone())
            .chain(conclusions.iter().cloned())
            .collect();
        let next = self.get_membership(
            element,
            &rest,
            &remaining[1..],
            &next_conclusions,
            is_set_of,
        )?;
        let extras = difference(&union(&first.1, &next.1), conclusions);
        let node_conclusions: Vec<Expr> = extras.iter().rev().chain(conclusions).cloned().collect();
        Ok((
            self.extension(
                &node_conclusions,
                "zenon_in_addElt",
                &[element.clone(), value, rest],
                &[conclusion],
                &[vec![is_value], vec![is_in_rest]],
                vec![first.0.clone(), next.0],
            )?,
            extras,
        ))
    }

    /// The non-membership in an enumerated set, one element at a time.
    fn get_non_membership(
        &mut self,
        element: &Expr,
        set: &Expr,
        sub: &Translated,
        conclusions: &[Expr],
        is_set_of: bool,
    ) -> Result<Translated, ZenonError> {
        let Some((value, rest)) = get_split(self.exprs, set, is_set_of) else {
            return Ok(sub.clone());
        };
        let conclusion = self.exprs.enot(&self.member(element, set));
        let is_not_value = self.exprs.enot(&self.equal(element, &value));
        let is_not_in_rest = self.exprs.enot(&self.member(element, &rest));
        let next_conclusions: Vec<Expr> = [is_not_value.clone(), is_not_in_rest.clone()]
            .into_iter()
            .chain(conclusions.iter().cloned())
            .collect();
        let next = self.get_non_membership(element, &rest, sub, &next_conclusions, is_set_of)?;
        let extras = difference(&next.1, conclusions);
        let node_conclusions: Vec<Expr> = extras.iter().rev().chain(conclusions).cloned().collect();
        Ok((
            self.extension(
                &node_conclusions,
                "zenon_notin_addElt",
                &[element.clone(), value, rest],
                &[conclusion],
                &[vec![is_not_value, is_not_in_rest]],
                vec![next.0],
            )?,
            extras,
        ))
    }
}

/// Zenon's Ext_tla.to_llproof, for a rule of the extension and its translated subproofs.
pub fn get_tla_ll_proof(
    translate_expr: &mut dyn FnMut(&Expr) -> Result<Expr, ZenonError>,
    exprs: &Expressions,
    proof: &Proof,
    subproofs: &[Translated],
) -> Result<Translated, ZenonError> {
    let mut translation = TlaTranslation {
        translate_expr,
        exprs,
    };
    let rule = &proof.rule;
    match rule.name {
        RuleName::InAddElt | RuleName::InSet => translation.get_membership(
            &rule.args[1],
            &rule.args[2],
            subproofs,
            &proof.conclusions,
            rule.name == RuleName::InSet,
        ),
        RuleName::NotinAddElt | RuleName::NotinSet => {
            if subproofs.len() != 1 {
                return Err(ZenonError::new(format!(
                    "Zenon: {} with {} subproofs",
                    rule.name.as_str(),
                    subproofs.len()
                )));
            }
            translation.get_non_membership(
                &rule.args[1],
                &rule.args[2],
                &subproofs[0],
                &proof.conclusions,
                rule.name == RuleName::NotinSet,
            )
        }
        RuleName::Notequivdef => {
            if subproofs.len() != 1 {
                return Err(ZenonError::new("Zenon: notequivdef with several subproofs"));
            }
            Ok(subproofs[0].clone())
        }
        _ => {
            let name = rule.name.as_str();
            let ll_args = get_shape(name).unwrap_or(single)(name, &rule.args)?;
            let extras = difference(
                &subproofs.iter().fold(Vec::new(), |accumulated, entry| {
                    union(&accumulated, &entry.1)
                }),
                &proof.conclusions,
            );
            let node_conclusions: Vec<Expr> = extras
                .iter()
                .rev()
                .chain(&proof.conclusions)
                .cloned()
                .collect();
            Ok((
                translation.extension(
                    &node_conclusions,
                    &ll_args.0,
                    &ll_args.1,
                    &ll_args.2,
                    &ll_args.3,
                    subproofs.iter().map(|entry| entry.0.clone()).collect(),
                )?,
                extras,
            ))
        }
    }
}

struct Postprocessor<'a> {
    exprs: &'a Expressions,
    cache: HashMap<Expr, Expr>,
}

impl Postprocessor<'_> {
    fn pp(&mut self, expression: &Expr) -> Result<Expr, ZenonError> {
        if let Some(cached) = self.cache.get(expression) {
            return Ok(cached.clone());
        }
        let exprs = self.exprs;
        let result = match expression.kind {
            Kind::Var | Kind::True | Kind::False => expression.clone(),
            Kind::Meta => {
                return Err(ZenonError::new(
                    "Zenon: a metavariable in a low-level proof",
                ));
            }
            Kind::App => {
                if &*expression.symbol != "$notequiv" {
                    let args = self.pp_all(&expression.args)?;
                    exprs.eapp(&expression.symbol, &args)
                } else {
                    if expression.args.len() != 2 {
                        return Err(ZenonError::new("Zenon: $notequiv without two arguments"));
                    }
                    let right = self.pp(&expression.args[1])?;
                    exprs.enot(&exprs.eequiv(&self.pp(&expression.args[0])?, &right))
                }
            }
            Kind::Not => exprs.enot(&self.pp(&expression.args[0])?),
            Kind::And | Kind::Or | Kind::Imply | Kind::Equiv => {
                let right = self.pp(&expression.args[1])?;
                connect(
                    exprs,
                    expression.kind,
                    &self.pp(&expression.args[0])?,
                    &right,
                )
            }
            Kind::All | Kind::Ex | Kind::Tau | Kind::Lam => exprs.binder(
                expression.kind,
                &expression.args[0],
                &expression.symbol,
                &self.pp(&expression.args[1])?,
            ),
        };
        self.cache.insert(expression.clone(), result.clone());
        Ok(result)
    }

    fn pp_all(&mut self, expressions: &[Expr]) -> Result<Vec<Expr>, ZenonError> {
        expressions
            .iter()
            .map(|expression| self.pp(expression))
            .collect()
    }

    fn pp_rule(&mut self, rule: &LlRule) -> Result<LlRule, ZenonError> {
        Ok(match rule {
            LlRule::False | LlRule::NotTrue => rule.clone(),
            LlRule::Axiom(formula) => LlRule::Axiom(self.pp(formula)?),
            LlRule::Cut(formula) => LlRule::Cut(self.pp(formula)?),
            LlRule::NotNot(formula) => LlRule::NotNot(self.pp(formula)?),
            LlRule::NotEq(term) => LlRule::NotEq(self.pp(term)?),
            LlRule::EqSym { left, right } => LlRule::EqSym {
                left: self.pp(left)?,
                right: self.pp(right)?,
            },
            LlRule::NotEqual { left, right } => LlRule::NotEqual {
                left: self.pp(left)?,
                right: self.pp(right)?,
            },
            LlRule::Connect {
                connective,
                left,
                right,
            } => LlRule::Connect {
                connective: *connective,
                left: self.pp(left)?,
                right: self.pp(right)?,
            },
            LlRule::NotConnect {
                connective,
                left,
                right,
            } => LlRule::NotConnect {
                connective: *connective,
                left: self.pp(left)?,
                right: self.pp(right)?,
            },
            LlRule::Ex { quantified, term } => LlRule::Ex {
                quantified: self.pp(quantified)?,
                term: self.pp(term)?,
            },
            LlRule::All { quantified, term } => LlRule::All {
                quantified: self.pp(quantified)?,
                term: self.pp(term)?,
            },
            LlRule::NotEx { quantified, term } => LlRule::NotEx {
                quantified: self.pp(quantified)?,
                term: self.pp(term)?,
            },
            LlRule::NotAll { quantified, term } => LlRule::NotAll {
                quantified: self.pp(quantified)?,
                term: self.pp(term)?,
            },
            LlRule::PNotP { positive, negative } => LlRule::PNotP {
                positive: self.pp(positive)?,
                negative: self.pp(negative)?,
            },
            LlRule::CongruenceLr {
                context,
                left,
                right,
            } => LlRule::CongruenceLr {
                context: self.pp(context)?,
                left: self.pp(left)?,
                right: self.pp(right)?,
            },
            LlRule::CongruenceRl {
                context,
                left,
                right,
            } => LlRule::CongruenceRl {
                context: self.pp(context)?,
                left: self.pp(left)?,
                right: self.pp(right)?,
            },
            LlRule::Definition {
                name,
                folded,
                unfolded,
            } => LlRule::Definition {
                name: name.clone(),
                folded: self.pp(folded)?,
                unfolded: self.pp(unfolded)?,
            },
            LlRule::Extension {
                name,
                args,
                conclusions,
                branches,
            } => LlRule::Extension {
                name: name.clone(),
                args: self.pp_all(args)?,
                conclusions: self.pp_all(conclusions)?,
                branches: branches
                    .iter()
                    .map(|branch| self.pp_all(branch))
                    .collect::<Result<_, _>>()?,
            },
            LlRule::Lemma { name, args } => LlRule::Lemma {
                name: name.clone(),
                args: self.pp_all(args)?,
            },
        })
    }

    fn pp_tree(&mut self, tree: &LlProof) -> Result<Rc<LlProof>, ZenonError> {
        Ok(Rc::new(LlProof {
            conclusions: self.pp_all(&tree.conclusions)?,
            rule: self.pp_rule(&tree.rule)?,
            subproofs: tree
                .subproofs
                .iter()
                .map(|subproof| self.pp_tree(subproof))
                .collect::<Result<_, _>>()?,
        }))
    }
}

/// Zenon's Ext_tla.postprocess: the lemmas with each $notequiv written as a negated equivalence.
pub fn postprocess_tla(exprs: &Expressions, lemmas: Vec<Lemma>) -> Result<Vec<Lemma>, ZenonError> {
    let mut postprocessor = Postprocessor {
        exprs,
        cache: HashMap::new(),
    };
    lemmas
        .into_iter()
        .map(|lemma| {
            Ok(Lemma {
                params: lemma
                    .params
                    .iter()
                    .map(|param| Ok((param.0.clone(), postprocessor.pp(&param.1)?)))
                    .collect::<Result<_, ZenonError>>()?,
                proof: postprocessor.pp_tree(&lemma.proof)?,
                name: lemma.name,
            })
        })
        .collect()
}
