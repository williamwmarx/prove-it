//! tlapm's PTL backend up to the text it sends LS4 (Pltl.process_obligation, Prep.flatten, and
//! Ls4's printer): temporal operators reduce to [], <> and prime, assumptions that hold
//! always get a [], and every other subformula becomes an atom named by a hash of its printed form.
//! The text is the negated obligation. A port of `src/prover/ptl/encode.ts`.

use std::rc::Rc;

use crate::errors::Result;
use crate::expression::{
    Bound, Builtin, Bullet, Defn, DefnCore, Expr, ExprCore, Hyp, HypCore, HypNode, Hyps, Param,
    ScopeRef, Sequent, Time, Visibility, adjoin, apply_builtin, at, expr, map_accumulate,
    map_scoped,
};
use crate::levels::get_level_info;
use crate::prep::action::{LEVEL_NUMBER_PREFIXES, get_hash_name, level_prefix};
use crate::substitution::{
    Substitution, SubstitutionNode, bump_by, shift, shift_expr, substitute_expr, substitute_hyp,
};
use crate::temporal::{expand_action, expand_fairness, expand_leadsto, get_time};

// Coalesce.rename_with_loc: each declared name gets its kind in front, or its level for a definition,
// as in VARIABLE_x_ and CONSTANT_i_, so atoms print with the names tlapm hashes. A variable a
// temporal quantifier binds keeps its name.
fn rename_sequent(scope: &ScopeRef, sequent: &Sequent) -> Result<Sequent> {
    let (inner, context) = map_accumulate(scope.clone(), &sequent.context, |current, hyp| {
        let renamed = rename_hyp(&current, hyp)?;
        Ok((adjoin(&current, &renamed), renamed))
    })?;
    Ok(Sequent {
        context,
        active: rename_declarations(&inner, &sequent.active)?,
    })
}

fn rename_hyp(current: &ScopeRef, hyp: &Hyp) -> Result<Hyp> {
    let core = match &hyp.core {
        HypCore::Fresh {
            name,
            shape,
            level,
            domain,
            domain_visibility,
        } => HypCore::Fresh {
            name: format!("{}_{name}_", level_prefix(*level)),
            shape: *shape,
            level: *level,
            domain: domain
                .as_ref()
                .map(|domain| rename_declarations(current, domain))
                .transpose()?,
            domain_visibility: *domain_visibility,
        },
        HypCore::Flex { name } => HypCore::Flex {
            name: format!("VARIABLE_{name}_"),
        },
        HypCore::Defn {
            definition,
            where_defined,
            visibility,
            is_local,
            is_constness_unset,
        } => {
            let DefnCore::Operator { name, body } = &definition.core else {
                return Ok(hyp.clone());
            };
            let body = rename_declarations(current, body)?;
            // The TypeScript prints undefined for a level past the prefixes.
            let level = LEVEL_NUMBER_PREFIXES
                .get(get_level_info(current, &body)?.level)
                .copied()
                .unwrap_or("undefined");
            HypCore::Defn {
                definition: Defn {
                    core: DefnCore::Operator {
                        name: format!("{level}_{name}_"),
                        body,
                    },
                    location: definition.location.clone(),
                },
                where_defined: *where_defined,
                visibility: *visibility,
                is_local: *is_local,
                is_constness_unset: *is_constness_unset,
            }
        }
        HypCore::Fact {
            expression,
            visibility,
            time,
            use_location,
        } => HypCore::Fact {
            expression: rename_declarations(current, expression)?,
            visibility: *visibility,
            time: *time,
            use_location: use_location.clone(),
        },
    };
    Ok(hyp.with_core(core))
}

fn rename_bounds(bounds: &[Bound]) -> Vec<Bound> {
    bounds
        .iter()
        .map(|bound| Bound {
            name: format!("{}_{}_", level_prefix(bound.level), bound.name),
            ..bound.clone()
        })
        .collect()
}

fn rename_declarations(scope: &ScopeRef, expression: &Expr) -> Result<Expr> {
    if let ExprCore::Sequent { sequent } = &expression.core {
        return Ok(expression.with_core(ExprCore::Sequent {
            sequent: rename_sequent(scope, sequent)?,
        }));
    }
    let mapped = map_scoped(
        scope,
        expression,
        &mut rename_declarations,
        &mut adjoin,
        Hyps::All,
    )?;
    let core = match &mapped.core {
        ExprCore::Lambda { params, body } => ExprCore::Lambda {
            params: params
                .iter()
                .map(|param| Param {
                    name: format!("Unknown_{}_", param.name),
                    ..param.clone()
                })
                .collect(),
            body: body.clone(),
        },
        ExprCore::Quant {
            quantifier,
            bounds,
            body,
        } => ExprCore::Quant {
            quantifier: *quantifier,
            bounds: rename_bounds(bounds),
            body: body.clone(),
        },
        ExprCore::Fcn { bounds, body } => ExprCore::Fcn {
            bounds: rename_bounds(bounds),
            body: body.clone(),
        },
        ExprCore::SetOf { element, bounds } => ExprCore::SetOf {
            element: element.clone(),
            bounds: rename_bounds(bounds),
        },
        ExprCore::Choose { name, domain, body } => ExprCore::Choose {
            name: format!("CONSTANT_{name}_"),
            domain: domain.clone(),
            body: body.clone(),
        },
        ExprCore::SetSt { name, domain, body } => ExprCore::SetSt {
            name: format!("CONSTANT_{name}_"),
            domain: domain.clone(),
            body: body.clone(),
        },
        _ => return Ok(mapped),
    };
    Ok(mapped.with_core(core))
}

/// `PreparedHyps`.
struct PreparedHyps {
    scope: ScopeRef,
    substitution: Substitution,
    context: Vec<Hyp>,
}

impl PreparedHyps {
    fn push(&mut self, hyp: Hyp) {
        let prepared = match &hyp.core {
            HypCore::Fact {
                expression,
                visibility: Visibility::Visible,
                time: Time::Always,
                use_location,
            } => hyp.with_core(HypCore::Fact {
                expression: apply_builtin(
                    Builtin::BoxTrue,
                    vec![expression.clone()],
                    &expression.props(),
                ),
                visibility: Visibility::Visible,
                time: Time::Always,
                use_location: use_location.clone(),
            }),
            _ => hyp,
        };
        self.context.push(prepared.clone());
        self.scope = adjoin(&self.scope, &prepared);
    }
}

// Pltl.expand_domains and Pltl.box_assumptions: NEW x \in S becomes NEW x and the fact x \in S, and
// each visible fact that holds always gets a [].
fn prepare_hyps(scope: &ScopeRef, expression: &Expr) -> Result<Expr> {
    let ExprCore::Sequent { sequent } = &expression.core else {
        return map_scoped(scope, expression, &mut prepare_hyps, &mut adjoin, Hyps::All);
    };
    let mut state = PreparedHyps {
        scope: scope.clone(),
        substitution: shift(0),
        context: Vec::new(),
    };
    for original in &sequent.context {
        let hyp = substitute_hyp(&state.substitution, original)?;
        let (
            HypCore::Fresh {
                name,
                shape,
                level,
                domain: Some(domain),
                domain_visibility,
            },
            HypCore::Fresh {
                domain: Some(original_domain),
                ..
            },
        ) = (&hyp.core, &original.core)
        else {
            let pushed = match &hyp.core {
                HypCore::Fact {
                    expression,
                    visibility,
                    time,
                    use_location,
                } => hyp.with_core(HypCore::Fact {
                    expression: prepare_hyps(&state.scope, expression)?,
                    visibility: *visibility,
                    time: *time,
                    use_location: use_location.clone(),
                }),
                _ => hyp.clone(),
            };
            state.push(pushed);
            state.substitution = bump_by(1, &state.substitution);
            continue;
        };
        let domain = prepare_hyps(&state.scope, domain)?;
        state.push(hyp.with_core(HypCore::Fresh {
            name: name.clone(),
            shape: *shape,
            level: *level,
            domain: None,
            domain_visibility: *domain_visibility,
        }));
        // tlapm judges the time of the domain as written, one hypothesis too deep.
        let membership = apply_builtin(
            Builtin::Mem,
            vec![
                at(ExprCore::Ix { index: 1 }, &domain),
                shift_expr(1, &domain)?,
            ],
            &domain.props(),
        );
        let time = if *level == crate::expression::Level::Constant {
            get_time(&state.scope, original_domain)?
        } else {
            Time::Now
        };
        state.push(Rc::new(HypNode {
            core: HypCore::Fact {
                expression: membership,
                visibility: *domain_visibility,
                time,
                use_location: None,
            },
            location: hyp.location.clone(),
        }));
        state.substitution = Rc::new(SubstitutionNode::Compose {
            outer: shift(1),
            inner: bump_by(1, &state.substitution),
        });
    }
    let active = substitute_expr(&state.substitution, &sequent.active)?;
    let active = prepare_hyps(&state.scope, &active)?;
    Ok(expression.with_core(ExprCore::Sequent {
        sequent: Sequent {
            context: state.context,
            active,
        },
    }))
}

fn get_binary(builtin: Builtin) -> Option<&'static str> {
    match builtin {
        Builtin::Conj => Some("&"),
        Builtin::Disj => Some("|"),
        Builtin::Implies => Some("->"),
        Builtin::Equiv => Some("<->"),
        _ => None,
    }
}

fn get_unary(builtin: Builtin) -> Option<&'static str> {
    match builtin {
        Builtin::Neg => Some("~"),
        Builtin::BoxTrue | Builtin::BoxFalse => Some("always"),
        Builtin::Diamond => Some("sometime"),
        Builtin::Prime => Some("next"),
        _ => None,
    }
}

// Prep.flatten, which tlapm applies after Pltl.process_obligation has made every equality an atom:
// TRUE drops out of the conjunctions of each visible fact, and a fact left with nothing disappears.
fn remove_true(expression: &Expr) -> Option<Expr> {
    match &expression.core {
        ExprCore::Internal {
            builtin: Builtin::TRUE,
        } => return None,
        ExprCore::List { bullet, items } if *bullet != Bullet::Or => {
            let items: Vec<Expr> = items.iter().filter_map(remove_true).collect();
            if items.len() <= 1 {
                return items.into_iter().next();
            }
            return Some(expression.with_core(ExprCore::List {
                bullet: Bullet::And,
                items,
            }));
        }
        _ => {}
    }
    let ExprCore::Apply { operator, args } = &expression.core else {
        return Some(expression.clone());
    };
    let (
        ExprCore::Internal {
            builtin: Builtin::Conj,
        },
        [left, right],
    ) = (&operator.core, args.as_slice())
    else {
        return Some(expression.clone());
    };
    match (remove_true(left), remove_true(right)) {
        (Some(left), Some(right)) => Some(expression.with_core(ExprCore::Apply {
            operator: operator.clone(),
            args: vec![left, right],
        })),
        (left, right) => left.or(right),
    }
}

const TRUE_TEXT: &str = "(cc | ~ cc)";

// Ls4's printer. A sequent becomes an implication from its visible facts, joined by &, and
// Prep.flatten applies to the facts of the outermost one.
fn print(hyps: &[Hyp], expression: &Expr, is_outermost: bool) -> Result<String> {
    let recurse = |inner: &Expr| print(hyps, inner, false);
    match &expression.core {
        ExprCore::Internal {
            builtin: Builtin::TRUE,
        } => return Ok(TRUE_TEXT.to_owned()),
        ExprCore::Internal {
            builtin: Builtin::FALSE,
        } => return Ok("(cc & ~ cc)".to_owned()),
        ExprCore::Apply { operator, args } => {
            if let ExprCore::Internal { builtin } = operator.core {
                if let (Some(binary), [left, right]) = (get_binary(builtin), args.as_slice()) {
                    return Ok(format!("({} {binary} {})", recurse(left)?, recurse(right)?));
                }
                if let (Some(unary), [operand]) = (get_unary(builtin), args.as_slice()) {
                    return Ok(format!("({unary} {})", recurse(operand)?));
                }
            }
        }
        ExprCore::List { bullet, items } => {
            let junction = if *bullet == Bullet::Or { "|" } else { "&" };
            let printed = items.iter().map(recurse).collect::<Result<Vec<_>>>()?;
            return Ok(printed
                .into_iter()
                .rev()
                .reduce(|right, left| format!("({left} {junction} {right})"))
                .unwrap_or_else(|| TRUE_TEXT.to_owned()));
        }
        ExprCore::Sequent { sequent } => {
            let mut inner = hyps.to_vec();
            let mut facts = Vec::new();
            for hyp in &sequent.context {
                let fact = match &hyp.core {
                    HypCore::Fact {
                        expression,
                        visibility: Visibility::Visible,
                        ..
                    } => {
                        if is_outermost {
                            remove_true(expression)
                        } else {
                            Some(expression.clone())
                        }
                    }
                    _ => None,
                };
                if let Some(fact) = fact {
                    facts.push(print(&inner, &fact, false)?);
                }
                inner.push(hyp.clone());
            }
            let goal = print(&inner, &sequent.active, false)?;
            return Ok(if facts.is_empty() {
                goal
            } else {
                format!("({} -> {goal})", facts.join(" & "))
            });
        }
        _ => {}
    }
    // Pltl.coalesce_fol names an atom as Coalesce does.
    get_hash_name(hyps, expression)
}

/// The text tlapm sends LS4 for an obligation after Prep.normalize_expand.
pub fn encode_ptl(sequent: &Sequent) -> Result<String> {
    let renamed = rename_declarations(
        &None,
        &expr(ExprCore::Sequent {
            sequent: sequent.clone(),
        }),
    )?;
    let prepared = prepare_hyps(
        &None,
        &expand_action(&expand_leadsto(&expand_fairness(&renamed)?)?)?,
    )?;
    Ok(format!("not ({})", print(&[], &prepared, true)?))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::prep::action::tests::{FIXTURES, is_expected_text, read_fixture};

    // The expected texts come from running `encode.ts` under Bun on the sequents of the action
    // frontend's fixtures. The first case's text is the one `tests/unit/ptl.test.ts` expects.

    #[test]
    fn encodes_as_the_typescript_does() {
        let mut failures = 0;
        let mut count = 0;
        for text in FIXTURES {
            let fixture = read_fixture(text);
            for case in &fixture.cases {
                count += 1;
                if !is_expected_text(encode_ptl(&fixture.input(case)), case.field("ptl")) {
                    failures += 1;
                }
            }
        }
        assert_eq!(count, 37);
        assert_eq!(failures, 0);
    }
}
