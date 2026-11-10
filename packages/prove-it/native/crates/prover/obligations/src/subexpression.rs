//! tlapm's Expr.Deref: a subexpression reference such as Op!2!<< resolves to the
//! subexpression it names, abstracted over the bound names it uses.
//! A port of `src/obligations/subexpression.ts`.

use std::rc::Rc;

use crate::errors::{ObligationError, Result};
use crate::expression::{
    Bound, BoundDomain, Defn, DefnCore, Expr, ExprCore, ExprNode, Hyp, HypCore, Level, Param,
    ParenForm, Quantifier, Selector, Visibility, Warn, WhereDefined, XlabelIndex, at, expr,
    get_bound_fresh, get_children, get_error_note, get_fresh, get_param_fresh, hyp, map_children,
    map_selector_args, to_index,
};
use crate::substitution::{cons_all, cons_substitution, shift, substitute_expr};

struct Resolution {
    params: Vec<Param>,
    definitions: Vec<Defn>,
    expression: Expr,
}

struct LabelMatch {
    context: Vec<Hyp>,
    expression: Expr,
    indices: Vec<XlabelIndex>,
}

/// What a selector resolves to, with the selectors left and whether it named a label.
struct Step {
    resolution: Resolution,
    rest: Vec<Selector>,
    is_label: bool,
}

const UNRESOLVED_NAME: &str = "$Bad";

fn unresolved() -> Expr {
    expr(ExprCore::Opaque {
        name: UNRESOLVED_NAME.to_owned(),
    })
}

fn is_unresolved(expression: &Expr) -> bool {
    matches!(&expression.core, ExprCore::Opaque { name } if name == UNRESOLVED_NAME)
}

fn strip_parens_and_atomic(expression: &Expr) -> Result<Expr> {
    let mapped = match &expression.core {
        ExprCore::Parens {
            expression: inner, ..
        } => strip_parens_and_atomic(inner)?,
        _ => map_children(expression, &mut |inner| strip_parens_and_atomic(inner))?,
    };
    if !mapped.is_atomic {
        return Ok(mapped);
    }
    Ok(Rc::new(ExprNode {
        core: mapped.core.clone(),
        location: mapped.location.clone(),
        is_atomic: false,
    }))
}

// Parentheses go everywhere but in the definitions of a LET.
fn strip_parens(expression: &Expr) -> Result<Expr> {
    match &expression.core {
        ExprCore::Let { definitions, body } => Ok(at(
            ExprCore::Let {
                definitions: definitions.clone(),
                body: strip_parens(body)?,
            },
            body,
        )),
        ExprCore::Parens {
            expression: inner, ..
        } => strip_parens(inner),
        _ => map_children(expression, &mut |inner| strip_parens(inner)),
    }
}

fn has_negative_index(expression: &Expr) -> bool {
    match &expression.core {
        ExprCore::Ix { index } => *index <= 0,
        _ => get_children(expression).iter().any(has_negative_index),
    }
}

/// `substituteExpr(shift(-(position - 1)), expression)`.
fn shift_down(position: usize, expression: &Expr) -> Result<Expr> {
    let amount = 1 - isize::try_from(position).map_err(|_| ObligationError::assert_failure())?;
    substitute_expr(&shift(amount), expression)
}

fn find_in_bounds(
    bounds: &[Bound],
    body: &Expr,
    label: &str,
    context: &[Hyp],
) -> Option<LabelMatch> {
    bounds
        .iter()
        .find_map(|bound| match &bound.domain {
            BoundDomain::Domain(domain) => find_label(domain, label, context),
            _ => None,
        })
        .or_else(|| {
            let inner: Vec<Hyp> = context
                .iter()
                .cloned()
                .chain(bounds.iter().map(get_bound_fresh))
                .collect();
            find_label(body, label, &inner)
        })
}

fn extended(context: &[Hyp], hyps: impl Iterator<Item = Hyp>) -> Vec<Hyp> {
    context.iter().cloned().chain(hyps).collect()
}

// Visit.iter's context for each binder, stopping at labels with other names and at declarations
// in an ASSUME.
fn find_label(expression: &Expr, label: &str, context: &[Hyp]) -> Option<LabelMatch> {
    let search = |inner: &Expr| find_label(inner, label, context);
    match &expression.core {
        ExprCore::Parens {
            expression: inner,
            form,
        } => match form {
            ParenForm::Xlabel {
                label: found,
                indices,
            } => (found == label).then(|| LabelMatch {
                context: context.to_vec(),
                expression: inner.clone(),
                indices: indices.clone(),
            }),
            _ => search(inner),
        },
        ExprCore::Lambda { params, body } => find_label(
            body,
            label,
            &extended(context, params.iter().map(get_param_fresh)),
        ),
        ExprCore::Let { definitions, body } => {
            let mut inner = context.to_vec();
            for definition in definitions {
                let found = match &definition.core {
                    DefnCore::Operator { body, .. } | DefnCore::Bpragma { body, .. } => {
                        find_label(body, label, &inner)
                    }
                    _ => None,
                };
                if found.is_some() {
                    return found;
                }
                inner.push(hyp(HypCore::Defn {
                    definition: definition.clone(),
                    where_defined: WhereDefined::Builtin,
                    visibility: Visibility::Visible,
                    is_local: true,
                    is_constness_unset: false,
                }));
            }
            find_label(body, label, &inner)
        }
        ExprCore::Quant { bounds, body, .. } | ExprCore::Fcn { bounds, body } => {
            find_in_bounds(bounds, body, label, context)
        }
        ExprCore::SetOf { element, bounds } => find_in_bounds(bounds, element, label, context),
        ExprCore::Tquant { names, body, .. } => find_label(
            body,
            label,
            &extended(
                context,
                names
                    .iter()
                    .map(|name| hyp(HypCore::Flex { name: name.clone() })),
            ),
        ),
        ExprCore::Choose { name, domain, body } => domain
            .as_ref()
            .and_then(search)
            .or_else(|| find_choice_body(name, body, label, context)),
        ExprCore::SetSt { name, domain, body } => {
            search(domain).or_else(|| find_choice_body(name, body, label, context))
        }
        ExprCore::Sequent { sequent } => {
            let mut inner = context.to_vec();
            for hyp in &sequent.context {
                let HypCore::Fact { expression, .. } = &hyp.core else {
                    return None;
                };
                let found = find_label(expression, label, &inner);
                if found.is_some() {
                    return found;
                }
                inner.push(hyp.clone());
            }
            find_label(&sequent.active, label, &inner)
        }
        _ => get_children(expression).iter().find_map(search),
    }
}

fn find_choice_body(name: &str, body: &Expr, label: &str, context: &[Hyp]) -> Option<LabelMatch> {
    find_label(
        body,
        label,
        &extended(
            context,
            std::iter::once(get_fresh(name, Level::Constant, 0)),
        ),
    )
}

fn get_ix(index: usize) -> Expr {
    expr(ExprCore::Ix {
        index: to_index(index),
    })
}

// The first count indices in reverse, and the rest past the parameters.
fn get_reversal(count: usize, param_count: usize) -> Result<crate::substitution::Substitution> {
    let amount =
        isize::try_from(count + param_count).map_err(|_| ObligationError::assert_failure())?;
    let indices: Vec<Expr> = (1..=count).map(get_ix).collect();
    Ok(cons_all(&indices, shift(amount)))
}

fn get_indices(count: usize) -> Vec<Expr> {
    (0..count).map(|index| get_ix(count - index)).collect()
}

fn instantiate(on_warning: &mut Warn, expression: &Expr, args: &[Expr]) -> Result<Expr> {
    match &expression.core {
        ExprCore::Quant { bounds, .. }
        | ExprCore::Fcn { bounds, .. }
        | ExprCore::SetOf { bounds, .. } => {
            if bounds.len() != args.len() {
                let expected = bounds.len();
                let message = format!(
                    "Arity mismatch in subexpression instance.\nExpected {expected} argument{}, but found{} {}.",
                    if expected == 1 { "" } else { "s" },
                    if args.len() < expected { " only" } else { "" },
                    args.len()
                );
                on_warning(get_error_note(expression.location.as_ref(), &message));
                return Err(ObligationError::proof_failure(
                    message,
                    "Expr.Deref.deref_inst",
                ));
            }
            let body = match &expression.core {
                ExprCore::SetOf { element, .. } => element,
                ExprCore::Quant { body, .. } | ExprCore::Fcn { body, .. } => body,
                _ => return Err(ObligationError::assert_failure()),
            };
            substitute_expr(&cons_all(args, shift(0)), body)
        }
        ExprCore::Tquant {
            quantifier,
            names,
            body,
        } => instantiate(
            on_warning,
            &at(
                ExprCore::Quant {
                    quantifier: *quantifier,
                    bounds: names
                        .iter()
                        .map(|name| Bound {
                            name: name.clone(),
                            level: Level::State,
                            domain: BoundDomain::NoDomain,
                        })
                        .collect(),
                    body: body.clone(),
                },
                expression,
            ),
            args,
        ),
        ExprCore::Lambda { params, body } => instantiate(
            on_warning,
            &at(
                ExprCore::Quant {
                    quantifier: Quantifier::Forall,
                    bounds: params
                        .iter()
                        .map(|param| Bound {
                            name: param.name.clone(),
                            level: Level::Unknown,
                            domain: BoundDomain::NoDomain,
                        })
                        .collect(),
                    body: body.clone(),
                },
                expression,
            ),
            args,
        ),
        ExprCore::SetSt { body, .. } | ExprCore::Choose { body, .. } => {
            if args.len() != 1 {
                let message = format!(
                    "Arity mismatch in subexpression instance.\nExpected 1 argument, but found {}.",
                    args.len()
                );
                on_warning(get_error_note(expression.location.as_ref(), &message));
                return Err(ObligationError::proof_failure(
                    message,
                    "Expr.Deref.deref_inst",
                ));
            }
            substitute_expr(&cons_all(args, shift(0)), body)
        }
        _ => {
            let message = "Cannot instantiate non-binding expression";
            on_warning(get_error_note(expression.location.as_ref(), message));
            Err(ObligationError::proof_failure(
                message,
                "Expr.Deref.deref_inst",
            ))
        }
    }
}

fn get_param(name: &str) -> Param {
    Param {
        name: name.to_owned(),
        shape: 0,
        location: None,
    }
}

fn abstract_bound(
    on_warning: &mut Warn,
    definition_count: usize,
    expression: &Expr,
) -> Result<(Vec<Param>, Expr)> {
    let params = match &expression.core {
        ExprCore::Quant { bounds, .. }
        | ExprCore::Fcn { bounds, .. }
        | ExprCore::SetOf { bounds, .. } => {
            bounds.iter().map(|bound| get_param(&bound.name)).collect()
        }
        ExprCore::Tquant { names, .. } => names.iter().map(|name| get_param(name)).collect(),
        ExprCore::Lambda { params, .. } => params.clone(),
        ExprCore::SetSt { name, .. } | ExprCore::Choose { name, .. } => vec![get_param(name)],
        _ => {
            let message = "Cannot abstract over bound variables in a non-binding expression";
            on_warning(get_error_note(expression.location.as_ref(), message));
            return Err(ObligationError::proof_failure(
                message,
                "Expr.Deref.deref_at",
            ));
        }
    };
    let shifted = substitute_expr(&get_reversal(definition_count, params.len())?, expression)?;
    let instance = instantiate(on_warning, &shifted, &get_indices(params.len()))?;
    Ok((params, instance))
}

fn check_at_most(
    on_warning: &mut Warn,
    position: usize,
    count: usize,
    origin: &Expr,
    message: &str,
) -> Result<()> {
    if position <= count {
        return Ok(());
    }
    on_warning(get_error_note(origin.location.as_ref(), message));
    Err(ObligationError::proof_failure(
        message,
        "Expr.Deref.deref_num",
    ))
}

/// The item at `position`; the TypeScript reads `undefined` at position 0, which no selector has.
fn pick_item(
    on_warning: &mut Warn,
    position: usize,
    origin: &Expr,
    message: &str,
    items: &[Expr],
) -> Result<Expr> {
    check_at_most(on_warning, position, items.len(), origin, message)?;
    position
        .checked_sub(1)
        .and_then(|index| items.get(index))
        .cloned()
        .ok_or_else(ObligationError::assert_failure)
}

fn tuple(elements: Vec<Expr>, from: &ExprNode) -> Expr {
    at(ExprCore::Tuple { elements }, from)
}

fn get_numbered(
    on_warning: &mut Warn,
    expression: &Expr,
    position: usize,
    origin: &Expr,
    message: &str,
) -> Result<(Vec<Defn>, Expr)> {
    if let ExprCore::With {
        expression: inner, ..
    } = &expression.core
    {
        return get_numbered(on_warning, inner, position, origin, message);
    }
    let picked = match &expression.core {
        ExprCore::Sequent { sequent } => {
            check_at_most(
                on_warning,
                position,
                sequent.context.len() + 1,
                origin,
                message,
            )?;
            let hyp = position
                .checked_sub(1)
                .and_then(|index| sequent.context.get(index));
            let shifted = match hyp.map(|hyp| &hyp.core) {
                Some(HypCore::Fact { expression, .. }) => shift_down(position, expression)?,
                Some(_) => {
                    let hyp_message = "subexpression reference does not resolve to an expression";
                    on_warning(get_error_note(expression.location.as_ref(), hyp_message));
                    return Err(ObligationError::proof_failure(
                        hyp_message,
                        "Expr.Deref.deref_num",
                    ));
                }
                None => shift_down(position, &sequent.active)?,
            };
            if has_negative_index(&shifted) {
                on_warning(get_error_note(
                    expression.location.as_ref(),
                    "subexpression of ASSUME/PROVE uses identifiers declared therein\nTlapm does not handle yet such subexpression namings.",
                ));
                return Err(ObligationError::proof_failure(
                    "Subexpression of ASSUME/PROVE uses identifiers declared therein\n\nTlapm does not handle yet such subexpression namings.",
                    "Expr.Deref.deref_num",
                ));
            }
            Some(shifted)
        }
        ExprCore::Apply { args, .. } => {
            Some(pick_item(on_warning, position, origin, message, args)?)
        }
        ExprCore::If {
            condition,
            consequent,
            alternative,
        } => Some(pick_item(
            on_warning,
            position,
            origin,
            message,
            &[condition.clone(), consequent.clone(), alternative.clone()],
        )?),
        ExprCore::List { items, .. } => {
            Some(pick_item(on_warning, position, origin, message, items)?)
        }
        ExprCore::SetEnum { elements } | ExprCore::Tuple { elements } => {
            Some(pick_item(on_warning, position, origin, message, elements)?)
        }
        ExprCore::Product { factors } => {
            Some(pick_item(on_warning, position, origin, message, factors)?)
        }
        ExprCore::Let { body, .. } => {
            check_at_most(on_warning, position, 1, origin, message)?;
            Some(body.clone())
        }
        ExprCore::Quant { bounds, .. }
        | ExprCore::SetOf { bounds, .. }
        | ExprCore::Fcn { bounds, .. } => {
            let domains: Vec<Expr> = bounds
                .iter()
                .filter_map(|bound| match &bound.domain {
                    BoundDomain::Domain(domain) => Some(domain.clone()),
                    _ => None,
                })
                .collect();
            Some(pick_item(on_warning, position, origin, message, &domains)?)
        }
        ExprCore::Choose {
            domain: Some(domain),
            ..
        }
        | ExprCore::SetSt { domain, .. } => Some(pick_item(
            on_warning,
            position,
            origin,
            message,
            std::slice::from_ref(domain),
        )?),
        ExprCore::Arrow { domain, range } => Some(pick_item(
            on_warning,
            position,
            origin,
            message,
            &[domain.clone(), range.clone()],
        )?),
        ExprCore::FcnApp { function, args } => {
            let argument = match args.as_slice() {
                [argument] => argument.clone(),
                _ => tuple(args.clone(), expression),
            };
            Some(pick_item(
                on_warning,
                position,
                origin,
                message,
                &[function.clone(), argument],
            )?)
        }
        ExprCore::Rect { fields } | ExprCore::Record { fields } => {
            let values: Vec<Expr> = fields.iter().map(|field| field.value.clone()).collect();
            Some(pick_item(on_warning, position, origin, message, &values)?)
        }
        ExprCore::Dot {
            expression: inner,
            field,
        } => Some(pick_item(
            on_warning,
            position,
            origin,
            message,
            &[
                inner.clone(),
                at(
                    ExprCore::String {
                        value: field.clone(),
                    },
                    expression,
                ),
            ],
        )?),
        ExprCore::Except { function, specs } => {
            let items: Vec<Expr> = std::iter::once(function.clone())
                .chain(specs.iter().map(|spec| spec.value.clone()))
                .collect();
            Some(pick_item(on_warning, position, origin, message, &items)?)
        }
        ExprCore::Sub {
            action, subscript, ..
        }
        | ExprCore::Tsub {
            action, subscript, ..
        } => Some(pick_item(
            on_warning,
            position,
            origin,
            message,
            &[action.clone(), subscript.clone()],
        )?),
        ExprCore::Fair {
            subscript, action, ..
        } => Some(pick_item(
            on_warning,
            position,
            origin,
            message,
            &[subscript.clone(), action.clone()],
        )?),
        ExprCore::Case { arms, other } => {
            let items: Vec<Expr> = arms
                .iter()
                .map(|arm| tuple(vec![arm.condition.clone(), arm.body.clone()], &arm.body))
                .chain(
                    other
                        .iter()
                        .map(|other| tuple(vec![unresolved(), other.clone()], other)),
                )
                .collect();
            Some(pick_item(on_warning, position, origin, message, &items)?)
        }
        _ => None,
    };
    let Some(result) = picked else {
        let empty_message = "Expression has no subexpressions";
        on_warning(get_error_note(expression.location.as_ref(), empty_message));
        return Err(ObligationError::proof_failure(
            empty_message,
            "Expr.Deref.deref_num",
        ));
    };
    if is_unresolved(&result) {
        let bad_message = format!("Cannot resolve subexpression reference !{position}");
        on_warning(get_error_note(expression.location.as_ref(), &bad_message));
        return Err(ObligationError::proof_failure(
            bad_message,
            "Expr.Deref.deref_num",
        ));
    }
    let definitions = match &expression.core {
        ExprCore::Let { definitions, .. } => definitions.clone(),
        _ => Vec::new(),
    };
    Ok((definitions, result))
}

// Reorders label arguments given in source order to the order of the label's de Bruijn indices.
fn permute(indices: &[usize], args: &[Expr]) -> Result<Vec<Expr>> {
    let to_signed =
        |value: usize| isize::try_from(value).map_err(|_| ObligationError::assert_failure());
    let count = to_signed(indices.len())?;
    let mut current = indices
        .iter()
        .map(|index| to_signed(*index))
        .collect::<Result<Vec<_>>>()?;
    for offset in (0..count).rev() {
        if current.contains(&(count - offset)) {
            continue;
        }
        current = current
            .iter()
            .map(|index| {
                if index + offset < count {
                    *index
                } else {
                    index - 1
                }
            })
            .collect();
    }
    // The TypeScript reads `undefined` past the arguments, which a label's indices never reach.
    current
        .iter()
        .map(|index| {
            usize::try_from(count - index)
                .ok()
                .and_then(|position| args.get(position))
                .cloned()
                .ok_or_else(ObligationError::assert_failure)
        })
        .collect()
}

fn resolve_label(
    on_warning: &mut Warn,
    definition_count: usize,
    expression: &Expr,
    label: &str,
    label_args: &[Expr],
) -> Result<Resolution> {
    let Some(found) = find_label(expression, label, &[]) else {
        on_warning(get_error_note(
            expression.location.as_ref(),
            &format!("Could not find label {label}"),
        ));
        return Ok(Resolution {
            params: Vec::new(),
            definitions: Vec::new(),
            expression: unresolved(),
        });
    };
    let indices = &found.indices;
    if indices.len() != label_args.len() && !label_args.is_empty() {
        let plural = if indices.len() == 1 { "" } else { "s" };
        let message = format!(
            "Expected {} argument{plural} for labelled reference !{label}, but found {}",
            indices.len(),
            label_args.len()
        );
        on_warning(get_error_note(found.expression.location.as_ref(), &message));
        return Err(ObligationError::proof_failure(
            message,
            "Expr.Deref.deref_lsub",
        ));
    }
    let params: Vec<Param> = if label_args.is_empty() {
        indices.iter().map(|index| get_param(&index.name)).collect()
    } else {
        Vec::new()
    };
    let args = if label_args.is_empty() {
        get_indices(indices.len())
    } else {
        label_args.to_vec()
    };
    let mut reified = found.expression.clone();
    for hyp in found.context.iter().rev() {
        reified = match &hyp.core {
            HypCore::Defn { definition, .. } => at(
                ExprCore::Let {
                    definitions: vec![definition.clone()],
                    body: reified.clone(),
                },
                &reified,
            ),
            HypCore::Fresh { name, .. } => at(
                ExprCore::Quant {
                    quantifier: Quantifier::Forall,
                    bounds: vec![Bound {
                        name: name.clone(),
                        level: Level::Constant,
                        domain: BoundDomain::NoDomain,
                    }],
                    body: reified.clone(),
                },
                &reified,
            ),
            _ => substitute_expr(&shift(-1), &reified)?,
        };
    }
    let shifted = substitute_expr(&get_reversal(definition_count, params.len())?, &reified)?;
    let mut definitions = Vec::new();
    let mut body = shifted;
    let index_values: Vec<usize> = indices.iter().map(|index| index.index).collect();
    let mut remaining = permute(&index_values, &args)?;
    while let Some(first) = remaining.first().cloned() {
        let next = match &body.core {
            ExprCore::Let {
                definitions: let_definitions,
                body: inner,
            } if let_definitions.len() == 1 => {
                definitions.push(let_definitions[0].clone());
                remaining = remaining
                    .iter()
                    .map(|arg| substitute_expr(&shift(1), arg))
                    .collect::<Result<_>>()?;
                inner.clone()
            }
            ExprCore::Quant {
                bounds,
                body: inner,
                ..
            } if bounds.len() == 1 => {
                remaining.remove(0);
                substitute_expr(&cons_substitution(first, shift(0)), inner)?
            }
            _ => {
                return Err(ObligationError::bug(
                    "File \"src/expr/e_deref.ml\", line 477, characters 21-33: Assertion failed",
                ));
            }
        };
        body = next;
    }
    Ok(Resolution {
        params,
        definitions,
        expression: body,
    })
}

fn resolve_let_operator(
    on_warning: &mut Warn,
    definition_count: usize,
    expression: &Expr,
    label: &str,
    args: &[Expr],
) -> Result<Resolution> {
    let ExprCore::Let { definitions, .. } = &expression.core else {
        on_warning(get_error_note(
            expression.location.as_ref(),
            "not a LET expression",
        ));
        return Err(ObligationError::proof_failure(
            "not a LET expression",
            "Expr.Deref.deref_letop",
        ));
    };
    let found = definitions
        .iter()
        .enumerate()
        .find_map(|(index, definition)| match &definition.core {
            DefnCore::Operator { name, body } if name == label => Some((index, body)),
            _ => None,
        });
    let Some((index, body)) = found else {
        let message = format!("no definition of operator {label}");
        on_warning(get_error_note(expression.location.as_ref(), &message));
        return Err(ObligationError::proof_failure(
            message,
            "Expr.Deref.deref_letop",
        ));
    };
    let labelled = match &body.core {
        ExprCore::Lambda {
            params,
            body: lambda_body,
        } => body.with_core(ExprCore::Lambda {
            params: params.clone(),
            body: at(
                ExprCore::Parens {
                    expression: lambda_body.clone(),
                    form: ParenForm::Xlabel {
                        label: label.to_owned(),
                        indices: params
                            .iter()
                            .enumerate()
                            .map(|(position, param)| XlabelIndex {
                                name: param.name.clone(),
                                index: params.len() - position,
                            })
                            .collect(),
                    },
                },
                lambda_body,
            ),
        }),
        _ => at(
            ExprCore::Parens {
                expression: body.clone(),
                form: ParenForm::Xlabel {
                    label: label.to_owned(),
                    indices: Vec::new(),
                },
            },
            body,
        ),
    };
    resolve_label(
        on_warning,
        definition_count,
        &at(
            ExprCore::Let {
                definitions: definitions[..index].to_vec(),
                body: labelled,
            },
            body,
        ),
        label,
        args,
    )
}

fn resolve_step(
    on_warning: &mut Warn,
    is_label: bool,
    state: &Resolution,
    selector: &Selector,
    rest: &[Selector],
) -> Result<Step> {
    let expression = if is_label {
        state.expression.clone()
    } else {
        strip_parens(&state.expression)?
    };
    let count = state.definitions.len();
    let step = |resolution: Resolution, rest: &[Selector], is_label: bool| Step {
        resolution,
        rest: rest.to_vec(),
        is_label,
    };
    let bare = |expression: Expr| Resolution {
        params: Vec::new(),
        definitions: Vec::new(),
        expression,
    };
    let numbered = |on_warning: &mut Warn, position: usize, message: &str| -> Result<Step> {
        let (definitions, inner) = get_numbered(
            on_warning,
            &expression,
            position,
            &state.expression,
            message,
        )?;
        Ok(step(
            Resolution {
                params: Vec::new(),
                definitions,
                expression: inner,
            },
            rest,
            false,
        ))
    };
    match selector {
        Selector::Down => {
            if let (ExprCore::Let { .. }, Some(Selector::Label { label, args }), true) =
                (&expression.core, rest.first(), is_label)
            {
                let result = resolve_let_operator(on_warning, count, &expression, label, args)?;
                return Ok(step(result, &rest[1..], true));
            }
            if is_label {
                return Ok(step(bare(expression.clone()), rest, false));
            }
            Err(ObligationError::proof_failure(
                "!: is forbidden for this expression.\n",
                "Expr.Deref.deref: !:",
            ))
        }
        Selector::Number(value) => {
            numbered(on_warning, *value, &format!("Cannot resolve !{value}"))
        }
        Selector::Left => numbered(on_warning, 1, "Cannot resolve !<<"),
        Selector::Right => numbered(on_warning, 2, "Cannot resolve !>>"),
        Selector::Instance(args) => {
            let instance = instantiate(on_warning, &expression, args)?;
            Ok(step(bare(instance), rest, false))
        }
        Selector::Label { label, args } => {
            let result = if matches!(expression.core, ExprCore::Let { .. }) && !is_label {
                resolve_let_operator(on_warning, count, &expression, label, args)?
            } else {
                resolve_label(on_warning, count, &expression, label, args)?
            };
            Ok(step(result, rest, true))
        }
        Selector::At => {
            let (params, inner) = abstract_bound(on_warning, count, &expression)?;
            Ok(step(
                Resolution {
                    params,
                    definitions: Vec::new(),
                    expression: inner,
                },
                rest,
                false,
            ))
        }
    }
}

fn resolve_selectors(
    on_warning: &mut Warn,
    is_label: bool,
    state: Resolution,
    selectors: &[Selector],
) -> Result<Expr> {
    let Some((selector, rest)) = selectors.split_first() else {
        let with_definitions = if state.definitions.is_empty() {
            state.expression
        } else {
            at(
                ExprCore::Let {
                    definitions: state.definitions,
                    body: state.expression.clone(),
                },
                &state.expression,
            )
        };
        let abstracted = if state.params.is_empty() {
            with_definitions
        } else {
            at(
                ExprCore::Lambda {
                    params: state.params,
                    body: with_definitions.clone(),
                },
                &with_definitions,
            )
        };
        let stripped = strip_parens_and_atomic(&abstracted)?;
        return Ok(Rc::new(ExprNode {
            core: stripped.core.clone(),
            location: stripped.location.clone(),
            is_atomic: true,
        }));
    };
    if state.expression.is_atomic {
        on_warning(get_error_note(
            state.expression.location.as_ref(),
            "Expression has no subexpressions",
        ));
        return Ok(unresolved());
    }
    let next = resolve_step(on_warning, is_label, &state, selector, rest)?;
    let shift_amount = isize::try_from(next.resolution.definitions.len())
        .map_err(|_| ObligationError::assert_failure())?;
    let next_selectors = next
        .rest
        .iter()
        .map(|item| map_selector_args(item, &mut |arg| substitute_expr(&shift(shift_amount), arg)))
        .collect::<Result<Vec<_>>>()?;
    let mut params = state.params;
    params.extend(next.resolution.params);
    let mut definitions = state.definitions;
    definitions.extend(next.resolution.definitions);
    resolve_selectors(
        on_warning,
        next.is_label,
        Resolution {
            params,
            definitions,
            expression: next.resolution.expression,
        },
        &next_selectors,
    )
}

fn get_initial_resolution(
    on_warning: &mut Warn,
    operator: &Expr,
    args: &[Expr],
) -> Result<Resolution> {
    if !args.is_empty() {
        return Ok(Resolution {
            params: Vec::new(),
            definitions: Vec::new(),
            expression: instantiate(on_warning, operator, args)?,
        });
    }
    if !matches!(operator.core, ExprCore::Lambda { .. }) {
        return Ok(Resolution {
            params: Vec::new(),
            definitions: Vec::new(),
            expression: operator.clone(),
        });
    }
    let (params, expression) = abstract_bound(on_warning, 0, operator)?;
    Ok(Resolution {
        params,
        definitions: Vec::new(),
        expression,
    })
}

pub fn resolve_subexpression(
    on_warning: &mut Warn,
    operator: &Expr,
    args: &[Expr],
    selectors: &[Selector],
) -> Result<Expr> {
    let initial = get_initial_resolution(on_warning, operator, args)?;
    let result = resolve_selectors(on_warning, true, initial, selectors)?;
    if is_unresolved(&result) {
        let message = "Could not resolve subexpression reference";
        on_warning(get_error_note(operator.location.as_ref(), message));
        return Err(ObligationError::proof_failure(message, "Expr.Anon: 2"));
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    // The expected outputs come from running `subexpression.ts` under Bun on the same inputs.
    use super::*;
    use crate::expression::{
        Builtin, Bullet, CaseArm, ExceptPoint, ExceptSpec, Fairness, Field, Locus, Modal, Sequent,
    };
    use crate::pragma::OldMethod;

    fn node(core: ExprCore, line: u32, is_atomic: bool) -> Expr {
        Rc::new(ExprNode {
            core,
            location: (line > 0).then(|| Locus {
                file: "T.tla".into(),
                start_line: line,
                start_column: 3,
                end_line: line,
                end_column: 9,
            }),
            is_atomic,
        })
    }

    fn param(name: &str) -> Param {
        get_param(name)
    }

    fn bound(name: &str, domain: Option<Expr>) -> Bound {
        Bound {
            name: name.to_owned(),
            level: Level::Constant,
            domain: domain.map_or(BoundDomain::NoDomain, BoundDomain::Domain),
        }
    }

    fn operator(name: &str, body: Expr) -> Defn {
        Defn {
            core: DefnCore::Operator {
                name: name.to_owned(),
                body,
            },
            location: None,
        }
    }

    fn xlabel(label: &str, indices: &[(&str, usize)]) -> ParenForm {
        ParenForm::Xlabel {
            label: label.to_owned(),
            indices: indices
                .iter()
                .map(|(name, index)| XlabelIndex {
                    name: (*name).to_owned(),
                    index: *index,
                })
                .collect(),
        }
    }

    fn fresh(name: &str) -> Hyp {
        get_fresh(name, Level::Constant, 0)
    }

    fn fact(expression: Expr) -> Hyp {
        hyp(HypCore::Fact {
            expression,
            visibility: Visibility::Visible,
            time: crate::expression::Time::Now,
            use_location: None,
        })
    }

    fn get_extra(expression: &Expr) -> String {
        let bound_names = |quantifier: Option<Quantifier>, bounds: &[Bound]| {
            quantifier
                .map(|quantifier| format!("{quantifier:?}"))
                .into_iter()
                .chain(bounds.iter().map(|bound| {
                    let domain = match bound.domain {
                        BoundDomain::Domain(_) => " in",
                        _ => "",
                    };
                    format!("{}{domain}:{:?}", bound.name, bound.level)
                }))
                .collect::<Vec<_>>()
                .join(" ")
        };
        match &expression.core {
            ExprCore::Ix { index } => index.to_string(),
            ExprCore::Opaque { name } => name.clone(),
            ExprCore::Internal { builtin } => builtin.name().to_owned(),
            ExprCore::String { value } => format!("{value:?}"),
            ExprCore::Lambda { params, .. } => params
                .iter()
                .map(|param| format!("{}/{}", param.name, param.shape))
                .collect::<Vec<_>>()
                .join(" "),
            ExprCore::Quant {
                quantifier, bounds, ..
            } => bound_names(Some(*quantifier), bounds),
            ExprCore::Fcn { bounds, .. } | ExprCore::SetOf { bounds, .. } => {
                bound_names(None, bounds)
            }
            ExprCore::Tquant {
                quantifier, names, ..
            } => std::iter::once(format!("{quantifier:?}"))
                .chain(names.iter().cloned())
                .collect::<Vec<_>>()
                .join(" "),
            ExprCore::Choose { name, .. } | ExprCore::SetSt { name, .. } => name.clone(),
            ExprCore::Let { definitions, .. } => definitions
                .iter()
                .map(|definition| definition.name().to_owned())
                .collect::<Vec<_>>()
                .join(" "),
            ExprCore::Parens { form, .. } => match form {
                ParenForm::Syntax => "Syntax".to_owned(),
                ParenForm::Nlabel { .. } => "Nlabel".to_owned(),
                ParenForm::Xlabel { label, indices } => format!(
                    "Xlabel {label} {}",
                    indices
                        .iter()
                        .map(|index| format!("{}:{}", index.name, index.index))
                        .collect::<Vec<_>>()
                        .join(" ")
                ),
            },
            ExprCore::Dot { field, .. } => field.clone(),
            _ => String::new(),
        }
    }

    fn show(expression: &Expr) -> String {
        let debug = format!("{:?}", expression.core);
        let kind = debug.split([' ', '{', '(']).next().unwrap_or_default();
        let extra = get_extra(expression);
        let children: Vec<String> = get_children(expression).iter().map(show).collect();
        format!(
            "{kind}{}{}{}{}",
            if extra.is_empty() {
                String::new()
            } else {
                format!("[{extra}]")
            },
            if children.is_empty() {
                String::new()
            } else {
                format!("({})", children.join(", "))
            },
            expression
                .location
                .as_ref()
                .map_or(String::new(), |locus| format!("@{}", locus.start_line)),
            if expression.is_atomic { "!" } else { "" }
        )
    }

    fn check(operator: Expr, args: Vec<Expr>, selectors: Vec<Selector>, expected: &str) {
        let mut lines = Vec::new();
        let result = resolve_subexpression(
            &mut |warning| {
                lines.push(format!(
                    "warn {}: {}",
                    format!("{:?}", warning.channel).to_lowercase(),
                    warning.text
                ))
            },
            &operator,
            &args,
            &selectors,
        );
        lines.push(match result {
            Ok(expression) => format!("ok: {}", show(&expression)),
            Err(ObligationError::Proof {
                message,
                failure,
                exception,
            }) => format!(
                "err TlaProofError: {} failure={} exception={}",
                crate::errors::quote_json(&message),
                failure.map_or("null".to_owned(), |failure| crate::errors::quote_json(
                    &failure
                )),
                crate::errors::quote_json(&exception)
            ),
            Err(error) => format!("err {}: {}", error.name(), error.message()),
        });
        assert_eq!(lines.join("\n"), expected);
    }

    #[test]
    fn lambda_alone() {
        check(
            node(
                ExprCore::Lambda {
                    params: vec![param("x"), param("y")],
                    body: node(
                        ExprCore::Apply {
                            operator: node(
                                ExprCore::Internal {
                                    builtin: Builtin::Plus,
                                },
                                0,
                                false,
                            ),
                            args: vec![
                                node(ExprCore::Ix { index: 2 }, 0, false),
                                node(ExprCore::Ix { index: 1 }, 0, false),
                            ],
                        },
                        2,
                        false,
                    ),
                },
                1,
                false,
            ),
            vec![],
            vec![],
            "ok: Lambda[x/0 y/0](Apply(Ix[2], Ix[1], Internal[Plus])@2)@2!",
        );
    }

    #[test]
    fn lambda_instantiated() {
        check(
            node(
                ExprCore::Lambda {
                    params: vec![param("x"), param("y")],
                    body: node(
                        ExprCore::Apply {
                            operator: node(
                                ExprCore::Internal {
                                    builtin: Builtin::Plus,
                                },
                                0,
                                false,
                            ),
                            args: vec![
                                node(ExprCore::Ix { index: 2 }, 0, false),
                                node(ExprCore::Ix { index: 1 }, 0, false),
                            ],
                        },
                        2,
                        false,
                    ),
                },
                1,
                false,
            ),
            vec![
                node(
                    ExprCore::Opaque {
                        name: "a".to_owned(),
                    },
                    0,
                    false,
                ),
                node(
                    ExprCore::Opaque {
                        name: "b".to_owned(),
                    },
                    0,
                    false,
                ),
            ],
            vec![],
            "ok: Apply(Opaque[a], Opaque[b], Internal[Plus])@2!",
        );
    }

    #[test]
    fn lambda_too_few_args() {
        check(
            node(
                ExprCore::Lambda {
                    params: vec![param("x"), param("y")],
                    body: node(
                        ExprCore::Apply {
                            operator: node(
                                ExprCore::Internal {
                                    builtin: Builtin::Plus,
                                },
                                0,
                                false,
                            ),
                            args: vec![
                                node(ExprCore::Ix { index: 2 }, 0, false),
                                node(ExprCore::Ix { index: 1 }, 0, false),
                            ],
                        },
                        2,
                        false,
                    ),
                },
                1,
                false,
            ),
            vec![node(
                ExprCore::Opaque {
                    name: "a".to_owned(),
                },
                0,
                false,
            )],
            vec![],
            "warn stderr: File \"T.tla\", line 1, characters 3-8:\nError: Arity mismatch in subexpression instance.\nExpected 2 arguments, but found only 1.\nerr TlaProofError: \"Arity mismatch in subexpression instance.\\nExpected 2 arguments, but found only 1.\" failure=\"Expr.Deref.deref_inst\" exception=\"Failure(\\\"Expr.Deref.deref_inst\\\")\"",
        );
    }

    #[test]
    fn lambda_too_many_args() {
        check(
            node(
                ExprCore::Lambda {
                    params: vec![param("x"), param("y")],
                    body: node(
                        ExprCore::Apply {
                            operator: node(
                                ExprCore::Internal {
                                    builtin: Builtin::Plus,
                                },
                                0,
                                false,
                            ),
                            args: vec![
                                node(ExprCore::Ix { index: 2 }, 0, false),
                                node(ExprCore::Ix { index: 1 }, 0, false),
                            ],
                        },
                        2,
                        false,
                    ),
                },
                1,
                false,
            ),
            vec![
                node(
                    ExprCore::Opaque {
                        name: "a".to_owned(),
                    },
                    0,
                    false,
                ),
                node(
                    ExprCore::Opaque {
                        name: "b".to_owned(),
                    },
                    0,
                    false,
                ),
                node(
                    ExprCore::Opaque {
                        name: "c".to_owned(),
                    },
                    0,
                    false,
                ),
            ],
            vec![],
            "warn stderr: File \"T.tla\", line 1, characters 3-8:\nError: Arity mismatch in subexpression instance.\nExpected 2 arguments, but found 3.\nerr TlaProofError: \"Arity mismatch in subexpression instance.\\nExpected 2 arguments, but found 3.\" failure=\"Expr.Deref.deref_inst\" exception=\"Failure(\\\"Expr.Deref.deref_inst\\\")\"",
        );
    }

    #[test]
    fn lambda_number() {
        check(
            node(
                ExprCore::Lambda {
                    params: vec![param("x"), param("y")],
                    body: node(
                        ExprCore::Apply {
                            operator: node(
                                ExprCore::Internal {
                                    builtin: Builtin::Plus,
                                },
                                0,
                                false,
                            ),
                            args: vec![
                                node(ExprCore::Ix { index: 2 }, 0, false),
                                node(ExprCore::Ix { index: 1 }, 0, false),
                            ],
                        },
                        2,
                        false,
                    ),
                },
                1,
                false,
            ),
            vec![],
            vec![Selector::Number(1)],
            "ok: Lambda[x/0 y/0](Ix[2])!",
        );
    }

    #[test]
    fn lambda_number_two() {
        check(
            node(
                ExprCore::Lambda {
                    params: vec![param("x"), param("y")],
                    body: node(
                        ExprCore::Apply {
                            operator: node(
                                ExprCore::Internal {
                                    builtin: Builtin::Plus,
                                },
                                0,
                                false,
                            ),
                            args: vec![
                                node(ExprCore::Ix { index: 2 }, 0, false),
                                node(ExprCore::Ix { index: 1 }, 0, false),
                            ],
                        },
                        2,
                        false,
                    ),
                },
                1,
                false,
            ),
            vec![],
            vec![Selector::Number(2)],
            "ok: Lambda[x/0 y/0](Ix[1])!",
        );
    }

    #[test]
    fn apply_out_of_range() {
        check(
            node(
                ExprCore::Lambda {
                    params: vec![param("x"), param("y")],
                    body: node(
                        ExprCore::Apply {
                            operator: node(
                                ExprCore::Internal {
                                    builtin: Builtin::Plus,
                                },
                                0,
                                false,
                            ),
                            args: vec![
                                node(ExprCore::Ix { index: 2 }, 0, false),
                                node(ExprCore::Ix { index: 1 }, 0, false),
                            ],
                        },
                        2,
                        false,
                    ),
                },
                1,
                false,
            ),
            vec![],
            vec![Selector::Number(3)],
            "warn stderr: File \"T.tla\", line 2, characters 3-8:\nError: Cannot resolve !3\nerr TlaProofError: \"Cannot resolve !3\" failure=\"Expr.Deref.deref_num\" exception=\"Failure(\\\"Expr.Deref.deref_num\\\")\"",
        );
    }

    #[test]
    fn if_left() {
        check(
            node(
                ExprCore::If {
                    condition: node(
                        ExprCore::Opaque {
                            name: "c".to_owned(),
                        },
                        0,
                        false,
                    ),
                    consequent: node(
                        ExprCore::Opaque {
                            name: "t".to_owned(),
                        },
                        0,
                        false,
                    ),
                    alternative: node(
                        ExprCore::Parens {
                            expression: node(
                                ExprCore::Opaque {
                                    name: "e".to_owned(),
                                },
                                0,
                                false,
                            ),
                            form: ParenForm::Syntax,
                        },
                        0,
                        false,
                    ),
                },
                4,
                false,
            ),
            vec![],
            vec![Selector::Left],
            "ok: Opaque[c]!",
        );
    }

    #[test]
    fn if_right() {
        check(
            node(
                ExprCore::If {
                    condition: node(
                        ExprCore::Opaque {
                            name: "c".to_owned(),
                        },
                        0,
                        false,
                    ),
                    consequent: node(
                        ExprCore::Opaque {
                            name: "t".to_owned(),
                        },
                        0,
                        false,
                    ),
                    alternative: node(
                        ExprCore::Parens {
                            expression: node(
                                ExprCore::Opaque {
                                    name: "e".to_owned(),
                                },
                                0,
                                false,
                            ),
                            form: ParenForm::Syntax,
                        },
                        0,
                        false,
                    ),
                },
                4,
                false,
            ),
            vec![],
            vec![Selector::Right],
            "ok: Opaque[t]!",
        );
    }

    #[test]
    fn if_third_strips_parens() {
        check(
            node(
                ExprCore::If {
                    condition: node(
                        ExprCore::Opaque {
                            name: "c".to_owned(),
                        },
                        0,
                        false,
                    ),
                    consequent: node(
                        ExprCore::Opaque {
                            name: "t".to_owned(),
                        },
                        0,
                        false,
                    ),
                    alternative: node(
                        ExprCore::Parens {
                            expression: node(
                                ExprCore::Opaque {
                                    name: "e".to_owned(),
                                },
                                0,
                                false,
                            ),
                            form: ParenForm::Syntax,
                        },
                        0,
                        false,
                    ),
                },
                4,
                false,
            ),
            vec![],
            vec![Selector::Number(3)],
            "ok: Opaque[e]!",
        );
    }

    #[test]
    fn if_fourth() {
        check(
            node(
                ExprCore::If {
                    condition: node(
                        ExprCore::Opaque {
                            name: "c".to_owned(),
                        },
                        0,
                        false,
                    ),
                    consequent: node(
                        ExprCore::Opaque {
                            name: "t".to_owned(),
                        },
                        0,
                        false,
                    ),
                    alternative: node(
                        ExprCore::Parens {
                            expression: node(
                                ExprCore::Opaque {
                                    name: "e".to_owned(),
                                },
                                0,
                                false,
                            ),
                            form: ParenForm::Syntax,
                        },
                        0,
                        false,
                    ),
                },
                4,
                false,
            ),
            vec![],
            vec![Selector::Number(4)],
            "warn stderr: File \"T.tla\", line 4, characters 3-8:\nError: Cannot resolve !4\nerr TlaProofError: \"Cannot resolve !4\" failure=\"Expr.Deref.deref_num\" exception=\"Failure(\\\"Expr.Deref.deref_num\\\")\"",
        );
    }

    #[test]
    fn number_into_atomic_leaf() {
        check(
            node(
                ExprCore::If {
                    condition: node(
                        ExprCore::Opaque {
                            name: "c".to_owned(),
                        },
                        0,
                        false,
                    ),
                    consequent: node(
                        ExprCore::Opaque {
                            name: "t".to_owned(),
                        },
                        0,
                        false,
                    ),
                    alternative: node(
                        ExprCore::Parens {
                            expression: node(
                                ExprCore::Opaque {
                                    name: "e".to_owned(),
                                },
                                0,
                                false,
                            ),
                            form: ParenForm::Syntax,
                        },
                        0,
                        false,
                    ),
                },
                4,
                false,
            ),
            vec![],
            vec![Selector::Number(1), Selector::Number(1)],
            "warn stderr: <unknown location>:\nError: Expression has no subexpressions\nerr TlaProofError: \"Expression has no subexpressions\" failure=\"Expr.Deref.deref_num\" exception=\"Failure(\\\"Expr.Deref.deref_num\\\")\"",
        );
    }

    #[test]
    fn quant_domain() {
        check(
            node(
                ExprCore::Quant {
                    quantifier: Quantifier::Forall,
                    bounds: vec![
                        bound(
                            "x",
                            Some(node(
                                ExprCore::Opaque {
                                    name: "S".to_owned(),
                                },
                                0,
                                false,
                            )),
                        ),
                        bound("y", None),
                        bound(
                            "z",
                            Some(node(
                                ExprCore::Opaque {
                                    name: "T".to_owned(),
                                },
                                0,
                                false,
                            )),
                        ),
                    ],
                    body: node(
                        ExprCore::Apply {
                            operator: node(
                                ExprCore::Internal {
                                    builtin: Builtin::Eq,
                                },
                                0,
                                false,
                            ),
                            args: vec![
                                node(ExprCore::Ix { index: 3 }, 0, false),
                                node(ExprCore::Ix { index: 1 }, 0, false),
                            ],
                        },
                        0,
                        false,
                    ),
                },
                5,
                false,
            ),
            vec![],
            vec![Selector::Number(2)],
            "ok: Opaque[T]!",
        );
    }

    #[test]
    fn quant_domain_missing() {
        check(
            node(
                ExprCore::Quant {
                    quantifier: Quantifier::Forall,
                    bounds: vec![
                        bound(
                            "x",
                            Some(node(
                                ExprCore::Opaque {
                                    name: "S".to_owned(),
                                },
                                0,
                                false,
                            )),
                        ),
                        bound("y", None),
                        bound(
                            "z",
                            Some(node(
                                ExprCore::Opaque {
                                    name: "T".to_owned(),
                                },
                                0,
                                false,
                            )),
                        ),
                    ],
                    body: node(
                        ExprCore::Apply {
                            operator: node(
                                ExprCore::Internal {
                                    builtin: Builtin::Eq,
                                },
                                0,
                                false,
                            ),
                            args: vec![
                                node(ExprCore::Ix { index: 3 }, 0, false),
                                node(ExprCore::Ix { index: 1 }, 0, false),
                            ],
                        },
                        0,
                        false,
                    ),
                },
                5,
                false,
            ),
            vec![],
            vec![Selector::Number(3)],
            "warn stderr: File \"T.tla\", line 5, characters 3-8:\nError: Cannot resolve !3\nerr TlaProofError: \"Cannot resolve !3\" failure=\"Expr.Deref.deref_num\" exception=\"Failure(\\\"Expr.Deref.deref_num\\\")\"",
        );
    }

    #[test]
    fn quant_at() {
        check(
            node(
                ExprCore::Quant {
                    quantifier: Quantifier::Forall,
                    bounds: vec![
                        bound(
                            "x",
                            Some(node(
                                ExprCore::Opaque {
                                    name: "S".to_owned(),
                                },
                                0,
                                false,
                            )),
                        ),
                        bound("y", None),
                        bound(
                            "z",
                            Some(node(
                                ExprCore::Opaque {
                                    name: "T".to_owned(),
                                },
                                0,
                                false,
                            )),
                        ),
                    ],
                    body: node(
                        ExprCore::Apply {
                            operator: node(
                                ExprCore::Internal {
                                    builtin: Builtin::Eq,
                                },
                                0,
                                false,
                            ),
                            args: vec![
                                node(ExprCore::Ix { index: 3 }, 0, false),
                                node(ExprCore::Ix { index: 1 }, 0, false),
                            ],
                        },
                        0,
                        false,
                    ),
                },
                5,
                false,
            ),
            vec![],
            vec![Selector::At],
            "ok: Lambda[x/0 y/0 z/0](Apply(Ix[3], Ix[1], Internal[Eq]))!",
        );
    }

    #[test]
    fn quant_instance() {
        check(
            node(
                ExprCore::Quant {
                    quantifier: Quantifier::Forall,
                    bounds: vec![
                        bound(
                            "x",
                            Some(node(
                                ExprCore::Opaque {
                                    name: "S".to_owned(),
                                },
                                0,
                                false,
                            )),
                        ),
                        bound("y", None),
                        bound(
                            "z",
                            Some(node(
                                ExprCore::Opaque {
                                    name: "T".to_owned(),
                                },
                                0,
                                false,
                            )),
                        ),
                    ],
                    body: node(
                        ExprCore::Apply {
                            operator: node(
                                ExprCore::Internal {
                                    builtin: Builtin::Eq,
                                },
                                0,
                                false,
                            ),
                            args: vec![
                                node(ExprCore::Ix { index: 3 }, 0, false),
                                node(ExprCore::Ix { index: 1 }, 0, false),
                            ],
                        },
                        0,
                        false,
                    ),
                },
                5,
                false,
            ),
            vec![],
            vec![Selector::Instance(vec![
                node(
                    ExprCore::Opaque {
                        name: "a".to_owned(),
                    },
                    0,
                    false,
                ),
                node(
                    ExprCore::Opaque {
                        name: "b".to_owned(),
                    },
                    0,
                    false,
                ),
                node(
                    ExprCore::Opaque {
                        name: "c".to_owned(),
                    },
                    0,
                    false,
                ),
            ])],
            "ok: Apply(Opaque[a], Opaque[c], Internal[Eq])!",
        );
    }

    #[test]
    fn quant_instance_few() {
        check(
            node(
                ExprCore::Quant {
                    quantifier: Quantifier::Forall,
                    bounds: vec![
                        bound(
                            "x",
                            Some(node(
                                ExprCore::Opaque {
                                    name: "S".to_owned(),
                                },
                                0,
                                false,
                            )),
                        ),
                        bound("y", None),
                        bound(
                            "z",
                            Some(node(
                                ExprCore::Opaque {
                                    name: "T".to_owned(),
                                },
                                0,
                                false,
                            )),
                        ),
                    ],
                    body: node(
                        ExprCore::Apply {
                            operator: node(
                                ExprCore::Internal {
                                    builtin: Builtin::Eq,
                                },
                                0,
                                false,
                            ),
                            args: vec![
                                node(ExprCore::Ix { index: 3 }, 0, false),
                                node(ExprCore::Ix { index: 1 }, 0, false),
                            ],
                        },
                        0,
                        false,
                    ),
                },
                5,
                false,
            ),
            vec![],
            vec![Selector::Instance(vec![node(
                ExprCore::Opaque {
                    name: "a".to_owned(),
                },
                0,
                false,
            )])],
            "warn stderr: File \"T.tla\", line 5, characters 3-8:\nError: Arity mismatch in subexpression instance.\nExpected 3 arguments, but found only 1.\nerr TlaProofError: \"Arity mismatch in subexpression instance.\\nExpected 3 arguments, but found only 1.\" failure=\"Expr.Deref.deref_inst\" exception=\"Failure(\\\"Expr.Deref.deref_inst\\\")\"",
        );
    }

    #[test]
    fn quant_instance_one_many() {
        check(
            node(
                ExprCore::Quant {
                    quantifier: Quantifier::Exists,
                    bounds: vec![bound("x", None)],
                    body: node(
                        ExprCore::Apply {
                            operator: node(
                                ExprCore::Internal {
                                    builtin: Builtin::Eq,
                                },
                                0,
                                false,
                            ),
                            args: vec![
                                node(ExprCore::Ix { index: 1 }, 0, false),
                                node(
                                    ExprCore::Opaque {
                                        name: "k".to_owned(),
                                    },
                                    0,
                                    false,
                                ),
                            ],
                        },
                        0,
                        false,
                    ),
                },
                6,
                false,
            ),
            vec![],
            vec![Selector::Instance(vec![
                node(
                    ExprCore::Opaque {
                        name: "a".to_owned(),
                    },
                    0,
                    false,
                ),
                node(
                    ExprCore::Opaque {
                        name: "b".to_owned(),
                    },
                    0,
                    false,
                ),
            ])],
            "warn stderr: File \"T.tla\", line 6, characters 3-8:\nError: Arity mismatch in subexpression instance.\nExpected 1 argument, but found 2.\nerr TlaProofError: \"Arity mismatch in subexpression instance.\\nExpected 1 argument, but found 2.\" failure=\"Expr.Deref.deref_inst\" exception=\"Failure(\\\"Expr.Deref.deref_inst\\\")\"",
        );
    }

    #[test]
    fn quant_instance_one_none() {
        check(
            node(
                ExprCore::Quant {
                    quantifier: Quantifier::Exists,
                    bounds: vec![bound("x", None)],
                    body: node(
                        ExprCore::Apply {
                            operator: node(
                                ExprCore::Internal {
                                    builtin: Builtin::Eq,
                                },
                                0,
                                false,
                            ),
                            args: vec![
                                node(ExprCore::Ix { index: 1 }, 0, false),
                                node(
                                    ExprCore::Opaque {
                                        name: "k".to_owned(),
                                    },
                                    0,
                                    false,
                                ),
                            ],
                        },
                        0,
                        false,
                    ),
                },
                6,
                false,
            ),
            vec![],
            vec![Selector::Instance(vec![])],
            "warn stderr: File \"T.tla\", line 6, characters 3-8:\nError: Arity mismatch in subexpression instance.\nExpected 1 argument, but found only 0.\nerr TlaProofError: \"Arity mismatch in subexpression instance.\\nExpected 1 argument, but found only 0.\" failure=\"Expr.Deref.deref_inst\" exception=\"Failure(\\\"Expr.Deref.deref_inst\\\")\"",
        );
    }

    #[test]
    fn quant_initial_args() {
        check(
            node(
                ExprCore::Quant {
                    quantifier: Quantifier::Exists,
                    bounds: vec![bound("x", None)],
                    body: node(
                        ExprCore::Apply {
                            operator: node(
                                ExprCore::Internal {
                                    builtin: Builtin::Eq,
                                },
                                0,
                                false,
                            ),
                            args: vec![
                                node(ExprCore::Ix { index: 1 }, 0, false),
                                node(
                                    ExprCore::Opaque {
                                        name: "k".to_owned(),
                                    },
                                    0,
                                    false,
                                ),
                            ],
                        },
                        0,
                        false,
                    ),
                },
                6,
                false,
            ),
            vec![node(
                ExprCore::Opaque {
                    name: "a".to_owned(),
                },
                0,
                false,
            )],
            vec![],
            "ok: Apply(Opaque[a], Opaque[k], Internal[Eq])!",
        );
    }

    #[test]
    fn choose_no_domain() {
        check(
            node(
                ExprCore::Choose {
                    name: "c".to_owned(),
                    domain: None,
                    body: node(
                        ExprCore::Apply {
                            operator: node(
                                ExprCore::Internal {
                                    builtin: Builtin::Eq,
                                },
                                0,
                                false,
                            ),
                            args: vec![
                                node(ExprCore::Ix { index: 1 }, 0, false),
                                node(
                                    ExprCore::Opaque {
                                        name: "v".to_owned(),
                                    },
                                    0,
                                    false,
                                ),
                            ],
                        },
                        0,
                        false,
                    ),
                },
                7,
                false,
            ),
            vec![],
            vec![Selector::Number(1)],
            "warn stderr: File \"T.tla\", line 7, characters 3-8:\nError: Expression has no subexpressions\nerr TlaProofError: \"Expression has no subexpressions\" failure=\"Expr.Deref.deref_num\" exception=\"Failure(\\\"Expr.Deref.deref_num\\\")\"",
        );
    }

    #[test]
    fn choose_at() {
        check(
            node(
                ExprCore::Choose {
                    name: "c".to_owned(),
                    domain: None,
                    body: node(
                        ExprCore::Apply {
                            operator: node(
                                ExprCore::Internal {
                                    builtin: Builtin::Eq,
                                },
                                0,
                                false,
                            ),
                            args: vec![
                                node(ExprCore::Ix { index: 1 }, 0, false),
                                node(
                                    ExprCore::Opaque {
                                        name: "v".to_owned(),
                                    },
                                    0,
                                    false,
                                ),
                            ],
                        },
                        0,
                        false,
                    ),
                },
                7,
                false,
            ),
            vec![],
            vec![Selector::At],
            "ok: Lambda[c/0](Apply(Ix[1], Opaque[v], Internal[Eq]))!",
        );
    }

    #[test]
    fn choose_instance_two() {
        check(
            node(
                ExprCore::Choose {
                    name: "c".to_owned(),
                    domain: None,
                    body: node(
                        ExprCore::Apply {
                            operator: node(
                                ExprCore::Internal {
                                    builtin: Builtin::Eq,
                                },
                                0,
                                false,
                            ),
                            args: vec![
                                node(ExprCore::Ix { index: 1 }, 0, false),
                                node(
                                    ExprCore::Opaque {
                                        name: "v".to_owned(),
                                    },
                                    0,
                                    false,
                                ),
                            ],
                        },
                        0,
                        false,
                    ),
                },
                7,
                false,
            ),
            vec![],
            vec![Selector::Instance(vec![
                node(
                    ExprCore::Opaque {
                        name: "a".to_owned(),
                    },
                    0,
                    false,
                ),
                node(
                    ExprCore::Opaque {
                        name: "b".to_owned(),
                    },
                    0,
                    false,
                ),
            ])],
            "warn stderr: File \"T.tla\", line 7, characters 3-8:\nError: Arity mismatch in subexpression instance.\nExpected 1 argument, but found 2.\nerr TlaProofError: \"Arity mismatch in subexpression instance.\\nExpected 1 argument, but found 2.\" failure=\"Expr.Deref.deref_inst\" exception=\"Failure(\\\"Expr.Deref.deref_inst\\\")\"",
        );
    }

    #[test]
    fn choose_domain() {
        check(
            node(
                ExprCore::Choose {
                    name: "c".to_owned(),
                    domain: Some(node(
                        ExprCore::Opaque {
                            name: "D".to_owned(),
                        },
                        0,
                        false,
                    )),
                    body: node(
                        ExprCore::Apply {
                            operator: node(
                                ExprCore::Internal {
                                    builtin: Builtin::Eq,
                                },
                                0,
                                false,
                            ),
                            args: vec![
                                node(ExprCore::Ix { index: 1 }, 0, false),
                                node(
                                    ExprCore::Opaque {
                                        name: "v".to_owned(),
                                    },
                                    0,
                                    false,
                                ),
                            ],
                        },
                        0,
                        false,
                    ),
                },
                7,
                false,
            ),
            vec![],
            vec![Selector::Number(1)],
            "ok: Opaque[D]!",
        );
    }

    #[test]
    fn setst_instance() {
        check(
            node(
                ExprCore::SetSt {
                    name: "s".to_owned(),
                    domain: node(
                        ExprCore::Opaque {
                            name: "D".to_owned(),
                        },
                        0,
                        false,
                    ),
                    body: node(
                        ExprCore::Apply {
                            operator: node(
                                ExprCore::Internal {
                                    builtin: Builtin::Eq,
                                },
                                0,
                                false,
                            ),
                            args: vec![
                                node(ExprCore::Ix { index: 1 }, 0, false),
                                node(ExprCore::Ix { index: 2 }, 0, false),
                            ],
                        },
                        0,
                        false,
                    ),
                },
                8,
                false,
            ),
            vec![],
            vec![Selector::Instance(vec![node(
                ExprCore::Opaque {
                    name: "a".to_owned(),
                },
                0,
                false,
            )])],
            "ok: Apply(Opaque[a], Ix[1], Internal[Eq])!",
        );
    }

    #[test]
    fn setst_number() {
        check(
            node(
                ExprCore::SetSt {
                    name: "s".to_owned(),
                    domain: node(
                        ExprCore::Opaque {
                            name: "D".to_owned(),
                        },
                        0,
                        false,
                    ),
                    body: node(
                        ExprCore::Apply {
                            operator: node(
                                ExprCore::Internal {
                                    builtin: Builtin::Eq,
                                },
                                0,
                                false,
                            ),
                            args: vec![
                                node(ExprCore::Ix { index: 1 }, 0, false),
                                node(ExprCore::Ix { index: 2 }, 0, false),
                            ],
                        },
                        0,
                        false,
                    ),
                },
                8,
                false,
            ),
            vec![],
            vec![Selector::Number(1)],
            "ok: Opaque[D]!",
        );
    }

    #[test]
    fn tquant_at() {
        check(
            node(
                ExprCore::Tquant {
                    quantifier: Quantifier::Exists,
                    names: vec!["u".to_owned(), "w".to_owned()],
                    body: node(
                        ExprCore::Apply {
                            operator: node(
                                ExprCore::Internal {
                                    builtin: Builtin::Eq,
                                },
                                0,
                                false,
                            ),
                            args: vec![
                                node(ExprCore::Ix { index: 1 }, 0, false),
                                node(ExprCore::Ix { index: 2 }, 0, false),
                            ],
                        },
                        0,
                        false,
                    ),
                },
                9,
                false,
            ),
            vec![],
            vec![Selector::At],
            "ok: Lambda[u/0 w/0](Apply(Ix[1], Ix[2], Internal[Eq]))!",
        );
    }

    #[test]
    fn tquant_instance() {
        check(
            node(
                ExprCore::Tquant {
                    quantifier: Quantifier::Exists,
                    names: vec!["u".to_owned(), "w".to_owned()],
                    body: node(
                        ExprCore::Apply {
                            operator: node(
                                ExprCore::Internal {
                                    builtin: Builtin::Eq,
                                },
                                0,
                                false,
                            ),
                            args: vec![
                                node(ExprCore::Ix { index: 1 }, 0, false),
                                node(ExprCore::Ix { index: 2 }, 0, false),
                            ],
                        },
                        0,
                        false,
                    ),
                },
                9,
                false,
            ),
            vec![],
            vec![Selector::Instance(vec![
                node(
                    ExprCore::Opaque {
                        name: "a".to_owned(),
                    },
                    0,
                    false,
                ),
                node(
                    ExprCore::Opaque {
                        name: "b".to_owned(),
                    },
                    0,
                    false,
                ),
            ])],
            "ok: Apply(Opaque[b], Opaque[a], Internal[Eq])!",
        );
    }

    #[test]
    fn tquant_number() {
        check(
            node(
                ExprCore::Tquant {
                    quantifier: Quantifier::Exists,
                    names: vec!["u".to_owned(), "w".to_owned()],
                    body: node(
                        ExprCore::Apply {
                            operator: node(
                                ExprCore::Internal {
                                    builtin: Builtin::Eq,
                                },
                                0,
                                false,
                            ),
                            args: vec![
                                node(ExprCore::Ix { index: 1 }, 0, false),
                                node(ExprCore::Ix { index: 2 }, 0, false),
                            ],
                        },
                        0,
                        false,
                    ),
                },
                9,
                false,
            ),
            vec![],
            vec![Selector::Number(1)],
            "warn stderr: File \"T.tla\", line 9, characters 3-8:\nError: Expression has no subexpressions\nerr TlaProofError: \"Expression has no subexpressions\" failure=\"Expr.Deref.deref_num\" exception=\"Failure(\\\"Expr.Deref.deref_num\\\")\"",
        );
    }

    #[test]
    fn apply_instance() {
        check(
            node(
                ExprCore::Lambda {
                    params: vec![param("x"), param("y")],
                    body: node(
                        ExprCore::Apply {
                            operator: node(
                                ExprCore::Internal {
                                    builtin: Builtin::Plus,
                                },
                                0,
                                false,
                            ),
                            args: vec![
                                node(ExprCore::Ix { index: 2 }, 0, false),
                                node(ExprCore::Ix { index: 1 }, 0, false),
                            ],
                        },
                        2,
                        false,
                    ),
                },
                1,
                false,
            ),
            vec![],
            vec![
                Selector::Number(1),
                Selector::Instance(vec![node(
                    ExprCore::Opaque {
                        name: "a".to_owned(),
                    },
                    0,
                    false,
                )]),
            ],
            "warn stderr: <unknown location>:\nError: Cannot instantiate non-binding expression\nerr TlaProofError: \"Cannot instantiate non-binding expression\" failure=\"Expr.Deref.deref_inst\" exception=\"Failure(\\\"Expr.Deref.deref_inst\\\")\"",
        );
    }

    #[test]
    fn apply_at() {
        check(
            node(
                ExprCore::Apply {
                    operator: node(
                        ExprCore::Opaque {
                            name: "F".to_owned(),
                        },
                        0,
                        false,
                    ),
                    args: vec![node(
                        ExprCore::Opaque {
                            name: "a".to_owned(),
                        },
                        0,
                        false,
                    )],
                },
                10,
                false,
            ),
            vec![],
            vec![Selector::At],
            "warn stderr: File \"T.tla\", line 10, characters 3-8:\nError: Cannot abstract over bound variables in a non-binding expression\nerr TlaProofError: \"Cannot abstract over bound variables in a non-binding expression\" failure=\"Expr.Deref.deref_at\" exception=\"Failure(\\\"Expr.Deref.deref_at\\\")\"",
        );
    }

    #[test]
    fn leaf_number() {
        check(
            node(
                ExprCore::Opaque {
                    name: "lone".to_owned(),
                },
                11,
                false,
            ),
            vec![],
            vec![Selector::Number(1)],
            "warn stderr: File \"T.tla\", line 11, characters 3-8:\nError: Expression has no subexpressions\nerr TlaProofError: \"Expression has no subexpressions\" failure=\"Expr.Deref.deref_num\" exception=\"Failure(\\\"Expr.Deref.deref_num\\\")\"",
        );
    }

    #[test]
    fn setof() {
        check(
            node(
                ExprCore::SetOf {
                    element: node(
                        ExprCore::Apply {
                            operator: node(
                                ExprCore::Internal {
                                    builtin: Builtin::Plus,
                                },
                                0,
                                false,
                            ),
                            args: vec![
                                node(ExprCore::Ix { index: 1 }, 0, false),
                                node(
                                    ExprCore::Opaque {
                                        name: "q".to_owned(),
                                    },
                                    0,
                                    false,
                                ),
                            ],
                        },
                        0,
                        false,
                    ),
                    bounds: vec![bound(
                        "x",
                        Some(node(
                            ExprCore::Opaque {
                                name: "S".to_owned(),
                            },
                            0,
                            false,
                        )),
                    )],
                },
                12,
                false,
            ),
            vec![],
            vec![Selector::Number(1)],
            "ok: Opaque[S]!",
        );
    }

    #[test]
    fn setof_instance() {
        check(
            node(
                ExprCore::SetOf {
                    element: node(
                        ExprCore::Apply {
                            operator: node(
                                ExprCore::Internal {
                                    builtin: Builtin::Plus,
                                },
                                0,
                                false,
                            ),
                            args: vec![
                                node(ExprCore::Ix { index: 1 }, 0, false),
                                node(
                                    ExprCore::Opaque {
                                        name: "q".to_owned(),
                                    },
                                    0,
                                    false,
                                ),
                            ],
                        },
                        0,
                        false,
                    ),
                    bounds: vec![bound(
                        "x",
                        Some(node(
                            ExprCore::Opaque {
                                name: "S".to_owned(),
                            },
                            0,
                            false,
                        )),
                    )],
                },
                12,
                false,
            ),
            vec![],
            vec![Selector::Instance(vec![node(
                ExprCore::Opaque {
                    name: "a".to_owned(),
                },
                0,
                false,
            )])],
            "ok: Apply(Opaque[a], Opaque[q], Internal[Plus])!",
        );
    }

    #[test]
    fn fcn_at() {
        check(
            node(
                ExprCore::Fcn {
                    bounds: vec![bound(
                        "x",
                        Some(node(
                            ExprCore::Opaque {
                                name: "S".to_owned(),
                            },
                            0,
                            false,
                        )),
                    )],
                    body: node(
                        ExprCore::Apply {
                            operator: node(
                                ExprCore::Opaque {
                                    name: "g".to_owned(),
                                },
                                0,
                                false,
                            ),
                            args: vec![node(ExprCore::Ix { index: 1 }, 0, false)],
                        },
                        0,
                        false,
                    ),
                },
                13,
                false,
            ),
            vec![],
            vec![Selector::At],
            "ok: Lambda[x/0](Apply(Ix[1], Opaque[g]))!",
        );
    }

    #[test]
    fn fcnapp_one() {
        check(
            node(
                ExprCore::FcnApp {
                    function: node(
                        ExprCore::Opaque {
                            name: "f".to_owned(),
                        },
                        0,
                        false,
                    ),
                    args: vec![node(
                        ExprCore::Opaque {
                            name: "a".to_owned(),
                        },
                        0,
                        false,
                    )],
                },
                0,
                false,
            ),
            vec![],
            vec![Selector::Number(2)],
            "ok: Opaque[a]!",
        );
    }

    #[test]
    fn fcnapp_two() {
        check(
            node(
                ExprCore::FcnApp {
                    function: node(
                        ExprCore::Opaque {
                            name: "f".to_owned(),
                        },
                        0,
                        false,
                    ),
                    args: vec![
                        node(
                            ExprCore::Opaque {
                                name: "a".to_owned(),
                            },
                            0,
                            false,
                        ),
                        node(
                            ExprCore::Opaque {
                                name: "b".to_owned(),
                            },
                            0,
                            false,
                        ),
                    ],
                },
                14,
                false,
            ),
            vec![],
            vec![Selector::Number(2)],
            "ok: Tuple(Opaque[a], Opaque[b])@14!",
        );
    }

    #[test]
    fn fcnapp_function() {
        check(
            node(
                ExprCore::FcnApp {
                    function: node(
                        ExprCore::Opaque {
                            name: "f".to_owned(),
                        },
                        0,
                        false,
                    ),
                    args: vec![node(
                        ExprCore::Opaque {
                            name: "a".to_owned(),
                        },
                        0,
                        false,
                    )],
                },
                0,
                false,
            ),
            vec![],
            vec![Selector::Left],
            "ok: Opaque[f]!",
        );
    }

    #[test]
    fn arrow() {
        check(
            node(
                ExprCore::Arrow {
                    domain: node(
                        ExprCore::Opaque {
                            name: "A".to_owned(),
                        },
                        0,
                        false,
                    ),
                    range: node(
                        ExprCore::Opaque {
                            name: "B".to_owned(),
                        },
                        0,
                        false,
                    ),
                },
                0,
                false,
            ),
            vec![],
            vec![Selector::Right],
            "ok: Opaque[B]!",
        );
    }

    #[test]
    fn rect() {
        check(
            node(
                ExprCore::Rect {
                    fields: vec![
                        Field {
                            name: "a".to_owned(),
                            value: node(
                                ExprCore::Opaque {
                                    name: "A".to_owned(),
                                },
                                0,
                                false,
                            ),
                        },
                        Field {
                            name: "b".to_owned(),
                            value: node(
                                ExprCore::Opaque {
                                    name: "B".to_owned(),
                                },
                                0,
                                false,
                            ),
                        },
                    ],
                },
                0,
                false,
            ),
            vec![],
            vec![Selector::Number(2)],
            "ok: Opaque[B]!",
        );
    }

    #[test]
    fn record() {
        check(
            node(
                ExprCore::Record {
                    fields: vec![Field {
                        name: "a".to_owned(),
                        value: node(
                            ExprCore::Opaque {
                                name: "A".to_owned(),
                            },
                            0,
                            false,
                        ),
                    }],
                },
                0,
                false,
            ),
            vec![],
            vec![Selector::Number(1)],
            "ok: Opaque[A]!",
        );
    }

    #[test]
    fn dot() {
        check(
            node(
                ExprCore::Dot {
                    expression: node(
                        ExprCore::Opaque {
                            name: "r".to_owned(),
                        },
                        0,
                        false,
                    ),
                    field: "fld".to_owned(),
                },
                15,
                false,
            ),
            vec![],
            vec![Selector::Number(2)],
            "ok: String[\"fld\"]@15!",
        );
    }

    #[test]
    fn except() {
        check(
            node(
                ExprCore::Except {
                    function: node(
                        ExprCore::Opaque {
                            name: "f".to_owned(),
                        },
                        0,
                        false,
                    ),
                    specs: vec![ExceptSpec {
                        trail: vec![ExceptPoint::Dot("a".to_owned())],
                        value: node(
                            ExprCore::Opaque {
                                name: "V".to_owned(),
                            },
                            0,
                            false,
                        ),
                    }],
                },
                0,
                false,
            ),
            vec![],
            vec![Selector::Number(2)],
            "ok: Opaque[V]!",
        );
    }

    #[test]
    fn sub() {
        check(
            node(
                ExprCore::Sub {
                    modal: Modal::Box,
                    action: node(
                        ExprCore::Opaque {
                            name: "A".to_owned(),
                        },
                        0,
                        false,
                    ),
                    subscript: node(
                        ExprCore::Opaque {
                            name: "v".to_owned(),
                        },
                        0,
                        false,
                    ),
                },
                0,
                false,
            ),
            vec![],
            vec![Selector::Number(2)],
            "ok: Opaque[v]!",
        );
    }

    #[test]
    fn tsub() {
        check(
            node(
                ExprCore::Tsub {
                    modal: Modal::Dia,
                    action: node(
                        ExprCore::Opaque {
                            name: "A".to_owned(),
                        },
                        0,
                        false,
                    ),
                    subscript: node(
                        ExprCore::Opaque {
                            name: "v".to_owned(),
                        },
                        0,
                        false,
                    ),
                },
                0,
                false,
            ),
            vec![],
            vec![Selector::Number(1)],
            "ok: Opaque[A]!",
        );
    }

    #[test]
    fn fair() {
        check(
            node(
                ExprCore::Fair {
                    fairness: Fairness::Weak,
                    subscript: node(
                        ExprCore::Opaque {
                            name: "v".to_owned(),
                        },
                        0,
                        false,
                    ),
                    action: node(
                        ExprCore::Opaque {
                            name: "A".to_owned(),
                        },
                        0,
                        false,
                    ),
                },
                0,
                false,
            ),
            vec![],
            vec![Selector::Number(1)],
            "ok: Opaque[v]!",
        );
    }

    #[test]
    fn case_arm() {
        check(
            node(
                ExprCore::Case {
                    arms: vec![CaseArm {
                        condition: node(
                            ExprCore::Opaque {
                                name: "p".to_owned(),
                            },
                            0,
                            false,
                        ),
                        body: node(
                            ExprCore::Opaque {
                                name: "x".to_owned(),
                            },
                            17,
                            false,
                        ),
                    }],
                    other: Some(node(
                        ExprCore::Opaque {
                            name: "y".to_owned(),
                        },
                        18,
                        false,
                    )),
                },
                16,
                false,
            ),
            vec![],
            vec![Selector::Number(1)],
            "ok: Tuple(Opaque[p], Opaque[x]@17)@17!",
        );
    }

    #[test]
    fn case_arm_part() {
        check(
            node(
                ExprCore::Case {
                    arms: vec![CaseArm {
                        condition: node(
                            ExprCore::Opaque {
                                name: "p".to_owned(),
                            },
                            0,
                            false,
                        ),
                        body: node(
                            ExprCore::Opaque {
                                name: "x".to_owned(),
                            },
                            17,
                            false,
                        ),
                    }],
                    other: Some(node(
                        ExprCore::Opaque {
                            name: "y".to_owned(),
                        },
                        18,
                        false,
                    )),
                },
                16,
                false,
            ),
            vec![],
            vec![Selector::Number(1), Selector::Number(2)],
            "ok: Opaque[x]@17!",
        );
    }

    #[test]
    fn case_other() {
        check(
            node(
                ExprCore::Case {
                    arms: vec![CaseArm {
                        condition: node(
                            ExprCore::Opaque {
                                name: "p".to_owned(),
                            },
                            0,
                            false,
                        ),
                        body: node(
                            ExprCore::Opaque {
                                name: "x".to_owned(),
                            },
                            17,
                            false,
                        ),
                    }],
                    other: Some(node(
                        ExprCore::Opaque {
                            name: "y".to_owned(),
                        },
                        18,
                        false,
                    )),
                },
                16,
                false,
            ),
            vec![],
            vec![Selector::Number(2)],
            "ok: Tuple(Opaque[$Bad], Opaque[y]@18)@18!",
        );
    }

    #[test]
    fn case_other_unresolved() {
        check(
            node(
                ExprCore::Case {
                    arms: vec![CaseArm {
                        condition: node(
                            ExprCore::Opaque {
                                name: "p".to_owned(),
                            },
                            0,
                            false,
                        ),
                        body: node(
                            ExprCore::Opaque {
                                name: "x".to_owned(),
                            },
                            17,
                            false,
                        ),
                    }],
                    other: Some(node(
                        ExprCore::Opaque {
                            name: "y".to_owned(),
                        },
                        18,
                        false,
                    )),
                },
                16,
                false,
            ),
            vec![],
            vec![Selector::Number(2), Selector::Number(1)],
            "warn stderr: File \"T.tla\", line 18, characters 3-8:\nError: Cannot resolve subexpression reference !1\nerr TlaProofError: \"Cannot resolve subexpression reference !1\" failure=\"Expr.Deref.deref_num\" exception=\"Failure(\\\"Expr.Deref.deref_num\\\")\"",
        );
    }

    #[test]
    fn case_beyond() {
        check(
            node(
                ExprCore::Case {
                    arms: vec![CaseArm {
                        condition: node(
                            ExprCore::Opaque {
                                name: "p".to_owned(),
                            },
                            0,
                            false,
                        ),
                        body: node(
                            ExprCore::Opaque {
                                name: "x".to_owned(),
                            },
                            17,
                            false,
                        ),
                    }],
                    other: Some(node(
                        ExprCore::Opaque {
                            name: "y".to_owned(),
                        },
                        18,
                        false,
                    )),
                },
                16,
                false,
            ),
            vec![],
            vec![Selector::Number(3)],
            "warn stderr: File \"T.tla\", line 16, characters 3-8:\nError: Cannot resolve !3\nerr TlaProofError: \"Cannot resolve !3\" failure=\"Expr.Deref.deref_num\" exception=\"Failure(\\\"Expr.Deref.deref_num\\\")\"",
        );
    }

    #[test]
    fn set_enum() {
        check(
            node(
                ExprCore::SetEnum {
                    elements: vec![
                        node(
                            ExprCore::Opaque {
                                name: "a".to_owned(),
                            },
                            0,
                            false,
                        ),
                        node(
                            ExprCore::Opaque {
                                name: "b".to_owned(),
                            },
                            0,
                            false,
                        ),
                    ],
                },
                0,
                false,
            ),
            vec![],
            vec![Selector::Number(2)],
            "ok: Opaque[b]!",
        );
    }

    #[test]
    fn tuple() {
        check(
            node(
                ExprCore::Tuple {
                    elements: vec![
                        node(
                            ExprCore::Opaque {
                                name: "a".to_owned(),
                            },
                            0,
                            false,
                        ),
                        node(
                            ExprCore::Opaque {
                                name: "b".to_owned(),
                            },
                            0,
                            false,
                        ),
                    ],
                },
                0,
                false,
            ),
            vec![],
            vec![Selector::Left],
            "ok: Opaque[a]!",
        );
    }

    #[test]
    fn product() {
        check(
            node(
                ExprCore::Product {
                    factors: vec![
                        node(
                            ExprCore::Opaque {
                                name: "A".to_owned(),
                            },
                            0,
                            false,
                        ),
                        node(
                            ExprCore::Opaque {
                                name: "B".to_owned(),
                            },
                            0,
                            false,
                        ),
                    ],
                },
                0,
                false,
            ),
            vec![],
            vec![Selector::Right],
            "ok: Opaque[B]!",
        );
    }

    #[test]
    fn list() {
        check(
            node(
                ExprCore::List {
                    bullet: Bullet::And,
                    items: vec![
                        node(
                            ExprCore::Opaque {
                                name: "a".to_owned(),
                            },
                            0,
                            false,
                        ),
                        node(
                            ExprCore::Opaque {
                                name: "b".to_owned(),
                            },
                            0,
                            false,
                        ),
                        node(
                            ExprCore::Opaque {
                                name: "c".to_owned(),
                            },
                            0,
                            false,
                        ),
                    ],
                },
                0,
                false,
            ),
            vec![],
            vec![Selector::Number(3)],
            "ok: Opaque[c]!",
        );
    }

    #[test]
    fn with() {
        check(
            node(
                ExprCore::With {
                    expression: node(
                        ExprCore::Tuple {
                            elements: vec![
                                node(
                                    ExprCore::Opaque {
                                        name: "a".to_owned(),
                                    },
                                    0,
                                    false,
                                ),
                                node(
                                    ExprCore::Opaque {
                                        name: "b".to_owned(),
                                    },
                                    0,
                                    false,
                                ),
                            ],
                        },
                        0,
                        false,
                    ),
                    method: OldMethod {
                        name: "zenon".to_owned(),
                        tactic: None,
                        timeout: None,
                    },
                },
                0,
                false,
            ),
            vec![],
            vec![Selector::Number(2)],
            "ok: Opaque[b]!",
        );
    }

    #[test]
    fn bad_item() {
        check(
            node(
                ExprCore::Apply {
                    operator: node(
                        ExprCore::Opaque {
                            name: "F".to_owned(),
                        },
                        0,
                        false,
                    ),
                    args: vec![node(
                        ExprCore::Opaque {
                            name: "$Bad".to_owned(),
                        },
                        0,
                        false,
                    )],
                },
                19,
                false,
            ),
            vec![],
            vec![Selector::Number(1)],
            "warn stderr: File \"T.tla\", line 19, characters 3-8:\nError: Cannot resolve subexpression reference !1\nerr TlaProofError: \"Cannot resolve subexpression reference !1\" failure=\"Expr.Deref.deref_num\" exception=\"Failure(\\\"Expr.Deref.deref_num\\\")\"",
        );
    }

    #[test]
    fn atomic() {
        check(
            node(
                ExprCore::Opaque {
                    name: "done".to_owned(),
                },
                20,
                true,
            ),
            vec![],
            vec![Selector::Number(1)],
            "warn stderr: File \"T.tla\", line 20, characters 3-8:\nError: Expression has no subexpressions\nwarn stderr: File \"T.tla\", line 20, characters 3-8:\nError: Could not resolve subexpression reference\nerr TlaProofError: \"Could not resolve subexpression reference\" failure=\"Expr.Anon: 2\" exception=\"Failure(\\\"Expr.Anon: 2\\\")\"",
        );
    }

    #[test]
    fn atomic_alone() {
        check(
            node(
                ExprCore::Tuple {
                    elements: vec![node(
                        ExprCore::Opaque {
                            name: "a".to_owned(),
                        },
                        0,
                        false,
                    )],
                },
                0,
                true,
            ),
            vec![],
            vec![],
            "ok: Tuple(Opaque[a])!",
        );
    }

    #[test]
    fn let_body() {
        check(
            node(
                ExprCore::Let {
                    definitions: vec![
                        operator(
                            "F",
                            node(
                                ExprCore::Lambda {
                                    params: vec![param("p")],
                                    body: node(
                                        ExprCore::Apply {
                                            operator: node(
                                                ExprCore::Internal {
                                                    builtin: Builtin::Plus,
                                                },
                                                0,
                                                false,
                                            ),
                                            args: vec![
                                                node(ExprCore::Ix { index: 1 }, 0, false),
                                                node(
                                                    ExprCore::Opaque {
                                                        name: "one".to_owned(),
                                                    },
                                                    0,
                                                    false,
                                                ),
                                            ],
                                        },
                                        0,
                                        false,
                                    ),
                                },
                                0,
                                false,
                            ),
                        ),
                        operator(
                            "G",
                            node(
                                ExprCore::Opaque {
                                    name: "g".to_owned(),
                                },
                                0,
                                false,
                            ),
                        ),
                    ],
                    body: node(
                        ExprCore::Apply {
                            operator: node(ExprCore::Ix { index: 2 }, 0, false),
                            args: vec![node(
                                ExprCore::Opaque {
                                    name: "two".to_owned(),
                                },
                                0,
                                false,
                            )],
                        },
                        22,
                        false,
                    ),
                },
                21,
                false,
            ),
            vec![],
            vec![Selector::Number(1)],
            "ok: Let[F G](Lambda[p/0](Apply(Ix[1], Opaque[one], Internal[Plus])), Opaque[g], Apply(Opaque[two], Ix[2])@22)@22!",
        );
    }

    #[test]
    fn let_two() {
        check(
            node(
                ExprCore::Let {
                    definitions: vec![
                        operator(
                            "F",
                            node(
                                ExprCore::Lambda {
                                    params: vec![param("p")],
                                    body: node(
                                        ExprCore::Apply {
                                            operator: node(
                                                ExprCore::Internal {
                                                    builtin: Builtin::Plus,
                                                },
                                                0,
                                                false,
                                            ),
                                            args: vec![
                                                node(ExprCore::Ix { index: 1 }, 0, false),
                                                node(
                                                    ExprCore::Opaque {
                                                        name: "one".to_owned(),
                                                    },
                                                    0,
                                                    false,
                                                ),
                                            ],
                                        },
                                        0,
                                        false,
                                    ),
                                },
                                0,
                                false,
                            ),
                        ),
                        operator(
                            "G",
                            node(
                                ExprCore::Opaque {
                                    name: "g".to_owned(),
                                },
                                0,
                                false,
                            ),
                        ),
                    ],
                    body: node(
                        ExprCore::Apply {
                            operator: node(ExprCore::Ix { index: 2 }, 0, false),
                            args: vec![node(
                                ExprCore::Opaque {
                                    name: "two".to_owned(),
                                },
                                0,
                                false,
                            )],
                        },
                        22,
                        false,
                    ),
                },
                21,
                false,
            ),
            vec![],
            vec![Selector::Number(2)],
            "warn stderr: File \"T.tla\", line 21, characters 3-8:\nError: Cannot resolve !2\nerr TlaProofError: \"Cannot resolve !2\" failure=\"Expr.Deref.deref_num\" exception=\"Failure(\\\"Expr.Deref.deref_num\\\")\"",
        );
    }

    #[test]
    fn let_body_args() {
        check(
            node(
                ExprCore::Let {
                    definitions: vec![
                        operator(
                            "F",
                            node(
                                ExprCore::Lambda {
                                    params: vec![param("p")],
                                    body: node(
                                        ExprCore::Apply {
                                            operator: node(
                                                ExprCore::Internal {
                                                    builtin: Builtin::Plus,
                                                },
                                                0,
                                                false,
                                            ),
                                            args: vec![
                                                node(ExprCore::Ix { index: 1 }, 0, false),
                                                node(
                                                    ExprCore::Opaque {
                                                        name: "one".to_owned(),
                                                    },
                                                    0,
                                                    false,
                                                ),
                                            ],
                                        },
                                        0,
                                        false,
                                    ),
                                },
                                0,
                                false,
                            ),
                        ),
                        operator(
                            "G",
                            node(
                                ExprCore::Opaque {
                                    name: "g".to_owned(),
                                },
                                0,
                                false,
                            ),
                        ),
                    ],
                    body: node(
                        ExprCore::Apply {
                            operator: node(ExprCore::Ix { index: 2 }, 0, false),
                            args: vec![node(
                                ExprCore::Opaque {
                                    name: "two".to_owned(),
                                },
                                0,
                                false,
                            )],
                        },
                        22,
                        false,
                    ),
                },
                21,
                false,
            ),
            vec![],
            vec![Selector::Number(1), Selector::Number(1)],
            "ok: Let[F G](Lambda[p/0](Apply(Ix[1], Opaque[one], Internal[Plus])), Opaque[g], Opaque[two])!",
        );
    }

    #[test]
    fn let_then_instance() {
        check(
            node(
                ExprCore::Let {
                    definitions: vec![operator(
                        "F",
                        node(
                            ExprCore::Opaque {
                                name: "f".to_owned(),
                            },
                            0,
                            false,
                        ),
                    )],
                    body: node(
                        ExprCore::Quant {
                            quantifier: Quantifier::Forall,
                            bounds: vec![bound("x", None)],
                            body: node(
                                ExprCore::Apply {
                                    operator: node(
                                        ExprCore::Internal {
                                            builtin: Builtin::Eq,
                                        },
                                        0,
                                        false,
                                    ),
                                    args: vec![
                                        node(ExprCore::Ix { index: 1 }, 0, false),
                                        node(ExprCore::Ix { index: 2 }, 0, false),
                                    ],
                                },
                                0,
                                false,
                            ),
                        },
                        0,
                        false,
                    ),
                },
                23,
                false,
            ),
            vec![],
            vec![
                Selector::Number(1),
                Selector::Instance(vec![node(ExprCore::Ix { index: 1 }, 0, false)]),
            ],
            "ok: Let[F](Opaque[f], Apply(Ix[2], Ix[1], Internal[Eq]))!",
        );
    }

    #[test]
    fn let_operator_label() {
        check(
            node(
                ExprCore::Let {
                    definitions: vec![
                        operator(
                            "F",
                            node(
                                ExprCore::Lambda {
                                    params: vec![param("p")],
                                    body: node(
                                        ExprCore::Apply {
                                            operator: node(
                                                ExprCore::Internal {
                                                    builtin: Builtin::Plus,
                                                },
                                                0,
                                                false,
                                            ),
                                            args: vec![
                                                node(ExprCore::Ix { index: 1 }, 0, false),
                                                node(
                                                    ExprCore::Opaque {
                                                        name: "one".to_owned(),
                                                    },
                                                    0,
                                                    false,
                                                ),
                                            ],
                                        },
                                        0,
                                        false,
                                    ),
                                },
                                0,
                                false,
                            ),
                        ),
                        operator(
                            "G",
                            node(
                                ExprCore::Opaque {
                                    name: "g".to_owned(),
                                },
                                0,
                                false,
                            ),
                        ),
                    ],
                    body: node(
                        ExprCore::Apply {
                            operator: node(ExprCore::Ix { index: 2 }, 0, false),
                            args: vec![node(
                                ExprCore::Opaque {
                                    name: "two".to_owned(),
                                },
                                0,
                                false,
                            )],
                        },
                        22,
                        false,
                    ),
                },
                21,
                false,
            ),
            vec![],
            vec![Selector::Label {
                label: "F".to_owned(),
                args: vec![],
            }],
            "warn stderr: File \"T.tla\", line 21, characters 3-8:\nError: Could not find label F\nwarn stderr: File \"T.tla\", line 21, characters 3-8:\nError: Could not resolve subexpression reference\nerr TlaProofError: \"Could not resolve subexpression reference\" failure=\"Expr.Anon: 2\" exception=\"Failure(\\\"Expr.Anon: 2\\\")\"",
        );
    }

    #[test]
    fn let_operator_label_args() {
        check(
            node(
                ExprCore::Let {
                    definitions: vec![
                        operator(
                            "F",
                            node(
                                ExprCore::Lambda {
                                    params: vec![param("p")],
                                    body: node(
                                        ExprCore::Apply {
                                            operator: node(
                                                ExprCore::Internal {
                                                    builtin: Builtin::Plus,
                                                },
                                                0,
                                                false,
                                            ),
                                            args: vec![
                                                node(ExprCore::Ix { index: 1 }, 0, false),
                                                node(
                                                    ExprCore::Opaque {
                                                        name: "one".to_owned(),
                                                    },
                                                    0,
                                                    false,
                                                ),
                                            ],
                                        },
                                        0,
                                        false,
                                    ),
                                },
                                0,
                                false,
                            ),
                        ),
                        operator(
                            "G",
                            node(
                                ExprCore::Opaque {
                                    name: "g".to_owned(),
                                },
                                0,
                                false,
                            ),
                        ),
                    ],
                    body: node(
                        ExprCore::Apply {
                            operator: node(ExprCore::Ix { index: 2 }, 0, false),
                            args: vec![node(
                                ExprCore::Opaque {
                                    name: "two".to_owned(),
                                },
                                0,
                                false,
                            )],
                        },
                        22,
                        false,
                    ),
                },
                21,
                false,
            ),
            vec![],
            vec![Selector::Label {
                label: "F".to_owned(),
                args: vec![node(
                    ExprCore::Opaque {
                        name: "arg".to_owned(),
                    },
                    0,
                    false,
                )],
            }],
            "warn stderr: File \"T.tla\", line 21, characters 3-8:\nError: Could not find label F\nwarn stderr: File \"T.tla\", line 21, characters 3-8:\nError: Could not resolve subexpression reference\nerr TlaProofError: \"Could not resolve subexpression reference\" failure=\"Expr.Anon: 2\" exception=\"Failure(\\\"Expr.Anon: 2\\\")\"",
        );
    }

    #[test]
    fn let_operator_label_bad_args() {
        check(
            node(
                ExprCore::Let {
                    definitions: vec![
                        operator(
                            "F",
                            node(
                                ExprCore::Lambda {
                                    params: vec![param("p")],
                                    body: node(
                                        ExprCore::Apply {
                                            operator: node(
                                                ExprCore::Internal {
                                                    builtin: Builtin::Plus,
                                                },
                                                0,
                                                false,
                                            ),
                                            args: vec![
                                                node(ExprCore::Ix { index: 1 }, 0, false),
                                                node(
                                                    ExprCore::Opaque {
                                                        name: "one".to_owned(),
                                                    },
                                                    0,
                                                    false,
                                                ),
                                            ],
                                        },
                                        0,
                                        false,
                                    ),
                                },
                                0,
                                false,
                            ),
                        ),
                        operator(
                            "G",
                            node(
                                ExprCore::Opaque {
                                    name: "g".to_owned(),
                                },
                                0,
                                false,
                            ),
                        ),
                    ],
                    body: node(
                        ExprCore::Apply {
                            operator: node(ExprCore::Ix { index: 2 }, 0, false),
                            args: vec![node(
                                ExprCore::Opaque {
                                    name: "two".to_owned(),
                                },
                                0,
                                false,
                            )],
                        },
                        22,
                        false,
                    ),
                },
                21,
                false,
            ),
            vec![],
            vec![Selector::Label {
                label: "F".to_owned(),
                args: vec![
                    node(
                        ExprCore::Opaque {
                            name: "a".to_owned(),
                        },
                        0,
                        false,
                    ),
                    node(
                        ExprCore::Opaque {
                            name: "b".to_owned(),
                        },
                        0,
                        false,
                    ),
                ],
            }],
            "warn stderr: File \"T.tla\", line 21, characters 3-8:\nError: Could not find label F\nwarn stderr: File \"T.tla\", line 21, characters 3-8:\nError: Could not resolve subexpression reference\nerr TlaProofError: \"Could not resolve subexpression reference\" failure=\"Expr.Anon: 2\" exception=\"Failure(\\\"Expr.Anon: 2\\\")\"",
        );
    }

    #[test]
    fn let_operator_down() {
        check(
            node(
                ExprCore::Let {
                    definitions: vec![
                        operator(
                            "F",
                            node(
                                ExprCore::Lambda {
                                    params: vec![param("p")],
                                    body: node(
                                        ExprCore::Apply {
                                            operator: node(
                                                ExprCore::Internal {
                                                    builtin: Builtin::Plus,
                                                },
                                                0,
                                                false,
                                            ),
                                            args: vec![
                                                node(ExprCore::Ix { index: 1 }, 0, false),
                                                node(
                                                    ExprCore::Opaque {
                                                        name: "one".to_owned(),
                                                    },
                                                    0,
                                                    false,
                                                ),
                                            ],
                                        },
                                        0,
                                        false,
                                    ),
                                },
                                0,
                                false,
                            ),
                        ),
                        operator(
                            "G",
                            node(
                                ExprCore::Opaque {
                                    name: "g".to_owned(),
                                },
                                0,
                                false,
                            ),
                        ),
                    ],
                    body: node(
                        ExprCore::Apply {
                            operator: node(ExprCore::Ix { index: 2 }, 0, false),
                            args: vec![node(
                                ExprCore::Opaque {
                                    name: "two".to_owned(),
                                },
                                0,
                                false,
                            )],
                        },
                        22,
                        false,
                    ),
                },
                21,
                false,
            ),
            vec![],
            vec![
                Selector::Down,
                Selector::Label {
                    label: "G".to_owned(),
                    args: vec![],
                },
            ],
            "ok: Let[F](Lambda[p/0](Apply(Ix[1], Opaque[one], Internal[Plus])), Opaque[g])!",
        );
    }

    #[test]
    fn let_operator_down_then() {
        check(
            node(
                ExprCore::Let {
                    definitions: vec![
                        operator(
                            "F",
                            node(
                                ExprCore::Lambda {
                                    params: vec![param("p")],
                                    body: node(
                                        ExprCore::Apply {
                                            operator: node(
                                                ExprCore::Internal {
                                                    builtin: Builtin::Plus,
                                                },
                                                0,
                                                false,
                                            ),
                                            args: vec![
                                                node(ExprCore::Ix { index: 1 }, 0, false),
                                                node(
                                                    ExprCore::Opaque {
                                                        name: "one".to_owned(),
                                                    },
                                                    0,
                                                    false,
                                                ),
                                            ],
                                        },
                                        0,
                                        false,
                                    ),
                                },
                                0,
                                false,
                            ),
                        ),
                        operator(
                            "G",
                            node(
                                ExprCore::Opaque {
                                    name: "g".to_owned(),
                                },
                                0,
                                false,
                            ),
                        ),
                    ],
                    body: node(
                        ExprCore::Apply {
                            operator: node(ExprCore::Ix { index: 2 }, 0, false),
                            args: vec![node(
                                ExprCore::Opaque {
                                    name: "two".to_owned(),
                                },
                                0,
                                false,
                            )],
                        },
                        22,
                        false,
                    ),
                },
                21,
                false,
            ),
            vec![],
            vec![
                Selector::Down,
                Selector::Label {
                    label: "F".to_owned(),
                    args: vec![],
                },
                Selector::Number(2),
            ],
            "ok: Lambda[p/0](Opaque[one])!",
        );
    }

    #[test]
    fn let_operator_missing() {
        check(
            node(
                ExprCore::Let {
                    definitions: vec![
                        operator(
                            "F",
                            node(
                                ExprCore::Lambda {
                                    params: vec![param("p")],
                                    body: node(
                                        ExprCore::Apply {
                                            operator: node(
                                                ExprCore::Internal {
                                                    builtin: Builtin::Plus,
                                                },
                                                0,
                                                false,
                                            ),
                                            args: vec![
                                                node(ExprCore::Ix { index: 1 }, 0, false),
                                                node(
                                                    ExprCore::Opaque {
                                                        name: "one".to_owned(),
                                                    },
                                                    0,
                                                    false,
                                                ),
                                            ],
                                        },
                                        0,
                                        false,
                                    ),
                                },
                                0,
                                false,
                            ),
                        ),
                        operator(
                            "G",
                            node(
                                ExprCore::Opaque {
                                    name: "g".to_owned(),
                                },
                                0,
                                false,
                            ),
                        ),
                    ],
                    body: node(
                        ExprCore::Apply {
                            operator: node(ExprCore::Ix { index: 2 }, 0, false),
                            args: vec![node(
                                ExprCore::Opaque {
                                    name: "two".to_owned(),
                                },
                                0,
                                false,
                            )],
                        },
                        22,
                        false,
                    ),
                },
                21,
                false,
            ),
            vec![],
            vec![
                Selector::Down,
                Selector::Label {
                    label: "H".to_owned(),
                    args: vec![],
                },
            ],
            "warn stderr: File \"T.tla\", line 21, characters 3-8:\nError: no definition of operator H\nerr TlaProofError: \"no definition of operator H\" failure=\"Expr.Deref.deref_letop\" exception=\"Failure(\\\"Expr.Deref.deref_letop\\\")\"",
        );
    }

    #[test]
    fn down_not_let() {
        check(
            node(
                ExprCore::Lambda {
                    params: vec![param("x"), param("y")],
                    body: node(
                        ExprCore::Apply {
                            operator: node(
                                ExprCore::Internal {
                                    builtin: Builtin::Plus,
                                },
                                0,
                                false,
                            ),
                            args: vec![
                                node(ExprCore::Ix { index: 2 }, 0, false),
                                node(ExprCore::Ix { index: 1 }, 0, false),
                            ],
                        },
                        2,
                        false,
                    ),
                },
                1,
                false,
            ),
            vec![],
            vec![Selector::Down, Selector::Number(1)],
            "ok: Lambda[x/0 y/0](Ix[2])!",
        );
    }

    #[test]
    fn down_forbidden() {
        check(
            node(
                ExprCore::Tuple {
                    elements: vec![
                        node(
                            ExprCore::Opaque {
                                name: "a".to_owned(),
                            },
                            0,
                            false,
                        ),
                        node(
                            ExprCore::Opaque {
                                name: "b".to_owned(),
                            },
                            0,
                            false,
                        ),
                    ],
                },
                0,
                false,
            ),
            vec![],
            vec![Selector::Number(1), Selector::Down],
            "err TlaProofError: \"!: is forbidden for this expression.\\n\" failure=\"Expr.Deref.deref: !:\" exception=\"Failure(\\\"Expr.Deref.deref: !:\\\")\"",
        );
    }

    #[test]
    fn down_last() {
        check(
            node(
                ExprCore::Tuple {
                    elements: vec![
                        node(
                            ExprCore::Opaque {
                                name: "a".to_owned(),
                            },
                            0,
                            false,
                        ),
                        node(
                            ExprCore::Opaque {
                                name: "b".to_owned(),
                            },
                            0,
                            false,
                        ),
                    ],
                },
                0,
                false,
            ),
            vec![],
            vec![Selector::Down],
            "ok: Tuple(Opaque[a], Opaque[b])!",
        );
    }

    #[test]
    fn let_after_number_label() {
        check(
            node(
                ExprCore::Tuple {
                    elements: vec![
                        node(
                            ExprCore::Let {
                                definitions: vec![
                                    operator(
                                        "F",
                                        node(
                                            ExprCore::Lambda {
                                                params: vec![param("p")],
                                                body: node(
                                                    ExprCore::Apply {
                                                        operator: node(
                                                            ExprCore::Internal {
                                                                builtin: Builtin::Plus,
                                                            },
                                                            0,
                                                            false,
                                                        ),
                                                        args: vec![
                                                            node(
                                                                ExprCore::Ix { index: 1 },
                                                                0,
                                                                false,
                                                            ),
                                                            node(
                                                                ExprCore::Opaque {
                                                                    name: "one".to_owned(),
                                                                },
                                                                0,
                                                                false,
                                                            ),
                                                        ],
                                                    },
                                                    0,
                                                    false,
                                                ),
                                            },
                                            0,
                                            false,
                                        ),
                                    ),
                                    operator(
                                        "G",
                                        node(
                                            ExprCore::Opaque {
                                                name: "g".to_owned(),
                                            },
                                            0,
                                            false,
                                        ),
                                    ),
                                ],
                                body: node(
                                    ExprCore::Apply {
                                        operator: node(ExprCore::Ix { index: 2 }, 0, false),
                                        args: vec![node(
                                            ExprCore::Opaque {
                                                name: "two".to_owned(),
                                            },
                                            0,
                                            false,
                                        )],
                                    },
                                    22,
                                    false,
                                ),
                            },
                            21,
                            false,
                        ),
                        node(
                            ExprCore::Opaque {
                                name: "z".to_owned(),
                            },
                            0,
                            false,
                        ),
                    ],
                },
                0,
                false,
            ),
            vec![],
            vec![
                Selector::Number(1),
                Selector::Label {
                    label: "G".to_owned(),
                    args: vec![],
                },
            ],
            "ok: Let[F](Lambda[p/0](Apply(Ix[1], Opaque[one], Internal[Plus])), Opaque[g])!",
        );
    }

    #[test]
    fn let_label_not_operator() {
        check(
            node(
                ExprCore::Let {
                    definitions: vec![
                        operator(
                            "F",
                            node(
                                ExprCore::Lambda {
                                    params: vec![param("p")],
                                    body: node(
                                        ExprCore::Apply {
                                            operator: node(
                                                ExprCore::Internal {
                                                    builtin: Builtin::Plus,
                                                },
                                                0,
                                                false,
                                            ),
                                            args: vec![
                                                node(ExprCore::Ix { index: 1 }, 0, false),
                                                node(
                                                    ExprCore::Opaque {
                                                        name: "one".to_owned(),
                                                    },
                                                    0,
                                                    false,
                                                ),
                                            ],
                                        },
                                        0,
                                        false,
                                    ),
                                },
                                0,
                                false,
                            ),
                        ),
                        operator(
                            "G",
                            node(
                                ExprCore::Opaque {
                                    name: "g".to_owned(),
                                },
                                0,
                                false,
                            ),
                        ),
                    ],
                    body: node(
                        ExprCore::Apply {
                            operator: node(ExprCore::Ix { index: 2 }, 0, false),
                            args: vec![node(
                                ExprCore::Opaque {
                                    name: "two".to_owned(),
                                },
                                0,
                                false,
                            )],
                        },
                        22,
                        false,
                    ),
                },
                21,
                false,
            ),
            vec![],
            vec![
                Selector::Number(1),
                Selector::Label {
                    label: "missing".to_owned(),
                    args: vec![],
                },
            ],
            "warn stderr: File \"T.tla\", line 22, characters 3-8:\nError: Could not find label missing\nok: Let[F G](Lambda[p/0](Apply(Ix[1], Opaque[one], Internal[Plus])), Opaque[g], Opaque[$Bad])!",
        );
    }

    #[test]
    fn label() {
        check(
            node(
                ExprCore::Quant {
                    quantifier: Quantifier::Forall,
                    bounds: vec![bound(
                        "x",
                        Some(node(
                            ExprCore::Opaque {
                                name: "S".to_owned(),
                            },
                            0,
                            false,
                        )),
                    )],
                    body: node(
                        ExprCore::Quant {
                            quantifier: Quantifier::Exists,
                            bounds: vec![bound("y", None)],
                            body: node(
                                ExprCore::Parens {
                                    expression: node(
                                        ExprCore::Apply {
                                            operator: node(
                                                ExprCore::Internal {
                                                    builtin: Builtin::Eq,
                                                },
                                                0,
                                                false,
                                            ),
                                            args: vec![
                                                node(ExprCore::Ix { index: 2 }, 0, false),
                                                node(ExprCore::Ix { index: 1 }, 0, false),
                                            ],
                                        },
                                        26,
                                        false,
                                    ),
                                    form: xlabel("lab", &[("x", 2), ("y", 1)]),
                                },
                                0,
                                false,
                            ),
                        },
                        25,
                        false,
                    ),
                },
                24,
                false,
            ),
            vec![],
            vec![Selector::Label {
                label: "lab".to_owned(),
                args: vec![],
            }],
            "ok: Lambda[x/0 y/0](Apply(Ix[2], Ix[1], Internal[Eq])@26)@26!",
        );
    }

    #[test]
    fn label_args() {
        check(
            node(
                ExprCore::Quant {
                    quantifier: Quantifier::Forall,
                    bounds: vec![bound(
                        "x",
                        Some(node(
                            ExprCore::Opaque {
                                name: "S".to_owned(),
                            },
                            0,
                            false,
                        )),
                    )],
                    body: node(
                        ExprCore::Quant {
                            quantifier: Quantifier::Exists,
                            bounds: vec![bound("y", None)],
                            body: node(
                                ExprCore::Parens {
                                    expression: node(
                                        ExprCore::Apply {
                                            operator: node(
                                                ExprCore::Internal {
                                                    builtin: Builtin::Eq,
                                                },
                                                0,
                                                false,
                                            ),
                                            args: vec![
                                                node(ExprCore::Ix { index: 2 }, 0, false),
                                                node(ExprCore::Ix { index: 1 }, 0, false),
                                            ],
                                        },
                                        26,
                                        false,
                                    ),
                                    form: xlabel("lab", &[("x", 2), ("y", 1)]),
                                },
                                0,
                                false,
                            ),
                        },
                        25,
                        false,
                    ),
                },
                24,
                false,
            ),
            vec![],
            vec![Selector::Label {
                label: "lab".to_owned(),
                args: vec![
                    node(
                        ExprCore::Opaque {
                            name: "a".to_owned(),
                        },
                        0,
                        false,
                    ),
                    node(
                        ExprCore::Opaque {
                            name: "b".to_owned(),
                        },
                        0,
                        false,
                    ),
                ],
            }],
            "ok: Apply(Opaque[a], Opaque[b], Internal[Eq])@26!",
        );
    }

    #[test]
    fn label_arg_count() {
        check(
            node(
                ExprCore::Quant {
                    quantifier: Quantifier::Forall,
                    bounds: vec![bound(
                        "x",
                        Some(node(
                            ExprCore::Opaque {
                                name: "S".to_owned(),
                            },
                            0,
                            false,
                        )),
                    )],
                    body: node(
                        ExprCore::Quant {
                            quantifier: Quantifier::Exists,
                            bounds: vec![bound("y", None)],
                            body: node(
                                ExprCore::Parens {
                                    expression: node(
                                        ExprCore::Apply {
                                            operator: node(
                                                ExprCore::Internal {
                                                    builtin: Builtin::Eq,
                                                },
                                                0,
                                                false,
                                            ),
                                            args: vec![
                                                node(ExprCore::Ix { index: 2 }, 0, false),
                                                node(ExprCore::Ix { index: 1 }, 0, false),
                                            ],
                                        },
                                        26,
                                        false,
                                    ),
                                    form: xlabel("lab", &[("x", 2), ("y", 1)]),
                                },
                                0,
                                false,
                            ),
                        },
                        25,
                        false,
                    ),
                },
                24,
                false,
            ),
            vec![],
            vec![Selector::Label {
                label: "lab".to_owned(),
                args: vec![node(
                    ExprCore::Opaque {
                        name: "a".to_owned(),
                    },
                    0,
                    false,
                )],
            }],
            "warn stderr: File \"T.tla\", line 26, characters 3-8:\nError: Expected 2 arguments for labelled reference !lab, but found 1\nerr TlaProofError: \"Expected 2 arguments for labelled reference !lab, but found 1\" failure=\"Expr.Deref.deref_lsub\" exception=\"Failure(\\\"Expr.Deref.deref_lsub\\\")\"",
        );
    }

    #[test]
    fn label_missing() {
        check(
            node(
                ExprCore::Quant {
                    quantifier: Quantifier::Forall,
                    bounds: vec![bound(
                        "x",
                        Some(node(
                            ExprCore::Opaque {
                                name: "S".to_owned(),
                            },
                            0,
                            false,
                        )),
                    )],
                    body: node(
                        ExprCore::Quant {
                            quantifier: Quantifier::Exists,
                            bounds: vec![bound("y", None)],
                            body: node(
                                ExprCore::Parens {
                                    expression: node(
                                        ExprCore::Apply {
                                            operator: node(
                                                ExprCore::Internal {
                                                    builtin: Builtin::Eq,
                                                },
                                                0,
                                                false,
                                            ),
                                            args: vec![
                                                node(ExprCore::Ix { index: 2 }, 0, false),
                                                node(ExprCore::Ix { index: 1 }, 0, false),
                                            ],
                                        },
                                        26,
                                        false,
                                    ),
                                    form: xlabel("lab", &[("x", 2), ("y", 1)]),
                                },
                                0,
                                false,
                            ),
                        },
                        25,
                        false,
                    ),
                },
                24,
                false,
            ),
            vec![],
            vec![Selector::Label {
                label: "nope".to_owned(),
                args: vec![],
            }],
            "warn stderr: File \"T.tla\", line 24, characters 3-8:\nError: Could not find label nope\nwarn stderr: File \"T.tla\", line 24, characters 3-8:\nError: Could not resolve subexpression reference\nerr TlaProofError: \"Could not resolve subexpression reference\" failure=\"Expr.Anon: 2\" exception=\"Failure(\\\"Expr.Anon: 2\\\")\"",
        );
    }

    #[test]
    fn label_then_number() {
        check(
            node(
                ExprCore::Quant {
                    quantifier: Quantifier::Forall,
                    bounds: vec![bound(
                        "x",
                        Some(node(
                            ExprCore::Opaque {
                                name: "S".to_owned(),
                            },
                            0,
                            false,
                        )),
                    )],
                    body: node(
                        ExprCore::Quant {
                            quantifier: Quantifier::Exists,
                            bounds: vec![bound("y", None)],
                            body: node(
                                ExprCore::Parens {
                                    expression: node(
                                        ExprCore::Apply {
                                            operator: node(
                                                ExprCore::Internal {
                                                    builtin: Builtin::Eq,
                                                },
                                                0,
                                                false,
                                            ),
                                            args: vec![
                                                node(ExprCore::Ix { index: 2 }, 0, false),
                                                node(ExprCore::Ix { index: 1 }, 0, false),
                                            ],
                                        },
                                        26,
                                        false,
                                    ),
                                    form: xlabel("lab", &[("x", 2), ("y", 1)]),
                                },
                                0,
                                false,
                            ),
                        },
                        25,
                        false,
                    ),
                },
                24,
                false,
            ),
            vec![],
            vec![
                Selector::Label {
                    label: "lab".to_owned(),
                    args: vec![],
                },
                Selector::Number(1),
            ],
            "ok: Lambda[x/0 y/0](Ix[2])!",
        );
    }

    #[test]
    fn label_swapped_args() {
        check(
            node(
                ExprCore::Quant {
                    quantifier: Quantifier::Forall,
                    bounds: vec![bound("x", None)],
                    body: node(
                        ExprCore::Quant {
                            quantifier: Quantifier::Exists,
                            bounds: vec![bound("y", None)],
                            body: node(
                                ExprCore::Parens {
                                    expression: node(
                                        ExprCore::Apply {
                                            operator: node(
                                                ExprCore::Internal {
                                                    builtin: Builtin::Eq,
                                                },
                                                0,
                                                false,
                                            ),
                                            args: vec![
                                                node(ExprCore::Ix { index: 2 }, 0, false),
                                                node(ExprCore::Ix { index: 1 }, 0, false),
                                            ],
                                        },
                                        0,
                                        false,
                                    ),
                                    form: xlabel("sw", &[("y", 1), ("x", 2)]),
                                },
                                0,
                                false,
                            ),
                        },
                        0,
                        false,
                    ),
                },
                0,
                false,
            ),
            vec![],
            vec![Selector::Label {
                label: "sw".to_owned(),
                args: vec![
                    node(
                        ExprCore::Opaque {
                            name: "a".to_owned(),
                        },
                        0,
                        false,
                    ),
                    node(
                        ExprCore::Opaque {
                            name: "b".to_owned(),
                        },
                        0,
                        false,
                    ),
                ],
            }],
            "ok: Apply(Opaque[b], Opaque[a], Internal[Eq])!",
        );
    }

    #[test]
    fn label_swapped() {
        check(
            node(
                ExprCore::Quant {
                    quantifier: Quantifier::Forall,
                    bounds: vec![bound("x", None)],
                    body: node(
                        ExprCore::Quant {
                            quantifier: Quantifier::Exists,
                            bounds: vec![bound("y", None)],
                            body: node(
                                ExprCore::Parens {
                                    expression: node(
                                        ExprCore::Apply {
                                            operator: node(
                                                ExprCore::Internal {
                                                    builtin: Builtin::Eq,
                                                },
                                                0,
                                                false,
                                            ),
                                            args: vec![
                                                node(ExprCore::Ix { index: 2 }, 0, false),
                                                node(ExprCore::Ix { index: 1 }, 0, false),
                                            ],
                                        },
                                        0,
                                        false,
                                    ),
                                    form: xlabel("sw", &[("y", 1), ("x", 2)]),
                                },
                                0,
                                false,
                            ),
                        },
                        0,
                        false,
                    ),
                },
                0,
                false,
            ),
            vec![],
            vec![Selector::Label {
                label: "sw".to_owned(),
                args: vec![],
            }],
            "ok: Lambda[y/0 x/0](Apply(Ix[1], Ix[2], Internal[Eq]))!",
        );
    }

    #[test]
    fn label_single_mismatch() {
        check(
            node(
                ExprCore::Quant {
                    quantifier: Quantifier::Forall,
                    bounds: vec![bound("x", None)],
                    body: node(
                        ExprCore::Parens {
                            expression: node(
                                ExprCore::Apply {
                                    operator: node(
                                        ExprCore::Internal {
                                            builtin: Builtin::Eq,
                                        },
                                        0,
                                        false,
                                    ),
                                    args: vec![
                                        node(ExprCore::Ix { index: 1 }, 0, false),
                                        node(
                                            ExprCore::Opaque {
                                                name: "k".to_owned(),
                                            },
                                            0,
                                            false,
                                        ),
                                    ],
                                },
                                28,
                                false,
                            ),
                            form: xlabel("one", &[("x", 1)]),
                        },
                        0,
                        false,
                    ),
                },
                0,
                false,
            ),
            vec![],
            vec![Selector::Label {
                label: "one".to_owned(),
                args: vec![
                    node(
                        ExprCore::Opaque {
                            name: "a".to_owned(),
                        },
                        0,
                        false,
                    ),
                    node(
                        ExprCore::Opaque {
                            name: "b".to_owned(),
                        },
                        0,
                        false,
                    ),
                ],
            }],
            "warn stderr: File \"T.tla\", line 28, characters 3-8:\nError: Expected 1 argument for labelled reference !one, but found 2\nerr TlaProofError: \"Expected 1 argument for labelled reference !one, but found 2\" failure=\"Expr.Deref.deref_lsub\" exception=\"Failure(\\\"Expr.Deref.deref_lsub\\\")\"",
        );
    }

    #[test]
    fn label_in_let() {
        check(
            node(
                ExprCore::Let {
                    definitions: vec![operator(
                        "D",
                        node(
                            ExprCore::Opaque {
                                name: "d".to_owned(),
                            },
                            0,
                            false,
                        ),
                    )],
                    body: node(
                        ExprCore::Parens {
                            expression: node(
                                ExprCore::Apply {
                                    operator: node(
                                        ExprCore::Internal {
                                            builtin: Builtin::Plus,
                                        },
                                        0,
                                        false,
                                    ),
                                    args: vec![
                                        node(ExprCore::Ix { index: 1 }, 0, false),
                                        node(
                                            ExprCore::Opaque {
                                                name: "k".to_owned(),
                                            },
                                            0,
                                            false,
                                        ),
                                    ],
                                },
                                0,
                                false,
                            ),
                            form: xlabel("in", &[]),
                        },
                        0,
                        false,
                    ),
                },
                29,
                false,
            ),
            vec![],
            vec![Selector::Label {
                label: "in".to_owned(),
                args: vec![],
            }],
            "ok: Let[D](Opaque[d], Apply(Ix[1], Opaque[k], Internal[Plus]))!",
        );
    }

    #[test]
    fn label_in_let_definition() {
        check(
            node(
                ExprCore::Let {
                    definitions: vec![
                        operator(
                            "D",
                            node(
                                ExprCore::Parens {
                                    expression: node(
                                        ExprCore::Opaque {
                                            name: "d".to_owned(),
                                        },
                                        0,
                                        false,
                                    ),
                                    form: xlabel("def", &[]),
                                },
                                0,
                                false,
                            ),
                        ),
                        operator(
                            "E",
                            node(
                                ExprCore::Opaque {
                                    name: "e".to_owned(),
                                },
                                0,
                                false,
                            ),
                        ),
                    ],
                    body: node(
                        ExprCore::Opaque {
                            name: "body".to_owned(),
                        },
                        0,
                        false,
                    ),
                },
                0,
                false,
            ),
            vec![],
            vec![Selector::Label {
                label: "def".to_owned(),
                args: vec![],
            }],
            "ok: Opaque[d]!",
        );
    }

    #[test]
    fn label_in_tquant() {
        check(
            node(
                ExprCore::Tquant {
                    quantifier: Quantifier::Forall,
                    names: vec!["t".to_owned()],
                    body: node(
                        ExprCore::Parens {
                            expression: node(
                                ExprCore::Apply {
                                    operator: node(
                                        ExprCore::Internal {
                                            builtin: Builtin::Eq,
                                        },
                                        0,
                                        false,
                                    ),
                                    args: vec![
                                        node(ExprCore::Ix { index: 1 }, 0, false),
                                        node(
                                            ExprCore::Opaque {
                                                name: "k".to_owned(),
                                            },
                                            0,
                                            false,
                                        ),
                                    ],
                                },
                                0,
                                false,
                            ),
                            form: xlabel("tl", &[]),
                        },
                        0,
                        false,
                    ),
                },
                0,
                false,
            ),
            vec![],
            vec![Selector::Label {
                label: "tl".to_owned(),
                args: vec![],
            }],
            "ok: Apply(Ix[0], Opaque[k], Internal[Eq])!",
        );
    }

    #[test]
    fn label_in_lambda() {
        check(
            node(
                ExprCore::Lambda {
                    params: vec![param("p"), param("q")],
                    body: node(
                        ExprCore::Parens {
                            expression: node(
                                ExprCore::Apply {
                                    operator: node(
                                        ExprCore::Internal {
                                            builtin: Builtin::Eq,
                                        },
                                        0,
                                        false,
                                    ),
                                    args: vec![
                                        node(ExprCore::Ix { index: 1 }, 0, false),
                                        node(ExprCore::Ix { index: 2 }, 0, false),
                                    ],
                                },
                                0,
                                false,
                            ),
                            form: xlabel("ll", &[("q", 1)]),
                        },
                        0,
                        false,
                    ),
                },
                0,
                false,
            ),
            vec![],
            vec![Selector::Label {
                label: "ll".to_owned(),
                args: vec![],
            }],
            "err TlaProofError: \"Oops, this seems to be a bug in TLAPM.\" failure=null exception=\"File \\\"src/expr/e_deref.ml\\\", line 477, characters 21-33: Assertion failed\"",
        );
    }

    #[test]
    fn label_in_choose() {
        check(
            node(
                ExprCore::Choose {
                    name: "c".to_owned(),
                    domain: Some(node(
                        ExprCore::Opaque {
                            name: "D".to_owned(),
                        },
                        0,
                        false,
                    )),
                    body: node(
                        ExprCore::Parens {
                            expression: node(
                                ExprCore::Apply {
                                    operator: node(
                                        ExprCore::Internal {
                                            builtin: Builtin::Eq,
                                        },
                                        0,
                                        false,
                                    ),
                                    args: vec![
                                        node(ExprCore::Ix { index: 1 }, 0, false),
                                        node(
                                            ExprCore::Opaque {
                                                name: "k".to_owned(),
                                            },
                                            0,
                                            false,
                                        ),
                                    ],
                                },
                                0,
                                false,
                            ),
                            form: xlabel("cl", &[("c", 1)]),
                        },
                        0,
                        false,
                    ),
                },
                0,
                false,
            ),
            vec![],
            vec![Selector::Label {
                label: "cl".to_owned(),
                args: vec![node(
                    ExprCore::Opaque {
                        name: "a".to_owned(),
                    },
                    0,
                    false,
                )],
            }],
            "ok: Apply(Opaque[a], Opaque[k], Internal[Eq])!",
        );
    }

    #[test]
    fn label_in_setst_domain() {
        check(
            node(
                ExprCore::SetSt {
                    name: "s".to_owned(),
                    domain: node(
                        ExprCore::Parens {
                            expression: node(
                                ExprCore::Opaque {
                                    name: "D".to_owned(),
                                },
                                0,
                                false,
                            ),
                            form: xlabel("sd", &[]),
                        },
                        0,
                        false,
                    ),
                    body: node(
                        ExprCore::Opaque {
                            name: "b".to_owned(),
                        },
                        0,
                        false,
                    ),
                },
                0,
                false,
            ),
            vec![],
            vec![Selector::Label {
                label: "sd".to_owned(),
                args: vec![],
            }],
            "ok: Opaque[D]!",
        );
    }

    #[test]
    fn label_in_quant_domain() {
        check(
            node(
                ExprCore::Quant {
                    quantifier: Quantifier::Forall,
                    bounds: vec![bound(
                        "x",
                        Some(node(
                            ExprCore::Parens {
                                expression: node(
                                    ExprCore::Opaque {
                                        name: "S".to_owned(),
                                    },
                                    0,
                                    false,
                                ),
                                form: xlabel("qd", &[]),
                            },
                            0,
                            false,
                        )),
                    )],
                    body: node(
                        ExprCore::Opaque {
                            name: "b".to_owned(),
                        },
                        0,
                        false,
                    ),
                },
                0,
                false,
            ),
            vec![],
            vec![Selector::Label {
                label: "qd".to_owned(),
                args: vec![],
            }],
            "ok: Opaque[S]!",
        );
    }

    #[test]
    fn label_other_name_stops() {
        check(
            node(
                ExprCore::Parens {
                    expression: node(
                        ExprCore::Parens {
                            expression: node(
                                ExprCore::Opaque {
                                    name: "i".to_owned(),
                                },
                                0,
                                false,
                            ),
                            form: xlabel("inner", &[]),
                        },
                        0,
                        false,
                    ),
                    form: xlabel("outer", &[]),
                },
                0,
                false,
            ),
            vec![],
            vec![Selector::Label {
                label: "inner".to_owned(),
                args: vec![],
            }],
            "warn stderr: <unknown location>:\nError: Could not find label inner\nwarn stderr: <unknown location>:\nError: Could not resolve subexpression reference\nerr TlaProofError: \"Could not resolve subexpression reference\" failure=\"Expr.Anon: 2\" exception=\"Failure(\\\"Expr.Anon: 2\\\")\"",
        );
    }

    #[test]
    fn label_nested_nlabel() {
        check(
            node(
                ExprCore::Parens {
                    expression: node(
                        ExprCore::Parens {
                            expression: node(
                                ExprCore::Opaque {
                                    name: "i".to_owned(),
                                },
                                0,
                                false,
                            ),
                            form: xlabel("inner", &[]),
                        },
                        0,
                        false,
                    ),
                    form: ParenForm::Nlabel {
                        label: "n".to_owned(),
                        names: vec![],
                    },
                },
                0,
                false,
            ),
            vec![],
            vec![Selector::Label {
                label: "inner".to_owned(),
                args: vec![],
            }],
            "ok: Opaque[i]!",
        );
    }

    #[test]
    fn label_bug() {
        check(
            node(
                ExprCore::Parens {
                    expression: node(
                        ExprCore::Opaque {
                            name: "v".to_owned(),
                        },
                        0,
                        false,
                    ),
                    form: xlabel("bug", &[("x", 1)]),
                },
                0,
                false,
            ),
            vec![],
            vec![Selector::Label {
                label: "bug".to_owned(),
                args: vec![],
            }],
            "err TlaProofError: \"Oops, this seems to be a bug in TLAPM.\" failure=null exception=\"File \\\"src/expr/e_deref.ml\\\", line 477, characters 21-33: Assertion failed\"",
        );
    }

    #[test]
    fn label_in_sequent() {
        check(
            node(
                ExprCore::Sequent {
                    sequent: Sequent {
                        context: vec![
                            fact(node(
                                ExprCore::Opaque {
                                    name: "A".to_owned(),
                                },
                                0,
                                false,
                            )),
                            fact(node(
                                ExprCore::Parens {
                                    expression: node(ExprCore::Ix { index: 1 }, 0, false),
                                    form: xlabel("sq", &[]),
                                },
                                0,
                                false,
                            )),
                        ],
                        active: node(
                            ExprCore::Opaque {
                                name: "C".to_owned(),
                            },
                            0,
                            false,
                        ),
                    },
                },
                0,
                false,
            ),
            vec![],
            vec![Selector::Label {
                label: "sq".to_owned(),
                args: vec![],
            }],
            "ok: Ix[0]!",
        );
    }

    #[test]
    fn label_sequent_stops() {
        check(
            node(
                ExprCore::Sequent {
                    sequent: Sequent {
                        context: vec![
                            fresh("x"),
                            fact(node(
                                ExprCore::Parens {
                                    expression: node(ExprCore::Ix { index: 1 }, 0, false),
                                    form: xlabel("sq", &[]),
                                },
                                0,
                                false,
                            )),
                        ],
                        active: node(
                            ExprCore::Opaque {
                                name: "C".to_owned(),
                            },
                            0,
                            false,
                        ),
                    },
                },
                0,
                false,
            ),
            vec![],
            vec![Selector::Label {
                label: "sq".to_owned(),
                args: vec![],
            }],
            "warn stderr: <unknown location>:\nError: Could not find label sq\nwarn stderr: <unknown location>:\nError: Could not resolve subexpression reference\nerr TlaProofError: \"Could not resolve subexpression reference\" failure=\"Expr.Anon: 2\" exception=\"Failure(\\\"Expr.Anon: 2\\\")\"",
        );
    }

    #[test]
    fn label_in_sequent_active() {
        check(
            node(
                ExprCore::Sequent {
                    sequent: Sequent {
                        context: vec![fact(node(
                            ExprCore::Opaque {
                                name: "A".to_owned(),
                            },
                            0,
                            false,
                        ))],
                        active: node(
                            ExprCore::Parens {
                                expression: node(
                                    ExprCore::Opaque {
                                        name: "C".to_owned(),
                                    },
                                    0,
                                    false,
                                ),
                                form: xlabel("ac", &[]),
                            },
                            0,
                            false,
                        ),
                    },
                },
                0,
                false,
            ),
            vec![],
            vec![Selector::Label {
                label: "ac".to_owned(),
                args: vec![],
            }],
            "ok: Opaque[C]!",
        );
    }

    #[test]
    fn label_after_atomic() {
        check(
            node(
                ExprCore::Quant {
                    quantifier: Quantifier::Forall,
                    bounds: vec![bound(
                        "x",
                        Some(node(
                            ExprCore::Opaque {
                                name: "S".to_owned(),
                            },
                            0,
                            false,
                        )),
                    )],
                    body: node(
                        ExprCore::Quant {
                            quantifier: Quantifier::Exists,
                            bounds: vec![bound("y", None)],
                            body: node(
                                ExprCore::Parens {
                                    expression: node(
                                        ExprCore::Apply {
                                            operator: node(
                                                ExprCore::Internal {
                                                    builtin: Builtin::Eq,
                                                },
                                                0,
                                                false,
                                            ),
                                            args: vec![
                                                node(ExprCore::Ix { index: 2 }, 0, false),
                                                node(ExprCore::Ix { index: 1 }, 0, false),
                                            ],
                                        },
                                        26,
                                        false,
                                    ),
                                    form: xlabel("lab", &[("x", 2), ("y", 1)]),
                                },
                                0,
                                false,
                            ),
                        },
                        25,
                        false,
                    ),
                },
                24,
                false,
            ),
            vec![],
            vec![
                Selector::Label {
                    label: "lab".to_owned(),
                    args: vec![],
                },
                Selector::Label {
                    label: "lab".to_owned(),
                    args: vec![],
                },
            ],
            "warn stderr: File \"T.tla\", line 26, characters 3-8:\nError: Could not find label lab\nok: Lambda[x/0 y/0](Opaque[$Bad])!",
        );
    }

    #[test]
    fn sequent_first() {
        check(
            node(
                ExprCore::Sequent {
                    sequent: Sequent {
                        context: vec![
                            fact(node(
                                ExprCore::Opaque {
                                    name: "A".to_owned(),
                                },
                                0,
                                false,
                            )),
                            fact(node(
                                ExprCore::Apply {
                                    operator: node(
                                        ExprCore::Opaque {
                                            name: "B".to_owned(),
                                        },
                                        0,
                                        false,
                                    ),
                                    args: vec![node(ExprCore::Ix { index: 1 }, 0, false)],
                                },
                                31,
                                false,
                            )),
                            fresh("x"),
                            fact(node(ExprCore::Ix { index: 1 }, 0, false)),
                        ],
                        active: node(
                            ExprCore::Apply {
                                operator: node(
                                    ExprCore::Opaque {
                                        name: "C".to_owned(),
                                    },
                                    0,
                                    false,
                                ),
                                args: vec![node(ExprCore::Ix { index: 5 }, 0, false)],
                            },
                            0,
                            false,
                        ),
                    },
                },
                30,
                false,
            ),
            vec![],
            vec![Selector::Number(1)],
            "ok: Opaque[A]!",
        );
    }

    #[test]
    fn sequent_second() {
        check(
            node(
                ExprCore::Sequent {
                    sequent: Sequent {
                        context: vec![
                            fact(node(
                                ExprCore::Opaque {
                                    name: "A".to_owned(),
                                },
                                0,
                                false,
                            )),
                            fact(node(
                                ExprCore::Apply {
                                    operator: node(
                                        ExprCore::Opaque {
                                            name: "B".to_owned(),
                                        },
                                        0,
                                        false,
                                    ),
                                    args: vec![node(ExprCore::Ix { index: 1 }, 0, false)],
                                },
                                31,
                                false,
                            )),
                            fresh("x"),
                            fact(node(ExprCore::Ix { index: 1 }, 0, false)),
                        ],
                        active: node(
                            ExprCore::Apply {
                                operator: node(
                                    ExprCore::Opaque {
                                        name: "C".to_owned(),
                                    },
                                    0,
                                    false,
                                ),
                                args: vec![node(ExprCore::Ix { index: 5 }, 0, false)],
                            },
                            0,
                            false,
                        ),
                    },
                },
                30,
                false,
            ),
            vec![],
            vec![Selector::Number(2)],
            "warn stderr: File \"T.tla\", line 30, characters 3-8:\nError: subexpression of ASSUME/PROVE uses identifiers declared therein\nTlapm does not handle yet such subexpression namings.\nerr TlaProofError: \"Subexpression of ASSUME/PROVE uses identifiers declared therein\\n\\nTlapm does not handle yet such subexpression namings.\" failure=\"Expr.Deref.deref_num\" exception=\"Failure(\\\"Expr.Deref.deref_num\\\")\"",
        );
    }

    #[test]
    fn sequent_fresh() {
        check(
            node(
                ExprCore::Sequent {
                    sequent: Sequent {
                        context: vec![
                            fact(node(
                                ExprCore::Opaque {
                                    name: "A".to_owned(),
                                },
                                0,
                                false,
                            )),
                            fact(node(
                                ExprCore::Apply {
                                    operator: node(
                                        ExprCore::Opaque {
                                            name: "B".to_owned(),
                                        },
                                        0,
                                        false,
                                    ),
                                    args: vec![node(ExprCore::Ix { index: 1 }, 0, false)],
                                },
                                31,
                                false,
                            )),
                            fresh("x"),
                            fact(node(ExprCore::Ix { index: 1 }, 0, false)),
                        ],
                        active: node(
                            ExprCore::Apply {
                                operator: node(
                                    ExprCore::Opaque {
                                        name: "C".to_owned(),
                                    },
                                    0,
                                    false,
                                ),
                                args: vec![node(ExprCore::Ix { index: 5 }, 0, false)],
                            },
                            0,
                            false,
                        ),
                    },
                },
                30,
                false,
            ),
            vec![],
            vec![Selector::Number(3)],
            "warn stderr: File \"T.tla\", line 30, characters 3-8:\nError: subexpression reference does not resolve to an expression\nerr TlaProofError: \"subexpression reference does not resolve to an expression\" failure=\"Expr.Deref.deref_num\" exception=\"Failure(\\\"Expr.Deref.deref_num\\\")\"",
        );
    }

    #[test]
    fn sequent_fact_uses_fresh() {
        check(
            node(
                ExprCore::Sequent {
                    sequent: Sequent {
                        context: vec![
                            fact(node(
                                ExprCore::Opaque {
                                    name: "A".to_owned(),
                                },
                                0,
                                false,
                            )),
                            fact(node(
                                ExprCore::Apply {
                                    operator: node(
                                        ExprCore::Opaque {
                                            name: "B".to_owned(),
                                        },
                                        0,
                                        false,
                                    ),
                                    args: vec![node(ExprCore::Ix { index: 1 }, 0, false)],
                                },
                                31,
                                false,
                            )),
                            fresh("x"),
                            fact(node(ExprCore::Ix { index: 1 }, 0, false)),
                        ],
                        active: node(
                            ExprCore::Apply {
                                operator: node(
                                    ExprCore::Opaque {
                                        name: "C".to_owned(),
                                    },
                                    0,
                                    false,
                                ),
                                args: vec![node(ExprCore::Ix { index: 5 }, 0, false)],
                            },
                            0,
                            false,
                        ),
                    },
                },
                30,
                false,
            ),
            vec![],
            vec![Selector::Number(4)],
            "warn stderr: File \"T.tla\", line 30, characters 3-8:\nError: subexpression of ASSUME/PROVE uses identifiers declared therein\nTlapm does not handle yet such subexpression namings.\nerr TlaProofError: \"Subexpression of ASSUME/PROVE uses identifiers declared therein\\n\\nTlapm does not handle yet such subexpression namings.\" failure=\"Expr.Deref.deref_num\" exception=\"Failure(\\\"Expr.Deref.deref_num\\\")\"",
        );
    }

    #[test]
    fn sequent_active() {
        check(
            node(
                ExprCore::Sequent {
                    sequent: Sequent {
                        context: vec![
                            fact(node(
                                ExprCore::Opaque {
                                    name: "A".to_owned(),
                                },
                                0,
                                false,
                            )),
                            fact(node(
                                ExprCore::Apply {
                                    operator: node(
                                        ExprCore::Opaque {
                                            name: "B".to_owned(),
                                        },
                                        0,
                                        false,
                                    ),
                                    args: vec![node(ExprCore::Ix { index: 1 }, 0, false)],
                                },
                                31,
                                false,
                            )),
                            fresh("x"),
                            fact(node(ExprCore::Ix { index: 1 }, 0, false)),
                        ],
                        active: node(
                            ExprCore::Apply {
                                operator: node(
                                    ExprCore::Opaque {
                                        name: "C".to_owned(),
                                    },
                                    0,
                                    false,
                                ),
                                args: vec![node(ExprCore::Ix { index: 5 }, 0, false)],
                            },
                            0,
                            false,
                        ),
                    },
                },
                30,
                false,
            ),
            vec![],
            vec![Selector::Number(5)],
            "ok: Apply(Ix[1], Opaque[C])!",
        );
    }

    #[test]
    fn sequent_beyond() {
        check(
            node(
                ExprCore::Sequent {
                    sequent: Sequent {
                        context: vec![
                            fact(node(
                                ExprCore::Opaque {
                                    name: "A".to_owned(),
                                },
                                0,
                                false,
                            )),
                            fact(node(
                                ExprCore::Apply {
                                    operator: node(
                                        ExprCore::Opaque {
                                            name: "B".to_owned(),
                                        },
                                        0,
                                        false,
                                    ),
                                    args: vec![node(ExprCore::Ix { index: 1 }, 0, false)],
                                },
                                31,
                                false,
                            )),
                            fresh("x"),
                            fact(node(ExprCore::Ix { index: 1 }, 0, false)),
                        ],
                        active: node(
                            ExprCore::Apply {
                                operator: node(
                                    ExprCore::Opaque {
                                        name: "C".to_owned(),
                                    },
                                    0,
                                    false,
                                ),
                                args: vec![node(ExprCore::Ix { index: 5 }, 0, false)],
                            },
                            0,
                            false,
                        ),
                    },
                },
                30,
                false,
            ),
            vec![],
            vec![Selector::Number(6)],
            "warn stderr: File \"T.tla\", line 30, characters 3-8:\nError: Cannot resolve !6\nerr TlaProofError: \"Cannot resolve !6\" failure=\"Expr.Deref.deref_num\" exception=\"Failure(\\\"Expr.Deref.deref_num\\\")\"",
        );
    }

    #[test]
    fn sequent_negative() {
        check(
            node(
                ExprCore::Sequent {
                    sequent: Sequent {
                        context: vec![
                            fact(node(
                                ExprCore::Opaque {
                                    name: "A".to_owned(),
                                },
                                0,
                                false,
                            )),
                            fact(node(
                                ExprCore::Opaque {
                                    name: "B".to_owned(),
                                },
                                0,
                                false,
                            )),
                        ],
                        active: node(
                            ExprCore::Apply {
                                operator: node(
                                    ExprCore::Opaque {
                                        name: "C".to_owned(),
                                    },
                                    0,
                                    false,
                                ),
                                args: vec![node(ExprCore::Ix { index: 1 }, 0, false)],
                            },
                            0,
                            false,
                        ),
                    },
                },
                32,
                false,
            ),
            vec![],
            vec![Selector::Number(3)],
            "warn stderr: File \"T.tla\", line 32, characters 3-8:\nError: subexpression of ASSUME/PROVE uses identifiers declared therein\nTlapm does not handle yet such subexpression namings.\nerr TlaProofError: \"Subexpression of ASSUME/PROVE uses identifiers declared therein\\n\\nTlapm does not handle yet such subexpression namings.\" failure=\"Expr.Deref.deref_num\" exception=\"Failure(\\\"Expr.Deref.deref_num\\\")\"",
        );
    }

    #[test]
    fn sequent_bound_inside() {
        check(
            node(
                ExprCore::Sequent {
                    sequent: Sequent {
                        context: vec![
                            fact(node(
                                ExprCore::Opaque {
                                    name: "A".to_owned(),
                                },
                                0,
                                false,
                            )),
                            fact(node(
                                ExprCore::Quant {
                                    quantifier: Quantifier::Forall,
                                    bounds: vec![bound("x", None)],
                                    body: node(
                                        ExprCore::Apply {
                                            operator: node(
                                                ExprCore::Internal {
                                                    builtin: Builtin::Eq,
                                                },
                                                0,
                                                false,
                                            ),
                                            args: vec![
                                                node(ExprCore::Ix { index: 1 }, 0, false),
                                                node(ExprCore::Ix { index: 3 }, 0, false),
                                            ],
                                        },
                                        0,
                                        false,
                                    ),
                                },
                                0,
                                false,
                            )),
                        ],
                        active: node(
                            ExprCore::Opaque {
                                name: "C".to_owned(),
                            },
                            0,
                            false,
                        ),
                    },
                },
                0,
                false,
            ),
            vec![],
            vec![Selector::Number(2)],
            "ok: Quant[Forall x:Constant](Apply(Ix[1], Ix[2], Internal[Eq]))!",
        );
    }

    #[test]
    fn sequent_bound_inside_negative() {
        check(
            node(
                ExprCore::Sequent {
                    sequent: Sequent {
                        context: vec![
                            fact(node(
                                ExprCore::Opaque {
                                    name: "A".to_owned(),
                                },
                                0,
                                false,
                            )),
                            fact(node(
                                ExprCore::Quant {
                                    quantifier: Quantifier::Forall,
                                    bounds: vec![bound("x", None)],
                                    body: node(
                                        ExprCore::Apply {
                                            operator: node(
                                                ExprCore::Internal {
                                                    builtin: Builtin::Eq,
                                                },
                                                0,
                                                false,
                                            ),
                                            args: vec![
                                                node(ExprCore::Ix { index: 1 }, 0, false),
                                                node(ExprCore::Ix { index: 2 }, 0, false),
                                            ],
                                        },
                                        0,
                                        false,
                                    ),
                                },
                                0,
                                false,
                            )),
                        ],
                        active: node(
                            ExprCore::Opaque {
                                name: "C".to_owned(),
                            },
                            0,
                            false,
                        ),
                    },
                },
                0,
                false,
            ),
            vec![],
            vec![Selector::Number(2)],
            "ok: Quant[Forall x:Constant](Apply(Ix[1], Ix[1], Internal[Eq]))!",
        );
    }

    #[test]
    fn label_selector_args_shift() {
        check(
            node(
                ExprCore::Let {
                    definitions: vec![operator(
                        "F",
                        node(
                            ExprCore::Opaque {
                                name: "f".to_owned(),
                            },
                            0,
                            false,
                        ),
                    )],
                    body: node(
                        ExprCore::Quant {
                            quantifier: Quantifier::Forall,
                            bounds: vec![bound("x", None)],
                            body: node(
                                ExprCore::Parens {
                                    expression: node(
                                        ExprCore::Apply {
                                            operator: node(
                                                ExprCore::Internal {
                                                    builtin: Builtin::Eq,
                                                },
                                                0,
                                                false,
                                            ),
                                            args: vec![
                                                node(ExprCore::Ix { index: 1 }, 0, false),
                                                node(ExprCore::Ix { index: 2 }, 0, false),
                                            ],
                                        },
                                        0,
                                        false,
                                    ),
                                    form: xlabel("lb", &[("x", 1)]),
                                },
                                0,
                                false,
                            ),
                        },
                        0,
                        false,
                    ),
                },
                33,
                false,
            ),
            vec![],
            vec![
                Selector::Number(1),
                Selector::Label {
                    label: "lb".to_owned(),
                    args: vec![node(ExprCore::Ix { index: 3 }, 0, false)],
                },
            ],
            "warn stderr: <unknown location>:\nError: Could not find label lb\nok: Let[F](Opaque[f], Opaque[$Bad])!",
        );
    }
}
