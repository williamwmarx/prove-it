//! tlapm's E_subst: substitutions for de Bruijn indices, applied to every part of an expression.
//! A port of `src/obligations/substitution.ts`.
//!
//! A substitution is persistent and shares its tail, as the TypeScript objects do, so it is an
//! `Rc` that clones cheaply. Shifts may be negative, so their amounts are `isize`; an index that
//! a substitution leaves below zero, which the TypeScript would build silently, is a bug here.

use std::rc::Rc;

use crate::errors::{ObligationError, Result};
use crate::expression::{
    Bound, CaseArm, Defn, DefnCore, Expr, ExprCore, ExprNode, Field, Hyp, HypCore,
    InstanceDefinition, Sequent, at, map_accumulate, map_bound_domains, map_defn_body,
    map_except_specs, map_selector_args, strip_props,
};

pub type Substitution = Rc<SubstitutionNode>;

#[derive(Debug)]
pub enum SubstitutionNode {
    Shift {
        amount: isize,
    },
    Cons {
        expression: Expr,
        rest: Substitution,
    },
    Compose {
        outer: Substitution,
        inner: Substitution,
    },
    Bump {
        amount: usize,
        rest: Substitution,
    },
}

pub fn shift(amount: isize) -> Substitution {
    Rc::new(SubstitutionNode::Shift { amount })
}

pub fn cons_substitution(expression: Expr, rest: Substitution) -> Substitution {
    Rc::new(SubstitutionNode::Cons { expression, rest })
}

/// Binds the expressions in order, so the last one becomes index 1.
pub fn cons_all(expressions: &[Expr], rest: Substitution) -> Substitution {
    expressions.iter().fold(rest, |inner, expression| {
        cons_substitution(expression.clone(), inner)
    })
}

pub fn bump_by(amount: usize, substitution: &Substitution) -> Substitution {
    match &**substitution {
        SubstitutionNode::Bump {
            amount: bumped,
            rest,
        } => Rc::new(SubstitutionNode::Bump {
            amount: bumped + amount,
            rest: rest.clone(),
        }),
        _ => Rc::new(SubstitutionNode::Bump {
            amount,
            rest: substitution.clone(),
        }),
    }
}

/// What `applyIndex` gives: an `Ix` carrying the properties of `from`, kept as a bare index until
/// the end because the TypeScript passes indices below one through a bump or a composition, which
/// may take them back up, or another expression.
enum Applied {
    Index(isize),
    Expression(Expr),
}

impl Applied {
    fn into_expr(self, from: &ExprNode) -> Result<Expr> {
        match self {
            Self::Index(index) => {
                let index =
                    usize::try_from(index).map_err(|_| ObligationError::assert_failure())?;
                Ok(at(ExprCore::Ix { index }, from))
            }
            Self::Expression(expression) => Ok(expression),
        }
    }
}

fn apply_index(substitution: &Substitution, index: isize, from: &ExprNode) -> Result<Applied> {
    match &**substitution {
        SubstitutionNode::Shift { amount } => Ok(Applied::Index(amount + index)),
        SubstitutionNode::Cons { expression, rest } => {
            if index == 1 {
                Ok(Applied::Expression(at(
                    strip_props(expression).core.clone(),
                    from,
                )))
            } else {
                apply_index(rest, index - 1, from)
            }
        }
        // Substituting into `Ix i @@ from` is applying the index to `from`.
        SubstitutionNode::Compose { outer, inner } => match apply_index(inner, index, from)? {
            Applied::Index(inner_index) => apply_index(outer, inner_index, from),
            Applied::Expression(expression) => {
                Ok(Applied::Expression(substitute_expr(outer, &expression)?))
            }
        },
        SubstitutionNode::Bump { amount, rest } => {
            let amount = isize::try_from(*amount).map_err(|_| ObligationError::assert_failure())?;
            if index <= amount {
                return Ok(Applied::Index(index));
            }
            match apply_index(rest, index - amount, from)? {
                Applied::Index(inner_index) => Ok(Applied::Index(amount + inner_index)),
                Applied::Expression(expression) => Ok(Applied::Expression(substitute_expr(
                    &shift(amount),
                    &expression,
                )?)),
            }
        }
    }
}

pub fn substitute_exprs(substitution: &Substitution, expressions: &[Expr]) -> Result<Vec<Expr>> {
    expressions
        .iter()
        .map(|expression| substitute_expr(substitution, expression))
        .collect()
}

/// Beta-reduces a lambda applied to arguments, as E_subst.normalize does.
pub fn normalize_apply(operator: &Expr, args: Vec<Expr>) -> Result<ExprCore> {
    match &operator.core {
        ExprCore::Lambda { params, body } => {
            if params.len() != args.len() {
                return Err(ObligationError::proof("Arity mismatch"));
            }
            Ok(
                strip_props(&substitute_expr(&cons_all(&args, shift(0)), body)?)
                    .core
                    .clone(),
            )
        }
        ExprCore::Apply {
            operator: inner,
            args: inner_args,
        } => Ok(ExprCore::Apply {
            operator: inner.clone(),
            args: inner_args.iter().cloned().chain(args).collect(),
        }),
        _ if args.is_empty() => Ok(strip_props(operator).core.clone()),
        _ => Ok(ExprCore::Apply {
            operator: operator.clone(),
            args,
        }),
    }
}

pub fn substitute_bounds(
    substitution: &Substitution,
    bounds: &[Bound],
) -> Result<(Substitution, Vec<Bound>)> {
    Ok((
        bump_by(bounds.len(), substitution),
        map_bound_domains(bounds, &mut |domain| substitute_expr(substitution, domain))?,
    ))
}

pub fn substitute_defn(substitution: &Substitution, definition: &Defn) -> Result<Defn> {
    match &definition.core {
        DefnCore::Recursive { .. } | DefnCore::Operator { .. } | DefnCore::Bpragma { .. } => {
            map_defn_body(definition, &mut |body| substitute_expr(substitution, body))
        }
        DefnCore::Instance { name, instance } => {
            let inner = bump_by(instance.args.len(), substitution);
            let substitutions = instance
                .substitutions
                .iter()
                .map(|entry| {
                    Ok(crate::expression::Substitution {
                        name: entry.name.clone(),
                        expression: substitute_expr(&inner, &entry.expression)?,
                    })
                })
                .collect::<Result<_>>()?;
            Ok(Defn {
                core: DefnCore::Instance {
                    name: name.clone(),
                    instance: InstanceDefinition {
                        substitutions,
                        ..instance.clone()
                    },
                },
                location: definition.location.clone(),
            })
        }
    }
}

pub fn substitute_hyp(substitution: &Substitution, hyp: &Hyp) -> Result<Hyp> {
    match &hyp.core {
        HypCore::Fresh {
            name,
            shape,
            level,
            domain: Some(domain),
            domain_visibility,
        } => Ok(hyp.with_core(HypCore::Fresh {
            name: name.clone(),
            shape: *shape,
            level: *level,
            domain: Some(substitute_expr(substitution, domain)?),
            domain_visibility: *domain_visibility,
        })),
        HypCore::Fresh { .. } | HypCore::Flex { .. } => Ok(hyp.clone()),
        HypCore::Defn {
            definition,
            where_defined,
            visibility,
            is_local,
            is_constness_unset,
        } => Ok(hyp.with_core(HypCore::Defn {
            definition: substitute_defn(substitution, definition)?,
            where_defined: *where_defined,
            visibility: *visibility,
            is_local: *is_local,
            is_constness_unset: *is_constness_unset,
        })),
        HypCore::Fact {
            expression,
            visibility,
            time,
            use_location,
        } => Ok(hyp.with_core(HypCore::Fact {
            expression: substitute_expr(substitution, expression)?,
            visibility: *visibility,
            time: *time,
            use_location: use_location.clone(),
        })),
    }
}

pub fn substitute_sequent(substitution: &Substitution, sequent: &Sequent) -> Result<Sequent> {
    let (inner, context) =
        map_accumulate(substitution.clone(), &sequent.context, |current, hyp| {
            let next = bump_by(1, &current);
            Ok((next, substitute_hyp(&current, hyp)?))
        })?;
    Ok(Sequent {
        context,
        active: substitute_expr(&inner, &sequent.active)?,
    })
}

pub fn substitute_expr(substitution: &Substitution, expression: &Expr) -> Result<Expr> {
    let recurse = |inner: &Expr| substitute_expr(substitution, inner);
    let core = match &expression.core {
        ExprCore::Internal { .. }
        | ExprCore::Opaque { .. }
        | ExprCore::String { .. }
        | ExprCore::Num { .. }
        | ExprCore::At { .. } => return Ok(expression.clone()),
        ExprCore::Ix { index } => {
            let index = isize::try_from(*index).map_err(|_| ObligationError::assert_failure())?;
            return apply_index(substitution, index, expression)?.into_expr(expression);
        }
        ExprCore::Apply { operator, args } => {
            let operator = recurse(operator)?;
            return Ok(at(
                normalize_apply(&operator, substitute_exprs(substitution, args)?)?,
                expression,
            ));
        }
        ExprCore::Bang {
            expression: inner,
            selectors,
        } => ExprCore::Bang {
            expression: recurse(inner)?,
            selectors: selectors
                .iter()
                .map(|selector| map_selector_args(selector, &mut |arg| recurse(arg)))
                .collect::<Result<_>>()?,
        },
        ExprCore::Lambda { params, body } => ExprCore::Lambda {
            params: params.clone(),
            body: substitute_expr(&bump_by(params.len(), substitution), body)?,
        },
        ExprCore::Let { definitions, body } => {
            let (inner, definitions) =
                map_accumulate(substitution.clone(), definitions, |current, definition| {
                    let next = bump_by(1, &current);
                    Ok((next, substitute_defn(&current, definition)?))
                })?;
            ExprCore::Let {
                definitions,
                body: substitute_expr(&inner, body)?,
            }
        }
        ExprCore::Sequent { sequent } => ExprCore::Sequent {
            sequent: substitute_sequent(substitution, sequent)?,
        },
        ExprCore::With {
            expression: inner,
            method,
        } => ExprCore::With {
            expression: recurse(inner)?,
            method: method.clone(),
        },
        ExprCore::Dot {
            expression: inner,
            field,
        } => ExprCore::Dot {
            expression: recurse(inner)?,
            field: field.clone(),
        },
        ExprCore::Parens {
            expression: inner,
            form,
        } => ExprCore::Parens {
            expression: recurse(inner)?,
            form: form.clone(),
        },
        ExprCore::If {
            condition,
            consequent,
            alternative,
        } => ExprCore::If {
            condition: recurse(condition)?,
            consequent: recurse(consequent)?,
            alternative: recurse(alternative)?,
        },
        ExprCore::List { bullet, items } => ExprCore::List {
            bullet: *bullet,
            items: substitute_exprs(substitution, items)?,
        },
        ExprCore::Quant {
            quantifier,
            bounds,
            body,
        } => {
            let (inner, bounds) = substitute_bounds(substitution, bounds)?;
            ExprCore::Quant {
                quantifier: *quantifier,
                bounds,
                body: substitute_expr(&inner, body)?,
            }
        }
        ExprCore::Fcn { bounds, body } => {
            let (inner, bounds) = substitute_bounds(substitution, bounds)?;
            ExprCore::Fcn {
                bounds,
                body: substitute_expr(&inner, body)?,
            }
        }
        ExprCore::Tquant {
            quantifier,
            names,
            body,
        } => ExprCore::Tquant {
            quantifier: *quantifier,
            names: names.clone(),
            body: substitute_expr(&bump_by(names.len(), substitution), body)?,
        },
        ExprCore::Choose { name, domain, body } => ExprCore::Choose {
            name: name.clone(),
            domain: domain.as_ref().map(recurse).transpose()?,
            body: substitute_expr(&bump_by(1, substitution), body)?,
        },
        ExprCore::SetSt { name, domain, body } => ExprCore::SetSt {
            name: name.clone(),
            domain: recurse(domain)?,
            body: substitute_expr(&bump_by(1, substitution), body)?,
        },
        ExprCore::SetOf { element, bounds } => {
            let (inner, bounds) = substitute_bounds(substitution, bounds)?;
            ExprCore::SetOf {
                bounds,
                element: substitute_expr(&inner, element)?,
            }
        }
        ExprCore::SetEnum { elements } => ExprCore::SetEnum {
            elements: substitute_exprs(substitution, elements)?,
        },
        ExprCore::Tuple { elements } => ExprCore::Tuple {
            elements: substitute_exprs(substitution, elements)?,
        },
        ExprCore::Arrow { domain, range } => ExprCore::Arrow {
            domain: recurse(domain)?,
            range: recurse(range)?,
        },
        ExprCore::FcnApp { function, args } => ExprCore::FcnApp {
            function: recurse(function)?,
            args: substitute_exprs(substitution, args)?,
        },
        ExprCore::Product { factors } => ExprCore::Product {
            factors: substitute_exprs(substitution, factors)?,
        },
        ExprCore::Rect { fields } => ExprCore::Rect {
            fields: substitute_fields(substitution, fields)?,
        },
        ExprCore::Record { fields } => ExprCore::Record {
            fields: substitute_fields(substitution, fields)?,
        },
        ExprCore::Except { function, specs } => ExprCore::Except {
            function: recurse(function)?,
            specs: map_except_specs(specs, &mut |inner| recurse(inner))?,
        },
        ExprCore::Sub {
            modal,
            action,
            subscript,
        } => ExprCore::Sub {
            modal: *modal,
            action: recurse(action)?,
            subscript: recurse(subscript)?,
        },
        ExprCore::Tsub {
            modal,
            action,
            subscript,
        } => ExprCore::Tsub {
            modal: *modal,
            action: recurse(action)?,
            subscript: recurse(subscript)?,
        },
        ExprCore::Fair {
            fairness,
            subscript,
            action,
        } => ExprCore::Fair {
            fairness: *fairness,
            action: recurse(action)?,
            subscript: recurse(subscript)?,
        },
        ExprCore::Case { arms, other } => ExprCore::Case {
            arms: arms
                .iter()
                .map(|arm| {
                    Ok(CaseArm {
                        condition: recurse(&arm.condition)?,
                        body: recurse(&arm.body)?,
                    })
                })
                .collect::<Result<_>>()?,
            other: other.as_ref().map(recurse).transpose()?,
        },
    };
    Ok(expression.with_core(core))
}

fn substitute_fields(substitution: &Substitution, fields: &[Field]) -> Result<Vec<Field>> {
    fields
        .iter()
        .map(|field| {
            Ok(Field {
                name: field.name.clone(),
                value: substitute_expr(substitution, &field.value)?,
            })
        })
        .collect()
}

pub fn shift_expr(amount: isize, expression: &Expr) -> Result<Expr> {
    if amount == 0 {
        Ok(expression.clone())
    } else {
        substitute_expr(&shift(amount), expression)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expression::{
        Bound, BoundDomain, Bullet, ExceptPoint, ExceptSpec, Fairness, HypNode, Level, Locus,
        Modal, Param, ParenForm, Quantifier, Selector, Time, Visibility, WhereDefined, expr,
        located,
    };
    use crate::pragma::OldMethod;

    // The expected text is what `src/obligations/substitution.ts` gives under Bun for the same
    // inputs, printed by the same printer.

    fn show_props(location: Option<&Locus>, is_atomic: bool) -> String {
        let line = location.map_or_else(String::new, |locus| format!("@{}", locus.start_line));
        format!("{line}{}", if is_atomic { "!" } else { "" })
    }

    fn show_list(items: &[Expr]) -> String {
        items.iter().map(show).collect::<Vec<_>>().join(" ")
    }

    fn show_bounds(bounds: &[Bound]) -> String {
        bounds
            .iter()
            .map(|bound| match &bound.domain {
                BoundDomain::Domain(domain) => format!("{}:{}", bound.name, show(domain)),
                BoundDomain::Ditto => format!("{}:ditto", bound.name),
                BoundDomain::NoDomain => bound.name.clone(),
            })
            .collect::<Vec<_>>()
            .join(" ")
    }

    fn show_defn(definition: &Defn) -> String {
        let body = match &definition.core {
            DefnCore::Recursive { name, .. } => format!("(rec {name})"),
            DefnCore::Operator { name, body } => format!("(def {name} {})", show(body)),
            DefnCore::Bpragma { name, body, .. } => format!("(bpragma {name} {})", show(body)),
            DefnCore::Instance { name, instance } => format!(
                "(instance {name} [{}] {})",
                instance.args.join(" "),
                instance
                    .substitutions
                    .iter()
                    .map(|entry| format!("{}<-{}", entry.name, show(&entry.expression)))
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
        };
        body + &show_props(definition.location.as_ref(), false)
    }

    fn show_hyp(hyp: &Hyp) -> String {
        let body = match &hyp.core {
            HypCore::Fresh { name, domain, .. } => match domain {
                Some(domain) => format!("(fresh {name} {})", show(domain)),
                None => format!("(fresh {name})"),
            },
            HypCore::Flex { name } => format!("(flex {name})"),
            HypCore::Defn {
                definition,
                visibility,
                ..
            } => format!("(defn {visibility:?} {})", show_defn(definition)),
            HypCore::Fact {
                expression,
                visibility,
                ..
            } => format!("(fact {visibility:?} {})", show(expression)),
        };
        body + &show_props(hyp.location.as_ref(), false)
    }

    fn show_sequent(sequent: &Sequent) -> String {
        format!(
            "(sequent [{}] {})",
            sequent
                .context
                .iter()
                .map(show_hyp)
                .collect::<Vec<_>>()
                .join(" "),
            show(&sequent.active)
        )
    }

    fn show_fields(fields: &[Field]) -> String {
        fields
            .iter()
            .map(|field| format!("{}={}", field.name, show(&field.value)))
            .collect::<Vec<_>>()
            .join(" ")
    }

    fn show(expression: &Expr) -> String {
        let body = match &expression.core {
            ExprCore::Ix { index } => format!("#{index}"),
            ExprCore::Opaque { name } => name.clone(),
            ExprCore::Internal { builtin } => format!("${}", builtin.name()),
            ExprCore::Lambda { params, body } => format!(
                "(lambda [{}] {})",
                params
                    .iter()
                    .map(|param| param.name.clone())
                    .collect::<Vec<_>>()
                    .join(" "),
                show(body)
            ),
            ExprCore::Sequent { sequent } => show_sequent(sequent),
            ExprCore::Bang {
                expression: inner,
                selectors,
            } => format!(
                "(bang {} {})",
                show(inner),
                selectors
                    .iter()
                    .map(|selector| match selector {
                        Selector::Instance(args) => format!("(inst {})", show_list(args)),
                        Selector::Label { label, args } => {
                            format!("(label {label} {})", show_list(args))
                        }
                        Selector::Down => "Down".to_owned(),
                        Selector::Number(_) => "Number".to_owned(),
                        Selector::Left => "Left".to_owned(),
                        Selector::Right => "Right".to_owned(),
                        Selector::At => "At".to_owned(),
                    })
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
            ExprCore::Apply { operator, args } => {
                format!("({} {})", show(operator), show_list(args))
            }
            ExprCore::With {
                expression: inner, ..
            } => format!("(with {})", show(inner)),
            ExprCore::If {
                condition,
                consequent,
                alternative,
            } => format!(
                "(if {} {} {})",
                show(condition),
                show(consequent),
                show(alternative)
            ),
            ExprCore::List { bullet, items } => {
                format!("(list {bullet:?} {})", show_list(items))
            }
            ExprCore::Let { definitions, body } => format!(
                "(let [{}] {})",
                definitions
                    .iter()
                    .map(show_defn)
                    .collect::<Vec<_>>()
                    .join(" "),
                show(body)
            ),
            ExprCore::Quant {
                quantifier,
                bounds,
                body,
            } => format!("({quantifier:?} [{}] {})", show_bounds(bounds), show(body)),
            ExprCore::Tquant {
                quantifier,
                names,
                body,
            } => format!("(t{quantifier:?} [{}] {})", names.join(" "), show(body)),
            ExprCore::Choose { name, domain, body } => match domain {
                Some(domain) => format!("(choose {name}:{} {})", show(domain), show(body)),
                None => format!("(choose {name} {})", show(body)),
            },
            ExprCore::SetSt { name, domain, body } => {
                format!("(setst {name}:{} {})", show(domain), show(body))
            }
            ExprCore::SetOf { element, bounds } => {
                format!("(setof {} [{}])", show(element), show_bounds(bounds))
            }
            ExprCore::SetEnum { elements } => format!("(setenum {})", show_list(elements)),
            ExprCore::Product { factors } => format!("(product {})", show_list(factors)),
            ExprCore::Tuple { elements } => format!("(tuple {})", show_list(elements)),
            ExprCore::Fcn { bounds, body } => {
                format!("(fcn [{}] {})", show_bounds(bounds), show(body))
            }
            ExprCore::FcnApp { function, args } => {
                format!("(fcnapp {} {})", show(function), show_list(args))
            }
            ExprCore::Arrow { domain, range } => {
                format!("(arrow {} {})", show(domain), show(range))
            }
            ExprCore::Rect { fields } => format!("(rect {})", show_fields(fields)),
            ExprCore::Record { fields } => format!("(record {})", show_fields(fields)),
            ExprCore::Except { function, specs } => format!(
                "(except {} {})",
                show(function),
                specs
                    .iter()
                    .map(|spec| format!(
                        "[{}]={}",
                        spec.trail
                            .iter()
                            .map(|point| match point {
                                ExceptPoint::Dot(field) => format!(".{field}"),
                                ExceptPoint::Apply(inner) => show(inner),
                            })
                            .collect::<Vec<_>>()
                            .join(" "),
                        show(&spec.value)
                    ))
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
            ExprCore::Dot {
                expression: inner,
                field,
            } => format!("(dot {} {field})", show(inner)),
            ExprCore::Sub {
                modal,
                action,
                subscript,
            } => format!("(sub {modal:?} {} {})", show(action), show(subscript)),
            ExprCore::Tsub {
                modal,
                action,
                subscript,
            } => format!("(tsub {modal:?} {} {})", show(action), show(subscript)),
            ExprCore::Fair {
                fairness,
                subscript,
                action,
            } => format!("(fair {fairness:?} {} {})", show(action), show(subscript)),
            ExprCore::Case { arms, other } => format!(
                "(case {}{})",
                arms.iter()
                    .map(|arm| format!("{}->{}", show(&arm.condition), show(&arm.body)))
                    .collect::<Vec<_>>()
                    .join(" "),
                other
                    .as_ref()
                    .map_or_else(String::new, |other| format!(" other->{}", show(other)))
            ),
            ExprCore::String { value } => format!("{value:?}"),
            ExprCore::Num { integer, fraction } => format!("{integer}.{fraction}"),
            ExprCore::At { is_except } => format!("@{is_except}"),
            ExprCore::Parens {
                expression: inner, ..
            } => format!("(parens {})", show(inner)),
        };
        body + &show_props(expression.location.as_ref(), expression.is_atomic)
    }

    fn attempt(result: Result<Expr>) -> String {
        result.map_or_else(
            |error| format!("error {}: {}", error.name(), error.message()),
            |expression| show(&expression),
        )
    }

    fn locus(line: u32) -> Option<Locus> {
        Some(Locus {
            file: Rc::from("f"),
            start_line: line,
            start_column: 1,
            end_line: line,
            end_column: 2,
        })
    }

    fn ix(index: usize) -> Expr {
        expr(ExprCore::Ix { index })
    }

    fn located_ix(index: usize, line: u32) -> Expr {
        located(ExprCore::Ix { index }, locus(line))
    }

    fn opaque(name: &str) -> Expr {
        expr(ExprCore::Opaque {
            name: name.to_owned(),
        })
    }

    fn apply(operator: Expr, args: Vec<Expr>) -> Expr {
        expr(ExprCore::Apply { operator, args })
    }

    fn lambda_core(names: &[&str], body: Expr) -> ExprCore {
        ExprCore::Lambda {
            params: names
                .iter()
                .map(|name| Param {
                    name: (*name).to_owned(),
                    shape: 0,
                    location: None,
                })
                .collect(),
            body,
        }
    }

    fn lambda(names: &[&str], body: Expr) -> Expr {
        expr(lambda_core(names, body))
    }

    fn bound(name: &str, domain: BoundDomain) -> Bound {
        Bound {
            name: name.to_owned(),
            level: Level::Constant,
            domain,
        }
    }

    fn with_domain(name: &str, domain: Expr) -> Bound {
        bound(name, BoundDomain::Domain(domain))
    }

    fn operator_defn(name: &str, body: Expr) -> Defn {
        Defn {
            core: DefnCore::Operator {
                name: name.to_owned(),
                body,
            },
            location: None,
        }
    }

    fn instance_defn() -> Defn {
        Defn {
            core: DefnCore::Instance {
                name: "I".to_owned(),
                instance: InstanceDefinition {
                    args: vec!["a".to_owned(), "b".to_owned()],
                    module: "M".to_owned(),
                    substitutions: vec![
                        crate::expression::Substitution {
                            name: "c".to_owned(),
                            expression: ix(1),
                        },
                        crate::expression::Substitution {
                            name: "d".to_owned(),
                            expression: ix(4),
                        },
                    ],
                    location: None,
                },
            },
            location: locus(9),
        }
    }

    fn fresh(name: &str, domain: Option<Expr>) -> Hyp {
        crate::expression::hyp(HypCore::Fresh {
            name: name.to_owned(),
            shape: 0,
            level: Level::Constant,
            domain,
            domain_visibility: Visibility::Visible,
        })
    }

    fn fact(expression: Expr, visibility: Visibility) -> Hyp {
        Rc::new(HypNode {
            core: HypCore::Fact {
                expression,
                visibility,
                time: Time::Now,
                use_location: None,
            },
            location: locus(11),
        })
    }

    fn defn_hyp(definition: Defn, visibility: Visibility) -> Hyp {
        crate::expression::hyp(HypCore::Defn {
            definition,
            where_defined: WhereDefined::User,
            visibility,
            is_local: false,
            is_constness_unset: true,
        })
    }

    /// Every binder kind, the hidden hypotheses of a sequent included.
    fn sequent() -> Sequent {
        Sequent {
            context: vec![
                fresh("x", Some(ix(1))),
                crate::expression::hyp(HypCore::Flex {
                    name: "v".to_owned(),
                }),
                defn_hyp(
                    operator_defn("D", apply(ix(2), vec![ix(5)])),
                    Visibility::Hidden,
                ),
                fact(ix(3), Visibility::Hidden),
                fact(ix(7), Visibility::Visible),
                fresh("y", None),
                defn_hyp(instance_defn(), Visibility::Visible),
            ],
            active: apply(ix(1), vec![ix(7), ix(8), ix(9)]),
        }
    }

    fn everything() -> Vec<Expr> {
        vec![
            ix(1),
            ix(2),
            ix(3),
            ix(4),
            located_ix(1, 5),
            located_ix(3, 6),
            Rc::new(ExprNode {
                core: ExprCore::Ix { index: 2 },
                location: None,
                is_atomic: true,
            }),
            opaque("o"),
            expr(ExprCore::Internal {
                builtin: crate::expression::Builtin::TRUE,
            }),
            expr(ExprCore::String {
                value: "s".to_owned(),
            }),
            expr(ExprCore::Num {
                integer: "1".to_owned(),
                fraction: "5".to_owned(),
            }),
            expr(ExprCore::At { is_except: true }),
            lambda(
                &["p", "q"],
                apply(opaque("f"), vec![ix(1), ix(2), ix(3), ix(4)]),
            ),
            located(
                ExprCore::Quant {
                    quantifier: Quantifier::Forall,
                    bounds: vec![
                        with_domain("a", ix(1)),
                        bound("b", BoundDomain::Ditto),
                        bound("c", BoundDomain::NoDomain),
                    ],
                    body: apply(ix(1), vec![ix(3), ix(4), ix(5)]),
                },
                locus(4),
            ),
            expr(ExprCore::Fcn {
                bounds: vec![with_domain("a", ix(2))],
                body: apply(ix(1), vec![ix(2)]),
            }),
            expr(ExprCore::SetOf {
                element: apply(ix(2), vec![ix(1), ix(3)]),
                bounds: vec![with_domain("a", ix(1)), bound("b", BoundDomain::NoDomain)],
            }),
            expr(ExprCore::Let {
                definitions: vec![
                    operator_defn("A", ix(1)),
                    Defn {
                        core: DefnCore::Recursive {
                            name: "R".to_owned(),
                            shape: 1,
                        },
                        location: None,
                    },
                    instance_defn(),
                    Defn {
                        core: DefnCore::Bpragma {
                            name: "B".to_owned(),
                            body: apply(ix(1), vec![ix(3), ix(4)]),
                            methods: Vec::new(),
                        },
                        location: None,
                    },
                ],
                body: apply(ix(1), vec![ix(4), ix(5), ix(6)]),
            }),
            expr(ExprCore::Sequent { sequent: sequent() }),
            expr(ExprCore::Choose {
                name: "c".to_owned(),
                domain: Some(ix(1)),
                body: apply(ix(1), vec![ix(2)]),
            }),
            expr(ExprCore::Choose {
                name: "c".to_owned(),
                domain: None,
                body: ix(2),
            }),
            expr(ExprCore::SetSt {
                name: "s".to_owned(),
                domain: ix(2),
                body: apply(ix(1), vec![ix(2), ix(3)]),
            }),
            expr(ExprCore::Tquant {
                quantifier: Quantifier::Exists,
                names: vec!["u".to_owned(), "w".to_owned()],
                body: apply(ix(1), vec![ix(2), ix(3)]),
            }),
            expr(ExprCore::Bang {
                expression: ix(1),
                selectors: vec![
                    Selector::Down,
                    Selector::Instance(vec![ix(2)]),
                    Selector::Label {
                        label: "L".to_owned(),
                        args: vec![ix(3)],
                    },
                    Selector::Number(2),
                ],
            }),
            expr(ExprCore::If {
                condition: ix(1),
                consequent: ix(2),
                alternative: ix(3),
            }),
            expr(ExprCore::List {
                bullet: Bullet::And,
                items: vec![ix(1), ix(2)],
            }),
            expr(ExprCore::SetEnum {
                elements: vec![ix(1), opaque("o")],
            }),
            expr(ExprCore::Tuple {
                elements: vec![ix(2)],
            }),
            expr(ExprCore::Product {
                factors: vec![ix(1), ix(3)],
            }),
            expr(ExprCore::Arrow {
                domain: ix(1),
                range: ix(2),
            }),
            expr(ExprCore::FcnApp {
                function: ix(1),
                args: vec![ix(2), ix(3)],
            }),
            expr(ExprCore::Rect {
                fields: vec![Field {
                    name: "a".to_owned(),
                    value: ix(1),
                }],
            }),
            expr(ExprCore::Record {
                fields: vec![
                    Field {
                        name: "a".to_owned(),
                        value: ix(2),
                    },
                    Field {
                        name: "b".to_owned(),
                        value: ix(3),
                    },
                ],
            }),
            expr(ExprCore::Except {
                function: ix(1),
                specs: vec![ExceptSpec {
                    trail: vec![ExceptPoint::Dot("f".to_owned()), ExceptPoint::Apply(ix(2))],
                    value: ix(3),
                }],
            }),
            expr(ExprCore::Dot {
                expression: ix(1),
                field: "g".to_owned(),
            }),
            expr(ExprCore::With {
                expression: ix(2),
                method: OldMethod {
                    name: "zenon".to_owned(),
                    tactic: None,
                    timeout: None,
                },
            }),
            expr(ExprCore::Parens {
                expression: ix(3),
                form: ParenForm::Syntax,
            }),
            expr(ExprCore::Sub {
                modal: Modal::Box,
                action: ix(1),
                subscript: ix(2),
            }),
            expr(ExprCore::Tsub {
                modal: Modal::Dia,
                action: ix(2),
                subscript: ix(3),
            }),
            expr(ExprCore::Fair {
                fairness: Fairness::Weak,
                subscript: ix(1),
                action: ix(2),
            }),
            expr(ExprCore::Case {
                arms: vec![CaseArm {
                    condition: ix(1),
                    body: ix(2),
                }],
                other: Some(ix(3)),
            }),
            expr(ExprCore::Case {
                arms: vec![CaseArm {
                    condition: ix(3),
                    body: ix(1),
                }],
                other: None,
            }),
            apply(
                located(
                    lambda_core(&["p", "q"], apply(ix(1), vec![ix(2), ix(3)])),
                    locus(7),
                ),
                vec![opaque("a"), located_ix(1, 8)],
            ),
            apply(apply(opaque("f"), vec![ix(1)]), vec![ix(2)]),
            apply(ix(1), vec![ix(2)]),
            located(
                ExprCore::Apply {
                    operator: ix(2),
                    args: Vec::new(),
                },
                locus(3),
            ),
        ]
    }

    fn substitute_everything(substitution: &Substitution) -> String {
        everything()
            .iter()
            .map(|expression| attempt(substitute_expr(substitution, expression)))
            .collect::<Vec<_>>()
            .join("\n")
    }

    #[test]
    fn shifts_by_zero() {
        assert_eq!(substitute_everything(&shift(0)), SHIFT_0);
    }

    #[test]
    fn shifts_up() {
        assert_eq!(substitute_everything(&shift(2)), SHIFT_2);
    }

    #[test]
    fn shifts_down() {
        assert_eq!(substitute_everything(&shift(-1)), SHIFT_NEG_1);
    }

    #[test]
    fn substitutes_conses() {
        let substitution = cons_all(
            &[
                located(
                    ExprCore::Opaque {
                        name: "a".to_owned(),
                    },
                    locus(1),
                ),
                lambda(&["z"], apply(ix(1), vec![ix(2)])),
            ],
            shift(0),
        );
        assert_eq!(substitute_everything(&substitution), CONS);
    }

    #[test]
    fn substitutes_a_cons_over_a_shift() {
        let substitution = cons_substitution(apply(opaque("g"), vec![ix(1)]), shift(3));
        assert_eq!(substitute_everything(&substitution), CONS_SHIFT);
    }

    #[test]
    fn substitutes_compositions() {
        let substitution = Rc::new(SubstitutionNode::Compose {
            outer: shift(1),
            inner: bump_by(1, &cons_substitution(ix(5), shift(0))),
        });
        assert_eq!(substitute_everything(&substitution), COMPOSE);
    }

    #[test]
    fn merges_bumps() {
        let substitution = bump_by(2, &bump_by(1, &shift(3)));
        assert!(matches!(
            &*substitution,
            SubstitutionNode::Bump { amount: 3, rest }
                if matches!(**rest, SubstitutionNode::Shift { amount: 3 })
        ));
        assert_eq!(substitute_everything(&substitution), BUMP);
    }

    #[test]
    fn bumps_conses() {
        let substitution = bump_by(1, &cons_all(&[opaque("x"), opaque("y")], shift(-2)));
        assert_eq!(substitute_everything(&substitution), BUMP_CONS);
    }

    #[test]
    fn substitutes_lists() {
        let substituted =
            substitute_exprs(&shift(1), &[ix(1), ix(2)]).map(|items| show_list(&items));
        assert_eq!(substituted.as_deref(), Ok("#2 #3"));
    }

    #[test]
    fn substitutes_bounds() -> Result<()> {
        let (inner, bounds) = substitute_bounds(
            &cons_substitution(opaque("k"), shift(0)),
            &[
                with_domain("a", ix(1)),
                bound("b", BoundDomain::Ditto),
                with_domain("c", ix(2)),
            ],
        )?;
        assert_eq!(show_bounds(&bounds), "a:k b:ditto c:#1");
        let body = substitute_expr(&inner, &apply(ix(1), vec![ix(2), ix(3), ix(4), ix(5)]))?;
        assert_eq!(show(&body), "(#1 #2 #3 k #4)");
        Ok(())
    }

    #[test]
    fn substitutes_definitions() -> Result<()> {
        assert_eq!(
            show_defn(&substitute_defn(&shift(1), &instance_defn())?),
            "(instance I [a b] c<-#1 d<-#5)@9"
        );
        let recursive = Defn {
            core: DefnCore::Recursive {
                name: "R".to_owned(),
                shape: 0,
            },
            location: locus(2),
        };
        assert_eq!(
            show_defn(&substitute_defn(&shift(1), &recursive)?),
            "(rec R)@2"
        );
        let operator = Defn {
            location: locus(2),
            ..operator_defn("O", ix(1))
        };
        assert_eq!(
            show_defn(&substitute_defn(&shift(1), &operator)?),
            "(def O #2)@2"
        );
        Ok(())
    }

    #[test]
    fn substitutes_hypotheses() -> Result<()> {
        let shown = sequent()
            .context
            .iter()
            .map(|hyp| Ok(show_hyp(&substitute_hyp(&shift(2), hyp)?)))
            .collect::<Result<Vec<_>>>()?;
        assert_eq!(
            shown,
            [
                "(fresh x #3)",
                "(flex v)",
                "(defn Hidden (def D (#4 #7)))",
                "(fact Hidden #5)@11",
                "(fact Visible #9)@11",
                "(fresh y)",
                "(defn Visible (instance I [a b] c<-#1 d<-#6)@9)",
            ]
        );
        let context = sequent().context;
        assert!(Rc::ptr_eq(
            &substitute_hyp(&shift(2), &context[1])?,
            &context[1]
        ));
        assert!(Rc::ptr_eq(
            &substitute_hyp(&shift(2), &context[5])?,
            &context[5]
        ));
        Ok(())
    }

    #[test]
    fn substitutes_sequents() -> Result<()> {
        let substituted =
            substitute_sequent(&cons_substitution(opaque("k"), shift(0)), &sequent())?;
        assert_eq!(
            show_sequent(&substituted),
            "(sequent [(fresh x k) (flex v) (defn Hidden (def D (#2 #4))) (fact Hidden #3)@11 \
             (fact Visible #6)@11 (fresh y) (defn Visible (instance I [a b] c<-#1 d<-#4)@9)] \
             (#1 #7 k #8))"
        );
        Ok(())
    }

    #[test]
    fn normalizes_applications() {
        let normalize =
            |operator: Expr, args: Vec<Expr>| attempt(normalize_apply(&operator, args).map(expr));
        assert_eq!(
            normalize(
                located(
                    ExprCore::Opaque {
                        name: "f".to_owned()
                    },
                    locus(1)
                ),
                Vec::new()
            ),
            "f"
        );
        assert_eq!(normalize(opaque("f"), vec![ix(1)]), "(f #1)");
        assert_eq!(
            normalize(apply(opaque("f"), vec![ix(1)]), vec![ix(2), ix(3)]),
            "(f #1 #2 #3)"
        );
        assert_eq!(
            normalize(lambda(&["p"], apply(ix(1), vec![ix(2)])), vec![opaque("a")]),
            "(a #1)"
        );
        assert_eq!(
            normalize(lambda(&["p"], ix(1)), vec![opaque("a"), opaque("b")]),
            "error TlaProofError: Arity mismatch"
        );
        assert_eq!(normalize(lambda(&[], ix(1)), Vec::new()), "#1");
    }

    #[test]
    fn shifts_expressions() -> Result<()> {
        let expression = located_ix(1, 4);
        assert!(Rc::ptr_eq(&shift_expr(0, &expression)?, &expression));
        assert_eq!(show(&shift_expr(0, &expression)?), "#1@4");
        assert_eq!(show(&shift_expr(3, &expression)?), "#4@4");
        assert_eq!(show(&shift_expr(-1, &ix(2))?), "#1");
        // The TypeScript builds `#-1` here, which no de Bruijn index can be.
        assert_eq!(
            attempt(shift_expr(-2, &ix(1))),
            "error TlaProofError: Oops, this seems to be a bug in TLAPM."
        );
        Ok(())
    }

    const SHIFT_0: &str = r#"#1
#2
#3
#4
#1@5
#3@6
#2!
o
$TRUE
"s"
1.5
@true
(lambda [p q] (f #1 #2 #3 #4))
(Forall [a:#1 b:ditto c] (#1 #3 #4 #5))@4
(fcn [a:#2] (#1 #2))
(setof (#2 #1 #3) [a:#1 b])
(let [(def A #1) (rec R) (instance I [a b] c<-#1 d<-#4)@9 (bpragma B (#1 #3 #4))] (#1 #4 #5 #6))
(sequent [(fresh x #1) (flex v) (defn Hidden (def D (#2 #5))) (fact Hidden #3)@11 (fact Visible #7)@11 (fresh y) (defn Visible (instance I [a b] c<-#1 d<-#4)@9)] (#1 #7 #8 #9))
(choose c:#1 (#1 #2))
(choose c #2)
(setst s:#2 (#1 #2 #3))
(tExists [u w] (#1 #2 #3))
(bang #1 Down (inst #2) (label L #3) Number)
(if #1 #2 #3)
(list And #1 #2)
(setenum #1 o)
(tuple #2)
(product #1 #3)
(arrow #1 #2)
(fcnapp #1 #2 #3)
(rect a=#1)
(record a=#2 b=#3)
(except #1 [.f #2]=#3)
(dot #1 g)
(with #2)
(parens #3)
(sub Box #1 #2)
(tsub Dia #2 #3)
(fair Weak #2 #1)
(case #1->#2 other->#3)
(case #3->#1)
(#1 a #1)
(f #1 #2)
(#1 #2)
#2@3"#;

    const SHIFT_2: &str = r#"#3
#4
#5
#6
#3@5
#5@6
#4!
o
$TRUE
"s"
1.5
@true
(lambda [p q] (f #1 #2 #5 #6))
(Forall [a:#3 b:ditto c] (#1 #3 #6 #7))@4
(fcn [a:#4] (#1 #4))
(setof (#2 #1 #5) [a:#3 b])
(let [(def A #3) (rec R) (instance I [a b] c<-#1 d<-#4)@9 (bpragma B (#1 #3 #6))] (#1 #4 #7 #8))
(sequent [(fresh x #3) (flex v) (defn Hidden (def D (#2 #7))) (fact Hidden #3)@11 (fact Visible #9)@11 (fresh y) (defn Visible (instance I [a b] c<-#1 d<-#4)@9)] (#1 #7 #10 #11))
(choose c:#3 (#1 #4))
(choose c #4)
(setst s:#4 (#1 #4 #5))
(tExists [u w] (#1 #2 #5))
(bang #3 Down (inst #4) (label L #5) Number)
(if #3 #4 #5)
(list And #3 #4)
(setenum #3 o)
(tuple #4)
(product #3 #5)
(arrow #3 #4)
(fcnapp #3 #4 #5)
(rect a=#3)
(record a=#4 b=#5)
(except #3 [.f #4]=#5)
(dot #3 g)
(with #4)
(parens #5)
(sub Box #3 #4)
(tsub Dia #4 #5)
(fair Weak #4 #3)
(case #3->#4 other->#5)
(case #5->#3)
(#3 a #3)
(f #3 #4)
(#3 #4)
#4@3"#;

    const SHIFT_NEG_1: &str = r#"#0
#1
#2
#3
#0@5
#2@6
#1!
o
$TRUE
"s"
1.5
@true
(lambda [p q] (f #1 #2 #2 #3))
(Forall [a:#0 b:ditto c] (#1 #3 #3 #4))@4
(fcn [a:#1] (#1 #1))
(setof (#2 #1 #2) [a:#0 b])
(let [(def A #0) (rec R) (instance I [a b] c<-#1 d<-#4)@9 (bpragma B (#1 #3 #3))] (#1 #4 #4 #5))
(sequent [(fresh x #0) (flex v) (defn Hidden (def D (#2 #4))) (fact Hidden #3)@11 (fact Visible #6)@11 (fresh y) (defn Visible (instance I [a b] c<-#1 d<-#4)@9)] (#1 #7 #7 #8))
(choose c:#0 (#1 #1))
(choose c #1)
(setst s:#1 (#1 #1 #2))
(tExists [u w] (#1 #2 #2))
(bang #0 Down (inst #1) (label L #2) Number)
(if #0 #1 #2)
(list And #0 #1)
(setenum #0 o)
(tuple #1)
(product #0 #2)
(arrow #0 #1)
(fcnapp #0 #1 #2)
(rect a=#0)
(record a=#1 b=#2)
(except #0 [.f #1]=#2)
(dot #0 g)
(with #1)
(parens #2)
(sub Box #0 #1)
(tsub Dia #1 #2)
(fair Weak #1 #0)
(case #0->#1 other->#2)
(case #2->#0)
(#0 a a)
(f #0 #1)
(#0 #1)
#1@3"#;

    const CONS: &str = r#"(lambda [z] (#1 #2))
a
#1
#2
(lambda [z] (#1 #2))@5
#1@6
a!
o
$TRUE
"s"
1.5
@true
(lambda [p q] (f #1 #2 (lambda [z] (#1 #4)) a))
(Forall [a:(lambda [z] (#1 #2)) b:ditto c] (#1 #3 (lambda [z] (#1 #5)) a))@4
(fcn [a:a] (#1 (lambda [z] (#1 #3))))
(setof (#2 #1 (lambda [z] (#1 #4))) [a:(lambda [z] (#1 #2)) b])
(let [(def A (lambda [z] (#1 #2))) (rec R) (instance I [a b] c<-#1 d<-#4)@9 (bpragma B (#1 #3 (lambda [z] (#1 #5))))] (#1 #4 (lambda [z] (#1 #6)) a))
(sequent [(fresh x (lambda [z] (#1 #2))) (flex v) (defn Hidden (def D (#2 #3))) (fact Hidden #3)@11 (fact Visible #5)@11 (fresh y) (defn Visible (instance I [a b] c<-#1 d<-#4)@9)] (#1 #7 (lambda [z] (#1 #9)) a))
(choose c:(lambda [z] (#1 #2)) (#1 (lambda [z] (#1 #3))))
(choose c (lambda [z] (#1 #3)))
(setst s:a (#1 (lambda [z] (#1 #3)) a))
(tExists [u w] (#1 #2 (lambda [z] (#1 #4))))
(bang (lambda [z] (#1 #2)) Down (inst a) (label L #1) Number)
(if (lambda [z] (#1 #2)) a #1)
(list And (lambda [z] (#1 #2)) a)
(setenum (lambda [z] (#1 #2)) o)
(tuple a)
(product (lambda [z] (#1 #2)) #1)
(arrow (lambda [z] (#1 #2)) a)
(fcnapp (lambda [z] (#1 #2)) a #1)
(rect a=(lambda [z] (#1 #2)))
(record a=a b=#1)
(except (lambda [z] (#1 #2)) [.f a]=#1)
(dot (lambda [z] (#1 #2)) g)
(with a)
(parens #1)
(sub Box (lambda [z] (#1 #2)) a)
(tsub Dia a #1)
(fair Weak a (lambda [z] (#1 #2)))
(case (lambda [z] (#1 #2))->a other->#1)
(case #1->(lambda [z] (#1 #2)))
error TlaProofError: Arity mismatch
(f (lambda [z] (#1 #2)) a)
(a #1)
a@3"#;

    const CONS_SHIFT: &str = r#"(g #1)
#4
#5
#6
(g #1)@5
#5@6
#4!
o
$TRUE
"s"
1.5
@true
(lambda [p q] (f #1 #2 (g #3) #6))
(Forall [a:(g #1) b:ditto c] (#1 #3 (g #4) #7))@4
(fcn [a:#4] (#1 (g #2)))
(setof (#2 #1 (g #3)) [a:(g #1) b])
(let [(def A (g #1)) (rec R) (instance I [a b] c<-#1 d<-#4)@9 (bpragma B (#1 #3 (g #4)))] (#1 #4 (g #5) #8))
(sequent [(fresh x (g #1)) (flex v) (defn Hidden (def D (#2 #7))) (fact Hidden #3)@11 (fact Visible #9)@11 (fresh y) (defn Visible (instance I [a b] c<-#1 d<-#4)@9)] (#1 #7 (g #8) #11))
(choose c:(g #1) (#1 (g #2)))
(choose c (g #2))
(setst s:#4 (#1 (g #2) #5))
(tExists [u w] (#1 #2 (g #3)))
(bang (g #1) Down (inst #4) (label L #5) Number)
(if (g #1) #4 #5)
(list And (g #1) #4)
(setenum (g #1) o)
(tuple #4)
(product (g #1) #5)
(arrow (g #1) #4)
(fcnapp (g #1) #4 #5)
(rect a=(g #1))
(record a=#4 b=#5)
(except (g #1) [.f #4]=#5)
(dot (g #1) g)
(with #4)
(parens #5)
(sub Box (g #1) #4)
(tsub Dia #4 #5)
(fair Weak #4 (g #1))
(case (g #1)->#4 other->#5)
(case #5->(g #1))
(g #1 a (g #1))
(f (g #1) #4)
(g #1 #4)
#4@3"#;

    const COMPOSE: &str = r#"#2
#7
#3
#4
#2@5
#3@6
#7!
o
$TRUE
"s"
1.5
@true
(lambda [p q] (f #1 #2 #4 #9))
(Forall [a:#2 b:ditto c] (#1 #3 #5 #10))@4
(fcn [a:#7] (#1 #3))
(setof (#2 #1 #4) [a:#2 b])
(let [(def A #2) (rec R) (instance I [a b] c<-#1 d<-#4)@9 (bpragma B (#1 #3 #5))] (#1 #4 #6 #11))
(sequent [(fresh x #2) (flex v) (defn Hidden (def D (#2 #5))) (fact Hidden #3)@11 (fact Visible #7)@11 (fresh y) (defn Visible (instance I [a b] c<-#1 d<-#4)@9)] (#1 #7 #9 #14))
(choose c:#2 (#1 #3))
(choose c #3)
(setst s:#7 (#1 #3 #8))
(tExists [u w] (#1 #2 #4))
(bang #2 Down (inst #7) (label L #3) Number)
(if #2 #7 #3)
(list And #2 #7)
(setenum #2 o)
(tuple #7)
(product #2 #3)
(arrow #2 #7)
(fcnapp #2 #7 #3)
(rect a=#2)
(record a=#7 b=#3)
(except #2 [.f #7]=#3)
(dot #2 g)
(with #7)
(parens #3)
(sub Box #2 #7)
(tsub Dia #7 #3)
(fair Weak #7 #2)
(case #2->#7 other->#3)
(case #3->#2)
(#2 a #2)
(f #2 #7)
(#2 #7)
#7@3"#;

    const BUMP: &str = r#"#1
#2
#3
#7
#1@5
#3@6
#2!
o
$TRUE
"s"
1.5
@true
(lambda [p q] (f #1 #2 #3 #4))
(Forall [a:#1 b:ditto c] (#1 #3 #4 #5))@4
(fcn [a:#2] (#1 #2))
(setof (#2 #1 #3) [a:#1 b])
(let [(def A #1) (rec R) (instance I [a b] c<-#1 d<-#4)@9 (bpragma B (#1 #3 #4))] (#1 #4 #5 #6))
(sequent [(fresh x #1) (flex v) (defn Hidden (def D (#2 #5))) (fact Hidden #3)@11 (fact Visible #7)@11 (fresh y) (defn Visible (instance I [a b] c<-#1 d<-#4)@9)] (#1 #7 #8 #9))
(choose c:#1 (#1 #2))
(choose c #2)
(setst s:#2 (#1 #2 #3))
(tExists [u w] (#1 #2 #3))
(bang #1 Down (inst #2) (label L #3) Number)
(if #1 #2 #3)
(list And #1 #2)
(setenum #1 o)
(tuple #2)
(product #1 #3)
(arrow #1 #2)
(fcnapp #1 #2 #3)
(rect a=#1)
(record a=#2 b=#3)
(except #1 [.f #2]=#3)
(dot #1 g)
(with #2)
(parens #3)
(sub Box #1 #2)
(tsub Dia #2 #3)
(fair Weak #2 #1)
(case #1->#2 other->#3)
(case #3->#1)
(#1 a #1)
(f #1 #2)
(#1 #2)
#2@3"#;

    const BUMP_CONS: &str = r#"#1
y
x
#0
#1@5
x@6
y!
o
$TRUE
"s"
1.5
@true
(lambda [p q] (f #1 #2 #3 y))
(Forall [a:#1 b:ditto c] (#1 #3 #4 y))@4
(fcn [a:y] (#1 #2))
(setof (#2 #1 #3) [a:#1 b])
(let [(def A #1) (rec R) (instance I [a b] c<-#1 d<-#4)@9 (bpragma B (#1 #3 #4))] (#1 #4 #5 y))
(sequent [(fresh x #1) (flex v) (defn Hidden (def D (#2 x))) (fact Hidden #3)@11 (fact Visible x)@11 (fresh y) (defn Visible (instance I [a b] c<-#1 d<-#4)@9)] (#1 #7 #8 y))
(choose c:#1 (#1 #2))
(choose c #2)
(setst s:y (#1 #2 y))
(tExists [u w] (#1 #2 #3))
(bang #1 Down (inst y) (label L x) Number)
(if #1 y x)
(list And #1 y)
(setenum #1 o)
(tuple y)
(product #1 x)
(arrow #1 y)
(fcnapp #1 y x)
(rect a=#1)
(record a=y b=x)
(except #1 [.f y]=x)
(dot #1 g)
(with y)
(parens x)
(sub Box #1 y)
(tsub Dia y x)
(fair Weak y #1)
(case #1->y other->x)
(case x->#1)
(#1 a #1)
(f #1 y)
(#1 y)
y@3"#;
}
