//! tlapm's E_eq: alpha-equivalence of expressions.
//! A port of `src/obligations/equality.ts`.

use std::collections::HashMap;

use crate::expression::{
    Bound, BoundDomain, Defn, DefnCore, ExceptPoint, Expr, ExprCore, ExprNode, Field, HypCore,
    HypNode, InstanceDefinition, Selector, Sequent,
};

fn is_equal_list<Item>(
    left: &[Item],
    right: &[Item],
    is_equal: impl Fn(&Item, &Item) -> bool,
) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .zip(right)
            .all(|(item, other)| is_equal(item, other))
}

fn is_equal_optional(left: Option<&ExprNode>, right: Option<&ExprNode>) -> bool {
    match (left, right) {
        (Some(left), Some(right)) => is_equal_expr(left, right),
        (left, right) => left.is_none() && right.is_none(),
    }
}

/// The fields as a JavaScript `Map` built from them holds them: each name at its first position,
/// with its last value.
fn get_field_map(fields: &[Field]) -> Vec<(&str, &ExprNode)> {
    let mut entries: Vec<(&str, &ExprNode)> = Vec::new();
    let mut positions = HashMap::new();
    for field in fields {
        match positions.get(field.name.as_str()) {
            Some(&position) => entries[position] = (field.name.as_str(), &*field.value),
            None => {
                positions.insert(field.name.as_str(), entries.len());
                entries.push((field.name.as_str(), &*field.value));
            }
        }
    }
    entries
}

fn is_equal_fields(left: &[Field], right: &[Field]) -> bool {
    let left_map = get_field_map(left);
    let right_map = get_field_map(right);
    if left_map.len() != right_map.len() {
        return false;
    }
    left_map.iter().all(|(name, value)| {
        right_map
            .iter()
            .find(|(other_name, _)| other_name == name)
            .is_some_and(|(_, other)| is_equal_expr(value, other))
    })
}

fn is_equal_bound(left: &Bound, right: &Bound) -> bool {
    left.level == right.level
        && match (&left.domain, &right.domain) {
            (BoundDomain::Domain(left), BoundDomain::Domain(right)) => is_equal_expr(left, right),
            (BoundDomain::NoDomain, BoundDomain::NoDomain)
            | (BoundDomain::Ditto, BoundDomain::Ditto) => true,
            _ => false,
        }
}

fn is_equal_selector(left: &Selector, right: &Selector) -> bool {
    match (left, right) {
        (Selector::Number(left), Selector::Number(right)) => left == right,
        (Selector::Instance(left), Selector::Instance(right)) => {
            is_equal_list(left, right, |left, right| is_equal_expr(left, right))
        }
        (
            Selector::Label {
                label: left_label,
                args: left_args,
            },
            Selector::Label {
                label: right_label,
                args: right_args,
            },
        ) => {
            left_label == right_label
                && is_equal_list(left_args, right_args, |left, right| {
                    is_equal_expr(left, right)
                })
        }
        (Selector::Down, Selector::Down)
        | (Selector::Left, Selector::Left)
        | (Selector::Right, Selector::Right)
        | (Selector::At, Selector::At) => true,
        _ => false,
    }
}

fn is_equal_defn(left: &Defn, right: &Defn) -> bool {
    match (&left.core, &right.core) {
        (DefnCore::Operator { body: left, .. }, DefnCore::Operator { body: right, .. })
        | (DefnCore::Bpragma { body: left, .. }, DefnCore::Bpragma { body: right, .. }) => {
            is_equal_expr(left, right)
        }
        (
            DefnCore::Instance { instance: left, .. },
            DefnCore::Instance {
                instance: right, ..
            },
        ) => {
            let get_substitutions = |instance: &InstanceDefinition| {
                instance
                    .substitutions
                    .iter()
                    .map(|entry| Field {
                        name: entry.name.clone(),
                        value: entry.expression.clone(),
                    })
                    .collect::<Vec<_>>()
            };
            is_equal_list(&left.args, &right.args, |left_arg, right_arg| {
                left_arg == right_arg
            }) && left.module == right.module
                && is_equal_fields(&get_substitutions(left), &get_substitutions(right))
        }
        _ => false,
    }
}

pub fn is_equal_hyp(left: &HypNode, right: &HypNode) -> bool {
    match (&left.core, &right.core) {
        (
            HypCore::Fresh {
                level: left_level,
                shape: left_shape,
                domain: left_domain,
                ..
            },
            HypCore::Fresh {
                level: right_level,
                shape: right_shape,
                domain: right_domain,
                ..
            },
        ) => {
            left_level == right_level
                && left_shape == right_shape
                && is_equal_optional(left_domain.as_deref(), right_domain.as_deref())
        }
        (HypCore::Flex { .. }, HypCore::Flex { .. }) => true,
        (
            HypCore::Defn {
                definition: left_definition,
                is_local: left_is_local,
                ..
            },
            HypCore::Defn {
                definition: right_definition,
                is_local: right_is_local,
                ..
            },
        ) => is_equal_defn(left_definition, right_definition) && left_is_local == right_is_local,
        (
            HypCore::Fact {
                expression: left, ..
            },
            HypCore::Fact {
                expression: right, ..
            },
        ) => is_equal_expr(left, right),
        _ => false,
    }
}

fn is_equal_sequent(left: &Sequent, right: &Sequent) -> bool {
    is_equal_list(&left.context, &right.context, |left, right| {
        is_equal_hyp(left, right)
    }) && is_equal_expr(&left.active, &right.active)
}

fn is_equal_exprs(left: &[Expr], right: &[Expr]) -> bool {
    is_equal_list(left, right, |left, right| is_equal_expr(left, right))
}

/// Alpha-equivalence, including E_eq's quirk of comparing only the first CASE arm.
pub fn is_equal_expr(left: &ExprNode, right: &ExprNode) -> bool {
    if let ExprCore::Parens { expression, .. } = &left.core {
        return is_equal_expr(expression, right);
    }
    if let ExprCore::Parens { expression, .. } = &right.core {
        return is_equal_expr(left, expression);
    }
    match (&left.core, &right.core) {
        (ExprCore::Ix { index: left }, ExprCore::Ix { index: right }) => left == right,
        (ExprCore::Opaque { name: left }, ExprCore::Opaque { name: right }) => left == right,
        (ExprCore::Internal { builtin: left }, ExprCore::Internal { builtin: right }) => {
            left == right
        }
        (
            ExprCore::Lambda {
                params: left_params,
                body: left_body,
            },
            ExprCore::Lambda {
                params: right_params,
                body: right_body,
            },
        ) => left_params.len() == right_params.len() && is_equal_expr(left_body, right_body),
        (
            ExprCore::Apply {
                operator: left_operator,
                args: left_args,
            },
            ExprCore::Apply {
                operator: right_operator,
                args: right_args,
            },
        ) => is_equal_expr(left_operator, right_operator) && is_equal_exprs(left_args, right_args),
        (ExprCore::Sequent { sequent: left }, ExprCore::Sequent { sequent: right }) => {
            is_equal_sequent(left, right)
        }
        (
            ExprCore::Bang {
                expression: left_expression,
                selectors: left_selectors,
            },
            ExprCore::Bang {
                expression: right_expression,
                selectors: right_selectors,
            },
        ) => {
            is_equal_expr(left_expression, right_expression)
                && is_equal_list(left_selectors, right_selectors, is_equal_selector)
        }
        (
            ExprCore::With {
                expression: left, ..
            },
            ExprCore::With {
                expression: right, ..
            },
        ) => is_equal_expr(left, right),
        (
            ExprCore::Let {
                definitions: left_definitions,
                body: left_body,
            },
            ExprCore::Let {
                definitions: right_definitions,
                body: right_body,
            },
        ) => {
            is_equal_list(left_definitions, right_definitions, is_equal_defn)
                && is_equal_expr(left_body, right_body)
        }
        (
            ExprCore::If {
                condition: left_condition,
                consequent: left_consequent,
                alternative: left_alternative,
            },
            ExprCore::If {
                condition: right_condition,
                consequent: right_consequent,
                alternative: right_alternative,
            },
        ) => {
            is_equal_expr(left_condition, right_condition)
                && is_equal_expr(left_consequent, right_consequent)
                && is_equal_expr(left_alternative, right_alternative)
        }
        (
            ExprCore::List {
                bullet: left_bullet,
                items: left_items,
            },
            ExprCore::List {
                bullet: right_bullet,
                items: right_items,
            },
        ) => left_bullet == right_bullet && is_equal_exprs(left_items, right_items),
        (
            ExprCore::Quant {
                quantifier: left_quantifier,
                bounds: left_bounds,
                body: left_body,
            },
            ExprCore::Quant {
                quantifier: right_quantifier,
                bounds: right_bounds,
                body: right_body,
            },
        ) => {
            left_quantifier == right_quantifier
                && is_equal_list(left_bounds, right_bounds, is_equal_bound)
                && is_equal_expr(left_body, right_body)
        }
        (
            ExprCore::Tquant {
                quantifier: left_quantifier,
                names: left_names,
                body: left_body,
            },
            ExprCore::Tquant {
                quantifier: right_quantifier,
                names: right_names,
                body: right_body,
            },
        ) => {
            left_quantifier == right_quantifier
                && is_equal_list(left_names, right_names, |left_name, right_name| {
                    left_name == right_name
                })
                && is_equal_expr(left_body, right_body)
        }
        (
            ExprCore::Choose {
                domain: left_domain,
                body: left_body,
                ..
            },
            ExprCore::Choose {
                domain: right_domain,
                body: right_body,
                ..
            },
        ) => {
            is_equal_optional(left_domain.as_deref(), right_domain.as_deref())
                && is_equal_expr(left_body, right_body)
        }
        (
            ExprCore::SetSt {
                domain: left_domain,
                body: left_body,
                ..
            },
            ExprCore::SetSt {
                domain: right_domain,
                body: right_body,
                ..
            },
        ) => is_equal_expr(left_domain, right_domain) && is_equal_expr(left_body, right_body),
        (
            ExprCore::SetOf {
                element: left_element,
                bounds: left_bounds,
            },
            ExprCore::SetOf {
                element: right_element,
                bounds: right_bounds,
            },
        ) => {
            is_equal_expr(left_element, right_element)
                && is_equal_list(left_bounds, right_bounds, is_equal_bound)
        }
        (ExprCore::SetEnum { elements: left }, ExprCore::SetEnum { elements: right })
        | (ExprCore::Tuple { elements: left }, ExprCore::Tuple { elements: right }) => {
            is_equal_exprs(left, right)
        }
        (
            ExprCore::Arrow {
                domain: left_domain,
                range: left_range,
            },
            ExprCore::Arrow {
                domain: right_domain,
                range: right_range,
            },
        ) => is_equal_expr(left_domain, right_domain) && is_equal_expr(left_range, right_range),
        (
            ExprCore::Fcn {
                bounds: left_bounds,
                body: left_body,
            },
            ExprCore::Fcn {
                bounds: right_bounds,
                body: right_body,
            },
        ) => {
            is_equal_list(left_bounds, right_bounds, is_equal_bound)
                && is_equal_expr(left_body, right_body)
        }
        (
            ExprCore::FcnApp {
                function: left_function,
                args: left_args,
            },
            ExprCore::FcnApp {
                function: right_function,
                args: right_args,
            },
        ) => {
            left_args.len() == right_args.len()
                && is_equal_expr(left_function, right_function)
                && is_equal_exprs(left_args, right_args)
        }
        (ExprCore::Product { factors: left }, ExprCore::Product { factors: right }) => {
            is_equal_exprs(left, right)
        }
        (ExprCore::Rect { fields: left }, ExprCore::Rect { fields: right })
        | (ExprCore::Record { fields: left }, ExprCore::Record { fields: right }) => {
            is_equal_fields(left, right)
        }
        (
            ExprCore::Except {
                function: left_function,
                specs: left_specs,
            },
            ExprCore::Except {
                function: right_function,
                specs: right_specs,
            },
        ) => {
            is_equal_expr(left_function, right_function)
                && is_equal_list(left_specs, right_specs, |left_spec, right_spec| {
                    is_equal_list(
                        &left_spec.trail,
                        &right_spec.trail,
                        |left_point, right_point| match (left_point, right_point) {
                            (ExceptPoint::Dot(left), ExceptPoint::Dot(right)) => left == right,
                            (ExceptPoint::Apply(left), ExceptPoint::Apply(right)) => {
                                is_equal_expr(left, right)
                            }
                            _ => false,
                        },
                    ) && is_equal_expr(&left_spec.value, &right_spec.value)
                })
        }
        (
            ExprCore::Dot {
                expression: left_expression,
                field: left_field,
            },
            ExprCore::Dot {
                expression: right_expression,
                field: right_field,
            },
        ) => is_equal_expr(left_expression, right_expression) && left_field == right_field,
        (
            ExprCore::Sub {
                modal: left_modal,
                action: left_action,
                subscript: left_subscript,
            },
            ExprCore::Sub {
                modal: right_modal,
                action: right_action,
                subscript: right_subscript,
            },
        )
        | (
            ExprCore::Tsub {
                modal: left_modal,
                action: left_action,
                subscript: left_subscript,
            },
            ExprCore::Tsub {
                modal: right_modal,
                action: right_action,
                subscript: right_subscript,
            },
        ) => {
            left_modal == right_modal
                && is_equal_expr(left_action, right_action)
                && is_equal_expr(left_subscript, right_subscript)
        }
        (
            ExprCore::Fair {
                fairness: left_fairness,
                subscript: left_subscript,
                action: left_action,
            },
            ExprCore::Fair {
                fairness: right_fairness,
                subscript: right_subscript,
                action: right_action,
            },
        ) => {
            left_fairness == right_fairness
                && is_equal_expr(left_subscript, right_subscript)
                && is_equal_expr(left_action, right_action)
        }
        (
            ExprCore::Case {
                arms: left_arms,
                other: left_other,
            },
            ExprCore::Case {
                arms: right_arms,
                other: right_other,
            },
        ) => {
            let is_arms_equal = match (left_arms.first(), right_arms.first()) {
                (Some(left_arm), Some(right_arm)) => {
                    is_equal_expr(&left_arm.condition, &right_arm.condition)
                        && is_equal_expr(&left_arm.body, &right_arm.body)
                }
                _ => left_arms.len() == right_arms.len(),
            };
            is_arms_equal && is_equal_optional(left_other.as_deref(), right_other.as_deref())
        }
        (ExprCore::String { value: left }, ExprCore::String { value: right }) => left == right,
        (
            ExprCore::Num {
                integer: left_integer,
                fraction: left_fraction,
            },
            ExprCore::Num {
                integer: right_integer,
                fraction: right_fraction,
            },
        ) => left_integer == right_integer && left_fraction == right_fraction,
        (ExprCore::At { is_except: left }, ExprCore::At { is_except: right }) => left == right,
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expression::{
        Builtin, Bullet, CaseArm, ExceptSpec, Fairness, Hyp, Level, Locus, Modal, Param, ParenForm,
        Quantifier, Substitution, Time, Visibility, WhereDefined, expr, hyp, located,
    };

    fn opaque(name: &str) -> Expr {
        expr(ExprCore::Opaque {
            name: name.to_owned(),
        })
    }

    fn get_x() -> Expr {
        opaque("x")
    }

    fn get_y() -> Expr {
        opaque("y")
    }

    fn apply(args: Vec<Expr>) -> Expr {
        expr(ExprCore::Apply {
            operator: expr(ExprCore::Internal {
                builtin: Builtin::Eq,
            }),
            args,
        })
    }

    fn parens(expression: Expr) -> Expr {
        expr(ExprCore::Parens {
            expression,
            form: ParenForm::Syntax,
        })
    }

    fn index(index: isize) -> Expr {
        expr(ExprCore::Ix { index })
    }

    fn case(arms: Vec<(Expr, Expr)>, other: Option<Expr>) -> Expr {
        expr(ExprCore::Case {
            arms: arms
                .into_iter()
                .map(|(condition, body)| CaseArm { condition, body })
                .collect(),
            other,
        })
    }

    fn get_fields(fields: Vec<(&str, Expr)>) -> Vec<Field> {
        fields
            .into_iter()
            .map(|(name, value)| Field {
                name: name.to_owned(),
                value,
            })
            .collect()
    }

    fn record(fields: Vec<(&str, Expr)>) -> Expr {
        expr(ExprCore::Record {
            fields: get_fields(fields),
        })
    }

    fn lambda(arity: usize, body: Expr) -> Expr {
        expr(ExprCore::Lambda {
            params: (0..arity)
                .map(|position| Param {
                    name: format!("p{position}"),
                    shape: 0,
                    location: None,
                })
                .collect(),
            body,
        })
    }

    fn bound(name: &str, level: Level, domain: BoundDomain) -> Bound {
        Bound {
            name: name.to_owned(),
            level,
            domain,
        }
    }

    fn quant(quantifier: Quantifier, bounds: Vec<Bound>) -> Expr {
        expr(ExprCore::Quant {
            quantifier,
            bounds,
            body: get_x(),
        })
    }

    fn fcn_app(args: Vec<Expr>) -> Expr {
        expr(ExprCore::FcnApp {
            function: get_x(),
            args,
        })
    }

    fn except(trail: Vec<ExceptPoint>) -> Expr {
        expr(ExprCore::Except {
            function: get_x(),
            specs: vec![ExceptSpec {
                trail,
                value: get_x(),
            }],
        })
    }

    fn bang(selectors: Vec<Selector>) -> Expr {
        expr(ExprCore::Bang {
            expression: get_x(),
            selectors,
        })
    }

    fn get_definition(core: DefnCore) -> Defn {
        Defn {
            core,
            location: None,
        }
    }

    fn operator(name: &str) -> Defn {
        get_definition(DefnCore::Operator {
            name: name.to_owned(),
            body: get_x(),
        })
    }

    fn instance(name: &str, module: &str, substitutions: Vec<(&str, Expr)>) -> Defn {
        get_definition(DefnCore::Instance {
            name: name.to_owned(),
            instance: InstanceDefinition {
                args: vec!["p".to_owned()],
                module: module.to_owned(),
                substitutions: substitutions
                    .into_iter()
                    .map(|(name, expression)| Substitution {
                        name: name.to_owned(),
                        expression,
                    })
                    .collect(),
                location: None,
            },
        })
    }

    fn let_in(definition: Defn) -> Expr {
        expr(ExprCore::Let {
            definitions: vec![definition],
            body: get_y(),
        })
    }

    fn choose(name: &str, domain: Option<Expr>) -> Expr {
        expr(ExprCore::Choose {
            name: name.to_owned(),
            domain,
            body: get_y(),
        })
    }

    fn label(value: usize) -> Vec<Selector> {
        vec![
            Selector::Down,
            Selector::Number(value),
            Selector::Label {
                label: "l".to_owned(),
                args: vec![get_y()],
            },
        ]
    }

    fn flex(name: &str) -> Hyp {
        hyp(HypCore::Flex {
            name: name.to_owned(),
        })
    }

    #[test]
    fn compares_expressions_as_the_typescript_does() {
        let at_line = |line| Locus {
            file: "f".into(),
            start_line: line,
            start_column: 1,
            end_line: line,
            end_column: 2,
        };
        let sub = |modal, is_temporal: bool| {
            let (action, subscript) = (get_x(), get_y());
            expr(if is_temporal {
                ExprCore::Tsub {
                    modal,
                    action,
                    subscript,
                }
            } else {
                ExprCore::Sub {
                    modal,
                    action,
                    subscript,
                }
            })
        };
        let fair = || {
            expr(ExprCore::Fair {
                fairness: Fairness::Weak,
                subscript: get_x(),
                action: get_y(),
            })
        };
        let none = || BoundDomain::NoDomain;
        let cases = [
            (
                "opaque same",
                get_x(),
                located(
                    ExprCore::Opaque {
                        name: "x".to_owned(),
                    },
                    Some(at_line(3)),
                ),
                true,
            ),
            ("opaque diff", get_x(), get_y(), false),
            ("ix", index(1), index(1), true),
            ("ix diff", index(1), index(2), false),
            ("parens left", parens(get_x()), get_x(), true),
            ("parens right", get_x(), parens(parens(get_x())), true),
            (
                "apply",
                apply(vec![get_x(), get_y()]),
                apply(vec![get_x(), get_y()]),
                true,
            ),
            (
                "apply arity",
                apply(vec![get_x(), get_y()]),
                apply(vec![get_x()]),
                false,
            ),
            ("kind mismatch", get_x(), index(1), false),
            (
                "lambda names",
                lambda(2, index(1)),
                lambda(2, index(1)),
                true,
            ),
            (
                "lambda arity",
                lambda(2, index(1)),
                lambda(1, index(1)),
                false,
            ),
            (
                "case first arm only",
                case(vec![(get_x(), get_y()), (get_x(), get_x())], None),
                case(vec![(get_x(), get_y()), (get_y(), get_y())], None),
                true,
            ),
            (
                "case arm count with first",
                case(vec![(get_x(), get_y())], None),
                case(vec![(get_x(), get_y()), (get_y(), get_y())], None),
                true,
            ),
            (
                "case empty vs nonempty",
                case(vec![], None),
                case(vec![(get_x(), get_y())], None),
                false,
            ),
            (
                "case other",
                case(vec![(get_x(), get_y())], Some(get_x())),
                case(vec![(get_x(), get_y())], None),
                false,
            ),
            (
                "case other diff",
                case(vec![(get_x(), get_y())], Some(get_x())),
                case(vec![(get_x(), get_y())], Some(get_y())),
                false,
            ),
            (
                "record order",
                record(vec![("a", get_x()), ("b", get_y())]),
                record(vec![("b", get_y()), ("a", get_x())]),
                true,
            ),
            (
                "record dup last wins",
                record(vec![("a", get_y()), ("a", get_x())]),
                record(vec![("a", get_x())]),
                true,
            ),
            (
                "record size",
                record(vec![("a", get_x())]),
                record(vec![("a", get_x()), ("b", get_y())]),
                false,
            ),
            (
                "rect vs record",
                expr(ExprCore::Rect {
                    fields: get_fields(vec![("a", get_x())]),
                }),
                record(vec![("a", get_x())]),
                false,
            ),
            (
                "quant bound names ignored",
                quant(
                    Quantifier::Forall,
                    vec![bound("a", Level::Constant, none())],
                ),
                quant(
                    Quantifier::Forall,
                    vec![bound("b", Level::Constant, none())],
                ),
                true,
            ),
            (
                "quant bound level",
                quant(
                    Quantifier::Forall,
                    vec![bound("a", Level::Constant, none())],
                ),
                quant(Quantifier::Forall, vec![bound("a", Level::State, none())]),
                false,
            ),
            (
                "quant domain",
                quant(
                    Quantifier::Exists,
                    vec![bound(
                        "a",
                        Level::Constant,
                        BoundDomain::Domain(opaque("S")),
                    )],
                ),
                quant(
                    Quantifier::Exists,
                    vec![bound(
                        "a",
                        Level::Constant,
                        BoundDomain::Domain(opaque("T")),
                    )],
                ),
                false,
            ),
            (
                "quant ditto vs none",
                quant(
                    Quantifier::Exists,
                    vec![bound("a", Level::Constant, BoundDomain::Ditto)],
                ),
                quant(
                    Quantifier::Exists,
                    vec![bound("a", Level::Constant, none())],
                ),
                false,
            ),
            (
                "quant quantifier",
                quant(Quantifier::Exists, vec![]),
                quant(Quantifier::Forall, vec![]),
                false,
            ),
            (
                "fcnapp",
                fcn_app(vec![get_y()]),
                fcn_app(vec![get_y()]),
                true,
            ),
            (
                "fcnapp args",
                fcn_app(vec![get_y()]),
                fcn_app(vec![get_y(), get_y()]),
                false,
            ),
            (
                "except",
                except(vec![
                    ExceptPoint::Dot("a".to_owned()),
                    ExceptPoint::Apply(get_y()),
                ]),
                except(vec![
                    ExceptPoint::Dot("a".to_owned()),
                    ExceptPoint::Apply(get_y()),
                ]),
                true,
            ),
            (
                "except trail",
                except(vec![ExceptPoint::Dot("a".to_owned())]),
                except(vec![ExceptPoint::Apply(get_y())]),
                false,
            ),
            ("bang selectors", bang(label(2)), bang(label(2)), true),
            (
                "bang number",
                bang(vec![Selector::Number(2)]),
                bang(vec![Selector::Number(3)]),
                false,
            ),
            (
                "bang kinds",
                bang(vec![Selector::Left]),
                bang(vec![Selector::Right]),
                false,
            ),
            (
                "let operator",
                let_in(operator("a")),
                let_in(operator("b")),
                true,
            ),
            (
                "let recursive never equal",
                let_in(get_definition(DefnCore::Recursive {
                    name: "a".to_owned(),
                    shape: 0,
                })),
                let_in(get_definition(DefnCore::Recursive {
                    name: "a".to_owned(),
                    shape: 0,
                })),
                false,
            ),
            (
                "let instance",
                let_in(instance("I", "M", vec![("c", get_x()), ("d", get_y())])),
                let_in(instance("J", "M", vec![("d", get_y()), ("c", get_x())])),
                true,
            ),
            (
                "let instance module",
                let_in(instance("I", "M", vec![])),
                let_in(instance("I", "N", vec![])),
                false,
            ),
            (
                "string",
                expr(ExprCore::String {
                    value: "é".to_owned(),
                }),
                expr(ExprCore::String {
                    value: "é".to_owned(),
                }),
                true,
            ),
            (
                "num",
                expr(ExprCore::Num {
                    integer: "1".to_owned(),
                    fraction: "5".to_owned(),
                }),
                expr(ExprCore::Num {
                    integer: "1".to_owned(),
                    fraction: String::new(),
                }),
                false,
            ),
            (
                "at",
                expr(ExprCore::At { is_except: true }),
                expr(ExprCore::At { is_except: false }),
                false,
            ),
            (
                "choose domain",
                choose("a", Some(get_x())),
                choose("b", None),
                false,
            ),
            ("choose none", choose("a", None), choose("b", None), true),
            (
                "tquant names",
                expr(ExprCore::Tquant {
                    quantifier: Quantifier::Forall,
                    names: vec!["v".to_owned()],
                    body: get_x(),
                }),
                expr(ExprCore::Tquant {
                    quantifier: Quantifier::Forall,
                    names: vec!["w".to_owned()],
                    body: get_x(),
                }),
                false,
            ),
            (
                "sub modal",
                sub(Modal::Box, false),
                sub(Modal::Dia, false),
                false,
            ),
            (
                "sub vs tsub",
                sub(Modal::Box, false),
                sub(Modal::Box, true),
                false,
            ),
            ("fair", fair(), fair(), true),
            (
                "dot field",
                expr(ExprCore::Dot {
                    expression: get_x(),
                    field: "a".to_owned(),
                }),
                expr(ExprCore::Dot {
                    expression: get_x(),
                    field: "b".to_owned(),
                }),
                false,
            ),
            (
                "setenum vs tuple",
                expr(ExprCore::SetEnum {
                    elements: vec![get_x()],
                }),
                expr(ExprCore::Tuple {
                    elements: vec![get_x()],
                }),
                false,
            ),
            (
                "list bullet",
                expr(ExprCore::List {
                    bullet: Bullet::And,
                    items: vec![get_x()],
                }),
                expr(ExprCore::List {
                    bullet: Bullet::Or,
                    items: vec![get_x()],
                }),
                false,
            ),
            (
                "sequent",
                expr(ExprCore::Sequent {
                    sequent: Sequent {
                        context: vec![flex("v")],
                        active: get_x(),
                    },
                }),
                expr(ExprCore::Sequent {
                    sequent: Sequent {
                        context: vec![flex("w")],
                        active: get_x(),
                    },
                }),
                true,
            ),
        ];
        for (label, left, right, expected) in cases {
            assert_eq!(is_equal_expr(&left, &right), expected, "{label}");
        }
    }

    #[test]
    fn compares_hypotheses_as_the_typescript_does() {
        let fresh = |name: &str, shape, domain| {
            hyp(HypCore::Fresh {
                name: name.to_owned(),
                shape,
                level: Level::Constant,
                domain,
                domain_visibility: Visibility::Visible,
            })
        };
        let definition = |definition, is_local| {
            hyp(HypCore::Defn {
                definition,
                where_defined: WhereDefined::User,
                visibility: Visibility::Visible,
                is_local,
                is_constness_unset: false,
            })
        };
        let fact = |visibility| {
            hyp(HypCore::Fact {
                expression: get_x(),
                visibility,
                time: Time::Now,
                use_location: None,
            })
        };
        let cases = [
            ("fresh", fresh("a", 0, None), fresh("b", 0, None), true),
            (
                "fresh shape",
                fresh("a", 0, None),
                fresh("a", 1, None),
                false,
            ),
            (
                "fresh domain",
                fresh("a", 0, Some(get_x())),
                fresh("a", 0, None),
                false,
            ),
            ("flex", flex("a"), flex("b"), true),
            (
                "defn local",
                definition(operator("a"), true),
                definition(operator("a"), false),
                false,
            ),
            (
                "defn",
                definition(operator("a"), true),
                definition(operator("b"), true),
                true,
            ),
            (
                "fact",
                fact(Visibility::Visible),
                fact(Visibility::Hidden),
                true,
            ),
            ("fact vs flex", fact(Visibility::Visible), flex("x"), false),
        ];
        for (label, left, right, expected) in cases {
            assert_eq!(is_equal_hyp(&left, &right), expected, "{label}");
        }
    }
}
