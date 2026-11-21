//! Conservative positive proof that a call graph contains no operator-valued binding.
use crate::ast::{Definition, DefinitionKind, Expr, ExpressionKind, Name};
use crate::environment::Environment;
use crate::spec::get_definition;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

enum Work {
    Expression(Expr, Vec<Name>),
    Leave(*const Definition),
    LeaveExpression(*const crate::ast::Expression, Vec<Name>),
}

/// Unknown lexical, substitution, instance, selector and recursive paths return true.
pub(crate) fn may_use_operator_values(expression: &Expr, environment: &Environment) -> bool {
    let mut pending = vec![Work::Expression(expression.clone(), Vec::new())];
    let mut active = HashSet::new();
    let mut complete = HashSet::new();
    let mut expressions: HashMap<(*const crate::ast::Expression, Vec<Name>), (Expr, bool)> =
        HashMap::new();
    while let Some(item) = pending.pop() {
        let (node, bound) = match item {
            Work::Leave(key) => {
                active.remove(&key);
                complete.insert(key);
                continue;
            }
            Work::LeaveExpression(key, bound) => {
                if let Some(entry) = expressions.get_mut(&(key, bound)) {
                    entry.1 = true;
                }
                continue;
            }
            Work::Expression(node, bound) => (node, bound),
        };
        let identity = (Rc::as_ptr(&node), bound.clone());
        if let Some((held, complete)) = expressions.get(&identity) {
            if !Rc::ptr_eq(held, &node) || !*complete {
                return true;
            }
            continue;
        }
        expressions.insert(identity.clone(), (node.clone(), false));
        pending.push(Work::LeaveExpression(identity.0, identity.1));
        if environment.tables.is_substitution(&node) || environment.tables.is_selection(&node) {
            return true;
        }
        match &node.kind {
            ExpressionKind::Identifier {
                selector_ranges: Some(_),
                ..
            }
            | ExpressionKind::Apply {
                selector_ranges: Some(_),
                ..
            }
            | ExpressionKind::Apply {
                argument_counts: Some(_),
                ..
            } => return true,
            _ => {}
        }
        match &node.kind {
            ExpressionKind::Number { .. }
            | ExpressionKind::Decimal { .. }
            | ExpressionKind::String { .. } => {}
            ExpressionKind::Identifier { .. } if node.is_locally_resolved() => {
                if !node.reference().is_some_and(|name| bound.contains(&name)) {
                    return true;
                }
            }
            ExpressionKind::Apply { .. } if node.is_locally_resolved() => return true,
            ExpressionKind::Identifier { .. } | ExpressionKind::Apply { .. } => {
                let Some(name) = node.reference() else {
                    return true;
                };
                let target = environment.substitutions.get(&name).unwrap_or(&name);
                if target != &name && environment.substitutions.contains_key(target) {
                    return true;
                }
                if let Some(definition) = get_definition(&name, environment) {
                    let key = Rc::as_ptr(definition);
                    if active.contains(&key) {
                        return true;
                    }
                    if definition.is_recursive {
                        return true;
                    }
                    let DefinitionKind::Operator { params, .. } = &definition.kind else {
                        return true;
                    };
                    let argument_count = match &node.kind {
                        ExpressionKind::Identifier { .. } => 0,
                        ExpressionKind::Apply { args, .. } => args.len(),
                        _ => return true,
                    };
                    if params.len() != argument_count
                        || params.iter().any(|parameter| parameter.arity != 0)
                    {
                        return true;
                    }
                    if !complete.contains(&key) {
                        let mut formal = params
                            .iter()
                            .map(|parameter| parameter.name.clone())
                            .collect::<Vec<_>>();
                        formal.sort();
                        formal.dedup();
                        active.insert(key);
                        pending.push(Work::Leave(key));
                        pending.push(Work::Expression(definition.body.clone(), formal));
                    }
                } else if !environment.variable_index.contains_key(target)
                    && !environment.constants.contains_key(target)
                    && !environment.builtins.contains_key(target)
                {
                    return true;
                }
            }
            ExpressionKind::OperatorReference { .. }
            | ExpressionKind::Lambda { .. }
            | ExpressionKind::Let { .. }
            | ExpressionKind::Subexpression { .. }
            | ExpressionKind::ExceptAt
            | ExpressionKind::Label { .. } => return true,
            ExpressionKind::Fairness {
                enabled: Some(_), ..
            } => return true,
            ExpressionKind::Junction { .. }
            | ExpressionKind::Prime(_)
            | ExpressionKind::Unchanged(_)
            | ExpressionKind::Enabled(_)
            | ExpressionKind::Always(_)
            | ExpressionKind::Eventually(_)
            | ExpressionKind::If { .. }
            | ExpressionKind::Case { .. }
            | ExpressionKind::Quantified { .. }
            | ExpressionKind::UnboundedQuantifier { .. }
            | ExpressionKind::Choose { .. }
            | ExpressionKind::SetEnumeration(_)
            | ExpressionKind::SetFilter { .. }
            | ExpressionKind::SetMap { .. }
            | ExpressionKind::Tuple(_)
            | ExpressionKind::FunctionConstruction { .. }
            | ExpressionKind::FunctionSet { .. }
            | ExpressionKind::Record { .. }
            | ExpressionKind::Except { .. }
            | ExpressionKind::FunctionApplication { .. }
            | ExpressionKind::Bracket(_)
            | ExpressionKind::FieldAccess { .. }
            | ExpressionKind::Product(_)
            | ExpressionKind::Action { .. }
            | ExpressionKind::Fairness { enabled: None, .. } => {}
        }
        let result =
            crate::instances::map_children(&node, &environment.tables, &mut |child, names| {
                let mut next = bound.clone();
                next.extend(names.iter().cloned());
                next.sort();
                next.dedup();
                pending.push(Work::Expression(child.clone(), next));
                Ok(child.clone())
            });
        if result.is_err() {
            return true;
        }
    }
    false
}
