//! What the model section of the IR reads of a spec before the search: the scopes an instance's
//! definitions are read in, and a formula's level, as `liveness.ts`'s `getLevel` computes it.

use std::rc::Rc;

use crate::ast::*;
use crate::dependencies::{DefinitionFacts, Level};
use crate::environment::Environment;
use crate::instances::map_children;
use crate::resolve::Tables;

/// `Scope`: a name bound to an expression or an operator, in front of the scope it extends. The
/// front end evaluates nothing, so it holds no value.
pub struct Scope {
    pub name: Name,
    pub binding: Binding,
    pub parent: Option<Rc<Scope>>,
}

pub enum Binding {
    /// `Thunk`: an expression read in its own scope.
    Thunk {
        expression: Expr,
        scope: Option<Rc<Scope>>,
    },
    /// An operator `Closure`.
    Closure {
        name: Name,
        params: Vec<OperatorParam>,
        body: Expr,
        scope: Option<Rc<Scope>>,
    },
}

/// `lookupScope`.
pub fn lookup_scope<'a>(mut scope: Option<&'a Rc<Scope>>, name: &str) -> Option<&'a Binding> {
    while let Some(current) = scope {
        if &*current.name == name {
            return Some(&current.binding);
        }
        scope = current.parent.as_ref();
    }
    None
}

/// `getDefinition`: a definition by name, through the model's substitutions.
pub fn get_definition<'a>(name: &str, environment: &'a Environment) -> Option<&'a Rc<Definition>> {
    let key = environment
        .substitutions
        .get(name)
        .map_or(name, |key| &**key);
    environment.definitions.get(key)
}

/// `getLevel` (`liveness.ts`): the level of a formula read in a scope, with the names a binder in
/// it shadows read as constants.
pub fn get_level(
    expression: &Expr,
    scope: Option<&Rc<Scope>>,
    environment: &Environment,
    facts: &DefinitionFacts,
    shadowed: &[Name],
) -> Level {
    let get_binding_level = |name: &str| {
        Some(match lookup_scope(scope, name)? {
            Binding::Thunk { expression, scope } => {
                get_level(expression, scope.as_ref(), environment, facts, &[])
            }
            Binding::Closure { body, scope, .. } => {
                get_level(body, scope.as_ref(), environment, facts, &[])
            }
        })
    };
    let get_global_level = |name: &str| {
        if environment.variable_index.contains_key(name) {
            return Some(Level::Variable);
        }
        if environment.constants.contains_key(name) {
            return Some(Level::Constant);
        }
        if let Some(definition) = get_definition(name, environment) {
            return Some(facts.get_definition_level(definition, environment));
        }
        let key = environment
            .substitutions
            .get(name)
            .map_or(name, |key| &**key);
        let builtin = environment.builtins.get(key)?;
        Some(if builtin.flags & 1 != 0 && builtin.flags & 2 == 0 {
            Level::Variable
        } else {
            Level::Constant
        })
    };
    let get_name_level = |node: &Expr| {
        let name = node.reference().unwrap_or_default();
        if shadowed.contains(&name) {
            return Level::Constant;
        }
        if node.is_locally_resolved() {
            get_binding_level(&name)
                .or_else(|| get_global_level(&name))
                .unwrap_or(Level::Constant)
        } else {
            get_global_level(&name)
                .or_else(|| get_binding_level(&name))
                .unwrap_or(Level::Constant)
        }
    };
    let get_children_level = |node: &Expr| {
        let mut level = Level::Constant;
        let tables = Tables::default();
        let _ = map_children(node, &tables, &mut |child, bound| {
            let child_level = if bound.is_empty() {
                get_level(child, scope, environment, facts, shadowed)
            } else {
                let shadowed: Vec<Name> = shadowed.iter().chain(bound).cloned().collect();
                get_level(child, scope, environment, facts, &shadowed)
            };
            level = level.max(child_level);
            Ok(child.clone())
        });
        level
    };
    match &expression.kind {
        ExpressionKind::Prime(_) | ExpressionKind::Unchanged(_) | ExpressionKind::Action { .. } => {
            Level::Action
        }
        ExpressionKind::Enabled(_) => Level::Variable,
        ExpressionKind::Always(_)
        | ExpressionKind::Eventually(_)
        | ExpressionKind::Fairness { .. } => Level::Temporal,
        ExpressionKind::UnboundedQuantifier {
            is_temporal: true, ..
        } => Level::Temporal,
        ExpressionKind::Identifier { .. } | ExpressionKind::OperatorReference { .. } => {
            get_name_level(expression)
        }
        ExpressionKind::Apply { operator, .. } => match &**operator {
            "~>" | "-+->" => Level::Temporal,
            "\\cdot" => Level::Action,
            _ => get_name_level(expression).max(get_children_level(expression)),
        },
        _ => get_children_level(expression),
    }
}
